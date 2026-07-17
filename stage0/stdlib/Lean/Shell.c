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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getOptionOverrides___boxed(lean_object* v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = lean_internal_get_option_overrides(v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_505_);
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
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1(void){
_start:
{
lean_object* v___x_524_; uint32_t v___x_525_; uint32_t v___x_526_; uint8_t v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_524_ = lean_box(0);
v___x_525_ = l___private_Lean_Shell_0__Lean_defaultNumThreads;
v___x_526_ = l___private_Lean_Shell_0__Lean_defaultTrustLevel;
v___x_527_ = 0;
v___x_528_ = 0;
v___x_529_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0));
v___x_530_ = l_Lean_Options_empty;
v___x_531_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_529_);
lean_ctor_set(v___x_531_, 2, v___x_530_);
lean_ctor_set(v___x_531_, 3, v___x_524_);
lean_ctor_set(v___x_531_, 4, v___x_524_);
lean_ctor_set(v___x_531_, 5, v___x_524_);
lean_ctor_set(v___x_531_, 6, v___x_524_);
lean_ctor_set(v___x_531_, 7, v___x_524_);
lean_ctor_set(v___x_531_, 8, v___x_524_);
lean_ctor_set(v___x_531_, 9, v___x_529_);
lean_ctor_set(v___x_531_, 10, v___x_524_);
lean_ctor_set(v___x_531_, 11, v___x_524_);
lean_ctor_set(v___x_531_, 12, v___x_524_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*13 + 8, v___x_528_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*13 + 9, v___x_527_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*13 + 10, v___x_527_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*13 + 11, v___x_527_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*13 + 12, v___x_527_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*13 + 13, v___x_527_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*13 + 14, v___x_527_);
lean_ctor_set_uint32(v___x_531_, sizeof(void*)*13, v___x_526_);
lean_ctor_set_uint32(v___x_531_, sizeof(void*)*13 + 4, v___x_525_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*13 + 15, v___x_527_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*13 + 16, v___x_527_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*13 + 17, v___x_527_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object* v_x_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1);
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
lean_object* v_startInclusive_614_; lean_object* v_endExclusive_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_startInclusive_614_ = lean_ctor_get(v___x_610_, 1);
v_endExclusive_615_ = lean_ctor_get(v___x_610_, 2);
v___x_616_ = lean_nat_sub(v_endExclusive_615_, v_startInclusive_614_);
v___x_617_ = lean_nat_dec_eq(v_a_612_, v___x_616_);
lean_dec(v___x_616_);
if (v___x_617_ == 0)
{
uint32_t v___x_618_; uint32_t v___x_619_; uint8_t v___x_620_; 
v___x_618_ = lean_string_utf8_get_fast(v_arg_611_, v_a_612_);
v___x_619_ = 61;
v___x_620_ = lean_uint32_dec_eq(v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_box(0);
v___x_622_ = lean_string_utf8_next_fast(v_arg_611_, v_a_612_);
lean_dec(v_a_612_);
v_a_612_ = v___x_622_;
v_b_613_ = v___x_621_;
goto _start;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v_a_612_);
return v___x_624_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(lean_object* v___x_625_, lean_object* v_arg_626_, lean_object* v_a_627_, lean_object* v_b_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_625_, v_arg_626_, v_a_627_, v_b_628_);
lean_dec(v_b_628_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v___x_625_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption(lean_object* v_opts_633_, lean_object* v_arg_634_){
_start:
{
lean_object* v___y_637_; lean_object* v_searcher_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_searcher_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_string_utf8_byte_size(v_arg_634_);
lean_inc_ref(v_arg_634_);
v___x_670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_670_, 0, v_arg_634_);
lean_ctor_set(v___x_670_, 1, v_searcher_668_);
lean_ctor_set(v___x_670_, 2, v___x_669_);
v___x_671_ = lean_box(0);
v___x_672_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_670_, v_arg_634_, v_searcher_668_, v___x_671_);
lean_dec_ref_known(v___x_670_, 3);
if (lean_obj_tag(v___x_672_) == 0)
{
v___y_637_ = v___x_669_;
goto v___jp_636_;
}
else
{
lean_object* v_val_673_; 
v_val_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_val_673_);
lean_dec_ref_known(v___x_672_, 1);
v___y_637_ = v_val_673_;
goto v___jp_636_;
}
v___jp_636_:
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_string_utf8_byte_size(v_arg_634_);
v___x_639_ = lean_nat_dec_eq(v___y_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_657_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_657_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_657_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_657_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_name_648_; lean_object* v_val_649_; lean_object* v___x_650_; 
v___x_645_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_637_);
lean_inc_ref(v_arg_634_);
v___x_646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_646_, 0, v_arg_634_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
lean_ctor_set(v___x_646_, 2, v___y_637_);
v___x_647_ = lean_string_utf8_next_fast(v_arg_634_, v___y_637_);
lean_dec(v___y_637_);
v_name_648_ = l_String_Slice_toName(v___x_646_);
lean_dec_ref_known(v___x_646_, 3);
v_val_649_ = lean_string_utf8_extract(v_arg_634_, v___x_647_, v___x_638_);
lean_dec_ref(v_arg_634_);
v___x_650_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_641_, v_name_648_);
lean_dec(v_a_641_);
if (lean_obj_tag(v___x_650_) == 1)
{
lean_object* v_val_651_; lean_object* v___x_652_; 
lean_del_object(v___x_643_);
v_val_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = l_Lean_Language_Lean_setOption(v_opts_633_, v_val_651_, v_name_648_, v_val_649_);
return v___x_652_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_655_; 
lean_dec(v___x_650_);
v___x_653_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(v_opts_633_, v_name_648_, v_val_649_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_653_);
v___x_655_ = v___x_643_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
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
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec(v___y_637_);
lean_dec_ref(v_arg_634_);
lean_dec_ref(v_opts_633_);
v_a_658_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_640_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_640_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec(v___y_637_);
lean_dec_ref(v_arg_634_);
lean_dec_ref(v_opts_633_);
v___x_666_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_setConfigOption___closed__1));
v___x_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___boxed(lean_object* v_opts_674_, lean_object* v_arg_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_opts_674_, v_arg_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object* v___x_678_, lean_object* v_arg_679_, lean_object* v_inst_680_, lean_object* v_R_681_, lean_object* v_a_682_, lean_object* v_b_683_, lean_object* v_c_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_678_, v_arg_679_, v_a_682_, v_b_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object* v___x_686_, lean_object* v_arg_687_, lean_object* v_inst_688_, lean_object* v_R_689_, lean_object* v_a_690_, lean_object* v_b_691_, lean_object* v_c_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(v___x_686_, v_arg_687_, v_inst_688_, v_R_689_, v_a_690_, v_b_691_, v_c_692_);
lean_dec(v_b_691_);
lean_dec_ref(v_arg_687_);
lean_dec_ref(v___x_686_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(lean_object* v_msg_695_){
_start:
{
lean_object* v___f_697_; lean_object* v___x_698_; 
v___f_697_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_698_ = l_IO_eprint___redArg(v___f_697_, v_msg_695_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_714_; 
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v___x_698_, 0);
lean_dec(v_unused_715_);
v___x_708_ = v___x_698_;
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
else
{
lean_dec(v___x_698_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_box(0);
if (v_isShared_709_ == 0)
{
lean_ctor_set_tag(v___x_708_, 0);
lean_ctor_set(v___x_708_, 0, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(lean_object* v_msg_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(v_msg_716_);
return v_res_718_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_721_; lean_object* v___x_722_; 
v___x_721_ = 1;
v___x_722_ = lean_box_uint32(v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(lean_object* v_x_723_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = lean_apply_1(v_x_723_, lean_box(0));
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_746_; lean_object* v___f_747_; lean_object* v___x_748_; 
v_a_741_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_732_, 1);
v___x_746_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_747_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_748_ = l_IO_eprint___redArg(v___f_747_, v___x_746_);
lean_dec_ref(v___x_748_);
goto v___jp_742_;
v___jp_742_:
{
lean_object* v___x_743_; lean_object* v___f_744_; lean_object* v___x_745_; 
v___x_743_ = lean_io_error_to_string(v_a_741_);
v___f_744_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_745_ = l_IO_eprint___redArg(v___f_744_, v___x_743_);
lean_dec_ref(v___x_745_);
goto v___jp_728_;
}
}
v___jp_725_:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
v___jp_728_:
{
lean_object* v___x_729_; lean_object* v___f_730_; lean_object* v___x_731_; 
v___x_729_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_730_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_731_ = l_IO_eprint___redArg(v___f_730_, v___x_729_);
lean_dec_ref(v___x_731_);
goto v___jp_725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed(lean_object* v_x_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(v_x_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(lean_object* v_00_u03b1_752_, lean_object* v_x_753_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = lean_apply_1(v_x_753_, lean_box(0));
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_776_; lean_object* v___f_777_; lean_object* v___x_778_; 
v_a_771_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_762_, 1);
v___x_776_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_777_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_778_ = l_IO_eprint___redArg(v___f_777_, v___x_776_);
lean_dec_ref(v___x_778_);
goto v___jp_772_;
v___jp_772_:
{
lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___x_775_; 
v___x_773_ = lean_io_error_to_string(v_a_771_);
v___f_774_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_775_ = l_IO_eprint___redArg(v___f_774_, v___x_773_);
lean_dec_ref(v___x_775_);
goto v___jp_758_;
}
}
v___jp_755_:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
v___jp_758_:
{
lean_object* v___x_759_; lean_object* v___f_760_; lean_object* v___x_761_; 
v___x_759_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_760_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_761_ = l_IO_eprint___redArg(v___f_760_, v___x_759_);
lean_dec_ref(v___x_761_);
goto v___jp_755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___boxed(lean_object* v_00_u03b1_779_, lean_object* v_x_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(v_00_u03b1_779_, v_x_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(lean_object* v_opt_785_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___f_794_; lean_object* v___x_795_; 
v___x_790_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0));
v___x_791_ = lean_string_append(v___x_790_, v_opt_785_);
v___x_792_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_793_ = lean_string_append(v___x_791_, v___x_792_);
v___f_794_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_795_ = l_IO_eprint___redArg(v___f_794_, v___x_793_);
lean_dec_ref(v___x_795_);
goto v___jp_787_;
v___jp_787_:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___boxed(lean_object* v_opt_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(v_opt_796_);
lean_dec_ref(v_opt_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(lean_object* v_opt_801_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___f_810_; lean_object* v___x_811_; 
v___x_806_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0));
v___x_807_ = lean_string_append(v___x_806_, v_opt_801_);
v___x_808_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1));
v___x_809_ = lean_string_append(v___x_807_, v___x_808_);
v___f_810_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_811_ = l_IO_eprint___redArg(v___f_810_, v___x_809_);
lean_dec_ref(v___x_811_);
goto v___jp_803_;
v___jp_803_:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___boxed(lean_object* v_opt_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(v_opt_812_);
lean_dec_ref(v_opt_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(lean_object* v_s_815_){
_start:
{
lean_object* v___x_817_; lean_object* v_putStr_818_; lean_object* v___x_819_; 
v___x_817_ = lean_get_stderr();
v_putStr_818_ = lean_ctor_get(v___x_817_, 4);
lean_inc_ref(v_putStr_818_);
lean_dec_ref(v___x_817_);
v___x_819_ = lean_apply_2(v_putStr_818_, v_s_815_, lean_box(0));
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0___boxed(lean_object* v_s_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v_s_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(lean_object* v_s_823_){
_start:
{
lean_object* v___x_825_; lean_object* v_putStr_826_; lean_object* v___x_827_; 
v___x_825_ = lean_get_stdout();
v_putStr_826_ = lean_ctor_get(v___x_825_, 4);
lean_inc_ref(v_putStr_826_);
lean_dec_ref(v___x_825_);
v___x_827_ = lean_apply_2(v_putStr_826_, v_s_823_, lean_box(0));
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5___boxed(lean_object* v_s_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v_s_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object* v_s_831_){
_start:
{
uint32_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = 10;
v___x_834_ = lean_string_push(v_s_831_, v___x_833_);
v___x_835_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3___boxed(lean_object* v_s_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_s_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(lean_object* v_o_839_, lean_object* v_k_840_, uint8_t v_v_841_){
_start:
{
lean_object* v_map_842_; uint8_t v_hasTrace_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_857_; 
v_map_842_ = lean_ctor_get(v_o_839_, 0);
v_hasTrace_843_ = lean_ctor_get_uint8(v_o_839_, sizeof(void*)*1);
v_isSharedCheck_857_ = !lean_is_exclusive(v_o_839_);
if (v_isSharedCheck_857_ == 0)
{
v___x_845_ = v_o_839_;
v_isShared_846_ = v_isSharedCheck_857_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_map_842_);
lean_dec(v_o_839_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_857_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_847_, 0, v_v_841_);
lean_inc(v_k_840_);
v___x_848_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_840_, v___x_847_, v_map_842_);
if (v_hasTrace_843_ == 0)
{
lean_object* v___x_849_; uint8_t v___x_850_; lean_object* v___x_852_; 
v___x_849_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_850_ = l_Lean_Name_isPrefixOf(v___x_849_, v_k_840_);
lean_dec(v_k_840_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_848_);
v___x_852_ = v___x_845_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_848_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*1, v___x_850_);
return v___x_852_;
}
}
else
{
lean_object* v___x_855_; 
lean_dec(v_k_840_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_848_);
v___x_855_ = v___x_845_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_856_, sizeof(void*)*1, v_hasTrace_843_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1___boxed(lean_object* v_o_858_, lean_object* v_k_859_, lean_object* v_v_860_){
_start:
{
uint8_t v_v_boxed_861_; lean_object* v_res_862_; 
v_v_boxed_861_ = lean_unbox(v_v_860_);
v_res_862_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_o_858_, v_k_859_, v_v_boxed_861_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object* v_opts_863_, lean_object* v_opt_864_, uint8_t v_val_865_){
_start:
{
lean_object* v_name_866_; lean_object* v___x_867_; 
v_name_866_ = lean_ctor_get(v_opt_864_, 0);
lean_inc(v_name_866_);
lean_dec_ref(v_opt_864_);
v___x_867_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_opts_863_, v_name_866_, v_val_865_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object* v_opts_868_, lean_object* v_opt_869_, lean_object* v_val_870_){
_start:
{
uint8_t v_val_boxed_871_; lean_object* v_res_872_; 
v_val_boxed_871_ = lean_unbox(v_val_870_);
v_res_872_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_opts_868_, v_opt_869_, v_val_boxed_871_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(lean_object* v_o_873_, lean_object* v_k_874_, lean_object* v_v_875_){
_start:
{
lean_object* v_map_876_; uint8_t v_hasTrace_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_891_; 
v_map_876_ = lean_ctor_get(v_o_873_, 0);
v_hasTrace_877_ = lean_ctor_get_uint8(v_o_873_, sizeof(void*)*1);
v_isSharedCheck_891_ = !lean_is_exclusive(v_o_873_);
if (v_isSharedCheck_891_ == 0)
{
v___x_879_ = v_o_873_;
v_isShared_880_ = v_isSharedCheck_891_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_map_876_);
lean_dec(v_o_873_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_891_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_881_, 0, v_v_875_);
lean_inc(v_k_874_);
v___x_882_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_874_, v___x_881_, v_map_876_);
if (v_hasTrace_877_ == 0)
{
lean_object* v___x_883_; uint8_t v___x_884_; lean_object* v___x_886_; 
v___x_883_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_884_ = l_Lean_Name_isPrefixOf(v___x_883_, v_k_874_);
lean_dec(v_k_874_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_882_);
v___x_886_ = v___x_879_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_882_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*1, v___x_884_);
return v___x_886_;
}
}
else
{
lean_object* v___x_889_; 
lean_dec(v_k_874_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_882_);
v___x_889_ = v___x_879_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_890_, sizeof(void*)*1, v_hasTrace_877_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object* v_opts_892_, lean_object* v_opt_893_, lean_object* v_val_894_){
_start:
{
lean_object* v_name_895_; lean_object* v___x_896_; 
v_name_895_ = lean_ctor_get(v_opt_893_, 0);
lean_inc(v_name_895_);
lean_dec_ref(v_opt_893_);
v___x_896_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(v_opts_892_, v_name_895_, v_val_894_);
return v___x_896_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = l_System_Platform_numBits;
v___x_926_ = lean_unsigned_to_nat(2u);
v___x_927_ = lean_nat_pow(v___x_926_, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1(void){
_start:
{
uint32_t v___x_937_; lean_object* v___x_938_; 
v___x_937_ = 0;
v___x_938_ = lean_box_uint32(v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object* v_opts_939_, uint32_t v_opt_940_, lean_object* v_optArg_x3f_941_){
_start:
{
lean_object* v___y_1055_; lean_object* v___y_1101_; uint32_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = 101;
v___x_1162_ = lean_uint32_dec_eq(v_opt_940_, v___x_1161_);
if (v___x_1162_ == 0)
{
uint32_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = 106;
v___x_1164_ = lean_uint32_dec_eq(v_opt_940_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint32_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = 118;
v___x_1166_ = lean_uint32_dec_eq(v_opt_940_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint32_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = 86;
v___x_1168_ = lean_uint32_dec_eq(v_opt_940_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint32_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = 103;
v___x_1170_ = lean_uint32_dec_eq(v_opt_940_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint32_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = 104;
v___x_1172_ = lean_uint32_dec_eq(v_opt_940_, v___x_1171_);
if (v___x_1172_ == 0)
{
uint32_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 102;
v___x_1174_ = lean_uint32_dec_eq(v_opt_940_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint32_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = 99;
v___x_1176_ = lean_uint32_dec_eq(v_opt_940_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint32_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = 98;
v___x_1178_ = lean_uint32_dec_eq(v_opt_940_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint32_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = 115;
v___x_1180_ = lean_uint32_dec_eq(v_opt_940_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint32_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = 73;
v___x_1182_ = lean_uint32_dec_eq(v_opt_940_, v___x_1181_);
if (v___x_1182_ == 0)
{
uint32_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = 114;
v___x_1184_ = lean_uint32_dec_eq(v_opt_940_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint32_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = 111;
v___x_1186_ = lean_uint32_dec_eq(v_opt_940_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint32_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = 105;
v___x_1188_ = lean_uint32_dec_eq(v_opt_940_, v___x_1187_);
if (v___x_1188_ == 0)
{
uint32_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = 82;
v___x_1190_ = lean_uint32_dec_eq(v_opt_940_, v___x_1189_);
if (v___x_1190_ == 0)
{
uint32_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = 77;
v___x_1192_ = lean_uint32_dec_eq(v_opt_940_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint32_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = 84;
v___x_1194_ = lean_uint32_dec_eq(v_opt_940_, v___x_1193_);
if (v___x_1194_ == 0)
{
uint32_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = 116;
v___x_1196_ = lean_uint32_dec_eq(v_opt_940_, v___x_1195_);
if (v___x_1196_ == 0)
{
uint32_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = 113;
v___x_1198_ = lean_uint32_dec_eq(v_opt_940_, v___x_1197_);
if (v___x_1198_ == 0)
{
uint32_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 100;
v___x_1200_ = lean_uint32_dec_eq(v_opt_940_, v___x_1199_);
if (v___x_1200_ == 0)
{
uint32_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = 79;
v___x_1202_ = lean_uint32_dec_eq(v_opt_940_, v___x_1201_);
if (v___x_1202_ == 0)
{
uint32_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = 78;
v___x_1204_ = lean_uint32_dec_eq(v_opt_940_, v___x_1203_);
if (v___x_1204_ == 0)
{
uint32_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = 74;
v___x_1206_ = lean_uint32_dec_eq(v_opt_940_, v___x_1205_);
if (v___x_1206_ == 0)
{
uint32_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = 97;
v___x_1208_ = lean_uint32_dec_eq(v_opt_940_, v___x_1207_);
if (v___x_1208_ == 0)
{
uint32_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = 120;
v___x_1210_ = lean_uint32_dec_eq(v_opt_940_, v___x_1209_);
if (v___x_1210_ == 0)
{
uint32_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = 76;
v___x_1212_ = lean_uint32_dec_eq(v_opt_940_, v___x_1211_);
if (v___x_1212_ == 0)
{
uint32_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = 68;
v___x_1214_ = lean_uint32_dec_eq(v_opt_940_, v___x_1213_);
if (v___x_1214_ == 0)
{
uint32_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = 83;
v___x_1216_ = lean_uint32_dec_eq(v_opt_940_, v___x_1215_);
if (v___x_1216_ == 0)
{
uint32_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = 87;
v___x_1218_ = lean_uint32_dec_eq(v_opt_940_, v___x_1217_);
if (v___x_1218_ == 0)
{
uint32_t v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = 80;
v___x_1220_ = lean_uint32_dec_eq(v_opt_940_, v___x_1219_);
if (v___x_1220_ == 0)
{
uint32_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = 66;
v___x_1222_ = lean_uint32_dec_eq(v_opt_940_, v___x_1221_);
if (v___x_1222_ == 0)
{
uint32_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = 112;
v___x_1224_ = lean_uint32_dec_eq(v_opt_940_, v___x_1223_);
if (v___x_1224_ == 0)
{
uint32_t v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = 108;
v___x_1226_ = lean_uint32_dec_eq(v_opt_940_, v___x_1225_);
if (v___x_1226_ == 0)
{
uint32_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = 117;
v___x_1228_ = lean_uint32_dec_eq(v_opt_940_, v___x_1227_);
if (v___x_1228_ == 0)
{
uint32_t v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = 69;
v___x_1230_ = lean_uint32_dec_eq(v_opt_940_, v___x_1229_);
if (v___x_1230_ == 0)
{
uint32_t v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = 89;
v___x_1232_ = lean_uint32_dec_eq(v_opt_940_, v___x_1231_);
if (v___x_1232_ == 0)
{
uint32_t v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = 90;
v___x_1234_ = lean_uint32_dec_eq(v_opt_940_, v___x_1233_);
if (v___x_1234_ == 0)
{
uint32_t v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = 72;
v___x_1236_ = lean_uint32_dec_eq(v_opt_940_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_dec(v_optArg_x3f_941_);
lean_dec_ref(v_opts_939_);
goto v___jp_1073_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1238_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1237_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1279_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1279_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1279_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v_leanOpts_1243_; lean_object* v_forwardedArgs_1244_; uint8_t v_component_1245_; uint8_t v_printPrefix_1246_; uint8_t v_printLibDir_1247_; uint8_t v_useStdin_1248_; uint8_t v_onlyDeps_1249_; uint8_t v_onlySrcDeps_1250_; uint8_t v_depsJson_1251_; lean_object* v_opts_1252_; uint32_t v_trustLevel_1253_; uint32_t v_numThreads_1254_; lean_object* v_rootDir_x3f_1255_; lean_object* v_setupFileName_x3f_1256_; lean_object* v_oleanFileName_x3f_1257_; lean_object* v_ileanFileName_x3f_1258_; lean_object* v_cFileName_x3f_1259_; lean_object* v_bcFileName_x3f_1260_; uint8_t v_jsonOutput_1261_; lean_object* v_errorOnKinds_1262_; uint8_t v_printStats_1263_; uint8_t v_run_1264_; lean_object* v_incrSaveFileName_x3f_1265_; lean_object* v_incrLoadFileName_x3f_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1277_; 
v_leanOpts_1243_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1244_ = lean_ctor_get(v_opts_939_, 1);
v_component_1245_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1246_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1247_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1248_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1249_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1250_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1251_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1252_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1253_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1254_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1255_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1256_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1257_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1258_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1259_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1260_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1261_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1262_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1263_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1264_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1265_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1266_ = lean_ctor_get(v_opts_939_, 11);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v_opts_939_, 12);
lean_dec(v_unused_1278_);
v___x_1268_ = v_opts_939_;
v_isShared_1269_ = v_isSharedCheck_1277_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_incrLoadFileName_x3f_1266_);
lean_inc(v_incrSaveFileName_x3f_1265_);
lean_inc(v_errorOnKinds_1262_);
lean_inc(v_bcFileName_x3f_1260_);
lean_inc(v_cFileName_x3f_1259_);
lean_inc(v_ileanFileName_x3f_1258_);
lean_inc(v_oleanFileName_x3f_1257_);
lean_inc(v_setupFileName_x3f_1256_);
lean_inc(v_rootDir_x3f_1255_);
lean_inc(v_opts_1252_);
lean_inc(v_forwardedArgs_1244_);
lean_inc(v_leanOpts_1243_);
lean_dec(v_opts_939_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1277_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_a_1239_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 12, v___x_1270_);
v___x_1272_ = v___x_1268_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_leanOpts_1243_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_forwardedArgs_1244_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_opts_1252_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_rootDir_x3f_1255_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v_setupFileName_x3f_1256_);
lean_ctor_set(v_reuseFailAlloc_1276_, 5, v_oleanFileName_x3f_1257_);
lean_ctor_set(v_reuseFailAlloc_1276_, 6, v_ileanFileName_x3f_1258_);
lean_ctor_set(v_reuseFailAlloc_1276_, 7, v_cFileName_x3f_1259_);
lean_ctor_set(v_reuseFailAlloc_1276_, 8, v_bcFileName_x3f_1260_);
lean_ctor_set(v_reuseFailAlloc_1276_, 9, v_errorOnKinds_1262_);
lean_ctor_set(v_reuseFailAlloc_1276_, 10, v_incrSaveFileName_x3f_1265_);
lean_ctor_set(v_reuseFailAlloc_1276_, 11, v_incrLoadFileName_x3f_1266_);
lean_ctor_set(v_reuseFailAlloc_1276_, 12, v___x_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, sizeof(void*)*13 + 8, v_component_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, sizeof(void*)*13 + 9, v_printPrefix_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, sizeof(void*)*13 + 10, v_printLibDir_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, sizeof(void*)*13 + 11, v_useStdin_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, sizeof(void*)*13 + 12, v_onlyDeps_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, sizeof(void*)*13 + 13, v_onlySrcDeps_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, sizeof(void*)*13 + 14, v_depsJson_1251_);
lean_ctor_set_uint32(v_reuseFailAlloc_1276_, sizeof(void*)*13, v_trustLevel_1253_);
lean_ctor_set_uint32(v_reuseFailAlloc_1276_, sizeof(void*)*13 + 4, v_numThreads_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, sizeof(void*)*13 + 15, v_jsonOutput_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, sizeof(void*)*13 + 16, v_printStats_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, sizeof(void*)*13 + 17, v_run_1264_);
v___x_1272_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1274_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1272_);
v___x_1274_ = v___x_1241_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec_ref(v_opts_939_);
v_a_1280_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1284_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1285_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1284_);
lean_dec_ref(v___x_1285_);
goto v___jp_1281_;
v___jp_1281_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_io_error_to_string(v_a_1280_);
v___x_1283_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1282_);
lean_dec_ref(v___x_1283_);
goto v___jp_1045_;
}
}
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1287_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1286_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1328_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1328_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1328_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_leanOpts_1292_; lean_object* v_forwardedArgs_1293_; uint8_t v_component_1294_; uint8_t v_printPrefix_1295_; uint8_t v_printLibDir_1296_; uint8_t v_useStdin_1297_; uint8_t v_onlyDeps_1298_; uint8_t v_onlySrcDeps_1299_; uint8_t v_depsJson_1300_; lean_object* v_opts_1301_; uint32_t v_trustLevel_1302_; uint32_t v_numThreads_1303_; lean_object* v_rootDir_x3f_1304_; lean_object* v_setupFileName_x3f_1305_; lean_object* v_oleanFileName_x3f_1306_; lean_object* v_ileanFileName_x3f_1307_; lean_object* v_cFileName_x3f_1308_; lean_object* v_bcFileName_x3f_1309_; uint8_t v_jsonOutput_1310_; lean_object* v_errorOnKinds_1311_; uint8_t v_printStats_1312_; uint8_t v_run_1313_; lean_object* v_incrSaveFileName_x3f_1314_; lean_object* v_incrHeaderSaveFileName_x3f_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1326_; 
v_leanOpts_1292_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1293_ = lean_ctor_get(v_opts_939_, 1);
v_component_1294_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1295_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1296_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1297_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1298_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1299_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1300_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1301_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1302_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1303_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1304_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1305_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1306_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1307_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1308_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1309_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1310_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1311_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1312_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1313_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1314_ = lean_ctor_get(v_opts_939_, 10);
v_incrHeaderSaveFileName_x3f_1315_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v_opts_939_, 11);
lean_dec(v_unused_1327_);
v___x_1317_ = v_opts_939_;
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1315_);
lean_inc(v_incrSaveFileName_x3f_1314_);
lean_inc(v_errorOnKinds_1311_);
lean_inc(v_bcFileName_x3f_1309_);
lean_inc(v_cFileName_x3f_1308_);
lean_inc(v_ileanFileName_x3f_1307_);
lean_inc(v_oleanFileName_x3f_1306_);
lean_inc(v_setupFileName_x3f_1305_);
lean_inc(v_rootDir_x3f_1304_);
lean_inc(v_opts_1301_);
lean_inc(v_forwardedArgs_1293_);
lean_inc(v_leanOpts_1292_);
lean_dec(v_opts_939_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_a_1288_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 11, v___x_1319_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_leanOpts_1292_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_forwardedArgs_1293_);
lean_ctor_set(v_reuseFailAlloc_1325_, 2, v_opts_1301_);
lean_ctor_set(v_reuseFailAlloc_1325_, 3, v_rootDir_x3f_1304_);
lean_ctor_set(v_reuseFailAlloc_1325_, 4, v_setupFileName_x3f_1305_);
lean_ctor_set(v_reuseFailAlloc_1325_, 5, v_oleanFileName_x3f_1306_);
lean_ctor_set(v_reuseFailAlloc_1325_, 6, v_ileanFileName_x3f_1307_);
lean_ctor_set(v_reuseFailAlloc_1325_, 7, v_cFileName_x3f_1308_);
lean_ctor_set(v_reuseFailAlloc_1325_, 8, v_bcFileName_x3f_1309_);
lean_ctor_set(v_reuseFailAlloc_1325_, 9, v_errorOnKinds_1311_);
lean_ctor_set(v_reuseFailAlloc_1325_, 10, v_incrSaveFileName_x3f_1314_);
lean_ctor_set(v_reuseFailAlloc_1325_, 11, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1325_, 12, v_incrHeaderSaveFileName_x3f_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, sizeof(void*)*13 + 8, v_component_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, sizeof(void*)*13 + 9, v_printPrefix_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, sizeof(void*)*13 + 10, v_printLibDir_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, sizeof(void*)*13 + 11, v_useStdin_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, sizeof(void*)*13 + 12, v_onlyDeps_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, sizeof(void*)*13 + 13, v_onlySrcDeps_1299_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, sizeof(void*)*13 + 14, v_depsJson_1300_);
lean_ctor_set_uint32(v_reuseFailAlloc_1325_, sizeof(void*)*13, v_trustLevel_1302_);
lean_ctor_set_uint32(v_reuseFailAlloc_1325_, sizeof(void*)*13 + 4, v_numThreads_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, sizeof(void*)*13 + 15, v_jsonOutput_1310_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, sizeof(void*)*13 + 16, v_printStats_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, sizeof(void*)*13 + 17, v_run_1313_);
v___x_1321_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1323_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1321_);
v___x_1323_ = v___x_1290_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v_opts_939_);
v_a_1329_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1333_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1334_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1333_);
lean_dec_ref(v___x_1334_);
goto v___jp_1330_;
v___jp_1330_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_io_error_to_string(v_a_1329_);
v___x_1332_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1331_);
lean_dec_ref(v___x_1332_);
goto v___jp_1079_;
}
}
}
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1336_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1335_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1377_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1377_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1377_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_leanOpts_1341_; lean_object* v_forwardedArgs_1342_; uint8_t v_component_1343_; uint8_t v_printPrefix_1344_; uint8_t v_printLibDir_1345_; uint8_t v_useStdin_1346_; uint8_t v_onlyDeps_1347_; uint8_t v_onlySrcDeps_1348_; uint8_t v_depsJson_1349_; lean_object* v_opts_1350_; uint32_t v_trustLevel_1351_; uint32_t v_numThreads_1352_; lean_object* v_rootDir_x3f_1353_; lean_object* v_setupFileName_x3f_1354_; lean_object* v_oleanFileName_x3f_1355_; lean_object* v_ileanFileName_x3f_1356_; lean_object* v_cFileName_x3f_1357_; lean_object* v_bcFileName_x3f_1358_; uint8_t v_jsonOutput_1359_; lean_object* v_errorOnKinds_1360_; uint8_t v_printStats_1361_; uint8_t v_run_1362_; lean_object* v_incrLoadFileName_x3f_1363_; lean_object* v_incrHeaderSaveFileName_x3f_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1375_; 
v_leanOpts_1341_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1342_ = lean_ctor_get(v_opts_939_, 1);
v_component_1343_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1344_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1345_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1346_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1347_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1348_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1349_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1350_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1351_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1352_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1353_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1354_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1355_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1356_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1357_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1358_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1359_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1360_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1361_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1362_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrLoadFileName_x3f_1363_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1364_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v_opts_939_, 10);
lean_dec(v_unused_1376_);
v___x_1366_ = v_opts_939_;
v_isShared_1367_ = v_isSharedCheck_1375_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1364_);
lean_inc(v_incrLoadFileName_x3f_1363_);
lean_inc(v_errorOnKinds_1360_);
lean_inc(v_bcFileName_x3f_1358_);
lean_inc(v_cFileName_x3f_1357_);
lean_inc(v_ileanFileName_x3f_1356_);
lean_inc(v_oleanFileName_x3f_1355_);
lean_inc(v_setupFileName_x3f_1354_);
lean_inc(v_rootDir_x3f_1353_);
lean_inc(v_opts_1350_);
lean_inc(v_forwardedArgs_1342_);
lean_inc(v_leanOpts_1341_);
lean_dec(v_opts_939_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1375_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1368_, 0, v_a_1337_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 10, v___x_1368_);
v___x_1370_ = v___x_1366_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_leanOpts_1341_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_forwardedArgs_1342_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_opts_1350_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_rootDir_x3f_1353_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v_setupFileName_x3f_1354_);
lean_ctor_set(v_reuseFailAlloc_1374_, 5, v_oleanFileName_x3f_1355_);
lean_ctor_set(v_reuseFailAlloc_1374_, 6, v_ileanFileName_x3f_1356_);
lean_ctor_set(v_reuseFailAlloc_1374_, 7, v_cFileName_x3f_1357_);
lean_ctor_set(v_reuseFailAlloc_1374_, 8, v_bcFileName_x3f_1358_);
lean_ctor_set(v_reuseFailAlloc_1374_, 9, v_errorOnKinds_1360_);
lean_ctor_set(v_reuseFailAlloc_1374_, 10, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1374_, 11, v_incrLoadFileName_x3f_1363_);
lean_ctor_set(v_reuseFailAlloc_1374_, 12, v_incrHeaderSaveFileName_x3f_1364_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*13 + 8, v_component_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*13 + 9, v_printPrefix_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*13 + 10, v_printLibDir_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*13 + 11, v_useStdin_1346_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*13 + 12, v_onlyDeps_1347_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*13 + 13, v_onlySrcDeps_1348_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*13 + 14, v_depsJson_1349_);
lean_ctor_set_uint32(v_reuseFailAlloc_1374_, sizeof(void*)*13, v_trustLevel_1351_);
lean_ctor_set_uint32(v_reuseFailAlloc_1374_, sizeof(void*)*13 + 4, v_numThreads_1352_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*13 + 15, v_jsonOutput_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*13 + 16, v_printStats_1361_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*13 + 17, v_run_1362_);
v___x_1370_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1372_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1370_);
v___x_1372_ = v___x_1339_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec_ref(v_opts_939_);
v_a_1378_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1336_, 1);
v___x_1382_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1383_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1382_);
lean_dec_ref(v___x_1383_);
goto v___jp_1379_;
v___jp_1379_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_io_error_to_string(v_a_1378_);
v___x_1381_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1380_);
lean_dec_ref(v___x_1381_);
goto v___jp_1039_;
}
}
}
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1385_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1384_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1427_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1427_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1427_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v_leanOpts_1390_; lean_object* v_forwardedArgs_1391_; uint8_t v_component_1392_; uint8_t v_printPrefix_1393_; uint8_t v_printLibDir_1394_; uint8_t v_useStdin_1395_; uint8_t v_onlyDeps_1396_; uint8_t v_onlySrcDeps_1397_; uint8_t v_depsJson_1398_; lean_object* v_opts_1399_; uint32_t v_trustLevel_1400_; uint32_t v_numThreads_1401_; lean_object* v_rootDir_x3f_1402_; lean_object* v_setupFileName_x3f_1403_; lean_object* v_oleanFileName_x3f_1404_; lean_object* v_ileanFileName_x3f_1405_; lean_object* v_cFileName_x3f_1406_; lean_object* v_bcFileName_x3f_1407_; uint8_t v_jsonOutput_1408_; lean_object* v_errorOnKinds_1409_; uint8_t v_printStats_1410_; uint8_t v_run_1411_; lean_object* v_incrSaveFileName_x3f_1412_; lean_object* v_incrLoadFileName_x3f_1413_; lean_object* v_incrHeaderSaveFileName_x3f_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1426_; 
v_leanOpts_1390_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1391_ = lean_ctor_get(v_opts_939_, 1);
v_component_1392_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1393_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1394_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1395_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1396_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1397_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1398_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1399_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1400_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1401_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1402_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1403_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1404_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1405_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1406_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1407_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1408_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1409_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1410_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1411_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1412_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1413_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1414_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1416_ = v_opts_939_;
v_isShared_1417_ = v_isSharedCheck_1426_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1414_);
lean_inc(v_incrLoadFileName_x3f_1413_);
lean_inc(v_incrSaveFileName_x3f_1412_);
lean_inc(v_errorOnKinds_1409_);
lean_inc(v_bcFileName_x3f_1407_);
lean_inc(v_cFileName_x3f_1406_);
lean_inc(v_ileanFileName_x3f_1405_);
lean_inc(v_oleanFileName_x3f_1404_);
lean_inc(v_setupFileName_x3f_1403_);
lean_inc(v_rootDir_x3f_1402_);
lean_inc(v_opts_1399_);
lean_inc(v_forwardedArgs_1391_);
lean_inc(v_leanOpts_1390_);
lean_dec(v_opts_939_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1426_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1418_ = l_String_toName(v_a_1386_);
v___x_1419_ = lean_array_push(v_errorOnKinds_1409_, v___x_1418_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 9, v___x_1419_);
v___x_1421_ = v___x_1416_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_leanOpts_1390_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_forwardedArgs_1391_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_opts_1399_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_rootDir_x3f_1402_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v_setupFileName_x3f_1403_);
lean_ctor_set(v_reuseFailAlloc_1425_, 5, v_oleanFileName_x3f_1404_);
lean_ctor_set(v_reuseFailAlloc_1425_, 6, v_ileanFileName_x3f_1405_);
lean_ctor_set(v_reuseFailAlloc_1425_, 7, v_cFileName_x3f_1406_);
lean_ctor_set(v_reuseFailAlloc_1425_, 8, v_bcFileName_x3f_1407_);
lean_ctor_set(v_reuseFailAlloc_1425_, 9, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1425_, 10, v_incrSaveFileName_x3f_1412_);
lean_ctor_set(v_reuseFailAlloc_1425_, 11, v_incrLoadFileName_x3f_1413_);
lean_ctor_set(v_reuseFailAlloc_1425_, 12, v_incrHeaderSaveFileName_x3f_1414_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, sizeof(void*)*13 + 8, v_component_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, sizeof(void*)*13 + 9, v_printPrefix_1393_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, sizeof(void*)*13 + 10, v_printLibDir_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, sizeof(void*)*13 + 11, v_useStdin_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, sizeof(void*)*13 + 12, v_onlyDeps_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, sizeof(void*)*13 + 13, v_onlySrcDeps_1397_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, sizeof(void*)*13 + 14, v_depsJson_1398_);
lean_ctor_set_uint32(v_reuseFailAlloc_1425_, sizeof(void*)*13, v_trustLevel_1400_);
lean_ctor_set_uint32(v_reuseFailAlloc_1425_, sizeof(void*)*13 + 4, v_numThreads_1401_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, sizeof(void*)*13 + 15, v_jsonOutput_1408_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, sizeof(void*)*13 + 16, v_printStats_1410_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, sizeof(void*)*13 + 17, v_run_1411_);
v___x_1421_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1421_);
v___x_1423_ = v___x_1388_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec_ref(v_opts_939_);
v_a_1428_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1385_, 1);
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
goto v___jp_1085_;
}
}
}
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1435_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1434_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1476_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1476_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1476_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v_leanOpts_1440_; lean_object* v_forwardedArgs_1441_; uint8_t v_component_1442_; uint8_t v_printPrefix_1443_; uint8_t v_printLibDir_1444_; uint8_t v_useStdin_1445_; uint8_t v_onlyDeps_1446_; uint8_t v_onlySrcDeps_1447_; uint8_t v_depsJson_1448_; lean_object* v_opts_1449_; uint32_t v_trustLevel_1450_; uint32_t v_numThreads_1451_; lean_object* v_rootDir_x3f_1452_; lean_object* v_oleanFileName_x3f_1453_; lean_object* v_ileanFileName_x3f_1454_; lean_object* v_cFileName_x3f_1455_; lean_object* v_bcFileName_x3f_1456_; uint8_t v_jsonOutput_1457_; lean_object* v_errorOnKinds_1458_; uint8_t v_printStats_1459_; uint8_t v_run_1460_; lean_object* v_incrSaveFileName_x3f_1461_; lean_object* v_incrLoadFileName_x3f_1462_; lean_object* v_incrHeaderSaveFileName_x3f_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1474_; 
v_leanOpts_1440_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1441_ = lean_ctor_get(v_opts_939_, 1);
v_component_1442_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1443_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1444_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1445_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1446_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1447_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1448_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1449_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1450_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1451_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1452_ = lean_ctor_get(v_opts_939_, 3);
v_oleanFileName_x3f_1453_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1454_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1455_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1456_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1457_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1458_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1459_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1460_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1461_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1462_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1463_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v_opts_939_, 4);
lean_dec(v_unused_1475_);
v___x_1465_ = v_opts_939_;
v_isShared_1466_ = v_isSharedCheck_1474_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1463_);
lean_inc(v_incrLoadFileName_x3f_1462_);
lean_inc(v_incrSaveFileName_x3f_1461_);
lean_inc(v_errorOnKinds_1458_);
lean_inc(v_bcFileName_x3f_1456_);
lean_inc(v_cFileName_x3f_1455_);
lean_inc(v_ileanFileName_x3f_1454_);
lean_inc(v_oleanFileName_x3f_1453_);
lean_inc(v_rootDir_x3f_1452_);
lean_inc(v_opts_1449_);
lean_inc(v_forwardedArgs_1441_);
lean_inc(v_leanOpts_1440_);
lean_dec(v_opts_939_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1474_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1469_; 
v___x_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1467_, 0, v_a_1436_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 4, v___x_1467_);
v___x_1469_ = v___x_1465_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_leanOpts_1440_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_forwardedArgs_1441_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v_opts_1449_);
lean_ctor_set(v_reuseFailAlloc_1473_, 3, v_rootDir_x3f_1452_);
lean_ctor_set(v_reuseFailAlloc_1473_, 4, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1473_, 5, v_oleanFileName_x3f_1453_);
lean_ctor_set(v_reuseFailAlloc_1473_, 6, v_ileanFileName_x3f_1454_);
lean_ctor_set(v_reuseFailAlloc_1473_, 7, v_cFileName_x3f_1455_);
lean_ctor_set(v_reuseFailAlloc_1473_, 8, v_bcFileName_x3f_1456_);
lean_ctor_set(v_reuseFailAlloc_1473_, 9, v_errorOnKinds_1458_);
lean_ctor_set(v_reuseFailAlloc_1473_, 10, v_incrSaveFileName_x3f_1461_);
lean_ctor_set(v_reuseFailAlloc_1473_, 11, v_incrLoadFileName_x3f_1462_);
lean_ctor_set(v_reuseFailAlloc_1473_, 12, v_incrHeaderSaveFileName_x3f_1463_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*13 + 8, v_component_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*13 + 9, v_printPrefix_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*13 + 10, v_printLibDir_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*13 + 11, v_useStdin_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*13 + 12, v_onlyDeps_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*13 + 13, v_onlySrcDeps_1447_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*13 + 14, v_depsJson_1448_);
lean_ctor_set_uint32(v_reuseFailAlloc_1473_, sizeof(void*)*13, v_trustLevel_1450_);
lean_ctor_set_uint32(v_reuseFailAlloc_1473_, sizeof(void*)*13 + 4, v_numThreads_1451_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*13 + 15, v_jsonOutput_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*13 + 16, v_printStats_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*13 + 17, v_run_1460_);
v___x_1469_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1471_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1469_);
v___x_1471_ = v___x_1438_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec_ref(v_opts_939_);
v_a_1477_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1481_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1482_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1481_);
lean_dec_ref(v___x_1482_);
goto v___jp_1478_;
v___jp_1478_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_io_error_to_string(v_a_1477_);
v___x_1480_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1479_);
lean_dec_ref(v___x_1480_);
goto v___jp_1033_;
}
}
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1484_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1483_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1486_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc_n(v_a_1485_, 2);
lean_dec_ref_known(v___x_1484_, 1);
v___x_1486_ = lean_load_dynlib(v_a_1485_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1528_; 
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v___x_1486_, 0);
lean_dec(v_unused_1529_);
v___x_1488_ = v___x_1486_;
v_isShared_1489_ = v_isSharedCheck_1528_;
goto v_resetjp_1487_;
}
else
{
lean_dec(v___x_1486_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1528_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_leanOpts_1490_; lean_object* v_forwardedArgs_1491_; uint8_t v_component_1492_; uint8_t v_printPrefix_1493_; uint8_t v_printLibDir_1494_; uint8_t v_useStdin_1495_; uint8_t v_onlyDeps_1496_; uint8_t v_onlySrcDeps_1497_; uint8_t v_depsJson_1498_; lean_object* v_opts_1499_; uint32_t v_trustLevel_1500_; uint32_t v_numThreads_1501_; lean_object* v_rootDir_x3f_1502_; lean_object* v_setupFileName_x3f_1503_; lean_object* v_oleanFileName_x3f_1504_; lean_object* v_ileanFileName_x3f_1505_; lean_object* v_cFileName_x3f_1506_; lean_object* v_bcFileName_x3f_1507_; uint8_t v_jsonOutput_1508_; lean_object* v_errorOnKinds_1509_; uint8_t v_printStats_1510_; uint8_t v_run_1511_; lean_object* v_incrSaveFileName_x3f_1512_; lean_object* v_incrLoadFileName_x3f_1513_; lean_object* v_incrHeaderSaveFileName_x3f_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1527_; 
v_leanOpts_1490_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1491_ = lean_ctor_get(v_opts_939_, 1);
v_component_1492_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1493_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1494_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1495_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1496_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1497_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1498_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1499_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1500_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1501_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1502_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1503_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1504_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1505_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1506_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1507_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1508_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1509_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1510_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1511_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1512_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1513_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1514_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1516_ = v_opts_939_;
v_isShared_1517_ = v_isSharedCheck_1527_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1514_);
lean_inc(v_incrLoadFileName_x3f_1513_);
lean_inc(v_incrSaveFileName_x3f_1512_);
lean_inc(v_errorOnKinds_1509_);
lean_inc(v_bcFileName_x3f_1507_);
lean_inc(v_cFileName_x3f_1506_);
lean_inc(v_ileanFileName_x3f_1505_);
lean_inc(v_oleanFileName_x3f_1504_);
lean_inc(v_setupFileName_x3f_1503_);
lean_inc(v_rootDir_x3f_1502_);
lean_inc(v_opts_1499_);
lean_inc(v_forwardedArgs_1491_);
lean_inc(v_leanOpts_1490_);
lean_dec(v_opts_939_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1527_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1518_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1519_ = lean_string_append(v___x_1518_, v_a_1485_);
lean_dec(v_a_1485_);
v___x_1520_ = lean_array_push(v_forwardedArgs_1491_, v___x_1519_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 1, v___x_1520_);
v___x_1522_ = v___x_1516_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_leanOpts_1490_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v_opts_1499_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_rootDir_x3f_1502_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v_setupFileName_x3f_1503_);
lean_ctor_set(v_reuseFailAlloc_1526_, 5, v_oleanFileName_x3f_1504_);
lean_ctor_set(v_reuseFailAlloc_1526_, 6, v_ileanFileName_x3f_1505_);
lean_ctor_set(v_reuseFailAlloc_1526_, 7, v_cFileName_x3f_1506_);
lean_ctor_set(v_reuseFailAlloc_1526_, 8, v_bcFileName_x3f_1507_);
lean_ctor_set(v_reuseFailAlloc_1526_, 9, v_errorOnKinds_1509_);
lean_ctor_set(v_reuseFailAlloc_1526_, 10, v_incrSaveFileName_x3f_1512_);
lean_ctor_set(v_reuseFailAlloc_1526_, 11, v_incrLoadFileName_x3f_1513_);
lean_ctor_set(v_reuseFailAlloc_1526_, 12, v_incrHeaderSaveFileName_x3f_1514_);
lean_ctor_set_uint8(v_reuseFailAlloc_1526_, sizeof(void*)*13 + 8, v_component_1492_);
lean_ctor_set_uint8(v_reuseFailAlloc_1526_, sizeof(void*)*13 + 9, v_printPrefix_1493_);
lean_ctor_set_uint8(v_reuseFailAlloc_1526_, sizeof(void*)*13 + 10, v_printLibDir_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1526_, sizeof(void*)*13 + 11, v_useStdin_1495_);
lean_ctor_set_uint8(v_reuseFailAlloc_1526_, sizeof(void*)*13 + 12, v_onlyDeps_1496_);
lean_ctor_set_uint8(v_reuseFailAlloc_1526_, sizeof(void*)*13 + 13, v_onlySrcDeps_1497_);
lean_ctor_set_uint8(v_reuseFailAlloc_1526_, sizeof(void*)*13 + 14, v_depsJson_1498_);
lean_ctor_set_uint32(v_reuseFailAlloc_1526_, sizeof(void*)*13, v_trustLevel_1500_);
lean_ctor_set_uint32(v_reuseFailAlloc_1526_, sizeof(void*)*13 + 4, v_numThreads_1501_);
lean_ctor_set_uint8(v_reuseFailAlloc_1526_, sizeof(void*)*13 + 15, v_jsonOutput_1508_);
lean_ctor_set_uint8(v_reuseFailAlloc_1526_, sizeof(void*)*13 + 16, v_printStats_1510_);
lean_ctor_set_uint8(v_reuseFailAlloc_1526_, sizeof(void*)*13 + 17, v_run_1511_);
v___x_1522_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1524_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1522_);
v___x_1524_ = v___x_1488_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_dec(v_a_1485_);
lean_dec_ref(v_opts_939_);
v_a_1530_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1486_, 1);
v___x_1534_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1535_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1534_);
lean_dec_ref(v___x_1535_);
goto v___jp_1531_;
v___jp_1531_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_io_error_to_string(v_a_1530_);
v___x_1533_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1532_);
lean_dec_ref(v___x_1533_);
goto v___jp_1091_;
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec_ref(v_opts_939_);
v_a_1536_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1484_, 1);
v___x_1540_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1541_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1540_);
lean_dec_ref(v___x_1541_);
goto v___jp_1537_;
v___jp_1537_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_io_error_to_string(v_a_1536_);
v___x_1539_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1538_);
lean_dec_ref(v___x_1539_);
goto v___jp_1027_;
}
}
}
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1543_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1542_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1616_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1616_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1616_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v_fst_1549_; lean_object* v_snd_1550_; lean_object* v___y_1599_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1610_ = lean_unsigned_to_nat(0u);
v___x_1611_ = lean_string_utf8_byte_size(v_a_1544_);
lean_inc(v_a_1544_);
v___x_1612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1612_, 0, v_a_1544_);
lean_ctor_set(v___x_1612_, 1, v___x_1610_);
lean_ctor_set(v___x_1612_, 2, v___x_1611_);
v___x_1613_ = lean_box(0);
v___x_1614_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_1612_, v_a_1544_, v___x_1610_, v___x_1613_);
lean_dec_ref_known(v___x_1612_, 3);
if (lean_obj_tag(v___x_1614_) == 0)
{
v___y_1599_ = v___x_1611_;
goto v___jp_1598_;
}
else
{
lean_object* v_val_1615_; 
v_val_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v___y_1599_ = v_val_1615_;
goto v___jp_1598_;
}
v___jp_1548_:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_load_plugin(v_fst_1549_, v_snd_1550_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1593_; 
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; 
v_unused_1594_ = lean_ctor_get(v___x_1551_, 0);
lean_dec(v_unused_1594_);
v___x_1553_ = v___x_1551_;
v_isShared_1554_ = v_isSharedCheck_1593_;
goto v_resetjp_1552_;
}
else
{
lean_dec(v___x_1551_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1593_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_leanOpts_1555_; lean_object* v_forwardedArgs_1556_; uint8_t v_component_1557_; uint8_t v_printPrefix_1558_; uint8_t v_printLibDir_1559_; uint8_t v_useStdin_1560_; uint8_t v_onlyDeps_1561_; uint8_t v_onlySrcDeps_1562_; uint8_t v_depsJson_1563_; lean_object* v_opts_1564_; uint32_t v_trustLevel_1565_; uint32_t v_numThreads_1566_; lean_object* v_rootDir_x3f_1567_; lean_object* v_setupFileName_x3f_1568_; lean_object* v_oleanFileName_x3f_1569_; lean_object* v_ileanFileName_x3f_1570_; lean_object* v_cFileName_x3f_1571_; lean_object* v_bcFileName_x3f_1572_; uint8_t v_jsonOutput_1573_; lean_object* v_errorOnKinds_1574_; uint8_t v_printStats_1575_; uint8_t v_run_1576_; lean_object* v_incrSaveFileName_x3f_1577_; lean_object* v_incrLoadFileName_x3f_1578_; lean_object* v_incrHeaderSaveFileName_x3f_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1592_; 
v_leanOpts_1555_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1556_ = lean_ctor_get(v_opts_939_, 1);
v_component_1557_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1558_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1559_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1560_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1561_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1562_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1563_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1564_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1565_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1566_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1567_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1568_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1569_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1570_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1571_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1572_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1573_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1574_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1575_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1576_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1577_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1578_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1579_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1581_ = v_opts_939_;
v_isShared_1582_ = v_isSharedCheck_1592_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1579_);
lean_inc(v_incrLoadFileName_x3f_1578_);
lean_inc(v_incrSaveFileName_x3f_1577_);
lean_inc(v_errorOnKinds_1574_);
lean_inc(v_bcFileName_x3f_1572_);
lean_inc(v_cFileName_x3f_1571_);
lean_inc(v_ileanFileName_x3f_1570_);
lean_inc(v_oleanFileName_x3f_1569_);
lean_inc(v_setupFileName_x3f_1568_);
lean_inc(v_rootDir_x3f_1567_);
lean_inc(v_opts_1564_);
lean_inc(v_forwardedArgs_1556_);
lean_inc(v_leanOpts_1555_);
lean_dec(v_opts_939_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1592_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1583_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1584_ = lean_string_append(v___x_1583_, v_a_1544_);
lean_dec(v_a_1544_);
v___x_1585_ = lean_array_push(v_forwardedArgs_1556_, v___x_1584_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 1, v___x_1585_);
v___x_1587_ = v___x_1581_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_leanOpts_1555_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_opts_1564_);
lean_ctor_set(v_reuseFailAlloc_1591_, 3, v_rootDir_x3f_1567_);
lean_ctor_set(v_reuseFailAlloc_1591_, 4, v_setupFileName_x3f_1568_);
lean_ctor_set(v_reuseFailAlloc_1591_, 5, v_oleanFileName_x3f_1569_);
lean_ctor_set(v_reuseFailAlloc_1591_, 6, v_ileanFileName_x3f_1570_);
lean_ctor_set(v_reuseFailAlloc_1591_, 7, v_cFileName_x3f_1571_);
lean_ctor_set(v_reuseFailAlloc_1591_, 8, v_bcFileName_x3f_1572_);
lean_ctor_set(v_reuseFailAlloc_1591_, 9, v_errorOnKinds_1574_);
lean_ctor_set(v_reuseFailAlloc_1591_, 10, v_incrSaveFileName_x3f_1577_);
lean_ctor_set(v_reuseFailAlloc_1591_, 11, v_incrLoadFileName_x3f_1578_);
lean_ctor_set(v_reuseFailAlloc_1591_, 12, v_incrHeaderSaveFileName_x3f_1579_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 8, v_component_1557_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 9, v_printPrefix_1558_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 10, v_printLibDir_1559_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 11, v_useStdin_1560_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 12, v_onlyDeps_1561_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 13, v_onlySrcDeps_1562_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 14, v_depsJson_1563_);
lean_ctor_set_uint32(v_reuseFailAlloc_1591_, sizeof(void*)*13, v_trustLevel_1565_);
lean_ctor_set_uint32(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 4, v_numThreads_1566_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 15, v_jsonOutput_1573_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 16, v_printStats_1575_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 17, v_run_1576_);
v___x_1587_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1589_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1587_);
v___x_1589_ = v___x_1553_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec(v_a_1544_);
lean_dec_ref(v_opts_939_);
v_a_1595_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1596_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1597_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1596_);
lean_dec_ref(v___x_1597_);
v___y_1101_ = v_a_1595_;
goto v___jp_1100_;
}
}
v___jp_1598_:
{
lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = lean_string_utf8_byte_size(v_a_1544_);
v___x_1601_ = lean_nat_dec_eq(v___y_1599_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1602_ = lean_unsigned_to_nat(0u);
v___x_1603_ = lean_string_utf8_next_fast(v_a_1544_, v___y_1599_);
v___x_1604_ = lean_string_utf8_extract(v_a_1544_, v___x_1602_, v___y_1599_);
lean_dec(v___y_1599_);
v___x_1605_ = lean_string_utf8_extract(v_a_1544_, v___x_1603_, v___x_1600_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set_tag(v___x_1546_, 1);
lean_ctor_set(v___x_1546_, 0, v___x_1605_);
v___x_1607_ = v___x_1546_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
v_fst_1549_ = v___x_1604_;
v_snd_1550_ = v___x_1607_;
goto v___jp_1548_;
}
}
else
{
lean_object* v___x_1609_; 
lean_dec(v___y_1599_);
lean_del_object(v___x_1546_);
v___x_1609_ = lean_box(0);
lean_inc(v_a_1544_);
v_fst_1549_ = v_a_1544_;
v_snd_1550_ = v___x_1609_;
goto v___jp_1548_;
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec_ref(v_opts_939_);
v_a_1617_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1621_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1622_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1621_);
lean_dec_ref(v___x_1622_);
goto v___jp_1618_;
v___jp_1618_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_io_error_to_string(v_a_1617_);
v___x_1620_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1619_);
lean_dec_ref(v___x_1620_);
goto v___jp_1021_;
}
}
}
}
else
{
uint8_t v___x_1623_; 
v___x_1623_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__16, &l___private_Lean_Shell_0__Lean_displayHelp___closed__16_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
if (v___x_1623_ == 0)
{
lean_dec(v_optArg_x3f_941_);
lean_dec_ref(v_opts_939_);
goto v___jp_1073_;
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1625_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1624_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1634_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1634_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1634_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1632_; 
v___x_1630_ = lean_internal_enable_debug(v_a_1626_);
lean_dec(v_a_1626_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v_opts_939_);
v___x_1632_ = v___x_1628_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_opts_939_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec_ref(v_opts_939_);
v_a_1635_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1639_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1640_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1639_);
lean_dec_ref(v___x_1640_);
goto v___jp_1636_;
v___jp_1636_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_io_error_to_string(v_a_1635_);
v___x_1638_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1637_);
lean_dec_ref(v___x_1638_);
goto v___jp_1107_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1641_; lean_object* v_forwardedArgs_1642_; uint8_t v_component_1643_; uint8_t v_printPrefix_1644_; uint8_t v_printLibDir_1645_; uint8_t v_useStdin_1646_; uint8_t v_onlyDeps_1647_; uint8_t v_onlySrcDeps_1648_; uint8_t v_depsJson_1649_; lean_object* v_opts_1650_; uint32_t v_trustLevel_1651_; uint32_t v_numThreads_1652_; lean_object* v_rootDir_x3f_1653_; lean_object* v_setupFileName_x3f_1654_; lean_object* v_oleanFileName_x3f_1655_; lean_object* v_ileanFileName_x3f_1656_; lean_object* v_cFileName_x3f_1657_; lean_object* v_bcFileName_x3f_1658_; uint8_t v_jsonOutput_1659_; lean_object* v_errorOnKinds_1660_; uint8_t v_printStats_1661_; uint8_t v_run_1662_; lean_object* v_incrSaveFileName_x3f_1663_; lean_object* v_incrLoadFileName_x3f_1664_; lean_object* v_incrHeaderSaveFileName_x3f_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v_optArg_x3f_941_);
v_leanOpts_1641_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1642_ = lean_ctor_get(v_opts_939_, 1);
v_component_1643_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1644_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1645_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1646_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1647_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1648_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1649_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1650_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1651_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1652_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1653_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1654_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1655_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1656_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1657_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1658_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1659_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1660_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1661_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1662_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1663_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1664_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1665_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1667_ = v_opts_939_;
v_isShared_1668_ = v_isSharedCheck_1675_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1665_);
lean_inc(v_incrLoadFileName_x3f_1664_);
lean_inc(v_incrSaveFileName_x3f_1663_);
lean_inc(v_errorOnKinds_1660_);
lean_inc(v_bcFileName_x3f_1658_);
lean_inc(v_cFileName_x3f_1657_);
lean_inc(v_ileanFileName_x3f_1656_);
lean_inc(v_oleanFileName_x3f_1655_);
lean_inc(v_setupFileName_x3f_1654_);
lean_inc(v_rootDir_x3f_1653_);
lean_inc(v_opts_1650_);
lean_inc(v_forwardedArgs_1642_);
lean_inc(v_leanOpts_1641_);
lean_dec(v_opts_939_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1675_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1669_ = l_Lean_profiler;
v___x_1670_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1641_, v___x_1669_, v___x_1220_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1670_);
v___x_1672_ = v___x_1667_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_forwardedArgs_1642_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_opts_1650_);
lean_ctor_set(v_reuseFailAlloc_1674_, 3, v_rootDir_x3f_1653_);
lean_ctor_set(v_reuseFailAlloc_1674_, 4, v_setupFileName_x3f_1654_);
lean_ctor_set(v_reuseFailAlloc_1674_, 5, v_oleanFileName_x3f_1655_);
lean_ctor_set(v_reuseFailAlloc_1674_, 6, v_ileanFileName_x3f_1656_);
lean_ctor_set(v_reuseFailAlloc_1674_, 7, v_cFileName_x3f_1657_);
lean_ctor_set(v_reuseFailAlloc_1674_, 8, v_bcFileName_x3f_1658_);
lean_ctor_set(v_reuseFailAlloc_1674_, 9, v_errorOnKinds_1660_);
lean_ctor_set(v_reuseFailAlloc_1674_, 10, v_incrSaveFileName_x3f_1663_);
lean_ctor_set(v_reuseFailAlloc_1674_, 11, v_incrLoadFileName_x3f_1664_);
lean_ctor_set(v_reuseFailAlloc_1674_, 12, v_incrHeaderSaveFileName_x3f_1665_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*13 + 8, v_component_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*13 + 9, v_printPrefix_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*13 + 10, v_printLibDir_1645_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*13 + 11, v_useStdin_1646_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*13 + 12, v_onlyDeps_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*13 + 13, v_onlySrcDeps_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*13 + 14, v_depsJson_1649_);
lean_ctor_set_uint32(v_reuseFailAlloc_1674_, sizeof(void*)*13, v_trustLevel_1651_);
lean_ctor_set_uint32(v_reuseFailAlloc_1674_, sizeof(void*)*13 + 4, v_numThreads_1652_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*13 + 15, v_jsonOutput_1659_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*13 + 16, v_printStats_1661_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*13 + 17, v_run_1662_);
v___x_1672_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
return v___x_1673_;
}
}
}
}
else
{
lean_object* v_leanOpts_1676_; lean_object* v_forwardedArgs_1677_; uint8_t v_printPrefix_1678_; uint8_t v_printLibDir_1679_; uint8_t v_useStdin_1680_; uint8_t v_onlyDeps_1681_; uint8_t v_onlySrcDeps_1682_; uint8_t v_depsJson_1683_; lean_object* v_opts_1684_; uint32_t v_trustLevel_1685_; uint32_t v_numThreads_1686_; lean_object* v_rootDir_x3f_1687_; lean_object* v_setupFileName_x3f_1688_; lean_object* v_oleanFileName_x3f_1689_; lean_object* v_ileanFileName_x3f_1690_; lean_object* v_cFileName_x3f_1691_; lean_object* v_bcFileName_x3f_1692_; uint8_t v_jsonOutput_1693_; lean_object* v_errorOnKinds_1694_; uint8_t v_printStats_1695_; uint8_t v_run_1696_; lean_object* v_incrSaveFileName_x3f_1697_; lean_object* v_incrLoadFileName_x3f_1698_; lean_object* v_incrHeaderSaveFileName_x3f_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_optArg_x3f_941_);
v_leanOpts_1676_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1677_ = lean_ctor_get(v_opts_939_, 1);
v_printPrefix_1678_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1679_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1680_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1681_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1682_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1683_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1684_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1685_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1686_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1687_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1688_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1689_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1690_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1691_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1692_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1693_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1694_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1695_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1696_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1697_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1698_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1699_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1701_ = v_opts_939_;
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1699_);
lean_inc(v_incrLoadFileName_x3f_1698_);
lean_inc(v_incrSaveFileName_x3f_1697_);
lean_inc(v_errorOnKinds_1694_);
lean_inc(v_bcFileName_x3f_1692_);
lean_inc(v_cFileName_x3f_1691_);
lean_inc(v_ileanFileName_x3f_1690_);
lean_inc(v_oleanFileName_x3f_1689_);
lean_inc(v_setupFileName_x3f_1688_);
lean_inc(v_rootDir_x3f_1687_);
lean_inc(v_opts_1684_);
lean_inc(v_forwardedArgs_1677_);
lean_inc(v_leanOpts_1676_);
lean_dec(v_opts_939_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
uint8_t v___x_1703_; lean_object* v___x_1705_; 
v___x_1703_ = 2;
if (v_isShared_1702_ == 0)
{
v___x_1705_ = v___x_1701_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_leanOpts_1676_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_forwardedArgs_1677_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_opts_1684_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_rootDir_x3f_1687_);
lean_ctor_set(v_reuseFailAlloc_1707_, 4, v_setupFileName_x3f_1688_);
lean_ctor_set(v_reuseFailAlloc_1707_, 5, v_oleanFileName_x3f_1689_);
lean_ctor_set(v_reuseFailAlloc_1707_, 6, v_ileanFileName_x3f_1690_);
lean_ctor_set(v_reuseFailAlloc_1707_, 7, v_cFileName_x3f_1691_);
lean_ctor_set(v_reuseFailAlloc_1707_, 8, v_bcFileName_x3f_1692_);
lean_ctor_set(v_reuseFailAlloc_1707_, 9, v_errorOnKinds_1694_);
lean_ctor_set(v_reuseFailAlloc_1707_, 10, v_incrSaveFileName_x3f_1697_);
lean_ctor_set(v_reuseFailAlloc_1707_, 11, v_incrLoadFileName_x3f_1698_);
lean_ctor_set(v_reuseFailAlloc_1707_, 12, v_incrHeaderSaveFileName_x3f_1699_);
lean_ctor_set_uint8(v_reuseFailAlloc_1707_, sizeof(void*)*13 + 9, v_printPrefix_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1707_, sizeof(void*)*13 + 10, v_printLibDir_1679_);
lean_ctor_set_uint8(v_reuseFailAlloc_1707_, sizeof(void*)*13 + 11, v_useStdin_1680_);
lean_ctor_set_uint8(v_reuseFailAlloc_1707_, sizeof(void*)*13 + 12, v_onlyDeps_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1707_, sizeof(void*)*13 + 13, v_onlySrcDeps_1682_);
lean_ctor_set_uint8(v_reuseFailAlloc_1707_, sizeof(void*)*13 + 14, v_depsJson_1683_);
lean_ctor_set_uint32(v_reuseFailAlloc_1707_, sizeof(void*)*13, v_trustLevel_1685_);
lean_ctor_set_uint32(v_reuseFailAlloc_1707_, sizeof(void*)*13 + 4, v_numThreads_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1707_, sizeof(void*)*13 + 15, v_jsonOutput_1693_);
lean_ctor_set_uint8(v_reuseFailAlloc_1707_, sizeof(void*)*13 + 16, v_printStats_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1707_, sizeof(void*)*13 + 17, v_run_1696_);
v___x_1705_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; 
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*13 + 8, v___x_1703_);
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
return v___x_1706_;
}
}
}
}
else
{
lean_object* v_leanOpts_1709_; lean_object* v_forwardedArgs_1710_; uint8_t v_printPrefix_1711_; uint8_t v_printLibDir_1712_; uint8_t v_useStdin_1713_; uint8_t v_onlyDeps_1714_; uint8_t v_onlySrcDeps_1715_; uint8_t v_depsJson_1716_; lean_object* v_opts_1717_; uint32_t v_trustLevel_1718_; uint32_t v_numThreads_1719_; lean_object* v_rootDir_x3f_1720_; lean_object* v_setupFileName_x3f_1721_; lean_object* v_oleanFileName_x3f_1722_; lean_object* v_ileanFileName_x3f_1723_; lean_object* v_cFileName_x3f_1724_; lean_object* v_bcFileName_x3f_1725_; uint8_t v_jsonOutput_1726_; lean_object* v_errorOnKinds_1727_; uint8_t v_printStats_1728_; uint8_t v_run_1729_; lean_object* v_incrSaveFileName_x3f_1730_; lean_object* v_incrLoadFileName_x3f_1731_; lean_object* v_incrHeaderSaveFileName_x3f_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v_optArg_x3f_941_);
v_leanOpts_1709_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1710_ = lean_ctor_get(v_opts_939_, 1);
v_printPrefix_1711_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1712_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1713_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1714_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1715_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1716_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1717_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1718_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1719_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1720_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1721_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1722_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1723_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1724_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1725_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1726_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1727_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1728_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1729_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1730_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1731_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1732_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1734_ = v_opts_939_;
v_isShared_1735_ = v_isSharedCheck_1741_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1732_);
lean_inc(v_incrLoadFileName_x3f_1731_);
lean_inc(v_incrSaveFileName_x3f_1730_);
lean_inc(v_errorOnKinds_1727_);
lean_inc(v_bcFileName_x3f_1725_);
lean_inc(v_cFileName_x3f_1724_);
lean_inc(v_ileanFileName_x3f_1723_);
lean_inc(v_oleanFileName_x3f_1722_);
lean_inc(v_setupFileName_x3f_1721_);
lean_inc(v_rootDir_x3f_1720_);
lean_inc(v_opts_1717_);
lean_inc(v_forwardedArgs_1710_);
lean_inc(v_leanOpts_1709_);
lean_dec(v_opts_939_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1741_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
uint8_t v___x_1736_; lean_object* v___x_1738_; 
v___x_1736_ = 1;
if (v_isShared_1735_ == 0)
{
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_leanOpts_1709_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_forwardedArgs_1710_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_opts_1717_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_rootDir_x3f_1720_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_setupFileName_x3f_1721_);
lean_ctor_set(v_reuseFailAlloc_1740_, 5, v_oleanFileName_x3f_1722_);
lean_ctor_set(v_reuseFailAlloc_1740_, 6, v_ileanFileName_x3f_1723_);
lean_ctor_set(v_reuseFailAlloc_1740_, 7, v_cFileName_x3f_1724_);
lean_ctor_set(v_reuseFailAlloc_1740_, 8, v_bcFileName_x3f_1725_);
lean_ctor_set(v_reuseFailAlloc_1740_, 9, v_errorOnKinds_1727_);
lean_ctor_set(v_reuseFailAlloc_1740_, 10, v_incrSaveFileName_x3f_1730_);
lean_ctor_set(v_reuseFailAlloc_1740_, 11, v_incrLoadFileName_x3f_1731_);
lean_ctor_set(v_reuseFailAlloc_1740_, 12, v_incrHeaderSaveFileName_x3f_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*13 + 9, v_printPrefix_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*13 + 10, v_printLibDir_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*13 + 11, v_useStdin_1713_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*13 + 12, v_onlyDeps_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*13 + 13, v_onlySrcDeps_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*13 + 14, v_depsJson_1716_);
lean_ctor_set_uint32(v_reuseFailAlloc_1740_, sizeof(void*)*13, v_trustLevel_1718_);
lean_ctor_set_uint32(v_reuseFailAlloc_1740_, sizeof(void*)*13 + 4, v_numThreads_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*13 + 15, v_jsonOutput_1726_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*13 + 16, v_printStats_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*13 + 17, v_run_1729_);
v___x_1738_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; 
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*13 + 8, v___x_1736_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
}
}
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1743_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1742_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v_leanOpts_1745_; lean_object* v_forwardedArgs_1746_; uint8_t v_component_1747_; uint8_t v_printPrefix_1748_; uint8_t v_printLibDir_1749_; uint8_t v_useStdin_1750_; uint8_t v_onlyDeps_1751_; uint8_t v_onlySrcDeps_1752_; uint8_t v_depsJson_1753_; lean_object* v_opts_1754_; uint32_t v_trustLevel_1755_; uint32_t v_numThreads_1756_; lean_object* v_rootDir_x3f_1757_; lean_object* v_setupFileName_x3f_1758_; lean_object* v_oleanFileName_x3f_1759_; lean_object* v_ileanFileName_x3f_1760_; lean_object* v_cFileName_x3f_1761_; lean_object* v_bcFileName_x3f_1762_; uint8_t v_jsonOutput_1763_; lean_object* v_errorOnKinds_1764_; uint8_t v_printStats_1765_; uint8_t v_run_1766_; lean_object* v_incrSaveFileName_x3f_1767_; lean_object* v_incrLoadFileName_x3f_1768_; lean_object* v_incrHeaderSaveFileName_x3f_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1794_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref_known(v___x_1743_, 1);
v_leanOpts_1745_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1746_ = lean_ctor_get(v_opts_939_, 1);
v_component_1747_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1748_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1749_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1750_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1751_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1752_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1753_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1754_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1755_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1756_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1757_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1758_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1759_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1760_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1761_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1762_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1763_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1764_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1765_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1766_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1767_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1768_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1769_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1771_ = v_opts_939_;
v_isShared_1772_ = v_isSharedCheck_1794_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1769_);
lean_inc(v_incrLoadFileName_x3f_1768_);
lean_inc(v_incrSaveFileName_x3f_1767_);
lean_inc(v_errorOnKinds_1764_);
lean_inc(v_bcFileName_x3f_1762_);
lean_inc(v_cFileName_x3f_1761_);
lean_inc(v_ileanFileName_x3f_1760_);
lean_inc(v_oleanFileName_x3f_1759_);
lean_inc(v_setupFileName_x3f_1758_);
lean_inc(v_rootDir_x3f_1757_);
lean_inc(v_opts_1754_);
lean_inc(v_forwardedArgs_1746_);
lean_inc(v_leanOpts_1745_);
lean_dec(v_opts_939_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1794_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; 
lean_inc(v_a_1744_);
v___x_1773_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1745_, v_a_1744_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1787_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1787_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1787_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1778_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1779_ = lean_string_append(v___x_1778_, v_a_1744_);
lean_dec(v_a_1744_);
v___x_1780_ = lean_array_push(v_forwardedArgs_1746_, v___x_1779_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 1, v___x_1780_);
lean_ctor_set(v___x_1771_, 0, v_a_1774_);
v___x_1782_ = v___x_1771_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1774_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_opts_1754_);
lean_ctor_set(v_reuseFailAlloc_1786_, 3, v_rootDir_x3f_1757_);
lean_ctor_set(v_reuseFailAlloc_1786_, 4, v_setupFileName_x3f_1758_);
lean_ctor_set(v_reuseFailAlloc_1786_, 5, v_oleanFileName_x3f_1759_);
lean_ctor_set(v_reuseFailAlloc_1786_, 6, v_ileanFileName_x3f_1760_);
lean_ctor_set(v_reuseFailAlloc_1786_, 7, v_cFileName_x3f_1761_);
lean_ctor_set(v_reuseFailAlloc_1786_, 8, v_bcFileName_x3f_1762_);
lean_ctor_set(v_reuseFailAlloc_1786_, 9, v_errorOnKinds_1764_);
lean_ctor_set(v_reuseFailAlloc_1786_, 10, v_incrSaveFileName_x3f_1767_);
lean_ctor_set(v_reuseFailAlloc_1786_, 11, v_incrLoadFileName_x3f_1768_);
lean_ctor_set(v_reuseFailAlloc_1786_, 12, v_incrHeaderSaveFileName_x3f_1769_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*13 + 8, v_component_1747_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*13 + 9, v_printPrefix_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*13 + 10, v_printLibDir_1749_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*13 + 11, v_useStdin_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*13 + 12, v_onlyDeps_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*13 + 13, v_onlySrcDeps_1752_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*13 + 14, v_depsJson_1753_);
lean_ctor_set_uint32(v_reuseFailAlloc_1786_, sizeof(void*)*13, v_trustLevel_1755_);
lean_ctor_set_uint32(v_reuseFailAlloc_1786_, sizeof(void*)*13 + 4, v_numThreads_1756_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*13 + 15, v_jsonOutput_1763_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*13 + 16, v_printStats_1765_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*13 + 17, v_run_1766_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1782_);
v___x_1784_ = v___x_1776_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_del_object(v___x_1771_);
lean_dec(v_incrHeaderSaveFileName_x3f_1769_);
lean_dec(v_incrLoadFileName_x3f_1768_);
lean_dec(v_incrSaveFileName_x3f_1767_);
lean_dec_ref(v_errorOnKinds_1764_);
lean_dec(v_bcFileName_x3f_1762_);
lean_dec(v_cFileName_x3f_1761_);
lean_dec(v_ileanFileName_x3f_1760_);
lean_dec(v_oleanFileName_x3f_1759_);
lean_dec(v_setupFileName_x3f_1758_);
lean_dec(v_rootDir_x3f_1757_);
lean_dec_ref(v_opts_1754_);
lean_dec_ref(v_forwardedArgs_1746_);
lean_dec(v_a_1744_);
v_a_1788_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1773_, 1);
v___x_1792_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1793_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1792_);
lean_dec_ref(v___x_1793_);
goto v___jp_1789_;
v___jp_1789_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_io_error_to_string(v_a_1788_);
v___x_1791_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1790_);
lean_dec_ref(v___x_1791_);
goto v___jp_1015_;
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
lean_dec_ref(v_opts_939_);
v_a_1795_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1743_, 1);
v___x_1799_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1800_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1799_);
lean_dec_ref(v___x_1800_);
goto v___jp_1796_;
v___jp_1796_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_io_error_to_string(v_a_1795_);
v___x_1798_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1797_);
lean_dec_ref(v___x_1798_);
goto v___jp_1113_;
}
}
}
}
else
{
lean_object* v_leanOpts_1801_; lean_object* v_forwardedArgs_1802_; uint8_t v_component_1803_; uint8_t v_printPrefix_1804_; uint8_t v_useStdin_1805_; uint8_t v_onlyDeps_1806_; uint8_t v_onlySrcDeps_1807_; uint8_t v_depsJson_1808_; lean_object* v_opts_1809_; uint32_t v_trustLevel_1810_; uint32_t v_numThreads_1811_; lean_object* v_rootDir_x3f_1812_; lean_object* v_setupFileName_x3f_1813_; lean_object* v_oleanFileName_x3f_1814_; lean_object* v_ileanFileName_x3f_1815_; lean_object* v_cFileName_x3f_1816_; lean_object* v_bcFileName_x3f_1817_; uint8_t v_jsonOutput_1818_; lean_object* v_errorOnKinds_1819_; uint8_t v_printStats_1820_; uint8_t v_run_1821_; lean_object* v_incrSaveFileName_x3f_1822_; lean_object* v_incrLoadFileName_x3f_1823_; lean_object* v_incrHeaderSaveFileName_x3f_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1832_; 
lean_dec(v_optArg_x3f_941_);
v_leanOpts_1801_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1802_ = lean_ctor_get(v_opts_939_, 1);
v_component_1803_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1804_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_useStdin_1805_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1806_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1807_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1808_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1809_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1810_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1811_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1812_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1813_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1814_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1815_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1816_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1817_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1818_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1819_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1820_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1821_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1822_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1823_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1824_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1826_ = v_opts_939_;
v_isShared_1827_ = v_isSharedCheck_1832_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1824_);
lean_inc(v_incrLoadFileName_x3f_1823_);
lean_inc(v_incrSaveFileName_x3f_1822_);
lean_inc(v_errorOnKinds_1819_);
lean_inc(v_bcFileName_x3f_1817_);
lean_inc(v_cFileName_x3f_1816_);
lean_inc(v_ileanFileName_x3f_1815_);
lean_inc(v_oleanFileName_x3f_1814_);
lean_inc(v_setupFileName_x3f_1813_);
lean_inc(v_rootDir_x3f_1812_);
lean_inc(v_opts_1809_);
lean_inc(v_forwardedArgs_1802_);
lean_inc(v_leanOpts_1801_);
lean_dec(v_opts_939_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1832_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_leanOpts_1801_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_forwardedArgs_1802_);
lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_opts_1809_);
lean_ctor_set(v_reuseFailAlloc_1831_, 3, v_rootDir_x3f_1812_);
lean_ctor_set(v_reuseFailAlloc_1831_, 4, v_setupFileName_x3f_1813_);
lean_ctor_set(v_reuseFailAlloc_1831_, 5, v_oleanFileName_x3f_1814_);
lean_ctor_set(v_reuseFailAlloc_1831_, 6, v_ileanFileName_x3f_1815_);
lean_ctor_set(v_reuseFailAlloc_1831_, 7, v_cFileName_x3f_1816_);
lean_ctor_set(v_reuseFailAlloc_1831_, 8, v_bcFileName_x3f_1817_);
lean_ctor_set(v_reuseFailAlloc_1831_, 9, v_errorOnKinds_1819_);
lean_ctor_set(v_reuseFailAlloc_1831_, 10, v_incrSaveFileName_x3f_1822_);
lean_ctor_set(v_reuseFailAlloc_1831_, 11, v_incrLoadFileName_x3f_1823_);
lean_ctor_set(v_reuseFailAlloc_1831_, 12, v_incrHeaderSaveFileName_x3f_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 8, v_component_1803_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 9, v_printPrefix_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 11, v_useStdin_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 12, v_onlyDeps_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 13, v_onlySrcDeps_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 14, v_depsJson_1808_);
lean_ctor_set_uint32(v_reuseFailAlloc_1831_, sizeof(void*)*13, v_trustLevel_1810_);
lean_ctor_set_uint32(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 4, v_numThreads_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 15, v_jsonOutput_1818_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 16, v_printStats_1820_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 17, v_run_1821_);
v___x_1829_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1830_; 
lean_ctor_set_uint8(v___x_1829_, sizeof(void*)*13 + 10, v___x_1212_);
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
return v___x_1830_;
}
}
}
}
else
{
lean_object* v_leanOpts_1833_; lean_object* v_forwardedArgs_1834_; uint8_t v_component_1835_; uint8_t v_printLibDir_1836_; uint8_t v_useStdin_1837_; uint8_t v_onlyDeps_1838_; uint8_t v_onlySrcDeps_1839_; uint8_t v_depsJson_1840_; lean_object* v_opts_1841_; uint32_t v_trustLevel_1842_; uint32_t v_numThreads_1843_; lean_object* v_rootDir_x3f_1844_; lean_object* v_setupFileName_x3f_1845_; lean_object* v_oleanFileName_x3f_1846_; lean_object* v_ileanFileName_x3f_1847_; lean_object* v_cFileName_x3f_1848_; lean_object* v_bcFileName_x3f_1849_; uint8_t v_jsonOutput_1850_; lean_object* v_errorOnKinds_1851_; uint8_t v_printStats_1852_; uint8_t v_run_1853_; lean_object* v_incrSaveFileName_x3f_1854_; lean_object* v_incrLoadFileName_x3f_1855_; lean_object* v_incrHeaderSaveFileName_x3f_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_optArg_x3f_941_);
v_leanOpts_1833_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1834_ = lean_ctor_get(v_opts_939_, 1);
v_component_1835_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printLibDir_1836_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1837_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1838_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1839_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1840_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1841_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1842_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1843_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1844_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1845_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1846_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1847_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1848_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1849_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1850_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1851_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1852_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1853_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1854_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1855_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1856_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1858_ = v_opts_939_;
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1856_);
lean_inc(v_incrLoadFileName_x3f_1855_);
lean_inc(v_incrSaveFileName_x3f_1854_);
lean_inc(v_errorOnKinds_1851_);
lean_inc(v_bcFileName_x3f_1849_);
lean_inc(v_cFileName_x3f_1848_);
lean_inc(v_ileanFileName_x3f_1847_);
lean_inc(v_oleanFileName_x3f_1846_);
lean_inc(v_setupFileName_x3f_1845_);
lean_inc(v_rootDir_x3f_1844_);
lean_inc(v_opts_1841_);
lean_inc(v_forwardedArgs_1834_);
lean_inc(v_leanOpts_1833_);
lean_dec(v_opts_939_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_leanOpts_1833_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_forwardedArgs_1834_);
lean_ctor_set(v_reuseFailAlloc_1863_, 2, v_opts_1841_);
lean_ctor_set(v_reuseFailAlloc_1863_, 3, v_rootDir_x3f_1844_);
lean_ctor_set(v_reuseFailAlloc_1863_, 4, v_setupFileName_x3f_1845_);
lean_ctor_set(v_reuseFailAlloc_1863_, 5, v_oleanFileName_x3f_1846_);
lean_ctor_set(v_reuseFailAlloc_1863_, 6, v_ileanFileName_x3f_1847_);
lean_ctor_set(v_reuseFailAlloc_1863_, 7, v_cFileName_x3f_1848_);
lean_ctor_set(v_reuseFailAlloc_1863_, 8, v_bcFileName_x3f_1849_);
lean_ctor_set(v_reuseFailAlloc_1863_, 9, v_errorOnKinds_1851_);
lean_ctor_set(v_reuseFailAlloc_1863_, 10, v_incrSaveFileName_x3f_1854_);
lean_ctor_set(v_reuseFailAlloc_1863_, 11, v_incrLoadFileName_x3f_1855_);
lean_ctor_set(v_reuseFailAlloc_1863_, 12, v_incrHeaderSaveFileName_x3f_1856_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*13 + 8, v_component_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*13 + 10, v_printLibDir_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*13 + 11, v_useStdin_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*13 + 12, v_onlyDeps_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*13 + 13, v_onlySrcDeps_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*13 + 14, v_depsJson_1840_);
lean_ctor_set_uint32(v_reuseFailAlloc_1863_, sizeof(void*)*13, v_trustLevel_1842_);
lean_ctor_set_uint32(v_reuseFailAlloc_1863_, sizeof(void*)*13 + 4, v_numThreads_1843_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*13 + 15, v_jsonOutput_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*13 + 16, v_printStats_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1863_, sizeof(void*)*13 + 17, v_run_1853_);
v___x_1861_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; 
lean_ctor_set_uint8(v___x_1861_, sizeof(void*)*13 + 9, v___x_1210_);
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
return v___x_1862_;
}
}
}
}
else
{
lean_object* v_leanOpts_1865_; lean_object* v_forwardedArgs_1866_; uint8_t v_component_1867_; uint8_t v_printPrefix_1868_; uint8_t v_printLibDir_1869_; uint8_t v_useStdin_1870_; uint8_t v_onlyDeps_1871_; uint8_t v_onlySrcDeps_1872_; uint8_t v_depsJson_1873_; lean_object* v_opts_1874_; uint32_t v_trustLevel_1875_; uint32_t v_numThreads_1876_; lean_object* v_rootDir_x3f_1877_; lean_object* v_setupFileName_x3f_1878_; lean_object* v_oleanFileName_x3f_1879_; lean_object* v_ileanFileName_x3f_1880_; lean_object* v_cFileName_x3f_1881_; lean_object* v_bcFileName_x3f_1882_; uint8_t v_jsonOutput_1883_; lean_object* v_errorOnKinds_1884_; uint8_t v_run_1885_; lean_object* v_incrSaveFileName_x3f_1886_; lean_object* v_incrLoadFileName_x3f_1887_; lean_object* v_incrHeaderSaveFileName_x3f_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1896_; 
lean_dec(v_optArg_x3f_941_);
v_leanOpts_1865_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1866_ = lean_ctor_get(v_opts_939_, 1);
v_component_1867_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1868_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1869_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1870_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1871_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1872_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1873_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1874_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1875_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1876_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1877_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1878_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1879_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1880_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1881_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1882_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1883_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1884_ = lean_ctor_get(v_opts_939_, 9);
v_run_1885_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1886_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1887_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1888_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1890_ = v_opts_939_;
v_isShared_1891_ = v_isSharedCheck_1896_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1888_);
lean_inc(v_incrLoadFileName_x3f_1887_);
lean_inc(v_incrSaveFileName_x3f_1886_);
lean_inc(v_errorOnKinds_1884_);
lean_inc(v_bcFileName_x3f_1882_);
lean_inc(v_cFileName_x3f_1881_);
lean_inc(v_ileanFileName_x3f_1880_);
lean_inc(v_oleanFileName_x3f_1879_);
lean_inc(v_setupFileName_x3f_1878_);
lean_inc(v_rootDir_x3f_1877_);
lean_inc(v_opts_1874_);
lean_inc(v_forwardedArgs_1866_);
lean_inc(v_leanOpts_1865_);
lean_dec(v_opts_939_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1896_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_leanOpts_1865_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_forwardedArgs_1866_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_opts_1874_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_rootDir_x3f_1877_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_setupFileName_x3f_1878_);
lean_ctor_set(v_reuseFailAlloc_1895_, 5, v_oleanFileName_x3f_1879_);
lean_ctor_set(v_reuseFailAlloc_1895_, 6, v_ileanFileName_x3f_1880_);
lean_ctor_set(v_reuseFailAlloc_1895_, 7, v_cFileName_x3f_1881_);
lean_ctor_set(v_reuseFailAlloc_1895_, 8, v_bcFileName_x3f_1882_);
lean_ctor_set(v_reuseFailAlloc_1895_, 9, v_errorOnKinds_1884_);
lean_ctor_set(v_reuseFailAlloc_1895_, 10, v_incrSaveFileName_x3f_1886_);
lean_ctor_set(v_reuseFailAlloc_1895_, 11, v_incrLoadFileName_x3f_1887_);
lean_ctor_set(v_reuseFailAlloc_1895_, 12, v_incrHeaderSaveFileName_x3f_1888_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*13 + 8, v_component_1867_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*13 + 9, v_printPrefix_1868_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*13 + 10, v_printLibDir_1869_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*13 + 11, v_useStdin_1870_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*13 + 12, v_onlyDeps_1871_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*13 + 13, v_onlySrcDeps_1872_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*13 + 14, v_depsJson_1873_);
lean_ctor_set_uint32(v_reuseFailAlloc_1895_, sizeof(void*)*13, v_trustLevel_1875_);
lean_ctor_set_uint32(v_reuseFailAlloc_1895_, sizeof(void*)*13 + 4, v_numThreads_1876_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*13 + 15, v_jsonOutput_1883_);
lean_ctor_set_uint8(v_reuseFailAlloc_1895_, sizeof(void*)*13 + 17, v_run_1885_);
v___x_1893_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1894_; 
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*13 + 16, v___x_1208_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
}
}
else
{
lean_object* v_leanOpts_1897_; lean_object* v_forwardedArgs_1898_; uint8_t v_component_1899_; uint8_t v_printPrefix_1900_; uint8_t v_printLibDir_1901_; uint8_t v_useStdin_1902_; uint8_t v_onlyDeps_1903_; uint8_t v_onlySrcDeps_1904_; uint8_t v_depsJson_1905_; lean_object* v_opts_1906_; uint32_t v_trustLevel_1907_; uint32_t v_numThreads_1908_; lean_object* v_rootDir_x3f_1909_; lean_object* v_setupFileName_x3f_1910_; lean_object* v_oleanFileName_x3f_1911_; lean_object* v_ileanFileName_x3f_1912_; lean_object* v_cFileName_x3f_1913_; lean_object* v_bcFileName_x3f_1914_; lean_object* v_errorOnKinds_1915_; uint8_t v_printStats_1916_; uint8_t v_run_1917_; lean_object* v_incrSaveFileName_x3f_1918_; lean_object* v_incrLoadFileName_x3f_1919_; lean_object* v_incrHeaderSaveFileName_x3f_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_optArg_x3f_941_);
v_leanOpts_1897_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1898_ = lean_ctor_get(v_opts_939_, 1);
v_component_1899_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1900_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1901_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1902_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1903_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1904_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1905_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1906_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1907_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1908_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1909_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1910_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1911_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1912_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1913_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1914_ = lean_ctor_get(v_opts_939_, 8);
v_errorOnKinds_1915_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1916_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1917_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1918_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1919_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1920_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1922_ = v_opts_939_;
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1920_);
lean_inc(v_incrLoadFileName_x3f_1919_);
lean_inc(v_incrSaveFileName_x3f_1918_);
lean_inc(v_errorOnKinds_1915_);
lean_inc(v_bcFileName_x3f_1914_);
lean_inc(v_cFileName_x3f_1913_);
lean_inc(v_ileanFileName_x3f_1912_);
lean_inc(v_oleanFileName_x3f_1911_);
lean_inc(v_setupFileName_x3f_1910_);
lean_inc(v_rootDir_x3f_1909_);
lean_inc(v_opts_1906_);
lean_inc(v_forwardedArgs_1898_);
lean_inc(v_leanOpts_1897_);
lean_dec(v_opts_939_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_leanOpts_1897_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_forwardedArgs_1898_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_opts_1906_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v_rootDir_x3f_1909_);
lean_ctor_set(v_reuseFailAlloc_1927_, 4, v_setupFileName_x3f_1910_);
lean_ctor_set(v_reuseFailAlloc_1927_, 5, v_oleanFileName_x3f_1911_);
lean_ctor_set(v_reuseFailAlloc_1927_, 6, v_ileanFileName_x3f_1912_);
lean_ctor_set(v_reuseFailAlloc_1927_, 7, v_cFileName_x3f_1913_);
lean_ctor_set(v_reuseFailAlloc_1927_, 8, v_bcFileName_x3f_1914_);
lean_ctor_set(v_reuseFailAlloc_1927_, 9, v_errorOnKinds_1915_);
lean_ctor_set(v_reuseFailAlloc_1927_, 10, v_incrSaveFileName_x3f_1918_);
lean_ctor_set(v_reuseFailAlloc_1927_, 11, v_incrLoadFileName_x3f_1919_);
lean_ctor_set(v_reuseFailAlloc_1927_, 12, v_incrHeaderSaveFileName_x3f_1920_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*13 + 8, v_component_1899_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*13 + 9, v_printPrefix_1900_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*13 + 10, v_printLibDir_1901_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*13 + 11, v_useStdin_1902_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*13 + 12, v_onlyDeps_1903_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*13 + 13, v_onlySrcDeps_1904_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*13 + 14, v_depsJson_1905_);
lean_ctor_set_uint32(v_reuseFailAlloc_1927_, sizeof(void*)*13, v_trustLevel_1907_);
lean_ctor_set_uint32(v_reuseFailAlloc_1927_, sizeof(void*)*13 + 4, v_numThreads_1908_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*13 + 16, v_printStats_1916_);
lean_ctor_set_uint8(v_reuseFailAlloc_1927_, sizeof(void*)*13 + 17, v_run_1917_);
v___x_1925_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1926_; 
lean_ctor_set_uint8(v___x_1925_, sizeof(void*)*13 + 15, v___x_1206_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
}
}
else
{
lean_object* v_leanOpts_1929_; lean_object* v_forwardedArgs_1930_; uint8_t v_component_1931_; uint8_t v_printPrefix_1932_; uint8_t v_printLibDir_1933_; uint8_t v_useStdin_1934_; uint8_t v_onlySrcDeps_1935_; lean_object* v_opts_1936_; uint32_t v_trustLevel_1937_; uint32_t v_numThreads_1938_; lean_object* v_rootDir_x3f_1939_; lean_object* v_setupFileName_x3f_1940_; lean_object* v_oleanFileName_x3f_1941_; lean_object* v_ileanFileName_x3f_1942_; lean_object* v_cFileName_x3f_1943_; lean_object* v_bcFileName_x3f_1944_; uint8_t v_jsonOutput_1945_; lean_object* v_errorOnKinds_1946_; uint8_t v_printStats_1947_; uint8_t v_run_1948_; lean_object* v_incrSaveFileName_x3f_1949_; lean_object* v_incrLoadFileName_x3f_1950_; lean_object* v_incrHeaderSaveFileName_x3f_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_optArg_x3f_941_);
v_leanOpts_1929_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1930_ = lean_ctor_get(v_opts_939_, 1);
v_component_1931_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1932_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1933_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1934_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1935_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_opts_1936_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1937_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1938_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1939_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1940_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1941_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1942_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1943_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1944_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1945_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1946_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1947_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1948_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1949_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1950_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1951_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1953_ = v_opts_939_;
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1951_);
lean_inc(v_incrLoadFileName_x3f_1950_);
lean_inc(v_incrSaveFileName_x3f_1949_);
lean_inc(v_errorOnKinds_1946_);
lean_inc(v_bcFileName_x3f_1944_);
lean_inc(v_cFileName_x3f_1943_);
lean_inc(v_ileanFileName_x3f_1942_);
lean_inc(v_oleanFileName_x3f_1941_);
lean_inc(v_setupFileName_x3f_1940_);
lean_inc(v_rootDir_x3f_1939_);
lean_inc(v_opts_1936_);
lean_inc(v_forwardedArgs_1930_);
lean_inc(v_leanOpts_1929_);
lean_dec(v_opts_939_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1959_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_leanOpts_1929_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_forwardedArgs_1930_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v_opts_1936_);
lean_ctor_set(v_reuseFailAlloc_1958_, 3, v_rootDir_x3f_1939_);
lean_ctor_set(v_reuseFailAlloc_1958_, 4, v_setupFileName_x3f_1940_);
lean_ctor_set(v_reuseFailAlloc_1958_, 5, v_oleanFileName_x3f_1941_);
lean_ctor_set(v_reuseFailAlloc_1958_, 6, v_ileanFileName_x3f_1942_);
lean_ctor_set(v_reuseFailAlloc_1958_, 7, v_cFileName_x3f_1943_);
lean_ctor_set(v_reuseFailAlloc_1958_, 8, v_bcFileName_x3f_1944_);
lean_ctor_set(v_reuseFailAlloc_1958_, 9, v_errorOnKinds_1946_);
lean_ctor_set(v_reuseFailAlloc_1958_, 10, v_incrSaveFileName_x3f_1949_);
lean_ctor_set(v_reuseFailAlloc_1958_, 11, v_incrLoadFileName_x3f_1950_);
lean_ctor_set(v_reuseFailAlloc_1958_, 12, v_incrHeaderSaveFileName_x3f_1951_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*13 + 8, v_component_1931_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*13 + 9, v_printPrefix_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*13 + 10, v_printLibDir_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*13 + 11, v_useStdin_1934_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*13 + 13, v_onlySrcDeps_1935_);
lean_ctor_set_uint32(v_reuseFailAlloc_1958_, sizeof(void*)*13, v_trustLevel_1937_);
lean_ctor_set_uint32(v_reuseFailAlloc_1958_, sizeof(void*)*13 + 4, v_numThreads_1938_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*13 + 15, v_jsonOutput_1945_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*13 + 16, v_printStats_1947_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*13 + 17, v_run_1948_);
v___x_1956_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1957_; 
lean_ctor_set_uint8(v___x_1956_, sizeof(void*)*13 + 12, v___x_1204_);
lean_ctor_set_uint8(v___x_1956_, sizeof(void*)*13 + 14, v___x_1204_);
v___x_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
return v___x_1957_;
}
}
}
}
else
{
lean_object* v_leanOpts_1960_; lean_object* v_forwardedArgs_1961_; uint8_t v_component_1962_; uint8_t v_printPrefix_1963_; uint8_t v_printLibDir_1964_; uint8_t v_useStdin_1965_; uint8_t v_onlyDeps_1966_; uint8_t v_depsJson_1967_; lean_object* v_opts_1968_; uint32_t v_trustLevel_1969_; uint32_t v_numThreads_1970_; lean_object* v_rootDir_x3f_1971_; lean_object* v_setupFileName_x3f_1972_; lean_object* v_oleanFileName_x3f_1973_; lean_object* v_ileanFileName_x3f_1974_; lean_object* v_cFileName_x3f_1975_; lean_object* v_bcFileName_x3f_1976_; uint8_t v_jsonOutput_1977_; lean_object* v_errorOnKinds_1978_; uint8_t v_printStats_1979_; uint8_t v_run_1980_; lean_object* v_incrSaveFileName_x3f_1981_; lean_object* v_incrLoadFileName_x3f_1982_; lean_object* v_incrHeaderSaveFileName_x3f_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_optArg_x3f_941_);
v_leanOpts_1960_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1961_ = lean_ctor_get(v_opts_939_, 1);
v_component_1962_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1963_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1964_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1965_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_1966_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_depsJson_1967_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_1968_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_1969_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_1970_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1971_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_1972_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_1973_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_1974_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_1975_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_1976_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_1977_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_1978_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_1979_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_1980_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1981_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_1982_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_1983_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1985_ = v_opts_939_;
v_isShared_1986_ = v_isSharedCheck_1991_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1983_);
lean_inc(v_incrLoadFileName_x3f_1982_);
lean_inc(v_incrSaveFileName_x3f_1981_);
lean_inc(v_errorOnKinds_1978_);
lean_inc(v_bcFileName_x3f_1976_);
lean_inc(v_cFileName_x3f_1975_);
lean_inc(v_ileanFileName_x3f_1974_);
lean_inc(v_oleanFileName_x3f_1973_);
lean_inc(v_setupFileName_x3f_1972_);
lean_inc(v_rootDir_x3f_1971_);
lean_inc(v_opts_1968_);
lean_inc(v_forwardedArgs_1961_);
lean_inc(v_leanOpts_1960_);
lean_dec(v_opts_939_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1991_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_leanOpts_1960_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_forwardedArgs_1961_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_opts_1968_);
lean_ctor_set(v_reuseFailAlloc_1990_, 3, v_rootDir_x3f_1971_);
lean_ctor_set(v_reuseFailAlloc_1990_, 4, v_setupFileName_x3f_1972_);
lean_ctor_set(v_reuseFailAlloc_1990_, 5, v_oleanFileName_x3f_1973_);
lean_ctor_set(v_reuseFailAlloc_1990_, 6, v_ileanFileName_x3f_1974_);
lean_ctor_set(v_reuseFailAlloc_1990_, 7, v_cFileName_x3f_1975_);
lean_ctor_set(v_reuseFailAlloc_1990_, 8, v_bcFileName_x3f_1976_);
lean_ctor_set(v_reuseFailAlloc_1990_, 9, v_errorOnKinds_1978_);
lean_ctor_set(v_reuseFailAlloc_1990_, 10, v_incrSaveFileName_x3f_1981_);
lean_ctor_set(v_reuseFailAlloc_1990_, 11, v_incrLoadFileName_x3f_1982_);
lean_ctor_set(v_reuseFailAlloc_1990_, 12, v_incrHeaderSaveFileName_x3f_1983_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*13 + 8, v_component_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*13 + 9, v_printPrefix_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*13 + 10, v_printLibDir_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*13 + 11, v_useStdin_1965_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*13 + 12, v_onlyDeps_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*13 + 14, v_depsJson_1967_);
lean_ctor_set_uint32(v_reuseFailAlloc_1990_, sizeof(void*)*13, v_trustLevel_1969_);
lean_ctor_set_uint32(v_reuseFailAlloc_1990_, sizeof(void*)*13 + 4, v_numThreads_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*13 + 15, v_jsonOutput_1977_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*13 + 16, v_printStats_1979_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*13 + 17, v_run_1980_);
v___x_1988_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; 
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*13 + 13, v___x_1202_);
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_leanOpts_1992_; lean_object* v_forwardedArgs_1993_; uint8_t v_component_1994_; uint8_t v_printPrefix_1995_; uint8_t v_printLibDir_1996_; uint8_t v_useStdin_1997_; uint8_t v_onlySrcDeps_1998_; uint8_t v_depsJson_1999_; lean_object* v_opts_2000_; uint32_t v_trustLevel_2001_; uint32_t v_numThreads_2002_; lean_object* v_rootDir_x3f_2003_; lean_object* v_setupFileName_x3f_2004_; lean_object* v_oleanFileName_x3f_2005_; lean_object* v_ileanFileName_x3f_2006_; lean_object* v_cFileName_x3f_2007_; lean_object* v_bcFileName_x3f_2008_; uint8_t v_jsonOutput_2009_; lean_object* v_errorOnKinds_2010_; uint8_t v_printStats_2011_; uint8_t v_run_2012_; lean_object* v_incrSaveFileName_x3f_2013_; lean_object* v_incrLoadFileName_x3f_2014_; lean_object* v_incrHeaderSaveFileName_x3f_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v_optArg_x3f_941_);
v_leanOpts_1992_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_1993_ = lean_ctor_get(v_opts_939_, 1);
v_component_1994_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_1995_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_1996_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_1997_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1998_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_1999_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2000_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_2001_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_2002_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2003_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_2004_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_2005_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_2006_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_2007_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_2008_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_2009_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2010_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2011_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_2012_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2013_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2014_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2015_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2017_ = v_opts_939_;
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2015_);
lean_inc(v_incrLoadFileName_x3f_2014_);
lean_inc(v_incrSaveFileName_x3f_2013_);
lean_inc(v_errorOnKinds_2010_);
lean_inc(v_bcFileName_x3f_2008_);
lean_inc(v_cFileName_x3f_2007_);
lean_inc(v_ileanFileName_x3f_2006_);
lean_inc(v_oleanFileName_x3f_2005_);
lean_inc(v_setupFileName_x3f_2004_);
lean_inc(v_rootDir_x3f_2003_);
lean_inc(v_opts_2000_);
lean_inc(v_forwardedArgs_1993_);
lean_inc(v_leanOpts_1992_);
lean_dec(v_opts_939_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_leanOpts_1992_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_forwardedArgs_1993_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_opts_2000_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_rootDir_x3f_2003_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_setupFileName_x3f_2004_);
lean_ctor_set(v_reuseFailAlloc_2022_, 5, v_oleanFileName_x3f_2005_);
lean_ctor_set(v_reuseFailAlloc_2022_, 6, v_ileanFileName_x3f_2006_);
lean_ctor_set(v_reuseFailAlloc_2022_, 7, v_cFileName_x3f_2007_);
lean_ctor_set(v_reuseFailAlloc_2022_, 8, v_bcFileName_x3f_2008_);
lean_ctor_set(v_reuseFailAlloc_2022_, 9, v_errorOnKinds_2010_);
lean_ctor_set(v_reuseFailAlloc_2022_, 10, v_incrSaveFileName_x3f_2013_);
lean_ctor_set(v_reuseFailAlloc_2022_, 11, v_incrLoadFileName_x3f_2014_);
lean_ctor_set(v_reuseFailAlloc_2022_, 12, v_incrHeaderSaveFileName_x3f_2015_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*13 + 8, v_component_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*13 + 9, v_printPrefix_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*13 + 10, v_printLibDir_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*13 + 11, v_useStdin_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*13 + 13, v_onlySrcDeps_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*13 + 14, v_depsJson_1999_);
lean_ctor_set_uint32(v_reuseFailAlloc_2022_, sizeof(void*)*13, v_trustLevel_2001_);
lean_ctor_set_uint32(v_reuseFailAlloc_2022_, sizeof(void*)*13 + 4, v_numThreads_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*13 + 15, v_jsonOutput_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*13 + 16, v_printStats_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*13 + 17, v_run_2012_);
v___x_2020_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; 
lean_ctor_set_uint8(v___x_2020_, sizeof(void*)*13 + 12, v___x_1200_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
}
}
}
else
{
lean_object* v_leanOpts_2024_; lean_object* v_forwardedArgs_2025_; uint8_t v_component_2026_; uint8_t v_printPrefix_2027_; uint8_t v_printLibDir_2028_; uint8_t v_useStdin_2029_; uint8_t v_onlyDeps_2030_; uint8_t v_onlySrcDeps_2031_; uint8_t v_depsJson_2032_; lean_object* v_opts_2033_; uint32_t v_trustLevel_2034_; uint32_t v_numThreads_2035_; lean_object* v_rootDir_x3f_2036_; lean_object* v_setupFileName_x3f_2037_; lean_object* v_oleanFileName_x3f_2038_; lean_object* v_ileanFileName_x3f_2039_; lean_object* v_cFileName_x3f_2040_; lean_object* v_bcFileName_x3f_2041_; uint8_t v_jsonOutput_2042_; lean_object* v_errorOnKinds_2043_; uint8_t v_printStats_2044_; uint8_t v_run_2045_; lean_object* v_incrSaveFileName_x3f_2046_; lean_object* v_incrLoadFileName_x3f_2047_; lean_object* v_incrHeaderSaveFileName_x3f_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_optArg_x3f_941_);
v_leanOpts_2024_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_2025_ = lean_ctor_get(v_opts_939_, 1);
v_component_2026_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_2027_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_2028_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_2029_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_2030_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2031_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_2032_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2033_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_2034_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_2035_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2036_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_2037_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_2038_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_2039_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_2040_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_2041_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_2042_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2043_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2044_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_2045_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2046_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2047_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2048_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2050_ = v_opts_939_;
v_isShared_2051_ = v_isSharedCheck_2058_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2048_);
lean_inc(v_incrLoadFileName_x3f_2047_);
lean_inc(v_incrSaveFileName_x3f_2046_);
lean_inc(v_errorOnKinds_2043_);
lean_inc(v_bcFileName_x3f_2041_);
lean_inc(v_cFileName_x3f_2040_);
lean_inc(v_ileanFileName_x3f_2039_);
lean_inc(v_oleanFileName_x3f_2038_);
lean_inc(v_setupFileName_x3f_2037_);
lean_inc(v_rootDir_x3f_2036_);
lean_inc(v_opts_2033_);
lean_inc(v_forwardedArgs_2025_);
lean_inc(v_leanOpts_2024_);
lean_dec(v_opts_939_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2058_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2052_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_2053_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2024_, v___x_2052_, v___x_1196_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v___x_2053_);
v___x_2055_ = v___x_2050_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_forwardedArgs_2025_);
lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_opts_2033_);
lean_ctor_set(v_reuseFailAlloc_2057_, 3, v_rootDir_x3f_2036_);
lean_ctor_set(v_reuseFailAlloc_2057_, 4, v_setupFileName_x3f_2037_);
lean_ctor_set(v_reuseFailAlloc_2057_, 5, v_oleanFileName_x3f_2038_);
lean_ctor_set(v_reuseFailAlloc_2057_, 6, v_ileanFileName_x3f_2039_);
lean_ctor_set(v_reuseFailAlloc_2057_, 7, v_cFileName_x3f_2040_);
lean_ctor_set(v_reuseFailAlloc_2057_, 8, v_bcFileName_x3f_2041_);
lean_ctor_set(v_reuseFailAlloc_2057_, 9, v_errorOnKinds_2043_);
lean_ctor_set(v_reuseFailAlloc_2057_, 10, v_incrSaveFileName_x3f_2046_);
lean_ctor_set(v_reuseFailAlloc_2057_, 11, v_incrLoadFileName_x3f_2047_);
lean_ctor_set(v_reuseFailAlloc_2057_, 12, v_incrHeaderSaveFileName_x3f_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*13 + 8, v_component_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*13 + 9, v_printPrefix_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*13 + 10, v_printLibDir_2028_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*13 + 11, v_useStdin_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*13 + 12, v_onlyDeps_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*13 + 13, v_onlySrcDeps_2031_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*13 + 14, v_depsJson_2032_);
lean_ctor_set_uint32(v_reuseFailAlloc_2057_, sizeof(void*)*13, v_trustLevel_2034_);
lean_ctor_set_uint32(v_reuseFailAlloc_2057_, sizeof(void*)*13 + 4, v_numThreads_2035_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*13 + 15, v_jsonOutput_2042_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*13 + 16, v_printStats_2044_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*13 + 17, v_run_2045_);
v___x_2055_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
}
}
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_2060_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2059_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2114_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2114_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2114_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2065_ = lean_unsigned_to_nat(0u);
v___x_2066_ = lean_string_utf8_byte_size(v_a_2061_);
lean_inc(v_a_2061_);
v___x_2067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2067_, 0, v_a_2061_);
lean_ctor_set(v___x_2067_, 1, v___x_2065_);
lean_ctor_set(v___x_2067_, 2, v___x_2066_);
v___x_2068_ = l_String_Slice_toNat_x3f(v___x_2067_);
lean_dec_ref_known(v___x_2067_, 3);
if (lean_obj_tag(v___x_2068_) == 1)
{
lean_object* v_val_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_val_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_val_2069_);
lean_dec_ref_known(v___x_2068_, 1);
v___x_2070_ = lean_cstr_to_nat("4294967296");
v___x_2071_ = lean_nat_dec_lt(v_val_2069_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec(v_val_2069_);
lean_del_object(v___x_2063_);
lean_dec(v_a_2061_);
lean_dec_ref(v_opts_939_);
v___x_2072_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_2073_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2072_);
lean_dec_ref(v___x_2073_);
goto v___jp_1009_;
}
else
{
lean_object* v_leanOpts_2074_; lean_object* v_forwardedArgs_2075_; uint8_t v_component_2076_; uint8_t v_printPrefix_2077_; uint8_t v_printLibDir_2078_; uint8_t v_useStdin_2079_; uint8_t v_onlyDeps_2080_; uint8_t v_onlySrcDeps_2081_; uint8_t v_depsJson_2082_; lean_object* v_opts_2083_; uint32_t v_numThreads_2084_; lean_object* v_rootDir_x3f_2085_; lean_object* v_setupFileName_x3f_2086_; lean_object* v_oleanFileName_x3f_2087_; lean_object* v_ileanFileName_x3f_2088_; lean_object* v_cFileName_x3f_2089_; lean_object* v_bcFileName_x3f_2090_; uint8_t v_jsonOutput_2091_; lean_object* v_errorOnKinds_2092_; uint8_t v_printStats_2093_; uint8_t v_run_2094_; lean_object* v_incrSaveFileName_x3f_2095_; lean_object* v_incrLoadFileName_x3f_2096_; lean_object* v_incrHeaderSaveFileName_x3f_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2111_; 
v_leanOpts_2074_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_2075_ = lean_ctor_get(v_opts_939_, 1);
v_component_2076_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_2077_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_2078_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_2079_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_2080_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2081_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_2082_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2083_ = lean_ctor_get(v_opts_939_, 2);
v_numThreads_2084_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2085_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_2086_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_2087_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_2088_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_2089_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_2090_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_2091_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2092_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2093_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_2094_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2095_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2096_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2097_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2099_ = v_opts_939_;
v_isShared_2100_ = v_isSharedCheck_2111_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2097_);
lean_inc(v_incrLoadFileName_x3f_2096_);
lean_inc(v_incrSaveFileName_x3f_2095_);
lean_inc(v_errorOnKinds_2092_);
lean_inc(v_bcFileName_x3f_2090_);
lean_inc(v_cFileName_x3f_2089_);
lean_inc(v_ileanFileName_x3f_2088_);
lean_inc(v_oleanFileName_x3f_2087_);
lean_inc(v_setupFileName_x3f_2086_);
lean_inc(v_rootDir_x3f_2085_);
lean_inc(v_opts_2083_);
lean_inc(v_forwardedArgs_2075_);
lean_inc(v_leanOpts_2074_);
lean_dec(v_opts_939_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2111_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
uint32_t v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2101_ = lean_uint32_of_nat(v_val_2069_);
lean_dec(v_val_2069_);
v___x_2102_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_2103_ = lean_string_append(v___x_2102_, v_a_2061_);
lean_dec(v_a_2061_);
v___x_2104_ = lean_array_push(v_forwardedArgs_2075_, v___x_2103_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v___x_2104_);
v___x_2106_ = v___x_2099_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_leanOpts_2074_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_opts_2083_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_rootDir_x3f_2085_);
lean_ctor_set(v_reuseFailAlloc_2110_, 4, v_setupFileName_x3f_2086_);
lean_ctor_set(v_reuseFailAlloc_2110_, 5, v_oleanFileName_x3f_2087_);
lean_ctor_set(v_reuseFailAlloc_2110_, 6, v_ileanFileName_x3f_2088_);
lean_ctor_set(v_reuseFailAlloc_2110_, 7, v_cFileName_x3f_2089_);
lean_ctor_set(v_reuseFailAlloc_2110_, 8, v_bcFileName_x3f_2090_);
lean_ctor_set(v_reuseFailAlloc_2110_, 9, v_errorOnKinds_2092_);
lean_ctor_set(v_reuseFailAlloc_2110_, 10, v_incrSaveFileName_x3f_2095_);
lean_ctor_set(v_reuseFailAlloc_2110_, 11, v_incrLoadFileName_x3f_2096_);
lean_ctor_set(v_reuseFailAlloc_2110_, 12, v_incrHeaderSaveFileName_x3f_2097_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*13 + 8, v_component_2076_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*13 + 9, v_printPrefix_2077_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*13 + 10, v_printLibDir_2078_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*13 + 11, v_useStdin_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*13 + 12, v_onlyDeps_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*13 + 13, v_onlySrcDeps_2081_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*13 + 14, v_depsJson_2082_);
lean_ctor_set_uint32(v_reuseFailAlloc_2110_, sizeof(void*)*13 + 4, v_numThreads_2084_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*13 + 15, v_jsonOutput_2091_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*13 + 16, v_printStats_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*13 + 17, v_run_2094_);
v___x_2106_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
lean_ctor_set_uint32(v___x_2106_, sizeof(void*)*13, v___x_2101_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v___x_2106_);
v___x_2108_ = v___x_2063_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec(v___x_2068_);
lean_del_object(v___x_2063_);
lean_dec(v_a_2061_);
lean_dec_ref(v_opts_939_);
v___x_2112_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_2113_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2112_);
lean_dec_ref(v___x_2113_);
goto v___jp_1006_;
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_dec_ref(v_opts_939_);
v_a_2115_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2060_, 1);
v___x_2119_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2120_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2119_);
lean_dec_ref(v___x_2120_);
goto v___jp_2116_;
v___jp_2116_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_io_error_to_string(v_a_2115_);
v___x_2118_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2117_);
lean_dec_ref(v___x_2118_);
goto v___jp_1003_;
}
}
}
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_2122_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2121_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2174_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2125_ = v___x_2122_;
v_isShared_2126_ = v_isSharedCheck_2174_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2122_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2174_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = lean_string_utf8_byte_size(v_a_2123_);
lean_inc(v_a_2123_);
v___x_2129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2129_, 0, v_a_2123_);
lean_ctor_set(v___x_2129_, 1, v___x_2127_);
lean_ctor_set(v___x_2129_, 2, v___x_2128_);
v___x_2130_ = l_String_Slice_toNat_x3f(v___x_2129_);
lean_dec_ref_known(v___x_2129_, 3);
if (lean_obj_tag(v___x_2130_) == 1)
{
lean_object* v_val_2131_; lean_object* v_leanOpts_2132_; lean_object* v_forwardedArgs_2133_; uint8_t v_component_2134_; uint8_t v_printPrefix_2135_; uint8_t v_printLibDir_2136_; uint8_t v_useStdin_2137_; uint8_t v_onlyDeps_2138_; uint8_t v_onlySrcDeps_2139_; uint8_t v_depsJson_2140_; lean_object* v_opts_2141_; uint32_t v_trustLevel_2142_; uint32_t v_numThreads_2143_; lean_object* v_rootDir_x3f_2144_; lean_object* v_setupFileName_x3f_2145_; lean_object* v_oleanFileName_x3f_2146_; lean_object* v_ileanFileName_x3f_2147_; lean_object* v_cFileName_x3f_2148_; lean_object* v_bcFileName_x3f_2149_; uint8_t v_jsonOutput_2150_; lean_object* v_errorOnKinds_2151_; uint8_t v_printStats_2152_; uint8_t v_run_2153_; lean_object* v_incrSaveFileName_x3f_2154_; lean_object* v_incrLoadFileName_x3f_2155_; lean_object* v_incrHeaderSaveFileName_x3f_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2171_; 
v_val_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_val_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v_leanOpts_2132_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_2133_ = lean_ctor_get(v_opts_939_, 1);
v_component_2134_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_2135_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_2136_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_2137_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_2138_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2139_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_2140_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2141_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_2142_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_2143_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2144_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_2145_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_2146_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_2147_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_2148_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_2149_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_2150_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2151_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2152_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_2153_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2154_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2155_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2156_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2158_ = v_opts_939_;
v_isShared_2159_ = v_isSharedCheck_2171_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2156_);
lean_inc(v_incrLoadFileName_x3f_2155_);
lean_inc(v_incrSaveFileName_x3f_2154_);
lean_inc(v_errorOnKinds_2151_);
lean_inc(v_bcFileName_x3f_2149_);
lean_inc(v_cFileName_x3f_2148_);
lean_inc(v_ileanFileName_x3f_2147_);
lean_inc(v_oleanFileName_x3f_2146_);
lean_inc(v_setupFileName_x3f_2145_);
lean_inc(v_rootDir_x3f_2144_);
lean_inc(v_opts_2141_);
lean_inc(v_forwardedArgs_2133_);
lean_inc(v_leanOpts_2132_);
lean_dec(v_opts_939_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2171_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2160_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_2161_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2132_, v___x_2160_, v_val_2131_);
v___x_2162_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_2163_ = lean_string_append(v___x_2162_, v_a_2123_);
lean_dec(v_a_2123_);
v___x_2164_ = lean_array_push(v_forwardedArgs_2133_, v___x_2163_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 1, v___x_2164_);
lean_ctor_set(v___x_2158_, 0, v___x_2161_);
v___x_2166_ = v___x_2158_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_opts_2141_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v_rootDir_x3f_2144_);
lean_ctor_set(v_reuseFailAlloc_2170_, 4, v_setupFileName_x3f_2145_);
lean_ctor_set(v_reuseFailAlloc_2170_, 5, v_oleanFileName_x3f_2146_);
lean_ctor_set(v_reuseFailAlloc_2170_, 6, v_ileanFileName_x3f_2147_);
lean_ctor_set(v_reuseFailAlloc_2170_, 7, v_cFileName_x3f_2148_);
lean_ctor_set(v_reuseFailAlloc_2170_, 8, v_bcFileName_x3f_2149_);
lean_ctor_set(v_reuseFailAlloc_2170_, 9, v_errorOnKinds_2151_);
lean_ctor_set(v_reuseFailAlloc_2170_, 10, v_incrSaveFileName_x3f_2154_);
lean_ctor_set(v_reuseFailAlloc_2170_, 11, v_incrLoadFileName_x3f_2155_);
lean_ctor_set(v_reuseFailAlloc_2170_, 12, v_incrHeaderSaveFileName_x3f_2156_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*13 + 8, v_component_2134_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*13 + 9, v_printPrefix_2135_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*13 + 10, v_printLibDir_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*13 + 11, v_useStdin_2137_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*13 + 12, v_onlyDeps_2138_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*13 + 13, v_onlySrcDeps_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*13 + 14, v_depsJson_2140_);
lean_ctor_set_uint32(v_reuseFailAlloc_2170_, sizeof(void*)*13, v_trustLevel_2142_);
lean_ctor_set_uint32(v_reuseFailAlloc_2170_, sizeof(void*)*13 + 4, v_numThreads_2143_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*13 + 15, v_jsonOutput_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*13 + 16, v_printStats_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*13 + 17, v_run_2153_);
v___x_2166_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2168_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v___x_2166_);
v___x_2168_ = v___x_2125_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec(v___x_2130_);
lean_del_object(v___x_2125_);
lean_dec(v_a_2123_);
lean_dec_ref(v_opts_939_);
v___x_2172_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_2173_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2172_);
lean_dec_ref(v___x_2173_);
goto v___jp_1116_;
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec_ref(v_opts_939_);
v_a_2175_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2179_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2180_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2179_);
lean_dec_ref(v___x_2180_);
goto v___jp_2176_;
v___jp_2176_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = lean_io_error_to_string(v_a_2175_);
v___x_2178_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2177_);
lean_dec_ref(v___x_2178_);
goto v___jp_1122_;
}
}
}
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_2182_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2181_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2234_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2185_ = v___x_2182_;
v_isShared_2186_ = v_isSharedCheck_2234_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2182_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2234_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2187_ = lean_unsigned_to_nat(0u);
v___x_2188_ = lean_string_utf8_byte_size(v_a_2183_);
lean_inc(v_a_2183_);
v___x_2189_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2189_, 0, v_a_2183_);
lean_ctor_set(v___x_2189_, 1, v___x_2187_);
lean_ctor_set(v___x_2189_, 2, v___x_2188_);
v___x_2190_ = l_String_Slice_toNat_x3f(v___x_2189_);
lean_dec_ref_known(v___x_2189_, 3);
if (lean_obj_tag(v___x_2190_) == 1)
{
lean_object* v_val_2191_; lean_object* v_leanOpts_2192_; lean_object* v_forwardedArgs_2193_; uint8_t v_component_2194_; uint8_t v_printPrefix_2195_; uint8_t v_printLibDir_2196_; uint8_t v_useStdin_2197_; uint8_t v_onlyDeps_2198_; uint8_t v_onlySrcDeps_2199_; uint8_t v_depsJson_2200_; lean_object* v_opts_2201_; uint32_t v_trustLevel_2202_; uint32_t v_numThreads_2203_; lean_object* v_rootDir_x3f_2204_; lean_object* v_setupFileName_x3f_2205_; lean_object* v_oleanFileName_x3f_2206_; lean_object* v_ileanFileName_x3f_2207_; lean_object* v_cFileName_x3f_2208_; lean_object* v_bcFileName_x3f_2209_; uint8_t v_jsonOutput_2210_; lean_object* v_errorOnKinds_2211_; uint8_t v_printStats_2212_; uint8_t v_run_2213_; lean_object* v_incrSaveFileName_x3f_2214_; lean_object* v_incrLoadFileName_x3f_2215_; lean_object* v_incrHeaderSaveFileName_x3f_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2231_; 
v_val_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_val_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v_leanOpts_2192_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_2193_ = lean_ctor_get(v_opts_939_, 1);
v_component_2194_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_2195_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_2196_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_2197_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_2198_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2199_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_2200_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2201_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_2202_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_2203_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2204_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_2205_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_2206_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_2207_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_2208_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_2209_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_2210_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2211_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2212_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_2213_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2214_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2215_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2216_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2218_ = v_opts_939_;
v_isShared_2219_ = v_isSharedCheck_2231_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2216_);
lean_inc(v_incrLoadFileName_x3f_2215_);
lean_inc(v_incrSaveFileName_x3f_2214_);
lean_inc(v_errorOnKinds_2211_);
lean_inc(v_bcFileName_x3f_2209_);
lean_inc(v_cFileName_x3f_2208_);
lean_inc(v_ileanFileName_x3f_2207_);
lean_inc(v_oleanFileName_x3f_2206_);
lean_inc(v_setupFileName_x3f_2205_);
lean_inc(v_rootDir_x3f_2204_);
lean_inc(v_opts_2201_);
lean_inc(v_forwardedArgs_2193_);
lean_inc(v_leanOpts_2192_);
lean_dec(v_opts_939_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2231_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2220_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_2221_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2192_, v___x_2220_, v_val_2191_);
v___x_2222_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2223_ = lean_string_append(v___x_2222_, v_a_2183_);
lean_dec(v_a_2183_);
v___x_2224_ = lean_array_push(v_forwardedArgs_2193_, v___x_2223_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2224_);
lean_ctor_set(v___x_2218_, 0, v___x_2221_);
v___x_2226_ = v___x_2218_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_opts_2201_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v_rootDir_x3f_2204_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v_setupFileName_x3f_2205_);
lean_ctor_set(v_reuseFailAlloc_2230_, 5, v_oleanFileName_x3f_2206_);
lean_ctor_set(v_reuseFailAlloc_2230_, 6, v_ileanFileName_x3f_2207_);
lean_ctor_set(v_reuseFailAlloc_2230_, 7, v_cFileName_x3f_2208_);
lean_ctor_set(v_reuseFailAlloc_2230_, 8, v_bcFileName_x3f_2209_);
lean_ctor_set(v_reuseFailAlloc_2230_, 9, v_errorOnKinds_2211_);
lean_ctor_set(v_reuseFailAlloc_2230_, 10, v_incrSaveFileName_x3f_2214_);
lean_ctor_set(v_reuseFailAlloc_2230_, 11, v_incrLoadFileName_x3f_2215_);
lean_ctor_set(v_reuseFailAlloc_2230_, 12, v_incrHeaderSaveFileName_x3f_2216_);
lean_ctor_set_uint8(v_reuseFailAlloc_2230_, sizeof(void*)*13 + 8, v_component_2194_);
lean_ctor_set_uint8(v_reuseFailAlloc_2230_, sizeof(void*)*13 + 9, v_printPrefix_2195_);
lean_ctor_set_uint8(v_reuseFailAlloc_2230_, sizeof(void*)*13 + 10, v_printLibDir_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2230_, sizeof(void*)*13 + 11, v_useStdin_2197_);
lean_ctor_set_uint8(v_reuseFailAlloc_2230_, sizeof(void*)*13 + 12, v_onlyDeps_2198_);
lean_ctor_set_uint8(v_reuseFailAlloc_2230_, sizeof(void*)*13 + 13, v_onlySrcDeps_2199_);
lean_ctor_set_uint8(v_reuseFailAlloc_2230_, sizeof(void*)*13 + 14, v_depsJson_2200_);
lean_ctor_set_uint32(v_reuseFailAlloc_2230_, sizeof(void*)*13, v_trustLevel_2202_);
lean_ctor_set_uint32(v_reuseFailAlloc_2230_, sizeof(void*)*13 + 4, v_numThreads_2203_);
lean_ctor_set_uint8(v_reuseFailAlloc_2230_, sizeof(void*)*13 + 15, v_jsonOutput_2210_);
lean_ctor_set_uint8(v_reuseFailAlloc_2230_, sizeof(void*)*13 + 16, v_printStats_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2230_, sizeof(void*)*13 + 17, v_run_2213_);
v___x_2226_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2228_; 
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2226_);
v___x_2228_ = v___x_2185_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_dec(v___x_2190_);
lean_del_object(v___x_2185_);
lean_dec(v_a_2183_);
lean_dec_ref(v_opts_939_);
v___x_2232_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2233_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2232_);
lean_dec_ref(v___x_2233_);
goto v___jp_997_;
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec_ref(v_opts_939_);
v_a_2235_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2182_, 1);
v___x_2239_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2240_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2239_);
lean_dec_ref(v___x_2240_);
goto v___jp_2236_;
v___jp_2236_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_io_error_to_string(v_a_2235_);
v___x_2238_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2237_);
lean_dec_ref(v___x_2238_);
goto v___jp_994_;
}
}
}
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2242_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2241_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2286_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2286_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2286_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v_leanOpts_2247_; lean_object* v_forwardedArgs_2248_; uint8_t v_component_2249_; uint8_t v_printPrefix_2250_; uint8_t v_printLibDir_2251_; uint8_t v_useStdin_2252_; uint8_t v_onlyDeps_2253_; uint8_t v_onlySrcDeps_2254_; uint8_t v_depsJson_2255_; lean_object* v_opts_2256_; uint32_t v_trustLevel_2257_; uint32_t v_numThreads_2258_; lean_object* v_setupFileName_x3f_2259_; lean_object* v_oleanFileName_x3f_2260_; lean_object* v_ileanFileName_x3f_2261_; lean_object* v_cFileName_x3f_2262_; lean_object* v_bcFileName_x3f_2263_; uint8_t v_jsonOutput_2264_; lean_object* v_errorOnKinds_2265_; uint8_t v_printStats_2266_; uint8_t v_run_2267_; lean_object* v_incrSaveFileName_x3f_2268_; lean_object* v_incrLoadFileName_x3f_2269_; lean_object* v_incrHeaderSaveFileName_x3f_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2284_; 
v_leanOpts_2247_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_2248_ = lean_ctor_get(v_opts_939_, 1);
v_component_2249_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_2250_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_2251_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_2252_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_2253_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2254_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_2255_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2256_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_2257_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_2258_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_setupFileName_x3f_2259_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_2260_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_2261_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_2262_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_2263_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_2264_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2265_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2266_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_2267_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2268_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2269_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2270_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2284_ == 0)
{
lean_object* v_unused_2285_; 
v_unused_2285_ = lean_ctor_get(v_opts_939_, 3);
lean_dec(v_unused_2285_);
v___x_2272_ = v_opts_939_;
v_isShared_2273_ = v_isSharedCheck_2284_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2270_);
lean_inc(v_incrLoadFileName_x3f_2269_);
lean_inc(v_incrSaveFileName_x3f_2268_);
lean_inc(v_errorOnKinds_2265_);
lean_inc(v_bcFileName_x3f_2263_);
lean_inc(v_cFileName_x3f_2262_);
lean_inc(v_ileanFileName_x3f_2261_);
lean_inc(v_oleanFileName_x3f_2260_);
lean_inc(v_setupFileName_x3f_2259_);
lean_inc(v_opts_2256_);
lean_inc(v_forwardedArgs_2248_);
lean_inc(v_leanOpts_2247_);
lean_dec(v_opts_939_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2284_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2274_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2275_ = lean_string_append(v___x_2274_, v_a_2243_);
v___x_2276_ = lean_array_push(v_forwardedArgs_2248_, v___x_2275_);
v___x_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2277_, 0, v_a_2243_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 3, v___x_2277_);
lean_ctor_set(v___x_2272_, 1, v___x_2276_);
v___x_2279_ = v___x_2272_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_leanOpts_2247_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2283_, 2, v_opts_2256_);
lean_ctor_set(v_reuseFailAlloc_2283_, 3, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2283_, 4, v_setupFileName_x3f_2259_);
lean_ctor_set(v_reuseFailAlloc_2283_, 5, v_oleanFileName_x3f_2260_);
lean_ctor_set(v_reuseFailAlloc_2283_, 6, v_ileanFileName_x3f_2261_);
lean_ctor_set(v_reuseFailAlloc_2283_, 7, v_cFileName_x3f_2262_);
lean_ctor_set(v_reuseFailAlloc_2283_, 8, v_bcFileName_x3f_2263_);
lean_ctor_set(v_reuseFailAlloc_2283_, 9, v_errorOnKinds_2265_);
lean_ctor_set(v_reuseFailAlloc_2283_, 10, v_incrSaveFileName_x3f_2268_);
lean_ctor_set(v_reuseFailAlloc_2283_, 11, v_incrLoadFileName_x3f_2269_);
lean_ctor_set(v_reuseFailAlloc_2283_, 12, v_incrHeaderSaveFileName_x3f_2270_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*13 + 8, v_component_2249_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*13 + 9, v_printPrefix_2250_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*13 + 10, v_printLibDir_2251_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*13 + 11, v_useStdin_2252_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*13 + 12, v_onlyDeps_2253_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*13 + 13, v_onlySrcDeps_2254_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*13 + 14, v_depsJson_2255_);
lean_ctor_set_uint32(v_reuseFailAlloc_2283_, sizeof(void*)*13, v_trustLevel_2257_);
lean_ctor_set_uint32(v_reuseFailAlloc_2283_, sizeof(void*)*13 + 4, v_numThreads_2258_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*13 + 15, v_jsonOutput_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*13 + 16, v_printStats_2266_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*13 + 17, v_run_2267_);
v___x_2279_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2281_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2279_);
v___x_2281_ = v___x_2245_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec_ref(v_opts_939_);
v_a_2287_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2242_, 1);
v___x_2291_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2292_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2291_);
lean_dec_ref(v___x_2292_);
goto v___jp_2288_;
v___jp_2288_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = lean_io_error_to_string(v_a_2287_);
v___x_2290_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2289_);
lean_dec_ref(v___x_2290_);
goto v___jp_1128_;
}
}
}
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25));
v___x_2294_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2293_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2335_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2335_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2335_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_leanOpts_2299_; lean_object* v_forwardedArgs_2300_; uint8_t v_component_2301_; uint8_t v_printPrefix_2302_; uint8_t v_printLibDir_2303_; uint8_t v_useStdin_2304_; uint8_t v_onlyDeps_2305_; uint8_t v_onlySrcDeps_2306_; uint8_t v_depsJson_2307_; lean_object* v_opts_2308_; uint32_t v_trustLevel_2309_; uint32_t v_numThreads_2310_; lean_object* v_rootDir_x3f_2311_; lean_object* v_setupFileName_x3f_2312_; lean_object* v_oleanFileName_x3f_2313_; lean_object* v_cFileName_x3f_2314_; lean_object* v_bcFileName_x3f_2315_; uint8_t v_jsonOutput_2316_; lean_object* v_errorOnKinds_2317_; uint8_t v_printStats_2318_; uint8_t v_run_2319_; lean_object* v_incrSaveFileName_x3f_2320_; lean_object* v_incrLoadFileName_x3f_2321_; lean_object* v_incrHeaderSaveFileName_x3f_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2333_; 
v_leanOpts_2299_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_2300_ = lean_ctor_get(v_opts_939_, 1);
v_component_2301_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_2302_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_2303_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_2304_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_2305_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2306_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_2307_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2308_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_2309_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_2310_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2311_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_2312_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_2313_ = lean_ctor_get(v_opts_939_, 5);
v_cFileName_x3f_2314_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_2315_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_2316_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2317_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2318_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_2319_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2320_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2321_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2322_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v_opts_939_, 6);
lean_dec(v_unused_2334_);
v___x_2324_ = v_opts_939_;
v_isShared_2325_ = v_isSharedCheck_2333_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2322_);
lean_inc(v_incrLoadFileName_x3f_2321_);
lean_inc(v_incrSaveFileName_x3f_2320_);
lean_inc(v_errorOnKinds_2317_);
lean_inc(v_bcFileName_x3f_2315_);
lean_inc(v_cFileName_x3f_2314_);
lean_inc(v_oleanFileName_x3f_2313_);
lean_inc(v_setupFileName_x3f_2312_);
lean_inc(v_rootDir_x3f_2311_);
lean_inc(v_opts_2308_);
lean_inc(v_forwardedArgs_2300_);
lean_inc(v_leanOpts_2299_);
lean_dec(v_opts_939_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2333_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2326_, 0, v_a_2295_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 6, v___x_2326_);
v___x_2328_ = v___x_2324_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_leanOpts_2299_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_forwardedArgs_2300_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_opts_2308_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_rootDir_x3f_2311_);
lean_ctor_set(v_reuseFailAlloc_2332_, 4, v_setupFileName_x3f_2312_);
lean_ctor_set(v_reuseFailAlloc_2332_, 5, v_oleanFileName_x3f_2313_);
lean_ctor_set(v_reuseFailAlloc_2332_, 6, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2332_, 7, v_cFileName_x3f_2314_);
lean_ctor_set(v_reuseFailAlloc_2332_, 8, v_bcFileName_x3f_2315_);
lean_ctor_set(v_reuseFailAlloc_2332_, 9, v_errorOnKinds_2317_);
lean_ctor_set(v_reuseFailAlloc_2332_, 10, v_incrSaveFileName_x3f_2320_);
lean_ctor_set(v_reuseFailAlloc_2332_, 11, v_incrLoadFileName_x3f_2321_);
lean_ctor_set(v_reuseFailAlloc_2332_, 12, v_incrHeaderSaveFileName_x3f_2322_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*13 + 8, v_component_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*13 + 9, v_printPrefix_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*13 + 10, v_printLibDir_2303_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*13 + 11, v_useStdin_2304_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*13 + 12, v_onlyDeps_2305_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*13 + 13, v_onlySrcDeps_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*13 + 14, v_depsJson_2307_);
lean_ctor_set_uint32(v_reuseFailAlloc_2332_, sizeof(void*)*13, v_trustLevel_2309_);
lean_ctor_set_uint32(v_reuseFailAlloc_2332_, sizeof(void*)*13 + 4, v_numThreads_2310_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*13 + 15, v_jsonOutput_2316_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*13 + 16, v_printStats_2318_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*13 + 17, v_run_2319_);
v___x_2328_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2330_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2328_);
v___x_2330_ = v___x_2297_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec_ref(v_opts_939_);
v_a_2336_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2340_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2341_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2340_);
lean_dec_ref(v___x_2341_);
goto v___jp_2337_;
v___jp_2337_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_io_error_to_string(v_a_2336_);
v___x_2339_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2338_);
lean_dec_ref(v___x_2339_);
goto v___jp_988_;
}
}
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2343_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2342_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2384_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2384_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2384_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v_leanOpts_2348_; lean_object* v_forwardedArgs_2349_; uint8_t v_component_2350_; uint8_t v_printPrefix_2351_; uint8_t v_printLibDir_2352_; uint8_t v_useStdin_2353_; uint8_t v_onlyDeps_2354_; uint8_t v_onlySrcDeps_2355_; uint8_t v_depsJson_2356_; lean_object* v_opts_2357_; uint32_t v_trustLevel_2358_; uint32_t v_numThreads_2359_; lean_object* v_rootDir_x3f_2360_; lean_object* v_setupFileName_x3f_2361_; lean_object* v_ileanFileName_x3f_2362_; lean_object* v_cFileName_x3f_2363_; lean_object* v_bcFileName_x3f_2364_; uint8_t v_jsonOutput_2365_; lean_object* v_errorOnKinds_2366_; uint8_t v_printStats_2367_; uint8_t v_run_2368_; lean_object* v_incrSaveFileName_x3f_2369_; lean_object* v_incrLoadFileName_x3f_2370_; lean_object* v_incrHeaderSaveFileName_x3f_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2382_; 
v_leanOpts_2348_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_2349_ = lean_ctor_get(v_opts_939_, 1);
v_component_2350_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_2351_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_2352_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_2353_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_2354_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2355_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_2356_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2357_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_2358_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_2359_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2360_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_2361_ = lean_ctor_get(v_opts_939_, 4);
v_ileanFileName_x3f_2362_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_2363_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_2364_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_2365_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2366_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2367_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_2368_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2369_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2370_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2371_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2382_ == 0)
{
lean_object* v_unused_2383_; 
v_unused_2383_ = lean_ctor_get(v_opts_939_, 5);
lean_dec(v_unused_2383_);
v___x_2373_ = v_opts_939_;
v_isShared_2374_ = v_isSharedCheck_2382_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2371_);
lean_inc(v_incrLoadFileName_x3f_2370_);
lean_inc(v_incrSaveFileName_x3f_2369_);
lean_inc(v_errorOnKinds_2366_);
lean_inc(v_bcFileName_x3f_2364_);
lean_inc(v_cFileName_x3f_2363_);
lean_inc(v_ileanFileName_x3f_2362_);
lean_inc(v_setupFileName_x3f_2361_);
lean_inc(v_rootDir_x3f_2360_);
lean_inc(v_opts_2357_);
lean_inc(v_forwardedArgs_2349_);
lean_inc(v_leanOpts_2348_);
lean_dec(v_opts_939_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2382_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2375_, 0, v_a_2344_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 5, v___x_2375_);
v___x_2377_ = v___x_2373_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_leanOpts_2348_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_forwardedArgs_2349_);
lean_ctor_set(v_reuseFailAlloc_2381_, 2, v_opts_2357_);
lean_ctor_set(v_reuseFailAlloc_2381_, 3, v_rootDir_x3f_2360_);
lean_ctor_set(v_reuseFailAlloc_2381_, 4, v_setupFileName_x3f_2361_);
lean_ctor_set(v_reuseFailAlloc_2381_, 5, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2381_, 6, v_ileanFileName_x3f_2362_);
lean_ctor_set(v_reuseFailAlloc_2381_, 7, v_cFileName_x3f_2363_);
lean_ctor_set(v_reuseFailAlloc_2381_, 8, v_bcFileName_x3f_2364_);
lean_ctor_set(v_reuseFailAlloc_2381_, 9, v_errorOnKinds_2366_);
lean_ctor_set(v_reuseFailAlloc_2381_, 10, v_incrSaveFileName_x3f_2369_);
lean_ctor_set(v_reuseFailAlloc_2381_, 11, v_incrLoadFileName_x3f_2370_);
lean_ctor_set(v_reuseFailAlloc_2381_, 12, v_incrHeaderSaveFileName_x3f_2371_);
lean_ctor_set_uint8(v_reuseFailAlloc_2381_, sizeof(void*)*13 + 8, v_component_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2381_, sizeof(void*)*13 + 9, v_printPrefix_2351_);
lean_ctor_set_uint8(v_reuseFailAlloc_2381_, sizeof(void*)*13 + 10, v_printLibDir_2352_);
lean_ctor_set_uint8(v_reuseFailAlloc_2381_, sizeof(void*)*13 + 11, v_useStdin_2353_);
lean_ctor_set_uint8(v_reuseFailAlloc_2381_, sizeof(void*)*13 + 12, v_onlyDeps_2354_);
lean_ctor_set_uint8(v_reuseFailAlloc_2381_, sizeof(void*)*13 + 13, v_onlySrcDeps_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2381_, sizeof(void*)*13 + 14, v_depsJson_2356_);
lean_ctor_set_uint32(v_reuseFailAlloc_2381_, sizeof(void*)*13, v_trustLevel_2358_);
lean_ctor_set_uint32(v_reuseFailAlloc_2381_, sizeof(void*)*13 + 4, v_numThreads_2359_);
lean_ctor_set_uint8(v_reuseFailAlloc_2381_, sizeof(void*)*13 + 15, v_jsonOutput_2365_);
lean_ctor_set_uint8(v_reuseFailAlloc_2381_, sizeof(void*)*13 + 16, v_printStats_2367_);
lean_ctor_set_uint8(v_reuseFailAlloc_2381_, sizeof(void*)*13 + 17, v_run_2368_);
v___x_2377_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2379_; 
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2377_);
v___x_2379_ = v___x_2346_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_dec_ref(v_opts_939_);
v_a_2385_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2343_, 1);
v___x_2389_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2390_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2389_);
lean_dec_ref(v___x_2390_);
goto v___jp_2386_;
v___jp_2386_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_io_error_to_string(v_a_2385_);
v___x_2388_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2387_);
lean_dec_ref(v___x_2388_);
goto v___jp_1134_;
}
}
}
}
else
{
lean_object* v_leanOpts_2391_; lean_object* v_forwardedArgs_2392_; uint8_t v_component_2393_; uint8_t v_printPrefix_2394_; uint8_t v_printLibDir_2395_; uint8_t v_useStdin_2396_; uint8_t v_onlyDeps_2397_; uint8_t v_onlySrcDeps_2398_; uint8_t v_depsJson_2399_; lean_object* v_opts_2400_; uint32_t v_trustLevel_2401_; uint32_t v_numThreads_2402_; lean_object* v_rootDir_x3f_2403_; lean_object* v_setupFileName_x3f_2404_; lean_object* v_oleanFileName_x3f_2405_; lean_object* v_ileanFileName_x3f_2406_; lean_object* v_cFileName_x3f_2407_; lean_object* v_bcFileName_x3f_2408_; uint8_t v_jsonOutput_2409_; lean_object* v_errorOnKinds_2410_; uint8_t v_printStats_2411_; lean_object* v_incrSaveFileName_x3f_2412_; lean_object* v_incrLoadFileName_x3f_2413_; lean_object* v_incrHeaderSaveFileName_x3f_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2424_; 
lean_dec(v_optArg_x3f_941_);
v_leanOpts_2391_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_2392_ = lean_ctor_get(v_opts_939_, 1);
v_component_2393_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_2394_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_2395_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_2396_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_2397_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2398_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_2399_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2400_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_2401_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_2402_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2403_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_2404_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_2405_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_2406_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_2407_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_2408_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_2409_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2410_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2411_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_incrSaveFileName_x3f_2412_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2413_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2414_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2416_ = v_opts_939_;
v_isShared_2417_ = v_isSharedCheck_2424_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2414_);
lean_inc(v_incrLoadFileName_x3f_2413_);
lean_inc(v_incrSaveFileName_x3f_2412_);
lean_inc(v_errorOnKinds_2410_);
lean_inc(v_bcFileName_x3f_2408_);
lean_inc(v_cFileName_x3f_2407_);
lean_inc(v_ileanFileName_x3f_2406_);
lean_inc(v_oleanFileName_x3f_2405_);
lean_inc(v_setupFileName_x3f_2404_);
lean_inc(v_rootDir_x3f_2403_);
lean_inc(v_opts_2400_);
lean_inc(v_forwardedArgs_2392_);
lean_inc(v_leanOpts_2391_);
lean_dec(v_opts_939_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2424_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2418_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2419_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2391_, v___x_2418_, v___x_1182_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2419_);
v___x_2421_ = v___x_2416_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_forwardedArgs_2392_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_opts_2400_);
lean_ctor_set(v_reuseFailAlloc_2423_, 3, v_rootDir_x3f_2403_);
lean_ctor_set(v_reuseFailAlloc_2423_, 4, v_setupFileName_x3f_2404_);
lean_ctor_set(v_reuseFailAlloc_2423_, 5, v_oleanFileName_x3f_2405_);
lean_ctor_set(v_reuseFailAlloc_2423_, 6, v_ileanFileName_x3f_2406_);
lean_ctor_set(v_reuseFailAlloc_2423_, 7, v_cFileName_x3f_2407_);
lean_ctor_set(v_reuseFailAlloc_2423_, 8, v_bcFileName_x3f_2408_);
lean_ctor_set(v_reuseFailAlloc_2423_, 9, v_errorOnKinds_2410_);
lean_ctor_set(v_reuseFailAlloc_2423_, 10, v_incrSaveFileName_x3f_2412_);
lean_ctor_set(v_reuseFailAlloc_2423_, 11, v_incrLoadFileName_x3f_2413_);
lean_ctor_set(v_reuseFailAlloc_2423_, 12, v_incrHeaderSaveFileName_x3f_2414_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*13 + 8, v_component_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*13 + 9, v_printPrefix_2394_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*13 + 10, v_printLibDir_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*13 + 11, v_useStdin_2396_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*13 + 12, v_onlyDeps_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*13 + 13, v_onlySrcDeps_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*13 + 14, v_depsJson_2399_);
lean_ctor_set_uint32(v_reuseFailAlloc_2423_, sizeof(void*)*13, v_trustLevel_2401_);
lean_ctor_set_uint32(v_reuseFailAlloc_2423_, sizeof(void*)*13 + 4, v_numThreads_2402_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*13 + 15, v_jsonOutput_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*13 + 16, v_printStats_2411_);
v___x_2421_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; 
lean_ctor_set_uint8(v___x_2421_, sizeof(void*)*13 + 17, v___x_1184_);
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
return v___x_2422_;
}
}
}
}
else
{
lean_object* v_leanOpts_2425_; lean_object* v_forwardedArgs_2426_; uint8_t v_component_2427_; uint8_t v_printPrefix_2428_; uint8_t v_printLibDir_2429_; uint8_t v_onlyDeps_2430_; uint8_t v_onlySrcDeps_2431_; uint8_t v_depsJson_2432_; lean_object* v_opts_2433_; uint32_t v_trustLevel_2434_; uint32_t v_numThreads_2435_; lean_object* v_rootDir_x3f_2436_; lean_object* v_setupFileName_x3f_2437_; lean_object* v_oleanFileName_x3f_2438_; lean_object* v_ileanFileName_x3f_2439_; lean_object* v_cFileName_x3f_2440_; lean_object* v_bcFileName_x3f_2441_; uint8_t v_jsonOutput_2442_; lean_object* v_errorOnKinds_2443_; uint8_t v_printStats_2444_; uint8_t v_run_2445_; lean_object* v_incrSaveFileName_x3f_2446_; lean_object* v_incrLoadFileName_x3f_2447_; lean_object* v_incrHeaderSaveFileName_x3f_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v_optArg_x3f_941_);
v_leanOpts_2425_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_2426_ = lean_ctor_get(v_opts_939_, 1);
v_component_2427_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_2428_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_2429_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_onlyDeps_2430_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2431_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_2432_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2433_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_2434_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_2435_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2436_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_2437_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_2438_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_2439_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_2440_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_2441_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_2442_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2443_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2444_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_2445_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2446_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2447_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2448_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2450_ = v_opts_939_;
v_isShared_2451_ = v_isSharedCheck_2456_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2448_);
lean_inc(v_incrLoadFileName_x3f_2447_);
lean_inc(v_incrSaveFileName_x3f_2446_);
lean_inc(v_errorOnKinds_2443_);
lean_inc(v_bcFileName_x3f_2441_);
lean_inc(v_cFileName_x3f_2440_);
lean_inc(v_ileanFileName_x3f_2439_);
lean_inc(v_oleanFileName_x3f_2438_);
lean_inc(v_setupFileName_x3f_2437_);
lean_inc(v_rootDir_x3f_2436_);
lean_inc(v_opts_2433_);
lean_inc(v_forwardedArgs_2426_);
lean_inc(v_leanOpts_2425_);
lean_dec(v_opts_939_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2456_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_leanOpts_2425_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_forwardedArgs_2426_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_opts_2433_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v_rootDir_x3f_2436_);
lean_ctor_set(v_reuseFailAlloc_2455_, 4, v_setupFileName_x3f_2437_);
lean_ctor_set(v_reuseFailAlloc_2455_, 5, v_oleanFileName_x3f_2438_);
lean_ctor_set(v_reuseFailAlloc_2455_, 6, v_ileanFileName_x3f_2439_);
lean_ctor_set(v_reuseFailAlloc_2455_, 7, v_cFileName_x3f_2440_);
lean_ctor_set(v_reuseFailAlloc_2455_, 8, v_bcFileName_x3f_2441_);
lean_ctor_set(v_reuseFailAlloc_2455_, 9, v_errorOnKinds_2443_);
lean_ctor_set(v_reuseFailAlloc_2455_, 10, v_incrSaveFileName_x3f_2446_);
lean_ctor_set(v_reuseFailAlloc_2455_, 11, v_incrLoadFileName_x3f_2447_);
lean_ctor_set(v_reuseFailAlloc_2455_, 12, v_incrHeaderSaveFileName_x3f_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2455_, sizeof(void*)*13 + 8, v_component_2427_);
lean_ctor_set_uint8(v_reuseFailAlloc_2455_, sizeof(void*)*13 + 9, v_printPrefix_2428_);
lean_ctor_set_uint8(v_reuseFailAlloc_2455_, sizeof(void*)*13 + 10, v_printLibDir_2429_);
lean_ctor_set_uint8(v_reuseFailAlloc_2455_, sizeof(void*)*13 + 12, v_onlyDeps_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2455_, sizeof(void*)*13 + 13, v_onlySrcDeps_2431_);
lean_ctor_set_uint8(v_reuseFailAlloc_2455_, sizeof(void*)*13 + 14, v_depsJson_2432_);
lean_ctor_set_uint32(v_reuseFailAlloc_2455_, sizeof(void*)*13, v_trustLevel_2434_);
lean_ctor_set_uint32(v_reuseFailAlloc_2455_, sizeof(void*)*13 + 4, v_numThreads_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2455_, sizeof(void*)*13 + 15, v_jsonOutput_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2455_, sizeof(void*)*13 + 16, v_printStats_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2455_, sizeof(void*)*13 + 17, v_run_2445_);
v___x_2453_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
lean_object* v___x_2454_; 
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*13 + 11, v___x_1182_);
v___x_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
return v___x_2454_;
}
}
}
}
else
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2458_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2457_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2520_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2520_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2520_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2463_ = lean_unsigned_to_nat(0u);
v___x_2464_ = lean_string_utf8_byte_size(v_a_2459_);
lean_inc(v_a_2459_);
v___x_2465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2465_, 0, v_a_2459_);
lean_ctor_set(v___x_2465_, 1, v___x_2463_);
lean_ctor_set(v___x_2465_, 2, v___x_2464_);
v___x_2466_ = l_String_Slice_toNat_x3f(v___x_2465_);
lean_dec_ref_known(v___x_2465_, 3);
if (lean_obj_tag(v___x_2466_) == 1)
{
lean_object* v_val_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
v_val_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_val_2467_);
lean_dec_ref_known(v___x_2466_, 1);
v___x_2468_ = lean_unsigned_to_nat(4u);
v___x_2469_ = lean_unsigned_to_nat(2u);
v___x_2470_ = lean_nat_shiftr(v_val_2467_, v___x_2469_);
lean_dec(v_val_2467_);
v___x_2471_ = lean_nat_mul(v___x_2470_, v___x_2468_);
lean_dec(v___x_2470_);
v___x_2472_ = lean_unsigned_to_nat(1024u);
v___x_2473_ = lean_nat_mul(v___x_2471_, v___x_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28);
v___x_2475_ = lean_nat_dec_lt(v___x_2473_, v___x_2474_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_dec(v___x_2473_);
lean_del_object(v___x_2461_);
lean_dec(v_a_2459_);
lean_dec_ref(v_opts_939_);
v___x_2476_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2477_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2476_);
lean_dec_ref(v___x_2477_);
goto v___jp_982_;
}
else
{
size_t v___x_2478_; lean_object* v___x_2479_; lean_object* v_leanOpts_2480_; lean_object* v_forwardedArgs_2481_; uint8_t v_component_2482_; uint8_t v_printPrefix_2483_; uint8_t v_printLibDir_2484_; uint8_t v_useStdin_2485_; uint8_t v_onlyDeps_2486_; uint8_t v_onlySrcDeps_2487_; uint8_t v_depsJson_2488_; lean_object* v_opts_2489_; uint32_t v_trustLevel_2490_; uint32_t v_numThreads_2491_; lean_object* v_rootDir_x3f_2492_; lean_object* v_setupFileName_x3f_2493_; lean_object* v_oleanFileName_x3f_2494_; lean_object* v_ileanFileName_x3f_2495_; lean_object* v_cFileName_x3f_2496_; lean_object* v_bcFileName_x3f_2497_; uint8_t v_jsonOutput_2498_; lean_object* v_errorOnKinds_2499_; uint8_t v_printStats_2500_; uint8_t v_run_2501_; lean_object* v_incrSaveFileName_x3f_2502_; lean_object* v_incrLoadFileName_x3f_2503_; lean_object* v_incrHeaderSaveFileName_x3f_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2517_; 
v___x_2478_ = lean_usize_of_nat(v___x_2473_);
lean_dec(v___x_2473_);
v___x_2479_ = lean_internal_set_thread_stack_size(v___x_2478_);
v_leanOpts_2480_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_2481_ = lean_ctor_get(v_opts_939_, 1);
v_component_2482_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_2483_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_2484_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_2485_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_2486_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2487_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_2488_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2489_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_2490_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_2491_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2492_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_2493_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_2494_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_2495_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_2496_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_2497_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_2498_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2499_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2500_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_2501_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2502_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2503_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2504_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2517_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2506_ = v_opts_939_;
v_isShared_2507_ = v_isSharedCheck_2517_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2504_);
lean_inc(v_incrLoadFileName_x3f_2503_);
lean_inc(v_incrSaveFileName_x3f_2502_);
lean_inc(v_errorOnKinds_2499_);
lean_inc(v_bcFileName_x3f_2497_);
lean_inc(v_cFileName_x3f_2496_);
lean_inc(v_ileanFileName_x3f_2495_);
lean_inc(v_oleanFileName_x3f_2494_);
lean_inc(v_setupFileName_x3f_2493_);
lean_inc(v_rootDir_x3f_2492_);
lean_inc(v_opts_2489_);
lean_inc(v_forwardedArgs_2481_);
lean_inc(v_leanOpts_2480_);
lean_dec(v_opts_939_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2517_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2508_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2509_ = lean_string_append(v___x_2508_, v_a_2459_);
lean_dec(v_a_2459_);
v___x_2510_ = lean_array_push(v_forwardedArgs_2481_, v___x_2509_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 1, v___x_2510_);
v___x_2512_ = v___x_2506_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_leanOpts_2480_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2516_, 2, v_opts_2489_);
lean_ctor_set(v_reuseFailAlloc_2516_, 3, v_rootDir_x3f_2492_);
lean_ctor_set(v_reuseFailAlloc_2516_, 4, v_setupFileName_x3f_2493_);
lean_ctor_set(v_reuseFailAlloc_2516_, 5, v_oleanFileName_x3f_2494_);
lean_ctor_set(v_reuseFailAlloc_2516_, 6, v_ileanFileName_x3f_2495_);
lean_ctor_set(v_reuseFailAlloc_2516_, 7, v_cFileName_x3f_2496_);
lean_ctor_set(v_reuseFailAlloc_2516_, 8, v_bcFileName_x3f_2497_);
lean_ctor_set(v_reuseFailAlloc_2516_, 9, v_errorOnKinds_2499_);
lean_ctor_set(v_reuseFailAlloc_2516_, 10, v_incrSaveFileName_x3f_2502_);
lean_ctor_set(v_reuseFailAlloc_2516_, 11, v_incrLoadFileName_x3f_2503_);
lean_ctor_set(v_reuseFailAlloc_2516_, 12, v_incrHeaderSaveFileName_x3f_2504_);
lean_ctor_set_uint8(v_reuseFailAlloc_2516_, sizeof(void*)*13 + 8, v_component_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2516_, sizeof(void*)*13 + 9, v_printPrefix_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2516_, sizeof(void*)*13 + 10, v_printLibDir_2484_);
lean_ctor_set_uint8(v_reuseFailAlloc_2516_, sizeof(void*)*13 + 11, v_useStdin_2485_);
lean_ctor_set_uint8(v_reuseFailAlloc_2516_, sizeof(void*)*13 + 12, v_onlyDeps_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2516_, sizeof(void*)*13 + 13, v_onlySrcDeps_2487_);
lean_ctor_set_uint8(v_reuseFailAlloc_2516_, sizeof(void*)*13 + 14, v_depsJson_2488_);
lean_ctor_set_uint32(v_reuseFailAlloc_2516_, sizeof(void*)*13, v_trustLevel_2490_);
lean_ctor_set_uint32(v_reuseFailAlloc_2516_, sizeof(void*)*13 + 4, v_numThreads_2491_);
lean_ctor_set_uint8(v_reuseFailAlloc_2516_, sizeof(void*)*13 + 15, v_jsonOutput_2498_);
lean_ctor_set_uint8(v_reuseFailAlloc_2516_, sizeof(void*)*13 + 16, v_printStats_2500_);
lean_ctor_set_uint8(v_reuseFailAlloc_2516_, sizeof(void*)*13 + 17, v_run_2501_);
v___x_2512_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2514_; 
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2512_);
v___x_2514_ = v___x_2461_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
else
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec(v___x_2466_);
lean_del_object(v___x_2461_);
lean_dec(v_a_2459_);
lean_dec_ref(v_opts_939_);
v___x_2518_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2519_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2518_);
lean_dec_ref(v___x_2519_);
goto v___jp_979_;
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec_ref(v_opts_939_);
v_a_2521_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2458_, 1);
v___x_2525_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2526_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2525_);
lean_dec_ref(v___x_2526_);
goto v___jp_2522_;
v___jp_2522_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = lean_io_error_to_string(v_a_2521_);
v___x_2524_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2523_);
lean_dec_ref(v___x_2524_);
goto v___jp_976_;
}
}
}
}
else
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2528_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2527_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2569_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2569_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2569_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v_leanOpts_2533_; lean_object* v_forwardedArgs_2534_; uint8_t v_component_2535_; uint8_t v_printPrefix_2536_; uint8_t v_printLibDir_2537_; uint8_t v_useStdin_2538_; uint8_t v_onlyDeps_2539_; uint8_t v_onlySrcDeps_2540_; uint8_t v_depsJson_2541_; lean_object* v_opts_2542_; uint32_t v_trustLevel_2543_; uint32_t v_numThreads_2544_; lean_object* v_rootDir_x3f_2545_; lean_object* v_setupFileName_x3f_2546_; lean_object* v_oleanFileName_x3f_2547_; lean_object* v_ileanFileName_x3f_2548_; lean_object* v_cFileName_x3f_2549_; uint8_t v_jsonOutput_2550_; lean_object* v_errorOnKinds_2551_; uint8_t v_printStats_2552_; uint8_t v_run_2553_; lean_object* v_incrSaveFileName_x3f_2554_; lean_object* v_incrLoadFileName_x3f_2555_; lean_object* v_incrHeaderSaveFileName_x3f_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2567_; 
v_leanOpts_2533_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_2534_ = lean_ctor_get(v_opts_939_, 1);
v_component_2535_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_2536_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_2537_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_2538_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_2539_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2540_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_2541_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2542_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_2543_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_2544_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2545_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_2546_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_2547_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_2548_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_2549_ = lean_ctor_get(v_opts_939_, 7);
v_jsonOutput_2550_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2551_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2552_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_2553_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2554_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2555_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2556_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2567_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2567_ == 0)
{
lean_object* v_unused_2568_; 
v_unused_2568_ = lean_ctor_get(v_opts_939_, 8);
lean_dec(v_unused_2568_);
v___x_2558_ = v_opts_939_;
v_isShared_2559_ = v_isSharedCheck_2567_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2556_);
lean_inc(v_incrLoadFileName_x3f_2555_);
lean_inc(v_incrSaveFileName_x3f_2554_);
lean_inc(v_errorOnKinds_2551_);
lean_inc(v_cFileName_x3f_2549_);
lean_inc(v_ileanFileName_x3f_2548_);
lean_inc(v_oleanFileName_x3f_2547_);
lean_inc(v_setupFileName_x3f_2546_);
lean_inc(v_rootDir_x3f_2545_);
lean_inc(v_opts_2542_);
lean_inc(v_forwardedArgs_2534_);
lean_inc(v_leanOpts_2533_);
lean_dec(v_opts_939_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2567_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_a_2529_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 8, v___x_2560_);
v___x_2562_ = v___x_2558_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_leanOpts_2533_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_forwardedArgs_2534_);
lean_ctor_set(v_reuseFailAlloc_2566_, 2, v_opts_2542_);
lean_ctor_set(v_reuseFailAlloc_2566_, 3, v_rootDir_x3f_2545_);
lean_ctor_set(v_reuseFailAlloc_2566_, 4, v_setupFileName_x3f_2546_);
lean_ctor_set(v_reuseFailAlloc_2566_, 5, v_oleanFileName_x3f_2547_);
lean_ctor_set(v_reuseFailAlloc_2566_, 6, v_ileanFileName_x3f_2548_);
lean_ctor_set(v_reuseFailAlloc_2566_, 7, v_cFileName_x3f_2549_);
lean_ctor_set(v_reuseFailAlloc_2566_, 8, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2566_, 9, v_errorOnKinds_2551_);
lean_ctor_set(v_reuseFailAlloc_2566_, 10, v_incrSaveFileName_x3f_2554_);
lean_ctor_set(v_reuseFailAlloc_2566_, 11, v_incrLoadFileName_x3f_2555_);
lean_ctor_set(v_reuseFailAlloc_2566_, 12, v_incrHeaderSaveFileName_x3f_2556_);
lean_ctor_set_uint8(v_reuseFailAlloc_2566_, sizeof(void*)*13 + 8, v_component_2535_);
lean_ctor_set_uint8(v_reuseFailAlloc_2566_, sizeof(void*)*13 + 9, v_printPrefix_2536_);
lean_ctor_set_uint8(v_reuseFailAlloc_2566_, sizeof(void*)*13 + 10, v_printLibDir_2537_);
lean_ctor_set_uint8(v_reuseFailAlloc_2566_, sizeof(void*)*13 + 11, v_useStdin_2538_);
lean_ctor_set_uint8(v_reuseFailAlloc_2566_, sizeof(void*)*13 + 12, v_onlyDeps_2539_);
lean_ctor_set_uint8(v_reuseFailAlloc_2566_, sizeof(void*)*13 + 13, v_onlySrcDeps_2540_);
lean_ctor_set_uint8(v_reuseFailAlloc_2566_, sizeof(void*)*13 + 14, v_depsJson_2541_);
lean_ctor_set_uint32(v_reuseFailAlloc_2566_, sizeof(void*)*13, v_trustLevel_2543_);
lean_ctor_set_uint32(v_reuseFailAlloc_2566_, sizeof(void*)*13 + 4, v_numThreads_2544_);
lean_ctor_set_uint8(v_reuseFailAlloc_2566_, sizeof(void*)*13 + 15, v_jsonOutput_2550_);
lean_ctor_set_uint8(v_reuseFailAlloc_2566_, sizeof(void*)*13 + 16, v_printStats_2552_);
lean_ctor_set_uint8(v_reuseFailAlloc_2566_, sizeof(void*)*13 + 17, v_run_2553_);
v___x_2562_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
lean_object* v___x_2564_; 
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 0, v___x_2562_);
v___x_2564_ = v___x_2531_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_dec_ref(v_opts_939_);
v_a_2570_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2528_, 1);
v___x_2574_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2575_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2574_);
lean_dec_ref(v___x_2575_);
goto v___jp_2571_;
v___jp_2571_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = lean_io_error_to_string(v_a_2570_);
v___x_2573_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2572_);
lean_dec_ref(v___x_2573_);
goto v___jp_1140_;
}
}
}
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2577_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2576_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2618_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2618_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2618_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v_leanOpts_2582_; lean_object* v_forwardedArgs_2583_; uint8_t v_component_2584_; uint8_t v_printPrefix_2585_; uint8_t v_printLibDir_2586_; uint8_t v_useStdin_2587_; uint8_t v_onlyDeps_2588_; uint8_t v_onlySrcDeps_2589_; uint8_t v_depsJson_2590_; lean_object* v_opts_2591_; uint32_t v_trustLevel_2592_; uint32_t v_numThreads_2593_; lean_object* v_rootDir_x3f_2594_; lean_object* v_setupFileName_x3f_2595_; lean_object* v_oleanFileName_x3f_2596_; lean_object* v_ileanFileName_x3f_2597_; lean_object* v_bcFileName_x3f_2598_; uint8_t v_jsonOutput_2599_; lean_object* v_errorOnKinds_2600_; uint8_t v_printStats_2601_; uint8_t v_run_2602_; lean_object* v_incrSaveFileName_x3f_2603_; lean_object* v_incrLoadFileName_x3f_2604_; lean_object* v_incrHeaderSaveFileName_x3f_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2616_; 
v_leanOpts_2582_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_2583_ = lean_ctor_get(v_opts_939_, 1);
v_component_2584_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_2585_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_2586_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_2587_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_2588_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2589_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_2590_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2591_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_2592_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_numThreads_2593_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2594_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_2595_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_2596_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_2597_ = lean_ctor_get(v_opts_939_, 6);
v_bcFileName_x3f_2598_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_2599_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2600_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2601_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_2602_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2603_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2604_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2605_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2616_ == 0)
{
lean_object* v_unused_2617_; 
v_unused_2617_ = lean_ctor_get(v_opts_939_, 7);
lean_dec(v_unused_2617_);
v___x_2607_ = v_opts_939_;
v_isShared_2608_ = v_isSharedCheck_2616_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2605_);
lean_inc(v_incrLoadFileName_x3f_2604_);
lean_inc(v_incrSaveFileName_x3f_2603_);
lean_inc(v_errorOnKinds_2600_);
lean_inc(v_bcFileName_x3f_2598_);
lean_inc(v_ileanFileName_x3f_2597_);
lean_inc(v_oleanFileName_x3f_2596_);
lean_inc(v_setupFileName_x3f_2595_);
lean_inc(v_rootDir_x3f_2594_);
lean_inc(v_opts_2591_);
lean_inc(v_forwardedArgs_2583_);
lean_inc(v_leanOpts_2582_);
lean_dec(v_opts_939_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2616_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2609_, 0, v_a_2578_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 7, v___x_2609_);
v___x_2611_ = v___x_2607_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_leanOpts_2582_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_forwardedArgs_2583_);
lean_ctor_set(v_reuseFailAlloc_2615_, 2, v_opts_2591_);
lean_ctor_set(v_reuseFailAlloc_2615_, 3, v_rootDir_x3f_2594_);
lean_ctor_set(v_reuseFailAlloc_2615_, 4, v_setupFileName_x3f_2595_);
lean_ctor_set(v_reuseFailAlloc_2615_, 5, v_oleanFileName_x3f_2596_);
lean_ctor_set(v_reuseFailAlloc_2615_, 6, v_ileanFileName_x3f_2597_);
lean_ctor_set(v_reuseFailAlloc_2615_, 7, v___x_2609_);
lean_ctor_set(v_reuseFailAlloc_2615_, 8, v_bcFileName_x3f_2598_);
lean_ctor_set(v_reuseFailAlloc_2615_, 9, v_errorOnKinds_2600_);
lean_ctor_set(v_reuseFailAlloc_2615_, 10, v_incrSaveFileName_x3f_2603_);
lean_ctor_set(v_reuseFailAlloc_2615_, 11, v_incrLoadFileName_x3f_2604_);
lean_ctor_set(v_reuseFailAlloc_2615_, 12, v_incrHeaderSaveFileName_x3f_2605_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*13 + 8, v_component_2584_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*13 + 9, v_printPrefix_2585_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*13 + 10, v_printLibDir_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*13 + 11, v_useStdin_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*13 + 12, v_onlyDeps_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*13 + 13, v_onlySrcDeps_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*13 + 14, v_depsJson_2590_);
lean_ctor_set_uint32(v_reuseFailAlloc_2615_, sizeof(void*)*13, v_trustLevel_2592_);
lean_ctor_set_uint32(v_reuseFailAlloc_2615_, sizeof(void*)*13 + 4, v_numThreads_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*13 + 15, v_jsonOutput_2599_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*13 + 16, v_printStats_2601_);
lean_ctor_set_uint8(v_reuseFailAlloc_2615_, sizeof(void*)*13 + 17, v_run_2602_);
v___x_2611_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2613_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2611_);
v___x_2613_ = v___x_2580_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec_ref(v_opts_939_);
v_a_2619_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2577_, 1);
v___x_2623_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2624_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2623_);
lean_dec_ref(v___x_2624_);
goto v___jp_2620_;
v___jp_2620_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = lean_io_error_to_string(v_a_2619_);
v___x_2622_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2621_);
lean_dec_ref(v___x_2622_);
goto v___jp_970_;
}
}
}
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec(v_optArg_x3f_941_);
lean_dec_ref(v_opts_939_);
v___x_2625_ = l___private_Lean_Shell_0__Lean_featuresString;
v___x_2626_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2625_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2634_; 
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2634_ == 0)
{
lean_object* v_unused_2635_; 
v_unused_2635_ = lean_ctor_get(v___x_2626_, 0);
lean_dec(v_unused_2635_);
v___x_2628_ = v___x_2626_;
v_isShared_2629_ = v_isSharedCheck_2634_;
goto v_resetjp_2627_;
}
else
{
lean_dec(v___x_2626_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2634_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2630_; lean_object* v___x_2632_; 
v___x_2630_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2629_ == 0)
{
lean_ctor_set_tag(v___x_2628_, 1);
lean_ctor_set(v___x_2628_, 0, v___x_2630_);
v___x_2632_ = v___x_2628_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v_a_2636_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2626_, 1);
v___x_2640_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2641_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2640_);
lean_dec_ref(v___x_2641_);
goto v___jp_2637_;
v___jp_2637_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = lean_io_error_to_string(v_a_2636_);
v___x_2639_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2638_);
lean_dec_ref(v___x_2639_);
goto v___jp_1146_;
}
}
}
}
else
{
lean_object* v___x_2642_; 
lean_dec(v_optArg_x3f_941_);
lean_dec_ref(v_opts_939_);
v___x_2642_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1170_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2650_; 
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2650_ == 0)
{
lean_object* v_unused_2651_; 
v_unused_2651_ = lean_ctor_get(v___x_2642_, 0);
lean_dec(v_unused_2651_);
v___x_2644_ = v___x_2642_;
v_isShared_2645_ = v_isSharedCheck_2650_;
goto v_resetjp_2643_;
}
else
{
lean_dec(v___x_2642_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2650_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2646_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2645_ == 0)
{
lean_ctor_set_tag(v___x_2644_, 1);
lean_ctor_set(v___x_2644_, 0, v___x_2646_);
v___x_2648_ = v___x_2644_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v_a_2652_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2642_, 1);
v___x_2656_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2657_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2656_);
lean_dec_ref(v___x_2657_);
goto v___jp_2653_;
v___jp_2653_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_io_error_to_string(v_a_2652_);
v___x_2655_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2654_);
lean_dec_ref(v___x_2655_);
goto v___jp_964_;
}
}
}
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec(v_optArg_x3f_941_);
lean_dec_ref(v_opts_939_);
v___x_2658_ = l_Lean_githash;
v___x_2659_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2658_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2667_; 
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2667_ == 0)
{
lean_object* v_unused_2668_; 
v_unused_2668_ = lean_ctor_get(v___x_2659_, 0);
lean_dec(v_unused_2668_);
v___x_2661_ = v___x_2659_;
v_isShared_2662_ = v_isSharedCheck_2667_;
goto v_resetjp_2660_;
}
else
{
lean_dec(v___x_2659_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2667_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2663_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2662_ == 0)
{
lean_ctor_set_tag(v___x_2661_, 1);
lean_ctor_set(v___x_2661_, 0, v___x_2663_);
v___x_2665_ = v___x_2661_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_a_2669_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2673_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2674_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2673_);
lean_dec_ref(v___x_2674_);
goto v___jp_2670_;
v___jp_2670_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_io_error_to_string(v_a_2669_);
v___x_2672_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2671_);
lean_dec_ref(v___x_2672_);
goto v___jp_1152_;
}
}
}
}
else
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
lean_dec(v_optArg_x3f_941_);
lean_dec_ref(v_opts_939_);
v___x_2675_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2676_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2675_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2684_; 
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2684_ == 0)
{
lean_object* v_unused_2685_; 
v_unused_2685_ = lean_ctor_get(v___x_2676_, 0);
lean_dec(v_unused_2685_);
v___x_2678_ = v___x_2676_;
v_isShared_2679_ = v_isSharedCheck_2684_;
goto v_resetjp_2677_;
}
else
{
lean_dec(v___x_2676_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2684_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2680_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2679_ == 0)
{
lean_ctor_set_tag(v___x_2678_, 1);
lean_ctor_set(v___x_2678_, 0, v___x_2680_);
v___x_2682_ = v___x_2678_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_a_2686_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2676_, 1);
v___x_2690_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2691_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2690_);
lean_dec_ref(v___x_2691_);
goto v___jp_2687_;
v___jp_2687_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = lean_io_error_to_string(v_a_2686_);
v___x_2689_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2688_);
lean_dec_ref(v___x_2689_);
goto v___jp_958_;
}
}
}
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_dec(v_optArg_x3f_941_);
lean_dec_ref(v_opts_939_);
v___x_2692_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2693_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2692_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2701_; 
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; 
v_unused_2702_ = lean_ctor_get(v___x_2693_, 0);
lean_dec(v_unused_2702_);
v___x_2695_ = v___x_2693_;
v_isShared_2696_ = v_isSharedCheck_2701_;
goto v_resetjp_2694_;
}
else
{
lean_dec(v___x_2693_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2701_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2696_ == 0)
{
lean_ctor_set_tag(v___x_2695_, 1);
lean_ctor_set(v___x_2695_, 0, v___x_2697_);
v___x_2699_ = v___x_2695_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_a_2703_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2693_, 1);
v___x_2707_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2708_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2707_);
lean_dec_ref(v___x_2708_);
goto v___jp_2704_;
v___jp_2704_:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = lean_io_error_to_string(v_a_2703_);
v___x_2706_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2705_);
lean_dec_ref(v___x_2706_);
goto v___jp_1158_;
}
}
}
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2710_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2709_, v_optArg_x3f_941_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2764_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2764_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2764_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2715_ = lean_unsigned_to_nat(0u);
v___x_2716_ = lean_string_utf8_byte_size(v_a_2711_);
lean_inc(v_a_2711_);
v___x_2717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2717_, 0, v_a_2711_);
lean_ctor_set(v___x_2717_, 1, v___x_2715_);
lean_ctor_set(v___x_2717_, 2, v___x_2716_);
v___x_2718_ = l_String_Slice_toNat_x3f(v___x_2717_);
lean_dec_ref_known(v___x_2717_, 3);
if (lean_obj_tag(v___x_2718_) == 1)
{
lean_object* v_val_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; 
v_val_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_val_2719_);
lean_dec_ref_known(v___x_2718_, 1);
v___x_2720_ = lean_cstr_to_nat("4294967296");
v___x_2721_ = lean_nat_dec_lt(v_val_2719_, v___x_2720_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
lean_dec(v_val_2719_);
lean_del_object(v___x_2713_);
lean_dec(v_a_2711_);
lean_dec_ref(v_opts_939_);
v___x_2722_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__35));
v___x_2723_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2722_);
lean_dec_ref(v___x_2723_);
goto v___jp_952_;
}
else
{
lean_object* v_leanOpts_2724_; lean_object* v_forwardedArgs_2725_; uint8_t v_component_2726_; uint8_t v_printPrefix_2727_; uint8_t v_printLibDir_2728_; uint8_t v_useStdin_2729_; uint8_t v_onlyDeps_2730_; uint8_t v_onlySrcDeps_2731_; uint8_t v_depsJson_2732_; lean_object* v_opts_2733_; uint32_t v_trustLevel_2734_; lean_object* v_rootDir_x3f_2735_; lean_object* v_setupFileName_x3f_2736_; lean_object* v_oleanFileName_x3f_2737_; lean_object* v_ileanFileName_x3f_2738_; lean_object* v_cFileName_x3f_2739_; lean_object* v_bcFileName_x3f_2740_; uint8_t v_jsonOutput_2741_; lean_object* v_errorOnKinds_2742_; uint8_t v_printStats_2743_; uint8_t v_run_2744_; lean_object* v_incrSaveFileName_x3f_2745_; lean_object* v_incrLoadFileName_x3f_2746_; lean_object* v_incrHeaderSaveFileName_x3f_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2761_; 
v_leanOpts_2724_ = lean_ctor_get(v_opts_939_, 0);
v_forwardedArgs_2725_ = lean_ctor_get(v_opts_939_, 1);
v_component_2726_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 8);
v_printPrefix_2727_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 9);
v_printLibDir_2728_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 10);
v_useStdin_2729_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 11);
v_onlyDeps_2730_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2731_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 13);
v_depsJson_2732_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 14);
v_opts_2733_ = lean_ctor_get(v_opts_939_, 2);
v_trustLevel_2734_ = lean_ctor_get_uint32(v_opts_939_, sizeof(void*)*13);
v_rootDir_x3f_2735_ = lean_ctor_get(v_opts_939_, 3);
v_setupFileName_x3f_2736_ = lean_ctor_get(v_opts_939_, 4);
v_oleanFileName_x3f_2737_ = lean_ctor_get(v_opts_939_, 5);
v_ileanFileName_x3f_2738_ = lean_ctor_get(v_opts_939_, 6);
v_cFileName_x3f_2739_ = lean_ctor_get(v_opts_939_, 7);
v_bcFileName_x3f_2740_ = lean_ctor_get(v_opts_939_, 8);
v_jsonOutput_2741_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 15);
v_errorOnKinds_2742_ = lean_ctor_get(v_opts_939_, 9);
v_printStats_2743_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 16);
v_run_2744_ = lean_ctor_get_uint8(v_opts_939_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2745_ = lean_ctor_get(v_opts_939_, 10);
v_incrLoadFileName_x3f_2746_ = lean_ctor_get(v_opts_939_, 11);
v_incrHeaderSaveFileName_x3f_2747_ = lean_ctor_get(v_opts_939_, 12);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_opts_939_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2749_ = v_opts_939_;
v_isShared_2750_ = v_isSharedCheck_2761_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2747_);
lean_inc(v_incrLoadFileName_x3f_2746_);
lean_inc(v_incrSaveFileName_x3f_2745_);
lean_inc(v_errorOnKinds_2742_);
lean_inc(v_bcFileName_x3f_2740_);
lean_inc(v_cFileName_x3f_2739_);
lean_inc(v_ileanFileName_x3f_2738_);
lean_inc(v_oleanFileName_x3f_2737_);
lean_inc(v_setupFileName_x3f_2736_);
lean_inc(v_rootDir_x3f_2735_);
lean_inc(v_opts_2733_);
lean_inc(v_forwardedArgs_2725_);
lean_inc(v_leanOpts_2724_);
lean_dec(v_opts_939_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2761_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
uint32_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2751_ = lean_uint32_of_nat(v_val_2719_);
lean_dec(v_val_2719_);
v___x_2752_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__36));
v___x_2753_ = lean_string_append(v___x_2752_, v_a_2711_);
lean_dec(v_a_2711_);
v___x_2754_ = lean_array_push(v_forwardedArgs_2725_, v___x_2753_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 1, v___x_2754_);
v___x_2756_ = v___x_2749_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_leanOpts_2724_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2760_, 2, v_opts_2733_);
lean_ctor_set(v_reuseFailAlloc_2760_, 3, v_rootDir_x3f_2735_);
lean_ctor_set(v_reuseFailAlloc_2760_, 4, v_setupFileName_x3f_2736_);
lean_ctor_set(v_reuseFailAlloc_2760_, 5, v_oleanFileName_x3f_2737_);
lean_ctor_set(v_reuseFailAlloc_2760_, 6, v_ileanFileName_x3f_2738_);
lean_ctor_set(v_reuseFailAlloc_2760_, 7, v_cFileName_x3f_2739_);
lean_ctor_set(v_reuseFailAlloc_2760_, 8, v_bcFileName_x3f_2740_);
lean_ctor_set(v_reuseFailAlloc_2760_, 9, v_errorOnKinds_2742_);
lean_ctor_set(v_reuseFailAlloc_2760_, 10, v_incrSaveFileName_x3f_2745_);
lean_ctor_set(v_reuseFailAlloc_2760_, 11, v_incrLoadFileName_x3f_2746_);
lean_ctor_set(v_reuseFailAlloc_2760_, 12, v_incrHeaderSaveFileName_x3f_2747_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*13 + 8, v_component_2726_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*13 + 9, v_printPrefix_2727_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*13 + 10, v_printLibDir_2728_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*13 + 11, v_useStdin_2729_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*13 + 12, v_onlyDeps_2730_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*13 + 13, v_onlySrcDeps_2731_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*13 + 14, v_depsJson_2732_);
lean_ctor_set_uint32(v_reuseFailAlloc_2760_, sizeof(void*)*13, v_trustLevel_2734_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*13 + 15, v_jsonOutput_2741_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*13 + 16, v_printStats_2743_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*13 + 17, v_run_2744_);
v___x_2756_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
lean_object* v___x_2758_; 
lean_ctor_set_uint32(v___x_2756_, sizeof(void*)*13 + 4, v___x_2751_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v___x_2756_);
v___x_2758_ = v___x_2713_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
}
else
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_dec(v___x_2718_);
lean_del_object(v___x_2713_);
lean_dec(v_a_2711_);
lean_dec_ref(v_opts_939_);
v___x_2762_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__37));
v___x_2763_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2762_);
lean_dec_ref(v___x_2763_);
goto v___jp_949_;
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_dec_ref(v_opts_939_);
v_a_2765_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2769_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2770_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2769_);
lean_dec_ref(v___x_2770_);
goto v___jp_2766_;
v___jp_2766_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_io_error_to_string(v_a_2765_);
v___x_2768_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2767_);
lean_dec_ref(v___x_2768_);
goto v___jp_946_;
}
}
}
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_dec(v_optArg_x3f_941_);
v___x_2771_ = lean_internal_set_exit_on_panic(v___x_1162_);
v___x_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_opts_939_);
return v___x_2772_;
}
v___jp_943_:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
v___jp_946_:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_948_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_947_);
lean_dec_ref(v___x_948_);
goto v___jp_943_;
}
v___jp_949_:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
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
v___x_959_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_960_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_959_);
lean_dec_ref(v___x_960_);
goto v___jp_955_;
}
v___jp_961_:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
return v___x_963_;
}
v___jp_964_:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_966_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_965_);
lean_dec_ref(v___x_966_);
goto v___jp_961_;
}
v___jp_967_:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
v___jp_970_:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_972_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_971_);
lean_dec_ref(v___x_972_);
goto v___jp_967_;
}
v___jp_973_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
v___jp_976_:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_978_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_977_);
lean_dec_ref(v___x_978_);
goto v___jp_973_;
}
v___jp_979_:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
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
v___x_989_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_990_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_989_);
lean_dec_ref(v___x_990_);
goto v___jp_985_;
}
v___jp_991_:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
v___jp_994_:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_996_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_995_);
lean_dec_ref(v___x_996_);
goto v___jp_991_;
}
v___jp_997_:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
return v___x_999_;
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
v___x_1004_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1005_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1004_);
lean_dec_ref(v___x_1005_);
goto v___jp_1000_;
}
v___jp_1006_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
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
v___x_1016_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1017_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1016_);
lean_dec_ref(v___x_1017_);
goto v___jp_1012_;
}
v___jp_1018_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
return v___x_1020_;
}
v___jp_1021_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1023_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1022_);
lean_dec_ref(v___x_1023_);
goto v___jp_1018_;
}
v___jp_1024_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
return v___x_1026_;
}
v___jp_1027_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1029_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1028_);
lean_dec_ref(v___x_1029_);
goto v___jp_1024_;
}
v___jp_1030_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
return v___x_1032_;
}
v___jp_1033_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1035_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1034_);
lean_dec_ref(v___x_1035_);
goto v___jp_1030_;
}
v___jp_1036_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
return v___x_1038_;
}
v___jp_1039_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1041_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1040_);
lean_dec_ref(v___x_1041_);
goto v___jp_1036_;
}
v___jp_1042_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
v___jp_1045_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1047_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1046_);
lean_dec_ref(v___x_1047_);
goto v___jp_1042_;
}
v___jp_1048_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
return v___x_1050_;
}
v___jp_1051_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1053_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1052_);
lean_dec_ref(v___x_1053_);
goto v___jp_1048_;
}
v___jp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_io_error_to_string(v___y_1055_);
v___x_1057_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1056_);
lean_dec_ref(v___x_1057_);
goto v___jp_1051_;
}
v___jp_1058_:
{
uint8_t v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = 1;
v___x_1060_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1059_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1068_; 
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v___x_1060_, 0);
lean_dec(v_unused_1069_);
v___x_1062_ = v___x_1060_;
v_isShared_1063_ = v_isSharedCheck_1068_;
goto v_resetjp_1061_;
}
else
{
lean_dec(v___x_1060_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1068_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 1);
lean_ctor_set(v___x_1062_, 0, v___x_1064_);
v___x_1066_ = v___x_1062_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_a_1070_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1060_, 1);
v___x_1071_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1072_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1071_);
lean_dec_ref(v___x_1072_);
v___y_1055_ = v_a_1070_;
goto v___jp_1054_;
}
}
v___jp_1073_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
v___x_1075_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1074_);
lean_dec_ref(v___x_1075_);
goto v___jp_1058_;
}
v___jp_1076_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
v___jp_1079_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1081_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1080_);
lean_dec_ref(v___x_1081_);
goto v___jp_1076_;
}
v___jp_1082_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
v___jp_1085_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1087_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1086_);
lean_dec_ref(v___x_1087_);
goto v___jp_1082_;
}
v___jp_1088_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
v___jp_1091_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1093_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1092_);
lean_dec_ref(v___x_1093_);
goto v___jp_1088_;
}
v___jp_1094_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
v___jp_1097_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1099_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1098_);
lean_dec_ref(v___x_1099_);
goto v___jp_1094_;
}
v___jp_1100_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_io_error_to_string(v___y_1101_);
v___x_1103_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1102_);
lean_dec_ref(v___x_1103_);
goto v___jp_1097_;
}
v___jp_1104_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
v___jp_1107_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1109_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1108_);
lean_dec_ref(v___x_1109_);
goto v___jp_1104_;
}
v___jp_1110_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
v___jp_1113_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1115_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1114_);
lean_dec_ref(v___x_1115_);
goto v___jp_1110_;
}
v___jp_1116_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
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
v___x_1123_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1124_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1123_);
lean_dec_ref(v___x_1124_);
goto v___jp_1119_;
}
v___jp_1125_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
v___jp_1128_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1130_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1129_);
lean_dec_ref(v___x_1130_);
goto v___jp_1125_;
}
v___jp_1131_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
v___jp_1134_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1136_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1135_);
lean_dec_ref(v___x_1136_);
goto v___jp_1131_;
}
v___jp_1137_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
v___jp_1140_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1142_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1141_);
lean_dec_ref(v___x_1142_);
goto v___jp_1137_;
}
v___jp_1143_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
v___jp_1146_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1148_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1147_);
lean_dec_ref(v___x_1148_);
goto v___jp_1143_;
}
v___jp_1149_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
v___jp_1152_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1154_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1153_);
lean_dec_ref(v___x_1154_);
goto v___jp_1149_;
}
v___jp_1155_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
v___jp_1158_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1160_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1159_);
lean_dec_ref(v___x_1160_);
goto v___jp_1155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2773_, lean_object* v_opt_2774_, lean_object* v_optArg_x3f_2775_, lean_object* v_a_2776_){
_start:
{
uint32_t v_opt_boxed_2777_; lean_object* v_res_2778_; 
v_opt_boxed_2777_ = lean_unbox_uint32(v_opt_2774_);
lean_dec(v_opt_2774_);
v_res_2778_ = lean_shell_options_process(v_opts_2773_, v_opt_boxed_2777_, v_optArg_x3f_2775_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_opts_2779_, lean_object* v_opt_2780_){
_start:
{
lean_object* v_name_2781_; lean_object* v_defValue_2782_; lean_object* v_map_2783_; lean_object* v___x_2784_; 
v_name_2781_ = lean_ctor_get(v_opt_2780_, 0);
v_defValue_2782_ = lean_ctor_get(v_opt_2780_, 1);
v_map_2783_ = lean_ctor_get(v_opts_2779_, 0);
v___x_2784_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2783_, v_name_2781_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_inc(v_defValue_2782_);
return v_defValue_2782_;
}
else
{
lean_object* v_val_2785_; 
v_val_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_val_2785_);
lean_dec_ref_known(v___x_2784_, 1);
if (lean_obj_tag(v_val_2785_) == 3)
{
lean_object* v_v_2786_; 
v_v_2786_ = lean_ctor_get(v_val_2785_, 0);
lean_inc(v_v_2786_);
lean_dec_ref_known(v_val_2785_, 1);
return v_v_2786_;
}
else
{
lean_dec(v_val_2785_);
lean_inc(v_defValue_2782_);
return v_defValue_2782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_opts_2787_, lean_object* v_opt_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_opts_2787_, v_opt_2788_);
lean_dec_ref(v_opt_2788_);
lean_dec_ref(v_opts_2787_);
return v_res_2789_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2792_ = lean_string_utf8_byte_size(v___x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2793_){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v___x_2794_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2795_ = lean_string_utf8_byte_size(v_s_2793_);
v___x_2796_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1);
v___x_2797_ = lean_nat_dec_le(v___x_2796_, v___x_2795_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; 
lean_dec_ref(v_s_2793_);
v___x_2798_ = lean_box(0);
return v___x_2798_;
}
else
{
lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2799_ = lean_unsigned_to_nat(0u);
v___x_2800_ = lean_string_memcmp(v_s_2793_, v___x_2794_, v___x_2799_, v___x_2799_, v___x_2796_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; 
lean_dec_ref(v_s_2793_);
v___x_2801_ = lean_box(0);
return v___x_2801_;
}
else
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
lean_inc_ref(v_s_2793_);
v___x_2802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2802_, 0, v_s_2793_);
lean_ctor_set(v___x_2802_, 1, v___x_2799_);
lean_ctor_set(v___x_2802_, 2, v___x_2795_);
v___x_2803_ = l_String_Slice_pos_x21(v___x_2802_, v___x_2796_);
lean_dec_ref_known(v___x_2802_, 3);
v___x_2804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2804_, 0, v_s_2793_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
lean_ctor_set(v___x_2804_, 2, v___x_2795_);
v___x_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2806_, lean_object* v_pat_2807_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2806_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2809_, lean_object* v_pat_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2809_, v_pat_2810_);
lean_dec_ref(v_pat_2810_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v_x_2812_, lean_object* v_x_2813_, lean_object* v_v_2814_){
_start:
{
lean_inc_ref(v_v_2814_);
return v_v_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* v_x_2815_, lean_object* v_x_2816_, lean_object* v_v_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v_x_2815_, v_x_2816_, v_v_2817_);
lean_dec_ref(v_v_2817_);
lean_dec_ref(v_x_2816_);
lean_dec(v_x_2815_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object* v___x_2822_, lean_object* v___x_2823_, lean_object* v_mainModuleName_2824_, lean_object* v_a_2825_, uint8_t v___x_2826_, lean_object* v___x_2827_, lean_object* v_fileName_2828_, lean_object* v___x_2829_, lean_object* v___x_2830_, lean_object* v___x_2831_, lean_object* v___x_2832_, lean_object* v___x_2833_, lean_object* v___x_2834_, lean_object* v___x_2835_, lean_object* v___x_2836_, uint8_t v_run_2837_){
_start:
{
lean_object* v_a_2840_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v_env_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; lean_object* v_fileName_2852_; lean_object* v_fileMap_2853_; lean_object* v_currRecDepth_2854_; lean_object* v_ref_2855_; lean_object* v_currNamespace_2856_; lean_object* v_openDecls_2857_; lean_object* v_initHeartbeats_2858_; lean_object* v_maxHeartbeats_2859_; lean_object* v_quotContext_2860_; lean_object* v_currMacroScope_2861_; lean_object* v_cancelTk_x3f_2862_; uint8_t v_suppressElabErrors_2863_; lean_object* v_inheritedTraceOptions_2864_; lean_object* v___y_2865_; uint8_t v___y_2897_; uint8_t v___x_2917_; 
v___x_2843_ = lean_io_get_num_heartbeats();
v___x_2844_ = lean_st_mk_ref(v___x_2822_);
v___x_2845_ = l_Lean_inheritedTraceOptions;
v___x_2846_ = lean_st_ref_get(v___x_2845_);
v___x_2847_ = lean_st_ref_get(v___x_2844_);
v_env_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc_ref(v_env_2848_);
lean_dec(v___x_2847_);
v___x_2849_ = l_Lean_diagnostics;
v___x_2850_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v___x_2823_, v___x_2849_);
v___x_2917_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2848_);
lean_dec_ref(v_env_2848_);
if (v___x_2917_ == 0)
{
if (v___x_2850_ == 0)
{
lean_dec_ref(v___x_2827_);
lean_inc(v___x_2844_);
lean_inc(v___x_2832_);
v_fileName_2852_ = v_fileName_2828_;
v_fileMap_2853_ = v___x_2829_;
v_currRecDepth_2854_ = v___x_2830_;
v_ref_2855_ = v___x_2831_;
v_currNamespace_2856_ = v___x_2832_;
v_openDecls_2857_ = v___x_2833_;
v_initHeartbeats_2858_ = v___x_2843_;
v_maxHeartbeats_2859_ = v___x_2834_;
v_quotContext_2860_ = v___x_2832_;
v_currMacroScope_2861_ = v___x_2835_;
v_cancelTk_x3f_2862_ = v___x_2836_;
v_suppressElabErrors_2863_ = v_run_2837_;
v_inheritedTraceOptions_2864_ = v___x_2846_;
v___y_2865_ = v___x_2844_;
goto v___jp_2851_;
}
else
{
v___y_2897_ = v___x_2917_;
goto v___jp_2896_;
}
}
else
{
v___y_2897_ = v___x_2850_;
goto v___jp_2896_;
}
v___jp_2839_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = lean_mk_io_user_error(v_a_2840_);
v___x_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
return v___x_2842_;
}
v___jp_2851_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2866_ = l_Lean_maxRecDepth;
v___x_2867_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_2823_, v___x_2866_);
v___x_2868_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2868_, 0, v_fileName_2852_);
lean_ctor_set(v___x_2868_, 1, v_fileMap_2853_);
lean_ctor_set(v___x_2868_, 2, v___x_2823_);
lean_ctor_set(v___x_2868_, 3, v_currRecDepth_2854_);
lean_ctor_set(v___x_2868_, 4, v___x_2867_);
lean_ctor_set(v___x_2868_, 5, v_ref_2855_);
lean_ctor_set(v___x_2868_, 6, v_currNamespace_2856_);
lean_ctor_set(v___x_2868_, 7, v_openDecls_2857_);
lean_ctor_set(v___x_2868_, 8, v_initHeartbeats_2858_);
lean_ctor_set(v___x_2868_, 9, v_maxHeartbeats_2859_);
lean_ctor_set(v___x_2868_, 10, v_quotContext_2860_);
lean_ctor_set(v___x_2868_, 11, v_currMacroScope_2861_);
lean_ctor_set(v___x_2868_, 12, v_cancelTk_x3f_2862_);
lean_ctor_set(v___x_2868_, 13, v_inheritedTraceOptions_2864_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*14, v___x_2850_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*14 + 1, v_suppressElabErrors_2863_);
v___x_2869_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2824_, v___x_2868_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec_ref_known(v___x_2868_, 14);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v___x_2871_ = lean_st_ref_get(v___x_2844_);
lean_dec(v___x_2844_);
lean_dec(v___x_2871_);
v___x_2872_ = lean_string_to_utf8(v_a_2870_);
lean_dec(v_a_2870_);
v___x_2873_ = lean_io_prim_handle_write(v_a_2825_, v___x_2872_);
lean_dec_ref(v___x_2872_);
return v___x_2873_;
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v___x_2844_);
v_a_2874_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2876_ = v___x_2869_;
v_isShared_2877_ = v_isSharedCheck_2895_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2869_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2895_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
if (lean_obj_tag(v_a_2874_) == 0)
{
lean_object* v_msg_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2882_; 
v_msg_2878_ = lean_ctor_get(v_a_2874_, 1);
lean_inc_ref(v_msg_2878_);
lean_dec_ref_known(v_a_2874_, 2);
v___x_2879_ = l_Lean_MessageData_toString(v_msg_2878_);
v___x_2880_ = lean_mk_io_user_error(v___x_2879_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 0, v___x_2880_);
v___x_2882_ = v___x_2876_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
else
{
lean_object* v_id_2884_; lean_object* v___x_2885_; 
lean_del_object(v___x_2876_);
v_id_2884_ = lean_ctor_get(v_a_2874_, 0);
lean_inc(v_id_2884_);
lean_dec_ref_known(v_a_2874_, 2);
v___x_2885_ = l_Lean_InternalExceptionId_getName(v_id_2884_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
lean_dec(v_id_2884_);
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2885_, 1);
v___x_2887_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0));
v___x_2888_ = l_Lean_Name_toString(v_a_2886_, v___x_2826_);
v___x_2889_ = lean_string_append(v___x_2887_, v___x_2888_);
lean_dec_ref(v___x_2888_);
v_a_2840_ = v___x_2889_;
goto v___jp_2839_;
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec_ref_known(v___x_2885_, 1);
v___x_2890_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1));
v___x_2891_ = l_Nat_reprFast(v_id_2884_);
v___x_2892_ = lean_string_append(v___x_2890_, v___x_2891_);
lean_dec_ref(v___x_2891_);
v___x_2893_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2));
v___x_2894_ = lean_string_append(v___x_2892_, v___x_2893_);
v_a_2840_ = v___x_2894_;
goto v___jp_2839_;
}
}
}
}
}
v___jp_2896_:
{
if (v___y_2897_ == 0)
{
lean_object* v___x_2898_; lean_object* v_env_2899_; lean_object* v_nextMacroScope_2900_; lean_object* v_ngen_2901_; lean_object* v_auxDeclNGen_2902_; lean_object* v_traceState_2903_; lean_object* v_messages_2904_; lean_object* v_infoState_2905_; lean_object* v_snapshotTasks_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2915_; 
v___x_2898_ = lean_st_ref_take(v___x_2844_);
v_env_2899_ = lean_ctor_get(v___x_2898_, 0);
v_nextMacroScope_2900_ = lean_ctor_get(v___x_2898_, 1);
v_ngen_2901_ = lean_ctor_get(v___x_2898_, 2);
v_auxDeclNGen_2902_ = lean_ctor_get(v___x_2898_, 3);
v_traceState_2903_ = lean_ctor_get(v___x_2898_, 4);
v_messages_2904_ = lean_ctor_get(v___x_2898_, 6);
v_infoState_2905_ = lean_ctor_get(v___x_2898_, 7);
v_snapshotTasks_2906_ = lean_ctor_get(v___x_2898_, 8);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2915_ == 0)
{
lean_object* v_unused_2916_; 
v_unused_2916_ = lean_ctor_get(v___x_2898_, 5);
lean_dec(v_unused_2916_);
v___x_2908_ = v___x_2898_;
v_isShared_2909_ = v_isSharedCheck_2915_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_snapshotTasks_2906_);
lean_inc(v_infoState_2905_);
lean_inc(v_messages_2904_);
lean_inc(v_traceState_2903_);
lean_inc(v_auxDeclNGen_2902_);
lean_inc(v_ngen_2901_);
lean_inc(v_nextMacroScope_2900_);
lean_inc(v_env_2899_);
lean_dec(v___x_2898_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2915_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2910_ = l_Lean_Kernel_enableDiag(v_env_2899_, v___x_2850_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 5, v___x_2827_);
lean_ctor_set(v___x_2908_, 0, v___x_2910_);
v___x_2912_ = v___x_2908_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_nextMacroScope_2900_);
lean_ctor_set(v_reuseFailAlloc_2914_, 2, v_ngen_2901_);
lean_ctor_set(v_reuseFailAlloc_2914_, 3, v_auxDeclNGen_2902_);
lean_ctor_set(v_reuseFailAlloc_2914_, 4, v_traceState_2903_);
lean_ctor_set(v_reuseFailAlloc_2914_, 5, v___x_2827_);
lean_ctor_set(v_reuseFailAlloc_2914_, 6, v_messages_2904_);
lean_ctor_set(v_reuseFailAlloc_2914_, 7, v_infoState_2905_);
lean_ctor_set(v_reuseFailAlloc_2914_, 8, v_snapshotTasks_2906_);
v___x_2912_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_st_ref_set(v___x_2844_, v___x_2912_);
lean_inc(v___x_2844_);
lean_inc(v___x_2832_);
v_fileName_2852_ = v_fileName_2828_;
v_fileMap_2853_ = v___x_2829_;
v_currRecDepth_2854_ = v___x_2830_;
v_ref_2855_ = v___x_2831_;
v_currNamespace_2856_ = v___x_2832_;
v_openDecls_2857_ = v___x_2833_;
v_initHeartbeats_2858_ = v___x_2843_;
v_maxHeartbeats_2859_ = v___x_2834_;
v_quotContext_2860_ = v___x_2832_;
v_currMacroScope_2861_ = v___x_2835_;
v_cancelTk_x3f_2862_ = v___x_2836_;
v_suppressElabErrors_2863_ = v_run_2837_;
v_inheritedTraceOptions_2864_ = v___x_2846_;
v___y_2865_ = v___x_2844_;
goto v___jp_2851_;
}
}
}
else
{
lean_dec_ref(v___x_2827_);
lean_inc(v___x_2844_);
lean_inc(v___x_2832_);
v_fileName_2852_ = v_fileName_2828_;
v_fileMap_2853_ = v___x_2829_;
v_currRecDepth_2854_ = v___x_2830_;
v_ref_2855_ = v___x_2831_;
v_currNamespace_2856_ = v___x_2832_;
v_openDecls_2857_ = v___x_2833_;
v_initHeartbeats_2858_ = v___x_2843_;
v_maxHeartbeats_2859_ = v___x_2834_;
v_quotContext_2860_ = v___x_2832_;
v_currMacroScope_2861_ = v___x_2835_;
v_cancelTk_x3f_2862_ = v___x_2836_;
v_suppressElabErrors_2863_ = v_run_2837_;
v_inheritedTraceOptions_2864_ = v___x_2846_;
v___y_2865_ = v___x_2844_;
goto v___jp_2851_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object** _args){
lean_object* v___x_2918_ = _args[0];
lean_object* v___x_2919_ = _args[1];
lean_object* v_mainModuleName_2920_ = _args[2];
lean_object* v_a_2921_ = _args[3];
lean_object* v___x_2922_ = _args[4];
lean_object* v___x_2923_ = _args[5];
lean_object* v_fileName_2924_ = _args[6];
lean_object* v___x_2925_ = _args[7];
lean_object* v___x_2926_ = _args[8];
lean_object* v___x_2927_ = _args[9];
lean_object* v___x_2928_ = _args[10];
lean_object* v___x_2929_ = _args[11];
lean_object* v___x_2930_ = _args[12];
lean_object* v___x_2931_ = _args[13];
lean_object* v___x_2932_ = _args[14];
lean_object* v_run_2933_ = _args[15];
lean_object* v___y_2934_ = _args[16];
_start:
{
uint8_t v___x_22495__boxed_2935_; uint8_t v_run_boxed_2936_; lean_object* v_res_2937_; 
v___x_22495__boxed_2935_ = lean_unbox(v___x_2922_);
v_run_boxed_2936_ = lean_unbox(v_run_2933_);
v_res_2937_ = l___private_Lean_Shell_0__Lean_shellMain___lam__1(v___x_2918_, v___x_2919_, v_mainModuleName_2920_, v_a_2921_, v___x_22495__boxed_2935_, v___x_2923_, v_fileName_2924_, v___x_2925_, v___x_2926_, v___x_2927_, v___x_2928_, v___x_2929_, v___x_2930_, v___x_2931_, v___x_2932_, v_run_boxed_2936_);
lean_dec(v_a_2921_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_2938_, lean_object* v_a_2939_, lean_object* v_b_2940_){
_start:
{
lean_object* v_str_2941_; lean_object* v_startInclusive_2942_; lean_object* v_endExclusive_2943_; lean_object* v___x_2944_; uint8_t v___x_2945_; 
v_str_2941_ = lean_ctor_get(v_val_2938_, 0);
v_startInclusive_2942_ = lean_ctor_get(v_val_2938_, 1);
v_endExclusive_2943_ = lean_ctor_get(v_val_2938_, 2);
v___x_2944_ = lean_nat_sub(v_endExclusive_2943_, v_startInclusive_2942_);
v___x_2945_ = lean_nat_dec_eq(v_a_2939_, v___x_2944_);
lean_dec(v___x_2944_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; uint32_t v___x_2947_; uint32_t v___x_2948_; uint8_t v___x_2949_; 
v___x_2946_ = lean_nat_add(v_startInclusive_2942_, v_a_2939_);
v___x_2947_ = lean_string_utf8_get_fast(v_str_2941_, v___x_2946_);
v___x_2948_ = 10;
v___x_2949_ = lean_uint32_dec_eq(v___x_2947_, v___x_2948_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
lean_dec(v_a_2939_);
v___x_2950_ = lean_box(0);
v___x_2951_ = lean_string_utf8_next_fast(v_str_2941_, v___x_2946_);
lean_dec(v___x_2946_);
v___x_2952_ = lean_nat_sub(v___x_2951_, v_startInclusive_2942_);
v_a_2939_ = v___x_2952_;
v_b_2940_ = v___x_2950_;
goto _start;
}
else
{
lean_object* v___x_2954_; 
lean_dec(v___x_2946_);
v___x_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2954_, 0, v_a_2939_);
return v___x_2954_;
}
}
else
{
lean_dec(v_a_2939_);
lean_inc(v_b_2940_);
return v_b_2940_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_2955_, lean_object* v_a_2956_, lean_object* v_b_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_2955_, v_a_2956_, v_b_2957_);
lean_dec(v_b_2957_);
lean_dec_ref(v_val_2955_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_2959_){
_start:
{
uint32_t v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = 10;
v___x_2962_ = lean_string_push(v_s_2959_, v___x_2961_);
v___x_2963_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_2964_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_s_2967_){
_start:
{
uint32_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2969_ = 10;
v___x_2970_ = lean_string_push(v_s_2967_, v___x_2969_);
v___x_2971_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_s_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_s_2972_);
return v_res_2974_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1(void){
_start:
{
lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2976_ = lean_box(0);
v___x_2977_ = lean_internal_has_address_sanitizer(v___x_2976_);
return v___x_2977_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_box(0);
v___x_2979_ = lean_internal_get_option_overrides(v___x_2978_);
return v___x_2979_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__6(void){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = l_Lean_Options_empty;
v___x_2985_ = l_Lean_Core_getMaxHeartbeats(v___x_2984_);
return v___x_2985_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__7(void){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = lean_unsigned_to_nat(1u);
v___x_2987_ = l_Lean_firstFrontendMacroScope;
v___x_2988_ = lean_nat_add(v___x_2987_, v___x_2986_);
return v___x_2988_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12(void){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2999_ = lean_unsigned_to_nat(32u);
v___x_3000_ = lean_mk_empty_array_with_capacity(v___x_2999_);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
return v___x_3001_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13(void){
_start:
{
size_t v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3002_ = ((size_t)5ULL);
v___x_3003_ = lean_unsigned_to_nat(0u);
v___x_3004_ = lean_unsigned_to_nat(32u);
v___x_3005_ = lean_mk_empty_array_with_capacity(v___x_3004_);
v___x_3006_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__12, &l___private_Lean_Shell_0__Lean_shellMain___closed__12_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12);
v___x_3007_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
lean_ctor_set(v___x_3007_, 1, v___x_3005_);
lean_ctor_set(v___x_3007_, 2, v___x_3003_);
lean_ctor_set(v___x_3007_, 3, v___x_3003_);
lean_ctor_set_usize(v___x_3007_, 4, v___x_3002_);
return v___x_3007_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14(void){
_start:
{
lean_object* v___x_3008_; uint64_t v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_3009_ = 0ULL;
v___x_3010_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3010_, 0, v___x_3008_);
lean_ctor_set_uint64(v___x_3010_, sizeof(void*)*1, v___x_3009_);
return v___x_3010_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15(void){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3011_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3012_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__15, &l___private_Lean_Shell_0__Lean_shellMain___closed__15_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15);
v___x_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
return v___x_3013_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__16, &l___private_Lean_Shell_0__Lean_shellMain___closed__16_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16);
v___x_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
return v___x_3015_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__18(void){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3016_ = l_Lean_NameSet_empty;
v___x_3017_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_3018_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
lean_ctor_set(v___x_3018_, 2, v___x_3016_);
return v___x_3018_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__19(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; lean_object* v___x_3022_; 
v___x_3019_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_3020_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__16, &l___private_Lean_Shell_0__Lean_shellMain___closed__16_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16);
v___x_3021_ = 1;
v___x_3022_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3022_, 0, v___x_3020_);
lean_ctor_set(v___x_3022_, 1, v___x_3020_);
lean_ctor_set(v___x_3022_, 2, v___x_3019_);
lean_ctor_set_uint8(v___x_3022_, sizeof(void*)*3, v___x_3021_);
return v___x_3022_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__24(void){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__23));
v___x_3029_ = lean_string_utf8_byte_size(v___x_3028_);
return v___x_3029_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__25(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3030_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__24, &l___private_Lean_Shell_0__Lean_shellMain___closed__24_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__24);
v___x_3031_ = lean_unsigned_to_nat(0u);
v___x_3032_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__23));
v___x_3033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set(v___x_3033_, 1, v___x_3031_);
lean_ctor_set(v___x_3033_, 2, v___x_3030_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* v_args_3037_, lean_object* v_opts_3038_){
_start:
{
lean_object* v_fns_3047_; uint8_t v_printPrefix_3066_; 
v_printPrefix_3066_ = lean_ctor_get_uint8(v_opts_3038_, sizeof(void*)*13 + 9);
if (v_printPrefix_3066_ == 0)
{
uint8_t v_printLibDir_3067_; 
v_printLibDir_3067_ = lean_ctor_get_uint8(v_opts_3038_, sizeof(void*)*13 + 10);
if (v_printLibDir_3067_ == 0)
{
lean_object* v_leanOpts_3068_; lean_object* v_forwardedArgs_3069_; uint8_t v_component_3070_; uint8_t v_useStdin_3071_; uint8_t v_onlyDeps_3072_; uint8_t v_onlySrcDeps_3073_; uint8_t v_depsJson_3074_; uint32_t v_trustLevel_3075_; lean_object* v_rootDir_x3f_3076_; lean_object* v_setupFileName_x3f_3077_; lean_object* v_oleanFileName_x3f_3078_; lean_object* v_ileanFileName_x3f_3079_; lean_object* v_cFileName_x3f_3080_; lean_object* v_bcFileName_x3f_3081_; uint8_t v_jsonOutput_3082_; lean_object* v_errorOnKinds_3083_; uint8_t v_printStats_3084_; uint8_t v_run_3085_; lean_object* v_incrSaveFileName_x3f_3086_; lean_object* v_incrLoadFileName_x3f_3087_; lean_object* v_incrHeaderSaveFileName_x3f_3088_; lean_object* v___f_3089_; lean_object* v___y_3091_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; uint8_t v___x_3133_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v_mainModuleName_3140_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v_contents_3241_; lean_object* v___y_3267_; lean_object* v_str_3268_; lean_object* v_startInclusive_3269_; lean_object* v_endExclusive_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v_fileName_3373_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3411_; lean_object* v___y_3412_; uint8_t v___y_3443_; lean_object* v_fst_3444_; lean_object* v_snd_3445_; uint8_t v___y_3447_; lean_object* v___x_3477_; lean_object* v_maxMemory_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; 
v_leanOpts_3068_ = lean_ctor_get(v_opts_3038_, 0);
lean_inc_ref(v_leanOpts_3068_);
v_forwardedArgs_3069_ = lean_ctor_get(v_opts_3038_, 1);
lean_inc_ref(v_forwardedArgs_3069_);
v_component_3070_ = lean_ctor_get_uint8(v_opts_3038_, sizeof(void*)*13 + 8);
v_useStdin_3071_ = lean_ctor_get_uint8(v_opts_3038_, sizeof(void*)*13 + 11);
v_onlyDeps_3072_ = lean_ctor_get_uint8(v_opts_3038_, sizeof(void*)*13 + 12);
v_onlySrcDeps_3073_ = lean_ctor_get_uint8(v_opts_3038_, sizeof(void*)*13 + 13);
v_depsJson_3074_ = lean_ctor_get_uint8(v_opts_3038_, sizeof(void*)*13 + 14);
v_trustLevel_3075_ = lean_ctor_get_uint32(v_opts_3038_, sizeof(void*)*13);
v_rootDir_x3f_3076_ = lean_ctor_get(v_opts_3038_, 3);
lean_inc(v_rootDir_x3f_3076_);
v_setupFileName_x3f_3077_ = lean_ctor_get(v_opts_3038_, 4);
lean_inc(v_setupFileName_x3f_3077_);
v_oleanFileName_x3f_3078_ = lean_ctor_get(v_opts_3038_, 5);
lean_inc(v_oleanFileName_x3f_3078_);
v_ileanFileName_x3f_3079_ = lean_ctor_get(v_opts_3038_, 6);
lean_inc(v_ileanFileName_x3f_3079_);
v_cFileName_x3f_3080_ = lean_ctor_get(v_opts_3038_, 7);
lean_inc(v_cFileName_x3f_3080_);
v_bcFileName_x3f_3081_ = lean_ctor_get(v_opts_3038_, 8);
lean_inc(v_bcFileName_x3f_3081_);
v_jsonOutput_3082_ = lean_ctor_get_uint8(v_opts_3038_, sizeof(void*)*13 + 15);
v_errorOnKinds_3083_ = lean_ctor_get(v_opts_3038_, 9);
lean_inc_ref(v_errorOnKinds_3083_);
v_printStats_3084_ = lean_ctor_get_uint8(v_opts_3038_, sizeof(void*)*13 + 16);
v_run_3085_ = lean_ctor_get_uint8(v_opts_3038_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_3086_ = lean_ctor_get(v_opts_3038_, 10);
lean_inc(v_incrSaveFileName_x3f_3086_);
v_incrLoadFileName_x3f_3087_ = lean_ctor_get(v_opts_3038_, 11);
lean_inc(v_incrLoadFileName_x3f_3087_);
v_incrHeaderSaveFileName_x3f_3088_ = lean_ctor_get(v_opts_3038_, 12);
lean_inc(v_incrHeaderSaveFileName_x3f_3088_);
lean_dec_ref(v_opts_3038_);
v___f_3089_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__0));
v___x_3105_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__2, &l___private_Lean_Shell_0__Lean_shellMain___closed__2_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2);
v___x_3106_ = l_Lean_Options_mergeBy(v___f_3089_, v_leanOpts_3068_, v___x_3105_);
v___x_3133_ = 1;
v___x_3477_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3478_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3106_, v___x_3477_);
v___x_3479_ = lean_unsigned_to_nat(0u);
v___x_3480_ = lean_nat_dec_eq(v_maxMemory_3478_, v___x_3479_);
if (v___x_3480_ == 0)
{
size_t v___x_3481_; size_t v___x_3482_; size_t v___x_3483_; size_t v___x_3484_; lean_object* v___x_3485_; 
v___x_3481_ = lean_usize_of_nat(v_maxMemory_3478_);
lean_dec(v_maxMemory_3478_);
v___x_3482_ = ((size_t)10ULL);
v___x_3483_ = lean_usize_shift_left(v___x_3481_, v___x_3482_);
v___x_3484_ = lean_usize_shift_left(v___x_3483_, v___x_3482_);
v___x_3485_ = lean_internal_set_max_memory(v___x_3484_);
goto v___jp_3468_;
}
else
{
lean_dec(v_maxMemory_3478_);
goto v___jp_3468_;
}
v___jp_3090_:
{
lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3092_ = lean_display_cumulative_profiling_times();
v___x_3093_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__1, &l___private_Lean_Shell_0__Lean_shellMain___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1);
if (v___x_3093_ == 0)
{
if (lean_obj_tag(v___y_3091_) == 0)
{
if (v___x_3093_ == 0)
{
uint8_t v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = 1;
v___x_3095_ = lean_io_exit(v___x_3094_);
return v___x_3095_;
}
else
{
goto v___jp_3043_;
}
}
else
{
lean_dec_ref_known(v___y_3091_, 1);
goto v___jp_3043_;
}
}
else
{
if (lean_obj_tag(v___y_3091_) == 0)
{
goto v___jp_3040_;
}
else
{
lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3103_; 
v_isSharedCheck_3103_ = !lean_is_exclusive(v___y_3091_);
if (v_isSharedCheck_3103_ == 0)
{
lean_object* v_unused_3104_; 
v_unused_3104_ = lean_ctor_get(v___y_3091_, 0);
lean_dec(v_unused_3104_);
v___x_3097_ = v___y_3091_;
v_isShared_3098_ = v_isSharedCheck_3103_;
goto v_resetjp_3096_;
}
else
{
lean_dec(v___y_3091_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3103_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
if (v___x_3093_ == 0)
{
lean_del_object(v___x_3097_);
goto v___jp_3040_;
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3099_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3098_ == 0)
{
lean_ctor_set_tag(v___x_3097_, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3099_);
v___x_3101_ = v___x_3097_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
}
}
v___jp_3107_:
{
if (lean_obj_tag(v_bcFileName_x3f_3081_) == 1)
{
lean_object* v_val_3111_; lean_object* v___x_3112_; 
v_val_3111_ = lean_ctor_get(v_bcFileName_x3f_3081_, 0);
lean_inc(v_val_3111_);
lean_dec_ref_known(v_bcFileName_x3f_3081_, 1);
v___x_3112_ = lean_init_llvm();
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_dec_ref_known(v___x_3112_, 1);
v___x_3113_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__3));
v___x_3114_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(v___x_3114_, 0, v___y_3110_);
lean_closure_set(v___x_3114_, 1, v___y_3109_);
lean_closure_set(v___x_3114_, 2, v_val_3111_);
v___x_3115_ = lean_box(0);
v___x_3116_ = l_Lean_profileitIOUnsafe___redArg(v___x_3113_, v___x_3106_, v___x_3114_, v___x_3115_);
lean_dec_ref(v___x_3106_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_dec_ref_known(v___x_3116_, 1);
v___y_3091_ = v___y_3108_;
goto v___jp_3090_;
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec(v___y_3108_);
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3116_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3116_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec(v_val_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___x_3106_);
v_a_3125_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3112_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3112_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
else
{
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___x_3106_);
lean_dec(v_bcFileName_x3f_3081_);
v___y_3091_ = v___y_3108_;
goto v___jp_3090_;
}
}
v___jp_3134_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = lean_unsigned_to_nat(0u);
v___x_3142_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__4));
lean_inc(v_mainModuleName_3140_);
lean_inc_ref(v___x_3106_);
v___x_3143_ = l_Lean_Elab_runFrontend(v___y_3139_, v___x_3106_, v___y_3137_, v_mainModuleName_3140_, v_trustLevel_3075_, v_oleanFileName_x3f_3078_, v_ileanFileName_x3f_3079_, v_jsonOutput_3082_, v_errorOnKinds_3083_, v___x_3142_, v_printStats_3084_, v___y_3136_, v_incrSaveFileName_x3f_3086_, v_incrLoadFileName_x3f_3087_, v_incrHeaderSaveFileName_x3f_3088_);
lean_dec_ref(v_errorOnKinds_3083_);
lean_dec(v_ileanFileName_x3f_3079_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3211_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3146_ = v___x_3143_;
v_isShared_3147_ = v_isSharedCheck_3211_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3143_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3211_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
if (lean_obj_tag(v_a_3144_) == 1)
{
if (v_run_3085_ == 0)
{
lean_del_object(v___x_3146_);
lean_dec(v___y_3138_);
if (lean_obj_tag(v_cFileName_x3f_3080_) == 1)
{
lean_object* v_val_3148_; lean_object* v_val_3149_; uint8_t v___x_3150_; lean_object* v___x_3151_; 
v_val_3148_ = lean_ctor_get(v_a_3144_, 0);
lean_inc(v_val_3148_);
v_val_3149_ = lean_ctor_get(v_cFileName_x3f_3080_, 0);
lean_inc(v_val_3149_);
lean_dec_ref_known(v_cFileName_x3f_3080_, 1);
v___x_3150_ = 1;
v___x_3151_ = lean_io_prim_handle_mk(v_val_3149_, v___x_3150_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___f_3172_; lean_object* v___x_3173_; 
lean_dec(v_val_3149_);
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
v___x_3153_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__5));
v___x_3154_ = l_Lean_instInhabitedFileMap_default;
v___x_3155_ = l_Lean_Options_empty;
v___x_3156_ = lean_box(0);
v___x_3157_ = lean_box(0);
v___x_3158_ = lean_box(0);
v___x_3159_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__6, &l___private_Lean_Shell_0__Lean_shellMain___closed__6_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__6);
v___x_3160_ = l_Lean_firstFrontendMacroScope;
v___x_3161_ = lean_box(0);
v___x_3162_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__7, &l___private_Lean_Shell_0__Lean_shellMain___closed__7_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__7);
v___x_3163_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__10));
v___x_3164_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__11));
v___x_3165_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__14, &l___private_Lean_Shell_0__Lean_shellMain___closed__14_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14);
v___x_3166_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__17, &l___private_Lean_Shell_0__Lean_shellMain___closed__17_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17);
v___x_3167_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__18, &l___private_Lean_Shell_0__Lean_shellMain___closed__18_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__18);
v___x_3168_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__19, &l___private_Lean_Shell_0__Lean_shellMain___closed__19_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__19);
lean_inc(v_val_3148_);
v___x_3169_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3169_, 0, v_val_3148_);
lean_ctor_set(v___x_3169_, 1, v___x_3162_);
lean_ctor_set(v___x_3169_, 2, v___x_3163_);
lean_ctor_set(v___x_3169_, 3, v___x_3164_);
lean_ctor_set(v___x_3169_, 4, v___x_3165_);
lean_ctor_set(v___x_3169_, 5, v___x_3166_);
lean_ctor_set(v___x_3169_, 6, v___x_3167_);
lean_ctor_set(v___x_3169_, 7, v___x_3168_);
lean_ctor_set(v___x_3169_, 8, v___x_3142_);
v___x_3170_ = lean_box(v___x_3133_);
v___x_3171_ = lean_box(v_run_3085_);
lean_inc(v_mainModuleName_3140_);
v___f_3172_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 17, 16);
lean_closure_set(v___f_3172_, 0, v___x_3169_);
lean_closure_set(v___f_3172_, 1, v___x_3155_);
lean_closure_set(v___f_3172_, 2, v_mainModuleName_3140_);
lean_closure_set(v___f_3172_, 3, v_a_3152_);
lean_closure_set(v___f_3172_, 4, v___x_3170_);
lean_closure_set(v___f_3172_, 5, v___x_3166_);
lean_closure_set(v___f_3172_, 6, v___y_3135_);
lean_closure_set(v___f_3172_, 7, v___x_3154_);
lean_closure_set(v___f_3172_, 8, v___x_3141_);
lean_closure_set(v___f_3172_, 9, v___x_3156_);
lean_closure_set(v___f_3172_, 10, v___x_3157_);
lean_closure_set(v___f_3172_, 11, v___x_3158_);
lean_closure_set(v___f_3172_, 12, v___x_3159_);
lean_closure_set(v___f_3172_, 13, v___x_3160_);
lean_closure_set(v___f_3172_, 14, v___x_3161_);
lean_closure_set(v___f_3172_, 15, v___x_3171_);
v___x_3173_ = l_Lean_profileitIOUnsafe___redArg(v___x_3153_, v___x_3106_, v___f_3172_, v___x_3157_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_dec_ref_known(v___x_3173_, 1);
v___y_3108_ = v_a_3144_;
v___y_3109_ = v_mainModuleName_3140_;
v___y_3110_ = v_val_3148_;
goto v___jp_3107_;
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec(v_val_3148_);
lean_dec_ref_known(v_a_3144_, 1);
lean_dec(v_mainModuleName_3140_);
lean_dec_ref(v___x_3106_);
lean_dec(v_bcFileName_x3f_3081_);
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3173_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_dec_ref_known(v___x_3151_, 1);
lean_dec(v_val_3148_);
lean_dec_ref_known(v_a_3144_, 1);
lean_dec(v_mainModuleName_3140_);
lean_dec_ref(v___y_3135_);
lean_dec_ref(v___x_3106_);
lean_dec(v_bcFileName_x3f_3081_);
v___x_3182_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___x_3183_ = lean_string_append(v___x_3182_, v_val_3149_);
lean_dec(v_val_3149_);
v___x_3184_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_3185_ = lean_string_append(v___x_3183_, v___x_3184_);
v___x_3186_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3185_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3194_; 
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; 
v_unused_3195_ = lean_ctor_get(v___x_3186_, 0);
lean_dec(v_unused_3195_);
v___x_3188_ = v___x_3186_;
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
else
{
lean_dec(v___x_3186_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3194_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3190_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v___x_3190_);
v___x_3192_ = v___x_3188_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
v_a_3196_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3186_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3186_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
}
else
{
lean_object* v_val_3204_; 
lean_dec_ref(v___y_3135_);
lean_dec(v_cFileName_x3f_3080_);
v_val_3204_ = lean_ctor_get(v_a_3144_, 0);
lean_inc(v_val_3204_);
v___y_3108_ = v_a_3144_;
v___y_3109_ = v_mainModuleName_3140_;
v___y_3110_ = v_val_3204_;
goto v___jp_3107_;
}
}
else
{
lean_object* v_val_3205_; uint32_t v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3209_; 
lean_dec(v_mainModuleName_3140_);
lean_dec_ref(v___y_3135_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
v_val_3205_ = lean_ctor_get(v_a_3144_, 0);
lean_inc(v_val_3205_);
lean_dec_ref_known(v_a_3144_, 1);
v___x_3206_ = lean_eval_main(v_val_3205_, v___x_3106_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___x_3106_);
lean_dec(v_val_3205_);
v___x_3207_ = lean_box_uint32(v___x_3206_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v___x_3207_);
v___x_3209_ = v___x_3146_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
else
{
lean_del_object(v___x_3146_);
lean_dec(v_mainModuleName_3140_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3135_);
lean_dec_ref(v___x_3106_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
v___y_3091_ = v_a_3144_;
goto v___jp_3090_;
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v_mainModuleName_3140_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3135_);
lean_dec_ref(v___x_3106_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
v_a_3212_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3143_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3143_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
v___jp_3220_:
{
if (lean_obj_tag(v___y_3226_) == 0)
{
lean_object* v_a_3227_; 
v_a_3227_ = lean_ctor_get(v___y_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___y_3226_, 1);
v___y_3135_ = v___y_3221_;
v___y_3136_ = v___y_3223_;
v___y_3137_ = v___y_3222_;
v___y_3138_ = v___y_3225_;
v___y_3139_ = v___y_3224_;
v_mainModuleName_3140_ = v_a_3227_;
goto v___jp_3134_;
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec_ref(v___x_3106_);
lean_dec(v_incrHeaderSaveFileName_x3f_3088_);
lean_dec(v_incrLoadFileName_x3f_3087_);
lean_dec(v_incrSaveFileName_x3f_3086_);
lean_dec_ref(v_errorOnKinds_3083_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
lean_dec(v_ileanFileName_x3f_3079_);
lean_dec(v_oleanFileName_x3f_3078_);
v_a_3228_ = lean_ctor_get(v___y_3226_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___y_3226_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___y_3226_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___y_3226_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
v___jp_3236_:
{
if (lean_obj_tag(v_setupFileName_x3f_3077_) == 0)
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_box(0);
if (lean_obj_tag(v___y_3240_) == 1)
{
lean_object* v_val_3243_; lean_object* v___x_3244_; 
v_val_3243_ = lean_ctor_get(v___y_3240_, 0);
lean_inc(v_val_3243_);
lean_dec_ref_known(v___y_3240_, 1);
v___x_3244_ = l_Lean_moduleNameOfFileName(v_val_3243_, v_rootDir_x3f_3076_);
if (lean_obj_tag(v___x_3244_) == 0)
{
v___y_3221_ = v___y_3237_;
v___y_3222_ = v___y_3238_;
v___y_3223_ = v___x_3242_;
v___y_3224_ = v_contents_3241_;
v___y_3225_ = v___y_3239_;
v___y_3226_ = v___x_3244_;
goto v___jp_3220_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_3078_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_3080_) == 0)
{
lean_object* v___x_3245_; 
lean_dec_ref_known(v___x_3244_, 1);
v___x_3245_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__22));
v___y_3135_ = v___y_3237_;
v___y_3136_ = v___x_3242_;
v___y_3137_ = v___y_3238_;
v___y_3138_ = v___y_3239_;
v___y_3139_ = v_contents_3241_;
v_mainModuleName_3140_ = v___x_3245_;
goto v___jp_3134_;
}
else
{
v___y_3221_ = v___y_3237_;
v___y_3222_ = v___y_3238_;
v___y_3223_ = v___x_3242_;
v___y_3224_ = v_contents_3241_;
v___y_3225_ = v___y_3239_;
v___y_3226_ = v___x_3244_;
goto v___jp_3220_;
}
}
else
{
v___y_3221_ = v___y_3237_;
v___y_3222_ = v___y_3238_;
v___y_3223_ = v___x_3242_;
v___y_3224_ = v_contents_3241_;
v___y_3225_ = v___y_3239_;
v___y_3226_ = v___x_3244_;
goto v___jp_3220_;
}
}
}
else
{
lean_object* v___x_3246_; 
lean_dec(v___y_3240_);
lean_dec(v_rootDir_x3f_3076_);
v___x_3246_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__22));
v___y_3135_ = v___y_3237_;
v___y_3136_ = v___x_3242_;
v___y_3137_ = v___y_3238_;
v___y_3138_ = v___y_3239_;
v___y_3139_ = v_contents_3241_;
v_mainModuleName_3140_ = v___x_3246_;
goto v___jp_3134_;
}
}
else
{
lean_object* v_val_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3265_; 
lean_dec(v___y_3240_);
lean_dec(v_rootDir_x3f_3076_);
v_val_3247_ = lean_ctor_get(v_setupFileName_x3f_3077_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v_setupFileName_x3f_3077_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3249_ = v_setupFileName_x3f_3077_;
v_isShared_3250_ = v_isSharedCheck_3265_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_val_3247_);
lean_dec(v_setupFileName_x3f_3077_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3265_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Lean_ModuleSetup_load(v_val_3247_);
lean_dec(v_val_3247_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v_name_3253_; lean_object* v___x_3255_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref_known(v___x_3251_, 1);
v_name_3253_ = lean_ctor_get(v_a_3252_, 0);
lean_inc(v_name_3253_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v_a_3252_);
v___x_3255_ = v___x_3249_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3252_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
v___y_3135_ = v___y_3237_;
v___y_3136_ = v___x_3255_;
v___y_3137_ = v___y_3238_;
v___y_3138_ = v___y_3239_;
v___y_3139_ = v_contents_3241_;
v_mainModuleName_3140_ = v_name_3253_;
goto v___jp_3134_;
}
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
lean_del_object(v___x_3249_);
lean_dec_ref(v_contents_3241_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___x_3106_);
lean_dec(v_incrHeaderSaveFileName_x3f_3088_);
lean_dec(v_incrLoadFileName_x3f_3087_);
lean_dec(v_incrSaveFileName_x3f_3086_);
lean_dec_ref(v_errorOnKinds_3083_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
lean_dec(v_ileanFileName_x3f_3079_);
lean_dec(v_oleanFileName_x3f_3078_);
v_a_3257_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3251_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3251_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
}
v___jp_3266_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; 
v___x_3275_ = lean_nat_add(v_startInclusive_3269_, v___y_3274_);
lean_dec(v___y_3274_);
lean_inc(v___x_3275_);
lean_inc_ref(v_str_3268_);
v___x_3276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3276_, 0, v_str_3268_);
lean_ctor_set(v___x_3276_, 1, v_startInclusive_3269_);
lean_ctor_set(v___x_3276_, 2, v___x_3275_);
v___x_3277_ = l_String_Slice_trimAscii(v___x_3276_);
v___x_3278_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__25, &l___private_Lean_Shell_0__Lean_shellMain___closed__25_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__25);
v___x_3279_ = l_String_Slice_beq(v___x_3277_, v___x_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_dec(v___x_3275_);
lean_dec(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v_endExclusive_3270_);
lean_dec_ref(v_str_3268_);
lean_dec_ref(v___y_3267_);
lean_dec_ref(v___x_3106_);
lean_dec(v_incrHeaderSaveFileName_x3f_3088_);
lean_dec(v_incrLoadFileName_x3f_3087_);
lean_dec(v_incrSaveFileName_x3f_3086_);
lean_dec_ref(v_errorOnKinds_3083_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
lean_dec(v_ileanFileName_x3f_3079_);
lean_dec(v_oleanFileName_x3f_3078_);
lean_dec(v_setupFileName_x3f_3077_);
lean_dec(v_rootDir_x3f_3076_);
v___x_3280_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__26));
v___x_3281_ = l_String_Slice_toString(v___x_3277_);
lean_dec_ref(v___x_3277_);
v___x_3282_ = lean_string_append(v___x_3280_, v___x_3281_);
lean_dec_ref(v___x_3281_);
v___x_3283_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_3284_ = lean_string_append(v___x_3282_, v___x_3283_);
v___x_3285_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3284_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3293_; 
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3293_ == 0)
{
lean_object* v_unused_3294_; 
v_unused_3294_ = lean_ctor_get(v___x_3285_, 0);
lean_dec(v_unused_3294_);
v___x_3287_ = v___x_3285_;
v_isShared_3288_ = v_isSharedCheck_3293_;
goto v_resetjp_3286_;
}
else
{
lean_dec(v___x_3285_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3293_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3289_; lean_object* v___x_3291_; 
v___x_3289_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 0, v___x_3289_);
v___x_3291_ = v___x_3287_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3289_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
v_a_3295_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3285_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3285_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
else
{
lean_object* v___x_3303_; 
lean_dec_ref(v___x_3277_);
v___x_3303_ = lean_string_utf8_extract(v_str_3268_, v___x_3275_, v_endExclusive_3270_);
lean_dec(v_endExclusive_3270_);
lean_dec(v___x_3275_);
lean_dec_ref(v_str_3268_);
v___y_3237_ = v___y_3267_;
v___y_3238_ = v___y_3271_;
v___y_3239_ = v___y_3272_;
v___y_3240_ = v___y_3273_;
v_contents_3241_ = v___x_3303_;
goto v___jp_3236_;
}
}
v___jp_3304_:
{
if (lean_obj_tag(v___y_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3310_; 
v_a_3309_ = lean_ctor_get(v___y_3308_, 0);
lean_inc(v_a_3309_);
lean_dec_ref_known(v___y_3308_, 1);
v___x_3310_ = lean_decode_lossy_utf8(v_a_3309_);
lean_dec(v_a_3309_);
if (v_onlyDeps_3072_ == 0)
{
if (v_onlySrcDeps_3073_ == 0)
{
lean_object* v___x_3311_; 
lean_inc_ref(v___x_3310_);
v___x_3311_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_3310_);
if (lean_obj_tag(v___x_3311_) == 1)
{
lean_object* v_val_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_dec_ref(v___x_3310_);
v_val_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_val_3312_);
lean_dec_ref_known(v___x_3311_, 1);
v___x_3313_ = lean_unsigned_to_nat(0u);
v___x_3314_ = lean_box(0);
v___x_3315_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3312_, v___x_3313_, v___x_3314_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_str_3316_; lean_object* v_startInclusive_3317_; lean_object* v_endExclusive_3318_; lean_object* v___x_3319_; 
v_str_3316_ = lean_ctor_get(v_val_3312_, 0);
lean_inc_ref(v_str_3316_);
v_startInclusive_3317_ = lean_ctor_get(v_val_3312_, 1);
lean_inc(v_startInclusive_3317_);
v_endExclusive_3318_ = lean_ctor_get(v_val_3312_, 2);
lean_inc(v_endExclusive_3318_);
lean_dec(v_val_3312_);
v___x_3319_ = lean_nat_sub(v_endExclusive_3318_, v_startInclusive_3317_);
lean_inc_ref(v___y_3306_);
v___y_3267_ = v___y_3306_;
v_str_3268_ = v_str_3316_;
v_startInclusive_3269_ = v_startInclusive_3317_;
v_endExclusive_3270_ = v_endExclusive_3318_;
v___y_3271_ = v___y_3306_;
v___y_3272_ = v___y_3305_;
v___y_3273_ = v___y_3307_;
v___y_3274_ = v___x_3319_;
goto v___jp_3266_;
}
else
{
lean_object* v_val_3320_; lean_object* v_str_3321_; lean_object* v_startInclusive_3322_; lean_object* v_endExclusive_3323_; 
v_val_3320_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_val_3320_);
lean_dec_ref_known(v___x_3315_, 1);
v_str_3321_ = lean_ctor_get(v_val_3312_, 0);
lean_inc_ref(v_str_3321_);
v_startInclusive_3322_ = lean_ctor_get(v_val_3312_, 1);
lean_inc(v_startInclusive_3322_);
v_endExclusive_3323_ = lean_ctor_get(v_val_3312_, 2);
lean_inc(v_endExclusive_3323_);
lean_dec(v_val_3312_);
lean_inc_ref(v___y_3306_);
v___y_3267_ = v___y_3306_;
v_str_3268_ = v_str_3321_;
v_startInclusive_3269_ = v_startInclusive_3322_;
v_endExclusive_3270_ = v_endExclusive_3323_;
v___y_3271_ = v___y_3306_;
v___y_3272_ = v___y_3305_;
v___y_3273_ = v___y_3307_;
v___y_3274_ = v_val_3320_;
goto v___jp_3266_;
}
}
else
{
lean_dec(v___x_3311_);
lean_inc_ref(v___y_3306_);
v___y_3237_ = v___y_3306_;
v___y_3238_ = v___y_3306_;
v___y_3239_ = v___y_3305_;
v___y_3240_ = v___y_3307_;
v_contents_3241_ = v___x_3310_;
goto v___jp_3236_;
}
}
else
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
lean_dec(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec_ref(v___x_3106_);
lean_dec(v_incrHeaderSaveFileName_x3f_3088_);
lean_dec(v_incrLoadFileName_x3f_3087_);
lean_dec(v_incrSaveFileName_x3f_3086_);
lean_dec_ref(v_errorOnKinds_3083_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
lean_dec(v_ileanFileName_x3f_3079_);
lean_dec(v_oleanFileName_x3f_3078_);
lean_dec(v_setupFileName_x3f_3077_);
lean_dec(v_rootDir_x3f_3076_);
v___x_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___y_3306_);
v___x_3325_ = l_Lean_Elab_printImportSrcs(v___x_3310_, v___x_3324_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3333_; 
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3333_ == 0)
{
lean_object* v_unused_3334_; 
v_unused_3334_ = lean_ctor_get(v___x_3325_, 0);
lean_dec(v_unused_3334_);
v___x_3327_ = v___x_3325_;
v_isShared_3328_ = v_isSharedCheck_3333_;
goto v_resetjp_3326_;
}
else
{
lean_dec(v___x_3325_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3333_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3329_; lean_object* v___x_3331_; 
v___x_3329_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 0, v___x_3329_);
v___x_3331_ = v___x_3327_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
v_a_3335_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3325_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3325_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
lean_dec(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec_ref(v___x_3106_);
lean_dec(v_incrHeaderSaveFileName_x3f_3088_);
lean_dec(v_incrLoadFileName_x3f_3087_);
lean_dec(v_incrSaveFileName_x3f_3086_);
lean_dec_ref(v_errorOnKinds_3083_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
lean_dec(v_ileanFileName_x3f_3079_);
lean_dec(v_oleanFileName_x3f_3078_);
lean_dec(v_setupFileName_x3f_3077_);
lean_dec(v_rootDir_x3f_3076_);
v___x_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3343_, 0, v___y_3306_);
v___x_3344_ = l_Lean_Elab_printImports(v___x_3310_, v___x_3343_);
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
v___x_3348_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
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
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___x_3106_);
lean_dec(v_incrHeaderSaveFileName_x3f_3088_);
lean_dec(v_incrLoadFileName_x3f_3087_);
lean_dec(v_incrSaveFileName_x3f_3086_);
lean_dec_ref(v_errorOnKinds_3083_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
lean_dec(v_ileanFileName_x3f_3079_);
lean_dec(v_oleanFileName_x3f_3078_);
lean_dec(v_setupFileName_x3f_3077_);
lean_dec(v_rootDir_x3f_3076_);
v_a_3362_ = lean_ctor_get(v___y_3308_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___y_3308_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___y_3308_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___y_3308_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
v___jp_3370_:
{
if (v_useStdin_3071_ == 0)
{
lean_object* v___x_3374_; 
v___x_3374_ = l_IO_FS_readBinFile(v_fileName_3373_);
v___y_3305_ = v___y_3371_;
v___y_3306_ = v_fileName_3373_;
v___y_3307_ = v___y_3372_;
v___y_3308_ = v___x_3374_;
goto v___jp_3304_;
}
else
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = lean_get_stdin();
v___x_3376_ = l_IO_FS_Stream_readBinToEnd(v___x_3375_);
v___y_3305_ = v___y_3371_;
v___y_3306_ = v_fileName_3373_;
v___y_3307_ = v___y_3372_;
v___y_3308_ = v___x_3376_;
goto v___jp_3304_;
}
}
v___jp_3377_:
{
if (lean_obj_tag(v___y_3379_) == 1)
{
lean_object* v_val_3380_; 
v_val_3380_ = lean_ctor_get(v___y_3379_, 0);
lean_inc(v_val_3380_);
v___y_3371_ = v___y_3378_;
v___y_3372_ = v___y_3379_;
v_fileName_3373_ = v_val_3380_;
goto v___jp_3370_;
}
else
{
if (v_useStdin_3071_ == 0)
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
lean_dec(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___x_3106_);
lean_dec(v_incrHeaderSaveFileName_x3f_3088_);
lean_dec(v_incrLoadFileName_x3f_3087_);
lean_dec(v_incrSaveFileName_x3f_3086_);
lean_dec_ref(v_errorOnKinds_3083_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
lean_dec(v_ileanFileName_x3f_3079_);
lean_dec(v_oleanFileName_x3f_3078_);
lean_dec(v_setupFileName_x3f_3077_);
lean_dec(v_rootDir_x3f_3076_);
v___x_3381_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__27));
v___x_3382_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3381_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v___x_3383_; 
lean_dec_ref_known(v___x_3382_, 1);
v___x_3383_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3133_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3391_; 
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3391_ == 0)
{
lean_object* v_unused_3392_; 
v_unused_3392_ = lean_ctor_get(v___x_3383_, 0);
lean_dec(v_unused_3392_);
v___x_3385_ = v___x_3383_;
v_isShared_3386_ = v_isSharedCheck_3391_;
goto v_resetjp_3384_;
}
else
{
lean_dec(v___x_3383_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3391_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; lean_object* v___x_3389_; 
v___x_3387_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v___x_3387_);
v___x_3389_ = v___x_3385_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3387_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
v_a_3393_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3383_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3383_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
v_a_3401_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3382_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3382_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
else
{
lean_object* v___x_3409_; 
v___x_3409_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__28));
v___y_3371_ = v___y_3378_;
v___y_3372_ = v___y_3379_;
v_fileName_3373_ = v___x_3409_;
goto v___jp_3370_;
}
}
}
v___jp_3410_:
{
uint8_t v___x_3413_; 
v___x_3413_ = l_List_isEmpty___redArg(v___y_3411_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_dec(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___x_3106_);
lean_dec(v_incrHeaderSaveFileName_x3f_3088_);
lean_dec(v_incrLoadFileName_x3f_3087_);
lean_dec(v_incrSaveFileName_x3f_3086_);
lean_dec_ref(v_errorOnKinds_3083_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
lean_dec(v_ileanFileName_x3f_3079_);
lean_dec(v_oleanFileName_x3f_3078_);
lean_dec(v_setupFileName_x3f_3077_);
lean_dec(v_rootDir_x3f_3076_);
v___x_3414_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__27));
v___x_3415_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3414_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v___x_3416_; 
lean_dec_ref_known(v___x_3415_, 1);
v___x_3416_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3133_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3424_; 
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3424_ == 0)
{
lean_object* v_unused_3425_; 
v_unused_3425_ = lean_ctor_get(v___x_3416_, 0);
lean_dec(v_unused_3425_);
v___x_3418_ = v___x_3416_;
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
else
{
lean_dec(v___x_3416_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3420_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3420_);
v___x_3422_ = v___x_3418_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
v_a_3426_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3416_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3416_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
v_a_3434_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3415_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3415_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
else
{
v___y_3378_ = v___y_3411_;
v___y_3379_ = v___y_3412_;
goto v___jp_3377_;
}
}
v___jp_3442_:
{
if (v_run_3085_ == 0)
{
v___y_3411_ = v_snd_3445_;
v___y_3412_ = v_fst_3444_;
goto v___jp_3410_;
}
else
{
if (v___y_3443_ == 0)
{
v___y_3378_ = v_snd_3445_;
v___y_3379_ = v_fst_3444_;
goto v___jp_3377_;
}
else
{
v___y_3411_ = v_snd_3445_;
v___y_3412_ = v_fst_3444_;
goto v___jp_3410_;
}
}
}
v___jp_3446_:
{
if (lean_obj_tag(v_args_3037_) == 0)
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_box(0);
v___y_3443_ = v___y_3447_;
v_fst_3444_ = v___x_3448_;
v_snd_3445_ = v_args_3037_;
goto v___jp_3442_;
}
else
{
lean_object* v_head_3449_; lean_object* v_tail_3450_; lean_object* v___x_3451_; 
v_head_3449_ = lean_ctor_get(v_args_3037_, 0);
lean_inc(v_head_3449_);
v_tail_3450_ = lean_ctor_get(v_args_3037_, 1);
lean_inc(v_tail_3450_);
lean_dec_ref_known(v_args_3037_, 2);
v___x_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3451_, 0, v_head_3449_);
v___y_3443_ = v___y_3447_;
v_fst_3444_ = v___x_3451_;
v_snd_3445_ = v_tail_3450_;
goto v___jp_3442_;
}
}
v___jp_3452_:
{
switch(v_component_3070_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_3069_);
if (v_onlyDeps_3072_ == 0)
{
v___y_3447_ = v_onlyDeps_3072_;
goto v___jp_3446_;
}
else
{
if (v_depsJson_3074_ == 0)
{
v___y_3447_ = v_depsJson_3074_;
goto v___jp_3446_;
}
else
{
lean_dec_ref(v___x_3106_);
lean_dec(v_incrHeaderSaveFileName_x3f_3088_);
lean_dec(v_incrLoadFileName_x3f_3087_);
lean_dec(v_incrSaveFileName_x3f_3086_);
lean_dec_ref(v_errorOnKinds_3083_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
lean_dec(v_ileanFileName_x3f_3079_);
lean_dec(v_oleanFileName_x3f_3078_);
lean_dec(v_setupFileName_x3f_3077_);
lean_dec(v_rootDir_x3f_3076_);
if (v_useStdin_3071_ == 0)
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_array_mk(v_args_3037_);
v_fns_3047_ = v___x_3453_;
goto v___jp_3046_;
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
lean_dec(v_args_3037_);
v___x_3454_ = lean_get_stdin();
v___x_3455_ = l_IO_FS_Stream_lines(v___x_3454_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3455_, 1);
v_fns_3047_ = v_a_3456_;
goto v___jp_3046_;
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
v_a_3457_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3455_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3455_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
lean_dec_ref(v___x_3106_);
lean_dec(v_incrHeaderSaveFileName_x3f_3088_);
lean_dec(v_incrLoadFileName_x3f_3087_);
lean_dec(v_incrSaveFileName_x3f_3086_);
lean_dec_ref(v_errorOnKinds_3083_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
lean_dec(v_ileanFileName_x3f_3079_);
lean_dec(v_oleanFileName_x3f_3078_);
lean_dec(v_setupFileName_x3f_3077_);
lean_dec(v_rootDir_x3f_3076_);
lean_dec(v_args_3037_);
v___x_3465_ = lean_array_to_list(v_forwardedArgs_3069_);
v___x_3466_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3465_);
return v___x_3466_;
}
default: 
{
lean_object* v___x_3467_; 
lean_dec(v_incrHeaderSaveFileName_x3f_3088_);
lean_dec(v_incrLoadFileName_x3f_3087_);
lean_dec(v_incrSaveFileName_x3f_3086_);
lean_dec_ref(v_errorOnKinds_3083_);
lean_dec(v_bcFileName_x3f_3081_);
lean_dec(v_cFileName_x3f_3080_);
lean_dec(v_ileanFileName_x3f_3079_);
lean_dec(v_oleanFileName_x3f_3078_);
lean_dec(v_setupFileName_x3f_3077_);
lean_dec(v_rootDir_x3f_3076_);
lean_dec_ref(v_forwardedArgs_3069_);
lean_dec(v_args_3037_);
v___x_3467_ = l_Lean_Server_FileWorker_workerMain(v___x_3106_);
return v___x_3467_;
}
}
}
v___jp_3468_:
{
lean_object* v___x_3469_; lean_object* v_timeout_3470_; lean_object* v___x_3471_; uint8_t v___x_3472_; 
v___x_3469_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3470_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3106_, v___x_3469_);
v___x_3471_ = lean_unsigned_to_nat(0u);
v___x_3472_ = lean_nat_dec_eq(v_timeout_3470_, v___x_3471_);
if (v___x_3472_ == 0)
{
size_t v___x_3473_; size_t v___x_3474_; size_t v___x_3475_; lean_object* v___x_3476_; 
v___x_3473_ = lean_usize_of_nat(v_timeout_3470_);
lean_dec(v_timeout_3470_);
v___x_3474_ = ((size_t)1000ULL);
v___x_3475_ = lean_usize_mul(v___x_3473_, v___x_3474_);
v___x_3476_ = lean_internal_set_max_heartbeat(v___x_3475_);
goto v___jp_3452_;
}
else
{
lean_dec(v_timeout_3470_);
goto v___jp_3452_;
}
}
}
else
{
lean_object* v___x_3486_; 
lean_dec_ref(v_opts_3038_);
lean_dec(v_args_3037_);
v___x_3486_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3488_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v___x_3488_ = l_Lean_getLibDir(v_a_3487_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v___x_3490_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3489_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3498_; 
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3498_ == 0)
{
lean_object* v_unused_3499_; 
v_unused_3499_ = lean_ctor_get(v___x_3490_, 0);
lean_dec(v_unused_3499_);
v___x_3492_ = v___x_3490_;
v_isShared_3493_ = v_isSharedCheck_3498_;
goto v_resetjp_3491_;
}
else
{
lean_dec(v___x_3490_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3498_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3494_; lean_object* v___x_3496_; 
v___x_3494_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v___x_3494_);
v___x_3496_ = v___x_3492_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3494_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
v_a_3500_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3490_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3490_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
v_a_3508_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3488_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3488_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
v_a_3516_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3486_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3486_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
else
{
lean_object* v___x_3524_; 
lean_dec_ref(v_opts_3038_);
lean_dec(v_args_3037_);
v___x_3524_ = l_Lean_getBuildDir();
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
v___jp_3040_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
return v___x_3042_;
}
v___jp_3043_:
{
uint8_t v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = 0;
v___x_3045_ = lean_io_exit(v___x_3044_);
return v___x_3045_;
}
v___jp_3046_:
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_printImportsJson(v_fns_3047_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3056_; 
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v___x_3048_, 0);
lean_dec(v_unused_3057_);
v___x_3050_ = v___x_3048_;
v_isShared_3051_ = v_isSharedCheck_3056_;
goto v_resetjp_3049_;
}
else
{
lean_dec(v___x_3048_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3056_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3052_; lean_object* v___x_3054_; 
v___x_3052_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___x_3052_);
v___x_3054_ = v___x_3050_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
v_a_3058_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3048_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3048_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3552_, lean_object* v_opts_3553_, lean_object* v_a_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = lean_shell_main(v_args_3552_, v_opts_3553_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3556_, lean_object* v_inst_3557_, lean_object* v_R_3558_, lean_object* v_a_3559_, lean_object* v_b_3560_, lean_object* v_c_3561_){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3556_, v_a_3559_, v_b_3560_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3563_, lean_object* v_inst_3564_, lean_object* v_R_3565_, lean_object* v_a_3566_, lean_object* v_b_3567_, lean_object* v_c_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3563_, v_inst_3564_, v_R_3565_, v_a_3566_, v_b_3567_, v_c_3568_);
lean_dec(v_b_3567_);
lean_dec_ref(v_val_3563_);
return v_res_3569_;
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
