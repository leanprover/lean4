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
lean_object* lean_display_cumulative_profiling_times();
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
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12(void){
_start:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = lean_box(0);
v___x_158_ = lean_internal_is_debug(v___x_157_);
return v___x_158_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36(void){
_start:
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = lean_box(0);
v___x_183_ = lean_internal_is_multi_thread(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp(uint8_t v_useStderr_188_){
_start:
{
lean_object* v___y_191_; lean_object* v___y_195_; lean_object* v_out_222_; 
if (v_useStderr_188_ == 0)
{
lean_object* v___x_278_; 
v___x_278_ = lean_get_stdout();
v_out_222_ = v___x_278_;
goto v___jp_221_;
}
else
{
lean_object* v___x_279_; 
v___x_279_ = lean_get_stderr();
v_out_222_ = v___x_279_;
goto v___jp_221_;
}
v___jp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__0));
v___x_193_ = l_IO_FS_Stream_putStrLn(v___y_191_, v___x_192_);
return v___x_193_;
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__1));
lean_inc_ref(v___y_195_);
v___x_197_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_196_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec_ref(v___x_197_);
v___x_198_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__2));
lean_inc_ref(v___y_195_);
v___x_199_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_198_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec_ref(v___x_199_);
v___x_200_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__3));
lean_inc_ref(v___y_195_);
v___x_201_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_200_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec_ref(v___x_201_);
v___x_202_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__4));
lean_inc_ref(v___y_195_);
v___x_203_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec_ref(v___x_203_);
v___x_204_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__5));
lean_inc_ref(v___y_195_);
v___x_205_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec_ref(v___x_205_);
v___x_206_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__6));
lean_inc_ref(v___y_195_);
v___x_207_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec_ref(v___x_207_);
v___x_208_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__7));
lean_inc_ref(v___y_195_);
v___x_209_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_208_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec_ref(v___x_209_);
v___x_210_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__8));
lean_inc_ref(v___y_195_);
v___x_211_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_210_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec_ref(v___x_211_);
v___x_212_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__9));
lean_inc_ref(v___y_195_);
v___x_213_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_212_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec_ref(v___x_213_);
v___x_214_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__10));
lean_inc_ref(v___y_195_);
v___x_215_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_214_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec_ref(v___x_215_);
v___x_216_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__11));
lean_inc_ref(v___y_195_);
v___x_217_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
uint8_t v___x_218_; 
lean_dec_ref(v___x_217_);
v___x_218_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__12, &l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12);
if (v___x_218_ == 0)
{
v___y_191_ = v___y_195_;
goto v___jp_190_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__13));
lean_inc_ref(v___y_195_);
v___x_220_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_219_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_dec_ref(v___x_220_);
v___y_191_ = v___y_195_;
goto v___jp_190_;
}
else
{
lean_dec_ref(v___y_195_);
return v___x_220_;
}
}
}
else
{
lean_dec_ref(v___y_195_);
return v___x_217_;
}
}
else
{
lean_dec_ref(v___y_195_);
return v___x_215_;
}
}
else
{
lean_dec_ref(v___y_195_);
return v___x_213_;
}
}
else
{
lean_dec_ref(v___y_195_);
return v___x_211_;
}
}
else
{
lean_dec_ref(v___y_195_);
return v___x_209_;
}
}
else
{
lean_dec_ref(v___y_195_);
return v___x_207_;
}
}
else
{
lean_dec_ref(v___y_195_);
return v___x_205_;
}
}
else
{
lean_dec_ref(v___y_195_);
return v___x_203_;
}
}
else
{
lean_dec_ref(v___y_195_);
return v___x_201_;
}
}
else
{
lean_dec_ref(v___y_195_);
return v___x_199_;
}
}
else
{
lean_dec_ref(v___y_195_);
return v___x_197_;
}
}
v___jp_221_:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = l___private_Lean_Shell_0__Lean_versionHeader;
lean_inc_ref(v_out_222_);
v___x_224_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref(v___x_224_);
v___x_225_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__14));
lean_inc_ref(v_out_222_);
v___x_226_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_225_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec_ref(v___x_226_);
v___x_227_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__15));
lean_inc_ref(v_out_222_);
v___x_228_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_227_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec_ref(v___x_228_);
v___x_229_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__16));
lean_inc_ref(v_out_222_);
v___x_230_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec_ref(v___x_230_);
v___x_231_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__17));
lean_inc_ref(v_out_222_);
v___x_232_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_231_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec_ref(v___x_232_);
v___x_233_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__18));
lean_inc_ref(v_out_222_);
v___x_234_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_233_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec_ref(v___x_234_);
v___x_235_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__19));
lean_inc_ref(v_out_222_);
v___x_236_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_235_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec_ref(v___x_236_);
v___x_237_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__20));
lean_inc_ref(v_out_222_);
v___x_238_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_237_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref(v___x_238_);
v___x_239_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__21));
lean_inc_ref(v_out_222_);
v___x_240_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_239_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec_ref(v___x_240_);
v___x_241_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__22));
lean_inc_ref(v_out_222_);
v___x_242_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_241_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec_ref(v___x_242_);
v___x_243_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__23));
lean_inc_ref(v_out_222_);
v___x_244_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_243_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec_ref(v___x_244_);
v___x_245_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__24));
lean_inc_ref(v_out_222_);
v___x_246_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_245_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref(v___x_246_);
v___x_247_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__25));
lean_inc_ref(v_out_222_);
v___x_248_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_247_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref(v___x_248_);
v___x_249_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__26));
lean_inc_ref(v_out_222_);
v___x_250_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_249_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec_ref(v___x_250_);
v___x_251_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__27));
lean_inc_ref(v_out_222_);
v___x_252_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec_ref(v___x_252_);
v___x_253_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__28));
lean_inc_ref(v_out_222_);
v___x_254_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_253_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref(v___x_254_);
v___x_255_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__29));
lean_inc_ref(v_out_222_);
v___x_256_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_255_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec_ref(v___x_256_);
v___x_257_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__30));
lean_inc_ref(v_out_222_);
v___x_258_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_257_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref(v___x_258_);
v___x_259_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__31));
lean_inc_ref(v_out_222_);
v___x_260_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_259_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec_ref(v___x_260_);
v___x_261_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__32));
lean_inc_ref(v_out_222_);
v___x_262_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_261_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref(v___x_262_);
v___x_263_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__33));
lean_inc_ref(v_out_222_);
v___x_264_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_263_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec_ref(v___x_264_);
v___x_265_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__34));
lean_inc_ref(v_out_222_);
v___x_266_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_265_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec_ref(v___x_266_);
v___x_267_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__35));
lean_inc_ref(v_out_222_);
v___x_268_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
uint8_t v___x_269_; 
lean_dec_ref(v___x_268_);
v___x_269_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__36, &l___private_Lean_Shell_0__Lean_displayHelp___closed__36_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36);
if (v___x_269_ == 0)
{
v___y_195_ = v_out_222_;
goto v___jp_194_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__37));
lean_inc_ref(v_out_222_);
v___x_271_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_270_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec_ref(v___x_271_);
v___x_272_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__38));
lean_inc_ref(v_out_222_);
v___x_273_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_272_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec_ref(v___x_273_);
v___x_274_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__39));
lean_inc_ref(v_out_222_);
v___x_275_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_274_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec_ref(v___x_275_);
v___x_276_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__40));
lean_inc_ref(v_out_222_);
v___x_277_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_276_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_dec_ref(v___x_277_);
v___y_195_ = v_out_222_;
goto v___jp_194_;
}
else
{
lean_dec_ref(v_out_222_);
return v___x_277_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_275_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_273_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_271_;
}
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_268_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_266_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_264_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_262_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_260_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_258_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_256_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_254_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_252_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_250_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_248_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_246_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_244_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_242_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_240_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_238_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_236_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_234_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_232_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_230_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_228_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_226_;
}
}
else
{
lean_dec_ref(v_out_222_);
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object* v_useStderr_280_, lean_object* v_a_281_){
_start:
{
uint8_t v_useStderr_boxed_282_; lean_object* v_res_283_; 
v_useStderr_boxed_282_ = lean_unbox(v_useStderr_280_);
v_res_283_ = l___private_Lean_Shell_0__Lean_displayHelp(v_useStderr_boxed_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(uint8_t v_x_284_){
_start:
{
switch(v_x_284_)
{
case 0:
{
lean_object* v___x_285_; 
v___x_285_ = lean_unsigned_to_nat(0u);
return v___x_285_;
}
case 1:
{
lean_object* v___x_286_; 
v___x_286_ = lean_unsigned_to_nat(1u);
return v___x_286_;
}
default: 
{
lean_object* v___x_287_; 
v___x_287_ = lean_unsigned_to_nat(2u);
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___boxed(lean_object* v_x_288_){
_start:
{
uint8_t v_x_boxed_289_; lean_object* v_res_290_; 
v_x_boxed_289_ = lean_unbox(v_x_288_);
v_res_290_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(v_x_boxed_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(uint8_t v_x_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(v_x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx___boxed(lean_object* v_x_293_){
_start:
{
uint8_t v_x_4__boxed_294_; lean_object* v_res_295_; 
v_x_4__boxed_294_ = lean_unbox(v_x_293_);
v_res_295_ = l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(v_x_4__boxed_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(lean_object* v_k_296_){
_start:
{
lean_inc(v_k_296_);
return v_k_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg___boxed(lean_object* v_k_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(v_k_297_);
lean_dec(v_k_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(lean_object* v_motive_299_, lean_object* v_ctorIdx_300_, uint8_t v_t_301_, lean_object* v_h_302_, lean_object* v_k_303_){
_start:
{
lean_inc(v_k_303_);
return v_k_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___boxed(lean_object* v_motive_304_, lean_object* v_ctorIdx_305_, lean_object* v_t_306_, lean_object* v_h_307_, lean_object* v_k_308_){
_start:
{
uint8_t v_t_boxed_309_; lean_object* v_res_310_; 
v_t_boxed_309_ = lean_unbox(v_t_306_);
v_res_310_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(v_motive_304_, v_ctorIdx_305_, v_t_boxed_309_, v_h_307_, v_k_308_);
lean_dec(v_k_308_);
lean_dec(v_ctorIdx_305_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(lean_object* v_frontend_311_){
_start:
{
lean_inc(v_frontend_311_);
return v_frontend_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg___boxed(lean_object* v_frontend_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(v_frontend_312_);
lean_dec(v_frontend_312_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(lean_object* v_motive_314_, uint8_t v_t_315_, lean_object* v_h_316_, lean_object* v_frontend_317_){
_start:
{
lean_inc(v_frontend_317_);
return v_frontend_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___boxed(lean_object* v_motive_318_, lean_object* v_t_319_, lean_object* v_h_320_, lean_object* v_frontend_321_){
_start:
{
uint8_t v_t_boxed_322_; lean_object* v_res_323_; 
v_t_boxed_322_ = lean_unbox(v_t_319_);
v_res_323_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(v_motive_318_, v_t_boxed_322_, v_h_320_, v_frontend_321_);
lean_dec(v_frontend_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(lean_object* v_watchdog_324_){
_start:
{
lean_inc(v_watchdog_324_);
return v_watchdog_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg___boxed(lean_object* v_watchdog_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(v_watchdog_325_);
lean_dec(v_watchdog_325_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(lean_object* v_motive_327_, uint8_t v_t_328_, lean_object* v_h_329_, lean_object* v_watchdog_330_){
_start:
{
lean_inc(v_watchdog_330_);
return v_watchdog_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___boxed(lean_object* v_motive_331_, lean_object* v_t_332_, lean_object* v_h_333_, lean_object* v_watchdog_334_){
_start:
{
uint8_t v_t_boxed_335_; lean_object* v_res_336_; 
v_t_boxed_335_ = lean_unbox(v_t_332_);
v_res_336_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(v_motive_331_, v_t_boxed_335_, v_h_333_, v_watchdog_334_);
lean_dec(v_watchdog_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(lean_object* v_worker_337_){
_start:
{
lean_inc(v_worker_337_);
return v_worker_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg___boxed(lean_object* v_worker_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(v_worker_338_);
lean_dec(v_worker_338_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(lean_object* v_motive_340_, uint8_t v_t_341_, lean_object* v_h_342_, lean_object* v_worker_343_){
_start:
{
lean_inc(v_worker_343_);
return v_worker_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___boxed(lean_object* v_motive_344_, lean_object* v_t_345_, lean_object* v_h_346_, lean_object* v_worker_347_){
_start:
{
uint8_t v_t_boxed_348_; lean_object* v_res_349_; 
v_t_boxed_348_ = lean_unbox(v_t_345_);
v_res_349_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(v_motive_344_, v_t_boxed_348_, v_h_346_, v_worker_347_);
lean_dec(v_worker_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object* v_name_350_, lean_object* v_decl_351_, lean_object* v_ref_352_){
_start:
{
lean_object* v_defValue_354_; lean_object* v_descr_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_381_; 
v_defValue_354_ = lean_ctor_get(v_decl_351_, 0);
v_descr_355_ = lean_ctor_get(v_decl_351_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_decl_351_);
if (v_isSharedCheck_381_ == 0)
{
v___x_357_ = v_decl_351_;
v_isShared_358_ = v_isSharedCheck_381_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_descr_355_);
lean_inc(v_defValue_354_);
lean_dec(v_decl_351_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_381_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_inc(v_defValue_354_);
v___x_359_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_359_, 0, v_defValue_354_);
lean_inc_n(v_name_350_, 2);
v___x_360_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_360_, 0, v_name_350_);
lean_ctor_set(v___x_360_, 1, v_ref_352_);
lean_ctor_set(v___x_360_, 2, v___x_359_);
lean_ctor_set(v___x_360_, 3, v_descr_355_);
v___x_361_ = lean_register_option(v_name_350_, v___x_360_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_371_; 
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_361_, 0);
lean_dec(v_unused_372_);
v___x_363_ = v___x_361_;
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
else
{
lean_dec(v___x_361_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v_defValue_354_);
lean_ctor_set(v___x_357_, 0, v_name_350_);
v___x_366_ = v___x_357_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_name_350_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_defValue_354_);
v___x_366_ = v_reuseFailAlloc_370_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_366_);
v___x_368_ = v___x_363_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_del_object(v___x_357_);
lean_dec(v_defValue_354_);
lean_dec(v_name_350_);
v_a_373_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_361_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_361_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_382_, lean_object* v_decl_383_, lean_object* v_ref_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v_name_382_, v_decl_383_, v_ref_384_);
return v_res_386_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_box(0);
v___x_391_ = lean_internal_get_default_max_memory(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_393_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_418_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_419_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_420_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_421_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_418_, v___x_419_, v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2____boxed(lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
return v_res_423_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_box(0);
v___x_428_ = lean_internal_get_default_max_heartbeat(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_430_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_436_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_437_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_438_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_439_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_436_, v___x_437_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2____boxed(lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(lean_object* v_name_442_, lean_object* v_decl_443_, lean_object* v_ref_444_){
_start:
{
lean_object* v_defValue_446_; lean_object* v_descr_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_474_; 
v_defValue_446_ = lean_ctor_get(v_decl_443_, 0);
v_descr_447_ = lean_ctor_get(v_decl_443_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_decl_443_);
if (v_isSharedCheck_474_ == 0)
{
v___x_449_ = v_decl_443_;
v_isShared_450_ = v_isSharedCheck_474_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_descr_447_);
lean_inc(v_defValue_446_);
lean_dec(v_decl_443_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_474_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_451_ = lean_alloc_ctor(1, 0, 1);
v___x_452_ = lean_unbox(v_defValue_446_);
lean_ctor_set_uint8(v___x_451_, 0, v___x_452_);
lean_inc_n(v_name_442_, 2);
v___x_453_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_453_, 0, v_name_442_);
lean_ctor_set(v___x_453_, 1, v_ref_444_);
lean_ctor_set(v___x_453_, 2, v___x_451_);
lean_ctor_set(v___x_453_, 3, v_descr_447_);
v___x_454_ = lean_register_option(v_name_442_, v___x_453_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_464_; 
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v___x_454_, 0);
lean_dec(v_unused_465_);
v___x_456_ = v___x_454_;
v_isShared_457_ = v_isSharedCheck_464_;
goto v_resetjp_455_;
}
else
{
lean_dec(v___x_454_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_464_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v_defValue_446_);
lean_ctor_set(v___x_449_, 0, v_name_442_);
v___x_459_ = v___x_449_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_name_442_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_defValue_446_);
v___x_459_ = v_reuseFailAlloc_463_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_461_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_459_);
v___x_461_ = v___x_456_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_del_object(v___x_449_);
lean_dec(v_defValue_446_);
lean_dec(v_name_442_);
v_a_466_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_454_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_454_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_475_, lean_object* v_decl_476_, lean_object* v_ref_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v_name_475_, v_decl_476_, v_ref_477_);
return v_res_479_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_box(0);
v___x_484_ = lean_internal_get_default_verbose(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_485_; uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_485_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_486_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_487_ = lean_box(v___x_486_);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_485_);
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultOptions___boxed(lean_object* v_x_00___x40_Lean_Shell_2553953037____hygCtx___hyg_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = lean_internal_get_default_options(v_x_00___x40_Lean_Shell_2553953037____hygCtx___hyg_500_);
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getHardwareCurrency___boxed(lean_object* v_x_00___x40_Lean_Shell_1910423346____hygCtx___hyg_513_){
_start:
{
uint32_t v_res_514_; lean_object* v_r_515_; 
v_res_514_ = lean_internal_get_hardware_concurrency(v_x_00___x40_Lean_Shell_1910423346____hygCtx___hyg_513_);
v_r_515_ = lean_box_uint32(v_res_514_);
return v_r_515_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0(void){
_start:
{
lean_object* v___x_516_; uint32_t v___x_517_; 
v___x_516_ = lean_box(0);
v___x_517_ = lean_internal_get_hardware_concurrency(v___x_516_);
return v___x_517_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads(void){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__36, &l___private_Lean_Shell_0__Lean_displayHelp___closed__36_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36);
if (v___x_518_ == 0)
{
uint32_t v___x_519_; 
v___x_519_ = 0;
return v___x_519_;
}
else
{
uint32_t v___x_520_; 
v___x_520_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0, &l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0);
return v___x_520_;
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_box(0);
v___x_522_ = lean_internal_get_default_options(v___x_521_);
return v___x_522_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2(void){
_start:
{
lean_object* v___x_525_; uint32_t v___x_526_; uint32_t v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_525_ = lean_box(0);
v___x_526_ = l___private_Lean_Shell_0__Lean_defaultNumThreads;
v___x_527_ = l___private_Lean_Shell_0__Lean_defaultTrustLevel;
v___x_528_ = l_Lean_Options_empty;
v___x_529_ = 0;
v___x_530_ = 0;
v___x_531_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1));
v___x_532_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0);
v___x_533_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_531_);
lean_ctor_set(v___x_533_, 2, v___x_528_);
lean_ctor_set(v___x_533_, 3, v___x_525_);
lean_ctor_set(v___x_533_, 4, v___x_525_);
lean_ctor_set(v___x_533_, 5, v___x_525_);
lean_ctor_set(v___x_533_, 6, v___x_525_);
lean_ctor_set(v___x_533_, 7, v___x_525_);
lean_ctor_set(v___x_533_, 8, v___x_525_);
lean_ctor_set(v___x_533_, 9, v___x_531_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*10 + 8, v___x_530_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*10 + 9, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*10 + 10, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*10 + 11, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*10 + 12, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*10 + 13, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*10 + 14, v___x_529_);
lean_ctor_set_uint32(v___x_533_, sizeof(void*)*10, v___x_527_);
lean_ctor_set_uint32(v___x_533_, sizeof(void*)*10 + 4, v___x_526_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*10 + 15, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*10 + 16, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*10 + 17, v___x_529_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object* v_x_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2);
return v___x_535_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_run(lean_object* v_opts_536_){
_start:
{
uint8_t v_run_537_; 
v_run_537_ = lean_ctor_get_uint8(v_opts_536_, sizeof(void*)*10 + 17);
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
lean_dec_ref(v___x_546_);
if (lean_obj_tag(v_val_548_) == 1)
{
uint8_t v_v_549_; 
v_v_549_ = lean_ctor_get_uint8(v_val_548_, 0);
lean_dec_ref(v_val_548_);
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
v_numThreads_563_ = lean_ctor_get_uint32(v_opts_562_, sizeof(void*)*10 + 4);
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
lean_dec_ref(v___x_672_);
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
lean_dec_ref(v___x_674_);
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
lean_dec_ref(v___x_648_);
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
lean_dec_ref(v___x_652_);
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
lean_dec_ref(v___x_734_);
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
lean_dec_ref(v___x_764_);
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
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = l_System_Platform_numBits;
v___x_925_ = lean_unsigned_to_nat(2u);
v___x_926_ = lean_nat_pow(v___x_925_, v___x_924_);
return v___x_926_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1(void){
_start:
{
uint32_t v___x_936_; lean_object* v___x_937_; 
v___x_936_ = 0;
v___x_937_ = lean_box_uint32(v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object* v_opts_938_, uint32_t v_opt_939_, lean_object* v_optArg_x3f_940_){
_start:
{
lean_object* v___y_1042_; uint32_t v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = 101;
v___x_1139_ = lean_uint32_dec_eq(v_opt_939_, v___x_1138_);
if (v___x_1139_ == 0)
{
uint32_t v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = 106;
v___x_1141_ = lean_uint32_dec_eq(v_opt_939_, v___x_1140_);
if (v___x_1141_ == 0)
{
uint32_t v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = 118;
v___x_1143_ = lean_uint32_dec_eq(v_opt_939_, v___x_1142_);
if (v___x_1143_ == 0)
{
uint32_t v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = 86;
v___x_1145_ = lean_uint32_dec_eq(v_opt_939_, v___x_1144_);
if (v___x_1145_ == 0)
{
uint32_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = 103;
v___x_1147_ = lean_uint32_dec_eq(v_opt_939_, v___x_1146_);
if (v___x_1147_ == 0)
{
uint32_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = 104;
v___x_1149_ = lean_uint32_dec_eq(v_opt_939_, v___x_1148_);
if (v___x_1149_ == 0)
{
uint32_t v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = 102;
v___x_1151_ = lean_uint32_dec_eq(v_opt_939_, v___x_1150_);
if (v___x_1151_ == 0)
{
uint32_t v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = 99;
v___x_1153_ = lean_uint32_dec_eq(v_opt_939_, v___x_1152_);
if (v___x_1153_ == 0)
{
uint32_t v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = 98;
v___x_1155_ = lean_uint32_dec_eq(v_opt_939_, v___x_1154_);
if (v___x_1155_ == 0)
{
uint32_t v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = 115;
v___x_1157_ = lean_uint32_dec_eq(v_opt_939_, v___x_1156_);
if (v___x_1157_ == 0)
{
uint32_t v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = 73;
v___x_1159_ = lean_uint32_dec_eq(v_opt_939_, v___x_1158_);
if (v___x_1159_ == 0)
{
uint32_t v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = 114;
v___x_1161_ = lean_uint32_dec_eq(v_opt_939_, v___x_1160_);
if (v___x_1161_ == 0)
{
uint32_t v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = 111;
v___x_1163_ = lean_uint32_dec_eq(v_opt_939_, v___x_1162_);
if (v___x_1163_ == 0)
{
uint32_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = 105;
v___x_1165_ = lean_uint32_dec_eq(v_opt_939_, v___x_1164_);
if (v___x_1165_ == 0)
{
uint32_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = 82;
v___x_1167_ = lean_uint32_dec_eq(v_opt_939_, v___x_1166_);
if (v___x_1167_ == 0)
{
uint32_t v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = 77;
v___x_1169_ = lean_uint32_dec_eq(v_opt_939_, v___x_1168_);
if (v___x_1169_ == 0)
{
uint32_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = 84;
v___x_1171_ = lean_uint32_dec_eq(v_opt_939_, v___x_1170_);
if (v___x_1171_ == 0)
{
uint32_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = 116;
v___x_1173_ = lean_uint32_dec_eq(v_opt_939_, v___x_1172_);
if (v___x_1173_ == 0)
{
uint32_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = 113;
v___x_1175_ = lean_uint32_dec_eq(v_opt_939_, v___x_1174_);
if (v___x_1175_ == 0)
{
uint32_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = 100;
v___x_1177_ = lean_uint32_dec_eq(v_opt_939_, v___x_1176_);
if (v___x_1177_ == 0)
{
uint32_t v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = 79;
v___x_1179_ = lean_uint32_dec_eq(v_opt_939_, v___x_1178_);
if (v___x_1179_ == 0)
{
uint32_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = 78;
v___x_1181_ = lean_uint32_dec_eq(v_opt_939_, v___x_1180_);
if (v___x_1181_ == 0)
{
uint32_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = 74;
v___x_1183_ = lean_uint32_dec_eq(v_opt_939_, v___x_1182_);
if (v___x_1183_ == 0)
{
uint32_t v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = 97;
v___x_1185_ = lean_uint32_dec_eq(v_opt_939_, v___x_1184_);
if (v___x_1185_ == 0)
{
uint32_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = 120;
v___x_1187_ = lean_uint32_dec_eq(v_opt_939_, v___x_1186_);
if (v___x_1187_ == 0)
{
uint32_t v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = 76;
v___x_1189_ = lean_uint32_dec_eq(v_opt_939_, v___x_1188_);
if (v___x_1189_ == 0)
{
uint32_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = 68;
v___x_1191_ = lean_uint32_dec_eq(v_opt_939_, v___x_1190_);
if (v___x_1191_ == 0)
{
uint32_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = 83;
v___x_1193_ = lean_uint32_dec_eq(v_opt_939_, v___x_1192_);
if (v___x_1193_ == 0)
{
uint32_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = 87;
v___x_1195_ = lean_uint32_dec_eq(v_opt_939_, v___x_1194_);
if (v___x_1195_ == 0)
{
uint32_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = 80;
v___x_1197_ = lean_uint32_dec_eq(v_opt_939_, v___x_1196_);
if (v___x_1197_ == 0)
{
uint32_t v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = 66;
v___x_1199_ = lean_uint32_dec_eq(v_opt_939_, v___x_1198_);
if (v___x_1199_ == 0)
{
uint32_t v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = 112;
v___x_1201_ = lean_uint32_dec_eq(v_opt_939_, v___x_1200_);
if (v___x_1201_ == 0)
{
uint32_t v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = 108;
v___x_1203_ = lean_uint32_dec_eq(v_opt_939_, v___x_1202_);
if (v___x_1203_ == 0)
{
uint32_t v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = 117;
v___x_1205_ = lean_uint32_dec_eq(v_opt_939_, v___x_1204_);
if (v___x_1205_ == 0)
{
uint32_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = 69;
v___x_1207_ = lean_uint32_dec_eq(v_opt_939_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_dec(v_optArg_x3f_940_);
lean_dec_ref(v_opts_938_);
goto v___jp_1060_;
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1209_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1208_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1248_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1248_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1248_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v_leanOpts_1214_; lean_object* v_forwardedArgs_1215_; uint8_t v_component_1216_; uint8_t v_printPrefix_1217_; uint8_t v_printLibDir_1218_; uint8_t v_useStdin_1219_; uint8_t v_onlyDeps_1220_; uint8_t v_onlySrcDeps_1221_; uint8_t v_depsJson_1222_; lean_object* v_opts_1223_; uint32_t v_trustLevel_1224_; uint32_t v_numThreads_1225_; lean_object* v_rootDir_x3f_1226_; lean_object* v_setupFileName_x3f_1227_; lean_object* v_oleanFileName_x3f_1228_; lean_object* v_ileanFileName_x3f_1229_; lean_object* v_cFileName_x3f_1230_; lean_object* v_bcFileName_x3f_1231_; uint8_t v_jsonOutput_1232_; lean_object* v_errorOnKinds_1233_; uint8_t v_printStats_1234_; uint8_t v_run_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1247_; 
v_leanOpts_1214_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1215_ = lean_ctor_get(v_opts_938_, 1);
v_component_1216_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1217_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1218_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1219_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1220_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1221_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1222_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1223_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1224_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1225_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1226_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1227_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1228_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1229_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1230_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1231_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1232_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1233_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1234_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1235_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1237_ = v_opts_938_;
v_isShared_1238_ = v_isSharedCheck_1247_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_errorOnKinds_1233_);
lean_inc(v_bcFileName_x3f_1231_);
lean_inc(v_cFileName_x3f_1230_);
lean_inc(v_ileanFileName_x3f_1229_);
lean_inc(v_oleanFileName_x3f_1228_);
lean_inc(v_setupFileName_x3f_1227_);
lean_inc(v_rootDir_x3f_1226_);
lean_inc(v_opts_1223_);
lean_inc(v_forwardedArgs_1215_);
lean_inc(v_leanOpts_1214_);
lean_dec(v_opts_938_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1247_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1239_ = l_String_toName(v_a_1210_);
v___x_1240_ = lean_array_push(v_errorOnKinds_1233_, v___x_1239_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 9, v___x_1240_);
v___x_1242_ = v___x_1237_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_leanOpts_1214_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_forwardedArgs_1215_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_opts_1223_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_rootDir_x3f_1226_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_setupFileName_x3f_1227_);
lean_ctor_set(v_reuseFailAlloc_1246_, 5, v_oleanFileName_x3f_1228_);
lean_ctor_set(v_reuseFailAlloc_1246_, 6, v_ileanFileName_x3f_1229_);
lean_ctor_set(v_reuseFailAlloc_1246_, 7, v_cFileName_x3f_1230_);
lean_ctor_set(v_reuseFailAlloc_1246_, 8, v_bcFileName_x3f_1231_);
lean_ctor_set(v_reuseFailAlloc_1246_, 9, v___x_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, sizeof(void*)*10 + 8, v_component_1216_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, sizeof(void*)*10 + 9, v_printPrefix_1217_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, sizeof(void*)*10 + 10, v_printLibDir_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, sizeof(void*)*10 + 11, v_useStdin_1219_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, sizeof(void*)*10 + 12, v_onlyDeps_1220_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, sizeof(void*)*10 + 13, v_onlySrcDeps_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, sizeof(void*)*10 + 14, v_depsJson_1222_);
lean_ctor_set_uint32(v_reuseFailAlloc_1246_, sizeof(void*)*10, v_trustLevel_1224_);
lean_ctor_set_uint32(v_reuseFailAlloc_1246_, sizeof(void*)*10 + 4, v_numThreads_1225_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, sizeof(void*)*10 + 15, v_jsonOutput_1232_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, sizeof(void*)*10 + 16, v_printStats_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, sizeof(void*)*10 + 17, v_run_1235_);
v___x_1242_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1244_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1242_);
v___x_1244_ = v___x_1212_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec_ref(v_opts_938_);
v_a_1249_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1249_);
lean_dec_ref(v___x_1209_);
v___x_1253_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1254_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1253_);
lean_dec_ref(v___x_1254_);
goto v___jp_1250_;
v___jp_1250_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_io_error_to_string(v_a_1249_);
v___x_1252_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1251_);
lean_dec_ref(v___x_1252_);
goto v___jp_1066_;
}
}
}
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1256_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1255_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1294_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1294_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1294_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v_leanOpts_1261_; lean_object* v_forwardedArgs_1262_; uint8_t v_component_1263_; uint8_t v_printPrefix_1264_; uint8_t v_printLibDir_1265_; uint8_t v_useStdin_1266_; uint8_t v_onlyDeps_1267_; uint8_t v_onlySrcDeps_1268_; uint8_t v_depsJson_1269_; lean_object* v_opts_1270_; uint32_t v_trustLevel_1271_; uint32_t v_numThreads_1272_; lean_object* v_rootDir_x3f_1273_; lean_object* v_oleanFileName_x3f_1274_; lean_object* v_ileanFileName_x3f_1275_; lean_object* v_cFileName_x3f_1276_; lean_object* v_bcFileName_x3f_1277_; uint8_t v_jsonOutput_1278_; lean_object* v_errorOnKinds_1279_; uint8_t v_printStats_1280_; uint8_t v_run_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1292_; 
v_leanOpts_1261_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1262_ = lean_ctor_get(v_opts_938_, 1);
v_component_1263_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1264_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1265_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1266_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1267_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1268_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1269_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1270_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1271_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1272_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1273_ = lean_ctor_get(v_opts_938_, 3);
v_oleanFileName_x3f_1274_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1275_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1276_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1277_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1278_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1279_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1280_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1281_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v_opts_938_, 4);
lean_dec(v_unused_1293_);
v___x_1283_ = v_opts_938_;
v_isShared_1284_ = v_isSharedCheck_1292_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_errorOnKinds_1279_);
lean_inc(v_bcFileName_x3f_1277_);
lean_inc(v_cFileName_x3f_1276_);
lean_inc(v_ileanFileName_x3f_1275_);
lean_inc(v_oleanFileName_x3f_1274_);
lean_inc(v_rootDir_x3f_1273_);
lean_inc(v_opts_1270_);
lean_inc(v_forwardedArgs_1262_);
lean_inc(v_leanOpts_1261_);
lean_dec(v_opts_938_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1292_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_a_1257_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 4, v___x_1285_);
v___x_1287_ = v___x_1283_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_leanOpts_1261_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_forwardedArgs_1262_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_opts_1270_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_rootDir_x3f_1273_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1291_, 5, v_oleanFileName_x3f_1274_);
lean_ctor_set(v_reuseFailAlloc_1291_, 6, v_ileanFileName_x3f_1275_);
lean_ctor_set(v_reuseFailAlloc_1291_, 7, v_cFileName_x3f_1276_);
lean_ctor_set(v_reuseFailAlloc_1291_, 8, v_bcFileName_x3f_1277_);
lean_ctor_set(v_reuseFailAlloc_1291_, 9, v_errorOnKinds_1279_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*10 + 8, v_component_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*10 + 9, v_printPrefix_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*10 + 10, v_printLibDir_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*10 + 11, v_useStdin_1266_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*10 + 12, v_onlyDeps_1267_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*10 + 13, v_onlySrcDeps_1268_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*10 + 14, v_depsJson_1269_);
lean_ctor_set_uint32(v_reuseFailAlloc_1291_, sizeof(void*)*10, v_trustLevel_1271_);
lean_ctor_set_uint32(v_reuseFailAlloc_1291_, sizeof(void*)*10 + 4, v_numThreads_1272_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*10 + 15, v_jsonOutput_1278_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*10 + 16, v_printStats_1280_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*10 + 17, v_run_1281_);
v___x_1287_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1289_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1287_);
v___x_1289_ = v___x_1259_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec_ref(v_opts_938_);
v_a_1295_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1295_);
lean_dec_ref(v___x_1256_);
v___x_1299_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1300_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1299_);
lean_dec_ref(v___x_1300_);
goto v___jp_1296_;
v___jp_1296_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_io_error_to_string(v_a_1295_);
v___x_1298_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1297_);
lean_dec_ref(v___x_1298_);
goto v___jp_1032_;
}
}
}
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1302_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1301_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1304_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc_n(v_a_1303_, 2);
lean_dec_ref(v___x_1302_);
v___x_1304_ = lean_load_dynlib(v_a_1303_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1343_; 
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v___x_1304_, 0);
lean_dec(v_unused_1344_);
v___x_1306_ = v___x_1304_;
v_isShared_1307_ = v_isSharedCheck_1343_;
goto v_resetjp_1305_;
}
else
{
lean_dec(v___x_1304_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1343_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v_leanOpts_1308_; lean_object* v_forwardedArgs_1309_; uint8_t v_component_1310_; uint8_t v_printPrefix_1311_; uint8_t v_printLibDir_1312_; uint8_t v_useStdin_1313_; uint8_t v_onlyDeps_1314_; uint8_t v_onlySrcDeps_1315_; uint8_t v_depsJson_1316_; lean_object* v_opts_1317_; uint32_t v_trustLevel_1318_; uint32_t v_numThreads_1319_; lean_object* v_rootDir_x3f_1320_; lean_object* v_setupFileName_x3f_1321_; lean_object* v_oleanFileName_x3f_1322_; lean_object* v_ileanFileName_x3f_1323_; lean_object* v_cFileName_x3f_1324_; lean_object* v_bcFileName_x3f_1325_; uint8_t v_jsonOutput_1326_; lean_object* v_errorOnKinds_1327_; uint8_t v_printStats_1328_; uint8_t v_run_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1342_; 
v_leanOpts_1308_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1309_ = lean_ctor_get(v_opts_938_, 1);
v_component_1310_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1311_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1312_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1313_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1314_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1315_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1316_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1317_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1318_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1319_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1320_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1321_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1322_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1323_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1324_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1325_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1326_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1327_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1328_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1329_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1331_ = v_opts_938_;
v_isShared_1332_ = v_isSharedCheck_1342_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_errorOnKinds_1327_);
lean_inc(v_bcFileName_x3f_1325_);
lean_inc(v_cFileName_x3f_1324_);
lean_inc(v_ileanFileName_x3f_1323_);
lean_inc(v_oleanFileName_x3f_1322_);
lean_inc(v_setupFileName_x3f_1321_);
lean_inc(v_rootDir_x3f_1320_);
lean_inc(v_opts_1317_);
lean_inc(v_forwardedArgs_1309_);
lean_inc(v_leanOpts_1308_);
lean_dec(v_opts_938_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1342_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1333_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1334_ = lean_string_append(v___x_1333_, v_a_1303_);
lean_dec(v_a_1303_);
v___x_1335_ = lean_array_push(v_forwardedArgs_1309_, v___x_1334_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v___x_1335_);
v___x_1337_ = v___x_1331_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_leanOpts_1308_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_opts_1317_);
lean_ctor_set(v_reuseFailAlloc_1341_, 3, v_rootDir_x3f_1320_);
lean_ctor_set(v_reuseFailAlloc_1341_, 4, v_setupFileName_x3f_1321_);
lean_ctor_set(v_reuseFailAlloc_1341_, 5, v_oleanFileName_x3f_1322_);
lean_ctor_set(v_reuseFailAlloc_1341_, 6, v_ileanFileName_x3f_1323_);
lean_ctor_set(v_reuseFailAlloc_1341_, 7, v_cFileName_x3f_1324_);
lean_ctor_set(v_reuseFailAlloc_1341_, 8, v_bcFileName_x3f_1325_);
lean_ctor_set(v_reuseFailAlloc_1341_, 9, v_errorOnKinds_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*10 + 8, v_component_1310_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*10 + 9, v_printPrefix_1311_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*10 + 10, v_printLibDir_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*10 + 11, v_useStdin_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*10 + 12, v_onlyDeps_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*10 + 13, v_onlySrcDeps_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*10 + 14, v_depsJson_1316_);
lean_ctor_set_uint32(v_reuseFailAlloc_1341_, sizeof(void*)*10, v_trustLevel_1318_);
lean_ctor_set_uint32(v_reuseFailAlloc_1341_, sizeof(void*)*10 + 4, v_numThreads_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*10 + 15, v_jsonOutput_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*10 + 16, v_printStats_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*10 + 17, v_run_1329_);
v___x_1337_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1339_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1337_);
v___x_1339_ = v___x_1306_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v_a_1303_);
lean_dec_ref(v_opts_938_);
v_a_1345_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1345_);
lean_dec_ref(v___x_1304_);
v___x_1349_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1350_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1349_);
lean_dec_ref(v___x_1350_);
goto v___jp_1346_;
v___jp_1346_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_io_error_to_string(v_a_1345_);
v___x_1348_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1347_);
lean_dec_ref(v___x_1348_);
goto v___jp_1072_;
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec_ref(v_opts_938_);
v_a_1351_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1351_);
lean_dec_ref(v___x_1302_);
v___x_1355_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1356_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1355_);
lean_dec_ref(v___x_1356_);
goto v___jp_1352_;
v___jp_1352_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_io_error_to_string(v_a_1351_);
v___x_1354_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1353_);
lean_dec_ref(v___x_1354_);
goto v___jp_1026_;
}
}
}
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1358_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1357_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1360_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc_n(v_a_1359_, 2);
lean_dec_ref(v___x_1358_);
v___x_1360_ = lean_load_plugin(v_a_1359_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1399_; 
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v___x_1360_, 0);
lean_dec(v_unused_1400_);
v___x_1362_ = v___x_1360_;
v_isShared_1363_ = v_isSharedCheck_1399_;
goto v_resetjp_1361_;
}
else
{
lean_dec(v___x_1360_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1399_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v_leanOpts_1364_; lean_object* v_forwardedArgs_1365_; uint8_t v_component_1366_; uint8_t v_printPrefix_1367_; uint8_t v_printLibDir_1368_; uint8_t v_useStdin_1369_; uint8_t v_onlyDeps_1370_; uint8_t v_onlySrcDeps_1371_; uint8_t v_depsJson_1372_; lean_object* v_opts_1373_; uint32_t v_trustLevel_1374_; uint32_t v_numThreads_1375_; lean_object* v_rootDir_x3f_1376_; lean_object* v_setupFileName_x3f_1377_; lean_object* v_oleanFileName_x3f_1378_; lean_object* v_ileanFileName_x3f_1379_; lean_object* v_cFileName_x3f_1380_; lean_object* v_bcFileName_x3f_1381_; uint8_t v_jsonOutput_1382_; lean_object* v_errorOnKinds_1383_; uint8_t v_printStats_1384_; uint8_t v_run_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1398_; 
v_leanOpts_1364_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1365_ = lean_ctor_get(v_opts_938_, 1);
v_component_1366_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1367_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1368_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1369_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1370_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1371_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1372_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1373_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1374_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1375_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1376_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1377_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1378_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1379_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1380_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1381_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1382_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1383_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1384_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1385_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1387_ = v_opts_938_;
v_isShared_1388_ = v_isSharedCheck_1398_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_errorOnKinds_1383_);
lean_inc(v_bcFileName_x3f_1381_);
lean_inc(v_cFileName_x3f_1380_);
lean_inc(v_ileanFileName_x3f_1379_);
lean_inc(v_oleanFileName_x3f_1378_);
lean_inc(v_setupFileName_x3f_1377_);
lean_inc(v_rootDir_x3f_1376_);
lean_inc(v_opts_1373_);
lean_inc(v_forwardedArgs_1365_);
lean_inc(v_leanOpts_1364_);
lean_dec(v_opts_938_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1398_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1389_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1390_ = lean_string_append(v___x_1389_, v_a_1359_);
lean_dec(v_a_1359_);
v___x_1391_ = lean_array_push(v_forwardedArgs_1365_, v___x_1390_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v___x_1391_);
v___x_1393_ = v___x_1387_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_leanOpts_1364_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_opts_1373_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_rootDir_x3f_1376_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_setupFileName_x3f_1377_);
lean_ctor_set(v_reuseFailAlloc_1397_, 5, v_oleanFileName_x3f_1378_);
lean_ctor_set(v_reuseFailAlloc_1397_, 6, v_ileanFileName_x3f_1379_);
lean_ctor_set(v_reuseFailAlloc_1397_, 7, v_cFileName_x3f_1380_);
lean_ctor_set(v_reuseFailAlloc_1397_, 8, v_bcFileName_x3f_1381_);
lean_ctor_set(v_reuseFailAlloc_1397_, 9, v_errorOnKinds_1383_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*10 + 8, v_component_1366_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*10 + 9, v_printPrefix_1367_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*10 + 10, v_printLibDir_1368_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*10 + 11, v_useStdin_1369_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*10 + 12, v_onlyDeps_1370_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*10 + 13, v_onlySrcDeps_1371_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*10 + 14, v_depsJson_1372_);
lean_ctor_set_uint32(v_reuseFailAlloc_1397_, sizeof(void*)*10, v_trustLevel_1374_);
lean_ctor_set_uint32(v_reuseFailAlloc_1397_, sizeof(void*)*10 + 4, v_numThreads_1375_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*10 + 15, v_jsonOutput_1382_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*10 + 16, v_printStats_1384_);
lean_ctor_set_uint8(v_reuseFailAlloc_1397_, sizeof(void*)*10 + 17, v_run_1385_);
v___x_1393_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1395_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1393_);
v___x_1395_ = v___x_1362_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec(v_a_1359_);
lean_dec_ref(v_opts_938_);
v_a_1401_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1401_);
lean_dec_ref(v___x_1360_);
v___x_1405_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1406_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1405_);
lean_dec_ref(v___x_1406_);
goto v___jp_1402_;
v___jp_1402_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_io_error_to_string(v_a_1401_);
v___x_1404_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1403_);
lean_dec_ref(v___x_1404_);
goto v___jp_1078_;
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec_ref(v_opts_938_);
v_a_1407_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1407_);
lean_dec_ref(v___x_1358_);
v___x_1411_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1412_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1411_);
lean_dec_ref(v___x_1412_);
goto v___jp_1408_;
v___jp_1408_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_io_error_to_string(v_a_1407_);
v___x_1410_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1409_);
lean_dec_ref(v___x_1410_);
goto v___jp_1020_;
}
}
}
}
else
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__12, &l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12);
if (v___x_1413_ == 0)
{
lean_dec(v_optArg_x3f_940_);
lean_dec_ref(v_opts_938_);
goto v___jp_1060_;
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1415_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1414_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = lean_internal_enable_debug(v_a_1416_);
lean_dec(v_a_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v_opts_938_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_opts_938_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec_ref(v_opts_938_);
v_a_1425_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1425_);
lean_dec_ref(v___x_1415_);
v___x_1429_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1430_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1429_);
lean_dec_ref(v___x_1430_);
goto v___jp_1426_;
v___jp_1426_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_io_error_to_string(v_a_1425_);
v___x_1428_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1427_);
lean_dec_ref(v___x_1428_);
goto v___jp_1084_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1431_; lean_object* v_forwardedArgs_1432_; uint8_t v_component_1433_; uint8_t v_printPrefix_1434_; uint8_t v_printLibDir_1435_; uint8_t v_useStdin_1436_; uint8_t v_onlyDeps_1437_; uint8_t v_onlySrcDeps_1438_; uint8_t v_depsJson_1439_; lean_object* v_opts_1440_; uint32_t v_trustLevel_1441_; uint32_t v_numThreads_1442_; lean_object* v_rootDir_x3f_1443_; lean_object* v_setupFileName_x3f_1444_; lean_object* v_oleanFileName_x3f_1445_; lean_object* v_ileanFileName_x3f_1446_; lean_object* v_cFileName_x3f_1447_; lean_object* v_bcFileName_x3f_1448_; uint8_t v_jsonOutput_1449_; lean_object* v_errorOnKinds_1450_; uint8_t v_printStats_1451_; uint8_t v_run_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_optArg_x3f_940_);
v_leanOpts_1431_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1432_ = lean_ctor_get(v_opts_938_, 1);
v_component_1433_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1434_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1435_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1436_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1437_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1438_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1439_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1440_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1441_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1442_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1443_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1444_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1445_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1446_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1447_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1448_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1449_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1450_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1451_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1452_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1454_ = v_opts_938_;
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_errorOnKinds_1450_);
lean_inc(v_bcFileName_x3f_1448_);
lean_inc(v_cFileName_x3f_1447_);
lean_inc(v_ileanFileName_x3f_1446_);
lean_inc(v_oleanFileName_x3f_1445_);
lean_inc(v_setupFileName_x3f_1444_);
lean_inc(v_rootDir_x3f_1443_);
lean_inc(v_opts_1440_);
lean_inc(v_forwardedArgs_1432_);
lean_inc(v_leanOpts_1431_);
lean_dec(v_opts_938_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1456_ = l_Lean_profiler;
v___x_1457_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1431_, v___x_1456_, v___x_1197_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1457_);
v___x_1459_ = v___x_1454_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_forwardedArgs_1432_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_opts_1440_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_rootDir_x3f_1443_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_setupFileName_x3f_1444_);
lean_ctor_set(v_reuseFailAlloc_1461_, 5, v_oleanFileName_x3f_1445_);
lean_ctor_set(v_reuseFailAlloc_1461_, 6, v_ileanFileName_x3f_1446_);
lean_ctor_set(v_reuseFailAlloc_1461_, 7, v_cFileName_x3f_1447_);
lean_ctor_set(v_reuseFailAlloc_1461_, 8, v_bcFileName_x3f_1448_);
lean_ctor_set(v_reuseFailAlloc_1461_, 9, v_errorOnKinds_1450_);
lean_ctor_set_uint8(v_reuseFailAlloc_1461_, sizeof(void*)*10 + 8, v_component_1433_);
lean_ctor_set_uint8(v_reuseFailAlloc_1461_, sizeof(void*)*10 + 9, v_printPrefix_1434_);
lean_ctor_set_uint8(v_reuseFailAlloc_1461_, sizeof(void*)*10 + 10, v_printLibDir_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1461_, sizeof(void*)*10 + 11, v_useStdin_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1461_, sizeof(void*)*10 + 12, v_onlyDeps_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1461_, sizeof(void*)*10 + 13, v_onlySrcDeps_1438_);
lean_ctor_set_uint8(v_reuseFailAlloc_1461_, sizeof(void*)*10 + 14, v_depsJson_1439_);
lean_ctor_set_uint32(v_reuseFailAlloc_1461_, sizeof(void*)*10, v_trustLevel_1441_);
lean_ctor_set_uint32(v_reuseFailAlloc_1461_, sizeof(void*)*10 + 4, v_numThreads_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1461_, sizeof(void*)*10 + 15, v_jsonOutput_1449_);
lean_ctor_set_uint8(v_reuseFailAlloc_1461_, sizeof(void*)*10 + 16, v_printStats_1451_);
lean_ctor_set_uint8(v_reuseFailAlloc_1461_, sizeof(void*)*10 + 17, v_run_1452_);
v___x_1459_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_leanOpts_1463_; lean_object* v_forwardedArgs_1464_; uint8_t v_printPrefix_1465_; uint8_t v_printLibDir_1466_; uint8_t v_useStdin_1467_; uint8_t v_onlyDeps_1468_; uint8_t v_onlySrcDeps_1469_; uint8_t v_depsJson_1470_; lean_object* v_opts_1471_; uint32_t v_trustLevel_1472_; uint32_t v_numThreads_1473_; lean_object* v_rootDir_x3f_1474_; lean_object* v_setupFileName_x3f_1475_; lean_object* v_oleanFileName_x3f_1476_; lean_object* v_ileanFileName_x3f_1477_; lean_object* v_cFileName_x3f_1478_; lean_object* v_bcFileName_x3f_1479_; uint8_t v_jsonOutput_1480_; lean_object* v_errorOnKinds_1481_; uint8_t v_printStats_1482_; uint8_t v_run_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_optArg_x3f_940_);
v_leanOpts_1463_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1464_ = lean_ctor_get(v_opts_938_, 1);
v_printPrefix_1465_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1466_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1467_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1468_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1469_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1470_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1471_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1472_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1473_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1474_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1475_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1476_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1477_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1478_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1479_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1480_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1481_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1482_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1483_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1485_ = v_opts_938_;
v_isShared_1486_ = v_isSharedCheck_1492_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_errorOnKinds_1481_);
lean_inc(v_bcFileName_x3f_1479_);
lean_inc(v_cFileName_x3f_1478_);
lean_inc(v_ileanFileName_x3f_1477_);
lean_inc(v_oleanFileName_x3f_1476_);
lean_inc(v_setupFileName_x3f_1475_);
lean_inc(v_rootDir_x3f_1474_);
lean_inc(v_opts_1471_);
lean_inc(v_forwardedArgs_1464_);
lean_inc(v_leanOpts_1463_);
lean_dec(v_opts_938_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1492_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
uint8_t v___x_1487_; lean_object* v___x_1489_; 
v___x_1487_ = 2;
if (v_isShared_1486_ == 0)
{
v___x_1489_ = v___x_1485_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_leanOpts_1463_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_forwardedArgs_1464_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_opts_1471_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_rootDir_x3f_1474_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v_setupFileName_x3f_1475_);
lean_ctor_set(v_reuseFailAlloc_1491_, 5, v_oleanFileName_x3f_1476_);
lean_ctor_set(v_reuseFailAlloc_1491_, 6, v_ileanFileName_x3f_1477_);
lean_ctor_set(v_reuseFailAlloc_1491_, 7, v_cFileName_x3f_1478_);
lean_ctor_set(v_reuseFailAlloc_1491_, 8, v_bcFileName_x3f_1479_);
lean_ctor_set(v_reuseFailAlloc_1491_, 9, v_errorOnKinds_1481_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*10 + 9, v_printPrefix_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*10 + 10, v_printLibDir_1466_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*10 + 11, v_useStdin_1467_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*10 + 12, v_onlyDeps_1468_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*10 + 13, v_onlySrcDeps_1469_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*10 + 14, v_depsJson_1470_);
lean_ctor_set_uint32(v_reuseFailAlloc_1491_, sizeof(void*)*10, v_trustLevel_1472_);
lean_ctor_set_uint32(v_reuseFailAlloc_1491_, sizeof(void*)*10 + 4, v_numThreads_1473_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*10 + 15, v_jsonOutput_1480_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*10 + 16, v_printStats_1482_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*10 + 17, v_run_1483_);
v___x_1489_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1490_; 
lean_ctor_set_uint8(v___x_1489_, sizeof(void*)*10 + 8, v___x_1487_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
}
}
}
else
{
lean_object* v_leanOpts_1493_; lean_object* v_forwardedArgs_1494_; uint8_t v_printPrefix_1495_; uint8_t v_printLibDir_1496_; uint8_t v_useStdin_1497_; uint8_t v_onlyDeps_1498_; uint8_t v_onlySrcDeps_1499_; uint8_t v_depsJson_1500_; lean_object* v_opts_1501_; uint32_t v_trustLevel_1502_; uint32_t v_numThreads_1503_; lean_object* v_rootDir_x3f_1504_; lean_object* v_setupFileName_x3f_1505_; lean_object* v_oleanFileName_x3f_1506_; lean_object* v_ileanFileName_x3f_1507_; lean_object* v_cFileName_x3f_1508_; lean_object* v_bcFileName_x3f_1509_; uint8_t v_jsonOutput_1510_; lean_object* v_errorOnKinds_1511_; uint8_t v_printStats_1512_; uint8_t v_run_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1522_; 
lean_dec(v_optArg_x3f_940_);
v_leanOpts_1493_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1494_ = lean_ctor_get(v_opts_938_, 1);
v_printPrefix_1495_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1496_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1497_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1498_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1499_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1500_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1501_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1502_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1503_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1504_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1505_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1506_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1507_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1508_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1509_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1510_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1511_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1512_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1513_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1515_ = v_opts_938_;
v_isShared_1516_ = v_isSharedCheck_1522_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_errorOnKinds_1511_);
lean_inc(v_bcFileName_x3f_1509_);
lean_inc(v_cFileName_x3f_1508_);
lean_inc(v_ileanFileName_x3f_1507_);
lean_inc(v_oleanFileName_x3f_1506_);
lean_inc(v_setupFileName_x3f_1505_);
lean_inc(v_rootDir_x3f_1504_);
lean_inc(v_opts_1501_);
lean_inc(v_forwardedArgs_1494_);
lean_inc(v_leanOpts_1493_);
lean_dec(v_opts_938_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1522_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
uint8_t v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = 1;
if (v_isShared_1516_ == 0)
{
v___x_1519_ = v___x_1515_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_leanOpts_1493_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_forwardedArgs_1494_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_opts_1501_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_rootDir_x3f_1504_);
lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_setupFileName_x3f_1505_);
lean_ctor_set(v_reuseFailAlloc_1521_, 5, v_oleanFileName_x3f_1506_);
lean_ctor_set(v_reuseFailAlloc_1521_, 6, v_ileanFileName_x3f_1507_);
lean_ctor_set(v_reuseFailAlloc_1521_, 7, v_cFileName_x3f_1508_);
lean_ctor_set(v_reuseFailAlloc_1521_, 8, v_bcFileName_x3f_1509_);
lean_ctor_set(v_reuseFailAlloc_1521_, 9, v_errorOnKinds_1511_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*10 + 9, v_printPrefix_1495_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*10 + 10, v_printLibDir_1496_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*10 + 11, v_useStdin_1497_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*10 + 12, v_onlyDeps_1498_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*10 + 13, v_onlySrcDeps_1499_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*10 + 14, v_depsJson_1500_);
lean_ctor_set_uint32(v_reuseFailAlloc_1521_, sizeof(void*)*10, v_trustLevel_1502_);
lean_ctor_set_uint32(v_reuseFailAlloc_1521_, sizeof(void*)*10 + 4, v_numThreads_1503_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*10 + 15, v_jsonOutput_1510_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*10 + 16, v_printStats_1512_);
lean_ctor_set_uint8(v_reuseFailAlloc_1521_, sizeof(void*)*10 + 17, v_run_1513_);
v___x_1519_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; 
lean_ctor_set_uint8(v___x_1519_, sizeof(void*)*10 + 8, v___x_1517_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
}
}
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1524_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1523_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v_leanOpts_1526_; lean_object* v_forwardedArgs_1527_; uint8_t v_component_1528_; uint8_t v_printPrefix_1529_; uint8_t v_printLibDir_1530_; uint8_t v_useStdin_1531_; uint8_t v_onlyDeps_1532_; uint8_t v_onlySrcDeps_1533_; uint8_t v_depsJson_1534_; lean_object* v_opts_1535_; uint32_t v_trustLevel_1536_; uint32_t v_numThreads_1537_; lean_object* v_rootDir_x3f_1538_; lean_object* v_setupFileName_x3f_1539_; lean_object* v_oleanFileName_x3f_1540_; lean_object* v_ileanFileName_x3f_1541_; lean_object* v_cFileName_x3f_1542_; lean_object* v_bcFileName_x3f_1543_; uint8_t v_jsonOutput_1544_; lean_object* v_errorOnKinds_1545_; uint8_t v_printStats_1546_; uint8_t v_run_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1572_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref(v___x_1524_);
v_leanOpts_1526_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1527_ = lean_ctor_get(v_opts_938_, 1);
v_component_1528_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1529_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1530_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1531_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1532_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1533_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1534_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1535_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1536_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1537_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1538_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1539_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1540_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1541_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1542_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1543_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1544_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1545_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1546_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1547_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1549_ = v_opts_938_;
v_isShared_1550_ = v_isSharedCheck_1572_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_errorOnKinds_1545_);
lean_inc(v_bcFileName_x3f_1543_);
lean_inc(v_cFileName_x3f_1542_);
lean_inc(v_ileanFileName_x3f_1541_);
lean_inc(v_oleanFileName_x3f_1540_);
lean_inc(v_setupFileName_x3f_1539_);
lean_inc(v_rootDir_x3f_1538_);
lean_inc(v_opts_1535_);
lean_inc(v_forwardedArgs_1527_);
lean_inc(v_leanOpts_1526_);
lean_dec(v_opts_938_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1572_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; 
lean_inc(v_a_1525_);
v___x_1551_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1526_, v_a_1525_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1565_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1565_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1565_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1556_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1557_ = lean_string_append(v___x_1556_, v_a_1525_);
lean_dec(v_a_1525_);
v___x_1558_ = lean_array_push(v_forwardedArgs_1527_, v___x_1557_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 1, v___x_1558_);
lean_ctor_set(v___x_1549_, 0, v_a_1552_);
v___x_1560_ = v___x_1549_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1552_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_opts_1535_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_rootDir_x3f_1538_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v_setupFileName_x3f_1539_);
lean_ctor_set(v_reuseFailAlloc_1564_, 5, v_oleanFileName_x3f_1540_);
lean_ctor_set(v_reuseFailAlloc_1564_, 6, v_ileanFileName_x3f_1541_);
lean_ctor_set(v_reuseFailAlloc_1564_, 7, v_cFileName_x3f_1542_);
lean_ctor_set(v_reuseFailAlloc_1564_, 8, v_bcFileName_x3f_1543_);
lean_ctor_set(v_reuseFailAlloc_1564_, 9, v_errorOnKinds_1545_);
lean_ctor_set_uint8(v_reuseFailAlloc_1564_, sizeof(void*)*10 + 8, v_component_1528_);
lean_ctor_set_uint8(v_reuseFailAlloc_1564_, sizeof(void*)*10 + 9, v_printPrefix_1529_);
lean_ctor_set_uint8(v_reuseFailAlloc_1564_, sizeof(void*)*10 + 10, v_printLibDir_1530_);
lean_ctor_set_uint8(v_reuseFailAlloc_1564_, sizeof(void*)*10 + 11, v_useStdin_1531_);
lean_ctor_set_uint8(v_reuseFailAlloc_1564_, sizeof(void*)*10 + 12, v_onlyDeps_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1564_, sizeof(void*)*10 + 13, v_onlySrcDeps_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1564_, sizeof(void*)*10 + 14, v_depsJson_1534_);
lean_ctor_set_uint32(v_reuseFailAlloc_1564_, sizeof(void*)*10, v_trustLevel_1536_);
lean_ctor_set_uint32(v_reuseFailAlloc_1564_, sizeof(void*)*10 + 4, v_numThreads_1537_);
lean_ctor_set_uint8(v_reuseFailAlloc_1564_, sizeof(void*)*10 + 15, v_jsonOutput_1544_);
lean_ctor_set_uint8(v_reuseFailAlloc_1564_, sizeof(void*)*10 + 16, v_printStats_1546_);
lean_ctor_set_uint8(v_reuseFailAlloc_1564_, sizeof(void*)*10 + 17, v_run_1547_);
v___x_1560_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1562_; 
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1560_);
v___x_1562_ = v___x_1554_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_del_object(v___x_1549_);
lean_dec_ref(v_errorOnKinds_1545_);
lean_dec(v_bcFileName_x3f_1543_);
lean_dec(v_cFileName_x3f_1542_);
lean_dec(v_ileanFileName_x3f_1541_);
lean_dec(v_oleanFileName_x3f_1540_);
lean_dec(v_setupFileName_x3f_1539_);
lean_dec(v_rootDir_x3f_1538_);
lean_dec_ref(v_opts_1535_);
lean_dec_ref(v_forwardedArgs_1527_);
lean_dec(v_a_1525_);
v_a_1566_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v___x_1551_);
v___x_1570_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1571_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1570_);
lean_dec_ref(v___x_1571_);
goto v___jp_1567_;
v___jp_1567_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_io_error_to_string(v_a_1566_);
v___x_1569_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1568_);
lean_dec_ref(v___x_1569_);
goto v___jp_1014_;
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec_ref(v_opts_938_);
v_a_1573_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1573_);
lean_dec_ref(v___x_1524_);
v___x_1577_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1578_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1577_);
lean_dec_ref(v___x_1578_);
goto v___jp_1574_;
v___jp_1574_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_io_error_to_string(v_a_1573_);
v___x_1576_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1575_);
lean_dec_ref(v___x_1576_);
goto v___jp_1090_;
}
}
}
}
else
{
lean_object* v_leanOpts_1579_; lean_object* v_forwardedArgs_1580_; uint8_t v_component_1581_; uint8_t v_printPrefix_1582_; uint8_t v_useStdin_1583_; uint8_t v_onlyDeps_1584_; uint8_t v_onlySrcDeps_1585_; uint8_t v_depsJson_1586_; lean_object* v_opts_1587_; uint32_t v_trustLevel_1588_; uint32_t v_numThreads_1589_; lean_object* v_rootDir_x3f_1590_; lean_object* v_setupFileName_x3f_1591_; lean_object* v_oleanFileName_x3f_1592_; lean_object* v_ileanFileName_x3f_1593_; lean_object* v_cFileName_x3f_1594_; lean_object* v_bcFileName_x3f_1595_; uint8_t v_jsonOutput_1596_; lean_object* v_errorOnKinds_1597_; uint8_t v_printStats_1598_; uint8_t v_run_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_optArg_x3f_940_);
v_leanOpts_1579_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1580_ = lean_ctor_get(v_opts_938_, 1);
v_component_1581_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1582_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_useStdin_1583_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1584_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1585_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1586_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1587_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1588_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1589_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1590_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1591_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1592_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1593_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1594_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1595_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1596_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1597_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1598_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1599_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1601_ = v_opts_938_;
v_isShared_1602_ = v_isSharedCheck_1607_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_errorOnKinds_1597_);
lean_inc(v_bcFileName_x3f_1595_);
lean_inc(v_cFileName_x3f_1594_);
lean_inc(v_ileanFileName_x3f_1593_);
lean_inc(v_oleanFileName_x3f_1592_);
lean_inc(v_setupFileName_x3f_1591_);
lean_inc(v_rootDir_x3f_1590_);
lean_inc(v_opts_1587_);
lean_inc(v_forwardedArgs_1580_);
lean_inc(v_leanOpts_1579_);
lean_dec(v_opts_938_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1607_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_leanOpts_1579_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_forwardedArgs_1580_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_opts_1587_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_rootDir_x3f_1590_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v_setupFileName_x3f_1591_);
lean_ctor_set(v_reuseFailAlloc_1606_, 5, v_oleanFileName_x3f_1592_);
lean_ctor_set(v_reuseFailAlloc_1606_, 6, v_ileanFileName_x3f_1593_);
lean_ctor_set(v_reuseFailAlloc_1606_, 7, v_cFileName_x3f_1594_);
lean_ctor_set(v_reuseFailAlloc_1606_, 8, v_bcFileName_x3f_1595_);
lean_ctor_set(v_reuseFailAlloc_1606_, 9, v_errorOnKinds_1597_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*10 + 8, v_component_1581_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*10 + 9, v_printPrefix_1582_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*10 + 11, v_useStdin_1583_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*10 + 12, v_onlyDeps_1584_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*10 + 13, v_onlySrcDeps_1585_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*10 + 14, v_depsJson_1586_);
lean_ctor_set_uint32(v_reuseFailAlloc_1606_, sizeof(void*)*10, v_trustLevel_1588_);
lean_ctor_set_uint32(v_reuseFailAlloc_1606_, sizeof(void*)*10 + 4, v_numThreads_1589_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*10 + 15, v_jsonOutput_1596_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*10 + 16, v_printStats_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*10 + 17, v_run_1599_);
v___x_1604_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; 
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*10 + 10, v___x_1189_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
}
}
}
else
{
lean_object* v_leanOpts_1608_; lean_object* v_forwardedArgs_1609_; uint8_t v_component_1610_; uint8_t v_printLibDir_1611_; uint8_t v_useStdin_1612_; uint8_t v_onlyDeps_1613_; uint8_t v_onlySrcDeps_1614_; uint8_t v_depsJson_1615_; lean_object* v_opts_1616_; uint32_t v_trustLevel_1617_; uint32_t v_numThreads_1618_; lean_object* v_rootDir_x3f_1619_; lean_object* v_setupFileName_x3f_1620_; lean_object* v_oleanFileName_x3f_1621_; lean_object* v_ileanFileName_x3f_1622_; lean_object* v_cFileName_x3f_1623_; lean_object* v_bcFileName_x3f_1624_; uint8_t v_jsonOutput_1625_; lean_object* v_errorOnKinds_1626_; uint8_t v_printStats_1627_; uint8_t v_run_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1636_; 
lean_dec(v_optArg_x3f_940_);
v_leanOpts_1608_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1609_ = lean_ctor_get(v_opts_938_, 1);
v_component_1610_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printLibDir_1611_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1612_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1613_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1614_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1615_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1616_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1617_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1618_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1619_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1620_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1621_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1622_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1623_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1624_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1625_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1626_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1627_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1628_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1636_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1630_ = v_opts_938_;
v_isShared_1631_ = v_isSharedCheck_1636_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_errorOnKinds_1626_);
lean_inc(v_bcFileName_x3f_1624_);
lean_inc(v_cFileName_x3f_1623_);
lean_inc(v_ileanFileName_x3f_1622_);
lean_inc(v_oleanFileName_x3f_1621_);
lean_inc(v_setupFileName_x3f_1620_);
lean_inc(v_rootDir_x3f_1619_);
lean_inc(v_opts_1616_);
lean_inc(v_forwardedArgs_1609_);
lean_inc(v_leanOpts_1608_);
lean_dec(v_opts_938_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1636_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_leanOpts_1608_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_forwardedArgs_1609_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_opts_1616_);
lean_ctor_set(v_reuseFailAlloc_1635_, 3, v_rootDir_x3f_1619_);
lean_ctor_set(v_reuseFailAlloc_1635_, 4, v_setupFileName_x3f_1620_);
lean_ctor_set(v_reuseFailAlloc_1635_, 5, v_oleanFileName_x3f_1621_);
lean_ctor_set(v_reuseFailAlloc_1635_, 6, v_ileanFileName_x3f_1622_);
lean_ctor_set(v_reuseFailAlloc_1635_, 7, v_cFileName_x3f_1623_);
lean_ctor_set(v_reuseFailAlloc_1635_, 8, v_bcFileName_x3f_1624_);
lean_ctor_set(v_reuseFailAlloc_1635_, 9, v_errorOnKinds_1626_);
lean_ctor_set_uint8(v_reuseFailAlloc_1635_, sizeof(void*)*10 + 8, v_component_1610_);
lean_ctor_set_uint8(v_reuseFailAlloc_1635_, sizeof(void*)*10 + 10, v_printLibDir_1611_);
lean_ctor_set_uint8(v_reuseFailAlloc_1635_, sizeof(void*)*10 + 11, v_useStdin_1612_);
lean_ctor_set_uint8(v_reuseFailAlloc_1635_, sizeof(void*)*10 + 12, v_onlyDeps_1613_);
lean_ctor_set_uint8(v_reuseFailAlloc_1635_, sizeof(void*)*10 + 13, v_onlySrcDeps_1614_);
lean_ctor_set_uint8(v_reuseFailAlloc_1635_, sizeof(void*)*10 + 14, v_depsJson_1615_);
lean_ctor_set_uint32(v_reuseFailAlloc_1635_, sizeof(void*)*10, v_trustLevel_1617_);
lean_ctor_set_uint32(v_reuseFailAlloc_1635_, sizeof(void*)*10 + 4, v_numThreads_1618_);
lean_ctor_set_uint8(v_reuseFailAlloc_1635_, sizeof(void*)*10 + 15, v_jsonOutput_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1635_, sizeof(void*)*10 + 16, v_printStats_1627_);
lean_ctor_set_uint8(v_reuseFailAlloc_1635_, sizeof(void*)*10 + 17, v_run_1628_);
v___x_1633_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1634_; 
lean_ctor_set_uint8(v___x_1633_, sizeof(void*)*10 + 9, v___x_1187_);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
return v___x_1634_;
}
}
}
}
else
{
lean_object* v_leanOpts_1637_; lean_object* v_forwardedArgs_1638_; uint8_t v_component_1639_; uint8_t v_printPrefix_1640_; uint8_t v_printLibDir_1641_; uint8_t v_useStdin_1642_; uint8_t v_onlyDeps_1643_; uint8_t v_onlySrcDeps_1644_; uint8_t v_depsJson_1645_; lean_object* v_opts_1646_; uint32_t v_trustLevel_1647_; uint32_t v_numThreads_1648_; lean_object* v_rootDir_x3f_1649_; lean_object* v_setupFileName_x3f_1650_; lean_object* v_oleanFileName_x3f_1651_; lean_object* v_ileanFileName_x3f_1652_; lean_object* v_cFileName_x3f_1653_; lean_object* v_bcFileName_x3f_1654_; uint8_t v_jsonOutput_1655_; lean_object* v_errorOnKinds_1656_; uint8_t v_run_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v_optArg_x3f_940_);
v_leanOpts_1637_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1638_ = lean_ctor_get(v_opts_938_, 1);
v_component_1639_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1640_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1641_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1642_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1643_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1644_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1645_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1646_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1647_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1648_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1649_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1650_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1651_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1652_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1653_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1654_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1655_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1656_ = lean_ctor_get(v_opts_938_, 9);
v_run_1657_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1659_ = v_opts_938_;
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_errorOnKinds_1656_);
lean_inc(v_bcFileName_x3f_1654_);
lean_inc(v_cFileName_x3f_1653_);
lean_inc(v_ileanFileName_x3f_1652_);
lean_inc(v_oleanFileName_x3f_1651_);
lean_inc(v_setupFileName_x3f_1650_);
lean_inc(v_rootDir_x3f_1649_);
lean_inc(v_opts_1646_);
lean_inc(v_forwardedArgs_1638_);
lean_inc(v_leanOpts_1637_);
lean_dec(v_opts_938_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_leanOpts_1637_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_forwardedArgs_1638_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_opts_1646_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_rootDir_x3f_1649_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v_setupFileName_x3f_1650_);
lean_ctor_set(v_reuseFailAlloc_1664_, 5, v_oleanFileName_x3f_1651_);
lean_ctor_set(v_reuseFailAlloc_1664_, 6, v_ileanFileName_x3f_1652_);
lean_ctor_set(v_reuseFailAlloc_1664_, 7, v_cFileName_x3f_1653_);
lean_ctor_set(v_reuseFailAlloc_1664_, 8, v_bcFileName_x3f_1654_);
lean_ctor_set(v_reuseFailAlloc_1664_, 9, v_errorOnKinds_1656_);
lean_ctor_set_uint8(v_reuseFailAlloc_1664_, sizeof(void*)*10 + 8, v_component_1639_);
lean_ctor_set_uint8(v_reuseFailAlloc_1664_, sizeof(void*)*10 + 9, v_printPrefix_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1664_, sizeof(void*)*10 + 10, v_printLibDir_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1664_, sizeof(void*)*10 + 11, v_useStdin_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1664_, sizeof(void*)*10 + 12, v_onlyDeps_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1664_, sizeof(void*)*10 + 13, v_onlySrcDeps_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1664_, sizeof(void*)*10 + 14, v_depsJson_1645_);
lean_ctor_set_uint32(v_reuseFailAlloc_1664_, sizeof(void*)*10, v_trustLevel_1647_);
lean_ctor_set_uint32(v_reuseFailAlloc_1664_, sizeof(void*)*10 + 4, v_numThreads_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1664_, sizeof(void*)*10 + 15, v_jsonOutput_1655_);
lean_ctor_set_uint8(v_reuseFailAlloc_1664_, sizeof(void*)*10 + 17, v_run_1657_);
v___x_1662_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; 
lean_ctor_set_uint8(v___x_1662_, sizeof(void*)*10 + 16, v___x_1185_);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
}
}
}
else
{
lean_object* v_leanOpts_1666_; lean_object* v_forwardedArgs_1667_; uint8_t v_component_1668_; uint8_t v_printPrefix_1669_; uint8_t v_printLibDir_1670_; uint8_t v_useStdin_1671_; uint8_t v_onlyDeps_1672_; uint8_t v_onlySrcDeps_1673_; uint8_t v_depsJson_1674_; lean_object* v_opts_1675_; uint32_t v_trustLevel_1676_; uint32_t v_numThreads_1677_; lean_object* v_rootDir_x3f_1678_; lean_object* v_setupFileName_x3f_1679_; lean_object* v_oleanFileName_x3f_1680_; lean_object* v_ileanFileName_x3f_1681_; lean_object* v_cFileName_x3f_1682_; lean_object* v_bcFileName_x3f_1683_; lean_object* v_errorOnKinds_1684_; uint8_t v_printStats_1685_; uint8_t v_run_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_optArg_x3f_940_);
v_leanOpts_1666_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1667_ = lean_ctor_get(v_opts_938_, 1);
v_component_1668_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1669_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1670_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1671_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1672_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1673_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1674_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1675_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1676_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1677_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1678_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1679_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1680_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1681_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1682_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1683_ = lean_ctor_get(v_opts_938_, 8);
v_errorOnKinds_1684_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1685_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1686_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1688_ = v_opts_938_;
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_errorOnKinds_1684_);
lean_inc(v_bcFileName_x3f_1683_);
lean_inc(v_cFileName_x3f_1682_);
lean_inc(v_ileanFileName_x3f_1681_);
lean_inc(v_oleanFileName_x3f_1680_);
lean_inc(v_setupFileName_x3f_1679_);
lean_inc(v_rootDir_x3f_1678_);
lean_inc(v_opts_1675_);
lean_inc(v_forwardedArgs_1667_);
lean_inc(v_leanOpts_1666_);
lean_dec(v_opts_938_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_leanOpts_1666_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_forwardedArgs_1667_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_opts_1675_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_rootDir_x3f_1678_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v_setupFileName_x3f_1679_);
lean_ctor_set(v_reuseFailAlloc_1693_, 5, v_oleanFileName_x3f_1680_);
lean_ctor_set(v_reuseFailAlloc_1693_, 6, v_ileanFileName_x3f_1681_);
lean_ctor_set(v_reuseFailAlloc_1693_, 7, v_cFileName_x3f_1682_);
lean_ctor_set(v_reuseFailAlloc_1693_, 8, v_bcFileName_x3f_1683_);
lean_ctor_set(v_reuseFailAlloc_1693_, 9, v_errorOnKinds_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*10 + 8, v_component_1668_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*10 + 9, v_printPrefix_1669_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*10 + 10, v_printLibDir_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*10 + 11, v_useStdin_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*10 + 12, v_onlyDeps_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*10 + 13, v_onlySrcDeps_1673_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*10 + 14, v_depsJson_1674_);
lean_ctor_set_uint32(v_reuseFailAlloc_1693_, sizeof(void*)*10, v_trustLevel_1676_);
lean_ctor_set_uint32(v_reuseFailAlloc_1693_, sizeof(void*)*10 + 4, v_numThreads_1677_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*10 + 16, v_printStats_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*10 + 17, v_run_1686_);
v___x_1691_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1692_; 
lean_ctor_set_uint8(v___x_1691_, sizeof(void*)*10 + 15, v___x_1183_);
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
return v___x_1692_;
}
}
}
}
else
{
lean_object* v_leanOpts_1695_; lean_object* v_forwardedArgs_1696_; uint8_t v_component_1697_; uint8_t v_printPrefix_1698_; uint8_t v_printLibDir_1699_; uint8_t v_useStdin_1700_; uint8_t v_onlySrcDeps_1701_; lean_object* v_opts_1702_; uint32_t v_trustLevel_1703_; uint32_t v_numThreads_1704_; lean_object* v_rootDir_x3f_1705_; lean_object* v_setupFileName_x3f_1706_; lean_object* v_oleanFileName_x3f_1707_; lean_object* v_ileanFileName_x3f_1708_; lean_object* v_cFileName_x3f_1709_; lean_object* v_bcFileName_x3f_1710_; uint8_t v_jsonOutput_1711_; lean_object* v_errorOnKinds_1712_; uint8_t v_printStats_1713_; uint8_t v_run_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_optArg_x3f_940_);
v_leanOpts_1695_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1696_ = lean_ctor_get(v_opts_938_, 1);
v_component_1697_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1698_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1699_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1700_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlySrcDeps_1701_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_opts_1702_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1703_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1704_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1705_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1706_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1707_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1708_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1709_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1710_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1711_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1712_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1713_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1714_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1716_ = v_opts_938_;
v_isShared_1717_ = v_isSharedCheck_1722_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_errorOnKinds_1712_);
lean_inc(v_bcFileName_x3f_1710_);
lean_inc(v_cFileName_x3f_1709_);
lean_inc(v_ileanFileName_x3f_1708_);
lean_inc(v_oleanFileName_x3f_1707_);
lean_inc(v_setupFileName_x3f_1706_);
lean_inc(v_rootDir_x3f_1705_);
lean_inc(v_opts_1702_);
lean_inc(v_forwardedArgs_1696_);
lean_inc(v_leanOpts_1695_);
lean_dec(v_opts_938_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1722_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_leanOpts_1695_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_forwardedArgs_1696_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_opts_1702_);
lean_ctor_set(v_reuseFailAlloc_1721_, 3, v_rootDir_x3f_1705_);
lean_ctor_set(v_reuseFailAlloc_1721_, 4, v_setupFileName_x3f_1706_);
lean_ctor_set(v_reuseFailAlloc_1721_, 5, v_oleanFileName_x3f_1707_);
lean_ctor_set(v_reuseFailAlloc_1721_, 6, v_ileanFileName_x3f_1708_);
lean_ctor_set(v_reuseFailAlloc_1721_, 7, v_cFileName_x3f_1709_);
lean_ctor_set(v_reuseFailAlloc_1721_, 8, v_bcFileName_x3f_1710_);
lean_ctor_set(v_reuseFailAlloc_1721_, 9, v_errorOnKinds_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1721_, sizeof(void*)*10 + 8, v_component_1697_);
lean_ctor_set_uint8(v_reuseFailAlloc_1721_, sizeof(void*)*10 + 9, v_printPrefix_1698_);
lean_ctor_set_uint8(v_reuseFailAlloc_1721_, sizeof(void*)*10 + 10, v_printLibDir_1699_);
lean_ctor_set_uint8(v_reuseFailAlloc_1721_, sizeof(void*)*10 + 11, v_useStdin_1700_);
lean_ctor_set_uint8(v_reuseFailAlloc_1721_, sizeof(void*)*10 + 13, v_onlySrcDeps_1701_);
lean_ctor_set_uint32(v_reuseFailAlloc_1721_, sizeof(void*)*10, v_trustLevel_1703_);
lean_ctor_set_uint32(v_reuseFailAlloc_1721_, sizeof(void*)*10 + 4, v_numThreads_1704_);
lean_ctor_set_uint8(v_reuseFailAlloc_1721_, sizeof(void*)*10 + 15, v_jsonOutput_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1721_, sizeof(void*)*10 + 16, v_printStats_1713_);
lean_ctor_set_uint8(v_reuseFailAlloc_1721_, sizeof(void*)*10 + 17, v_run_1714_);
v___x_1719_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; 
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*10 + 12, v___x_1181_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*10 + 14, v___x_1181_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
return v___x_1720_;
}
}
}
}
else
{
lean_object* v_leanOpts_1723_; lean_object* v_forwardedArgs_1724_; uint8_t v_component_1725_; uint8_t v_printPrefix_1726_; uint8_t v_printLibDir_1727_; uint8_t v_useStdin_1728_; uint8_t v_onlyDeps_1729_; uint8_t v_depsJson_1730_; lean_object* v_opts_1731_; uint32_t v_trustLevel_1732_; uint32_t v_numThreads_1733_; lean_object* v_rootDir_x3f_1734_; lean_object* v_setupFileName_x3f_1735_; lean_object* v_oleanFileName_x3f_1736_; lean_object* v_ileanFileName_x3f_1737_; lean_object* v_cFileName_x3f_1738_; lean_object* v_bcFileName_x3f_1739_; uint8_t v_jsonOutput_1740_; lean_object* v_errorOnKinds_1741_; uint8_t v_printStats_1742_; uint8_t v_run_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1751_; 
lean_dec(v_optArg_x3f_940_);
v_leanOpts_1723_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1724_ = lean_ctor_get(v_opts_938_, 1);
v_component_1725_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1726_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1727_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1728_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1729_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_depsJson_1730_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1731_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1732_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1733_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1734_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1735_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1736_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1737_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1738_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1739_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1740_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1741_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1742_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1743_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1745_ = v_opts_938_;
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_errorOnKinds_1741_);
lean_inc(v_bcFileName_x3f_1739_);
lean_inc(v_cFileName_x3f_1738_);
lean_inc(v_ileanFileName_x3f_1737_);
lean_inc(v_oleanFileName_x3f_1736_);
lean_inc(v_setupFileName_x3f_1735_);
lean_inc(v_rootDir_x3f_1734_);
lean_inc(v_opts_1731_);
lean_inc(v_forwardedArgs_1724_);
lean_inc(v_leanOpts_1723_);
lean_dec(v_opts_938_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_leanOpts_1723_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_forwardedArgs_1724_);
lean_ctor_set(v_reuseFailAlloc_1750_, 2, v_opts_1731_);
lean_ctor_set(v_reuseFailAlloc_1750_, 3, v_rootDir_x3f_1734_);
lean_ctor_set(v_reuseFailAlloc_1750_, 4, v_setupFileName_x3f_1735_);
lean_ctor_set(v_reuseFailAlloc_1750_, 5, v_oleanFileName_x3f_1736_);
lean_ctor_set(v_reuseFailAlloc_1750_, 6, v_ileanFileName_x3f_1737_);
lean_ctor_set(v_reuseFailAlloc_1750_, 7, v_cFileName_x3f_1738_);
lean_ctor_set(v_reuseFailAlloc_1750_, 8, v_bcFileName_x3f_1739_);
lean_ctor_set(v_reuseFailAlloc_1750_, 9, v_errorOnKinds_1741_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*10 + 8, v_component_1725_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*10 + 9, v_printPrefix_1726_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*10 + 10, v_printLibDir_1727_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*10 + 11, v_useStdin_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*10 + 12, v_onlyDeps_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*10 + 14, v_depsJson_1730_);
lean_ctor_set_uint32(v_reuseFailAlloc_1750_, sizeof(void*)*10, v_trustLevel_1732_);
lean_ctor_set_uint32(v_reuseFailAlloc_1750_, sizeof(void*)*10 + 4, v_numThreads_1733_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*10 + 15, v_jsonOutput_1740_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*10 + 16, v_printStats_1742_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*10 + 17, v_run_1743_);
v___x_1748_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1749_; 
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*10 + 13, v___x_1179_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
}
}
else
{
lean_object* v_leanOpts_1752_; lean_object* v_forwardedArgs_1753_; uint8_t v_component_1754_; uint8_t v_printPrefix_1755_; uint8_t v_printLibDir_1756_; uint8_t v_useStdin_1757_; uint8_t v_onlySrcDeps_1758_; uint8_t v_depsJson_1759_; lean_object* v_opts_1760_; uint32_t v_trustLevel_1761_; uint32_t v_numThreads_1762_; lean_object* v_rootDir_x3f_1763_; lean_object* v_setupFileName_x3f_1764_; lean_object* v_oleanFileName_x3f_1765_; lean_object* v_ileanFileName_x3f_1766_; lean_object* v_cFileName_x3f_1767_; lean_object* v_bcFileName_x3f_1768_; uint8_t v_jsonOutput_1769_; lean_object* v_errorOnKinds_1770_; uint8_t v_printStats_1771_; uint8_t v_run_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_optArg_x3f_940_);
v_leanOpts_1752_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1753_ = lean_ctor_get(v_opts_938_, 1);
v_component_1754_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1755_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1756_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1757_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlySrcDeps_1758_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1759_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1760_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1761_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1762_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1763_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1764_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1765_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1766_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1767_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1768_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1769_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1770_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1771_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1772_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1774_ = v_opts_938_;
v_isShared_1775_ = v_isSharedCheck_1780_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_errorOnKinds_1770_);
lean_inc(v_bcFileName_x3f_1768_);
lean_inc(v_cFileName_x3f_1767_);
lean_inc(v_ileanFileName_x3f_1766_);
lean_inc(v_oleanFileName_x3f_1765_);
lean_inc(v_setupFileName_x3f_1764_);
lean_inc(v_rootDir_x3f_1763_);
lean_inc(v_opts_1760_);
lean_inc(v_forwardedArgs_1753_);
lean_inc(v_leanOpts_1752_);
lean_dec(v_opts_938_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1780_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_leanOpts_1752_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_forwardedArgs_1753_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_opts_1760_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_rootDir_x3f_1763_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v_setupFileName_x3f_1764_);
lean_ctor_set(v_reuseFailAlloc_1779_, 5, v_oleanFileName_x3f_1765_);
lean_ctor_set(v_reuseFailAlloc_1779_, 6, v_ileanFileName_x3f_1766_);
lean_ctor_set(v_reuseFailAlloc_1779_, 7, v_cFileName_x3f_1767_);
lean_ctor_set(v_reuseFailAlloc_1779_, 8, v_bcFileName_x3f_1768_);
lean_ctor_set(v_reuseFailAlloc_1779_, 9, v_errorOnKinds_1770_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*10 + 8, v_component_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*10 + 9, v_printPrefix_1755_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*10 + 10, v_printLibDir_1756_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*10 + 11, v_useStdin_1757_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*10 + 13, v_onlySrcDeps_1758_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*10 + 14, v_depsJson_1759_);
lean_ctor_set_uint32(v_reuseFailAlloc_1779_, sizeof(void*)*10, v_trustLevel_1761_);
lean_ctor_set_uint32(v_reuseFailAlloc_1779_, sizeof(void*)*10 + 4, v_numThreads_1762_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*10 + 15, v_jsonOutput_1769_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*10 + 16, v_printStats_1771_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*10 + 17, v_run_1772_);
v___x_1777_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; 
lean_ctor_set_uint8(v___x_1777_, sizeof(void*)*10 + 12, v___x_1177_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_leanOpts_1781_; lean_object* v_forwardedArgs_1782_; uint8_t v_component_1783_; uint8_t v_printPrefix_1784_; uint8_t v_printLibDir_1785_; uint8_t v_useStdin_1786_; uint8_t v_onlyDeps_1787_; uint8_t v_onlySrcDeps_1788_; uint8_t v_depsJson_1789_; lean_object* v_opts_1790_; uint32_t v_trustLevel_1791_; uint32_t v_numThreads_1792_; lean_object* v_rootDir_x3f_1793_; lean_object* v_setupFileName_x3f_1794_; lean_object* v_oleanFileName_x3f_1795_; lean_object* v_ileanFileName_x3f_1796_; lean_object* v_cFileName_x3f_1797_; lean_object* v_bcFileName_x3f_1798_; uint8_t v_jsonOutput_1799_; lean_object* v_errorOnKinds_1800_; uint8_t v_printStats_1801_; uint8_t v_run_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_optArg_x3f_940_);
v_leanOpts_1781_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1782_ = lean_ctor_get(v_opts_938_, 1);
v_component_1783_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1784_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1785_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1786_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1787_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1788_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1789_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1790_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1791_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1792_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1793_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1794_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1795_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1796_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1797_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1798_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1799_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1800_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1801_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1802_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1804_ = v_opts_938_;
v_isShared_1805_ = v_isSharedCheck_1812_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_errorOnKinds_1800_);
lean_inc(v_bcFileName_x3f_1798_);
lean_inc(v_cFileName_x3f_1797_);
lean_inc(v_ileanFileName_x3f_1796_);
lean_inc(v_oleanFileName_x3f_1795_);
lean_inc(v_setupFileName_x3f_1794_);
lean_inc(v_rootDir_x3f_1793_);
lean_inc(v_opts_1790_);
lean_inc(v_forwardedArgs_1782_);
lean_inc(v_leanOpts_1781_);
lean_dec(v_opts_938_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1812_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1806_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_1807_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1781_, v___x_1806_, v___x_1173_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1807_);
v___x_1809_ = v___x_1804_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1807_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_forwardedArgs_1782_);
lean_ctor_set(v_reuseFailAlloc_1811_, 2, v_opts_1790_);
lean_ctor_set(v_reuseFailAlloc_1811_, 3, v_rootDir_x3f_1793_);
lean_ctor_set(v_reuseFailAlloc_1811_, 4, v_setupFileName_x3f_1794_);
lean_ctor_set(v_reuseFailAlloc_1811_, 5, v_oleanFileName_x3f_1795_);
lean_ctor_set(v_reuseFailAlloc_1811_, 6, v_ileanFileName_x3f_1796_);
lean_ctor_set(v_reuseFailAlloc_1811_, 7, v_cFileName_x3f_1797_);
lean_ctor_set(v_reuseFailAlloc_1811_, 8, v_bcFileName_x3f_1798_);
lean_ctor_set(v_reuseFailAlloc_1811_, 9, v_errorOnKinds_1800_);
lean_ctor_set_uint8(v_reuseFailAlloc_1811_, sizeof(void*)*10 + 8, v_component_1783_);
lean_ctor_set_uint8(v_reuseFailAlloc_1811_, sizeof(void*)*10 + 9, v_printPrefix_1784_);
lean_ctor_set_uint8(v_reuseFailAlloc_1811_, sizeof(void*)*10 + 10, v_printLibDir_1785_);
lean_ctor_set_uint8(v_reuseFailAlloc_1811_, sizeof(void*)*10 + 11, v_useStdin_1786_);
lean_ctor_set_uint8(v_reuseFailAlloc_1811_, sizeof(void*)*10 + 12, v_onlyDeps_1787_);
lean_ctor_set_uint8(v_reuseFailAlloc_1811_, sizeof(void*)*10 + 13, v_onlySrcDeps_1788_);
lean_ctor_set_uint8(v_reuseFailAlloc_1811_, sizeof(void*)*10 + 14, v_depsJson_1789_);
lean_ctor_set_uint32(v_reuseFailAlloc_1811_, sizeof(void*)*10, v_trustLevel_1791_);
lean_ctor_set_uint32(v_reuseFailAlloc_1811_, sizeof(void*)*10 + 4, v_numThreads_1792_);
lean_ctor_set_uint8(v_reuseFailAlloc_1811_, sizeof(void*)*10 + 15, v_jsonOutput_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1811_, sizeof(void*)*10 + 16, v_printStats_1801_);
lean_ctor_set_uint8(v_reuseFailAlloc_1811_, sizeof(void*)*10 + 17, v_run_1802_);
v___x_1809_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
}
}
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1814_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1813_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1865_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1865_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1865_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = lean_string_utf8_byte_size(v_a_1815_);
lean_inc(v_a_1815_);
v___x_1821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1821_, 0, v_a_1815_);
lean_ctor_set(v___x_1821_, 1, v___x_1819_);
lean_ctor_set(v___x_1821_, 2, v___x_1820_);
v___x_1822_ = l_String_Slice_toNat_x3f(v___x_1821_);
lean_dec_ref(v___x_1821_);
if (lean_obj_tag(v___x_1822_) == 1)
{
lean_object* v_val_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v_val_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_val_1823_);
lean_dec_ref(v___x_1822_);
v___x_1824_ = lean_cstr_to_nat("4294967296");
v___x_1825_ = lean_nat_dec_lt(v_val_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec(v_val_1823_);
lean_del_object(v___x_1817_);
lean_dec(v_a_1815_);
lean_dec_ref(v_opts_938_);
v___x_1826_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1827_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1826_);
lean_dec_ref(v___x_1827_);
goto v___jp_1008_;
}
else
{
lean_object* v_leanOpts_1828_; lean_object* v_forwardedArgs_1829_; uint8_t v_component_1830_; uint8_t v_printPrefix_1831_; uint8_t v_printLibDir_1832_; uint8_t v_useStdin_1833_; uint8_t v_onlyDeps_1834_; uint8_t v_onlySrcDeps_1835_; uint8_t v_depsJson_1836_; lean_object* v_opts_1837_; uint32_t v_numThreads_1838_; lean_object* v_rootDir_x3f_1839_; lean_object* v_setupFileName_x3f_1840_; lean_object* v_oleanFileName_x3f_1841_; lean_object* v_ileanFileName_x3f_1842_; lean_object* v_cFileName_x3f_1843_; lean_object* v_bcFileName_x3f_1844_; uint8_t v_jsonOutput_1845_; lean_object* v_errorOnKinds_1846_; uint8_t v_printStats_1847_; uint8_t v_run_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1862_; 
v_leanOpts_1828_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1829_ = lean_ctor_get(v_opts_938_, 1);
v_component_1830_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1831_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1832_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1833_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1834_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1835_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1836_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1837_ = lean_ctor_get(v_opts_938_, 2);
v_numThreads_1838_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1839_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1840_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1841_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1842_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1843_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1844_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1845_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1846_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1847_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1848_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1850_ = v_opts_938_;
v_isShared_1851_ = v_isSharedCheck_1862_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_errorOnKinds_1846_);
lean_inc(v_bcFileName_x3f_1844_);
lean_inc(v_cFileName_x3f_1843_);
lean_inc(v_ileanFileName_x3f_1842_);
lean_inc(v_oleanFileName_x3f_1841_);
lean_inc(v_setupFileName_x3f_1840_);
lean_inc(v_rootDir_x3f_1839_);
lean_inc(v_opts_1837_);
lean_inc(v_forwardedArgs_1829_);
lean_inc(v_leanOpts_1828_);
lean_dec(v_opts_938_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1862_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
uint32_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1852_ = lean_uint32_of_nat(v_val_1823_);
lean_dec(v_val_1823_);
v___x_1853_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1854_ = lean_string_append(v___x_1853_, v_a_1815_);
lean_dec(v_a_1815_);
v___x_1855_ = lean_array_push(v_forwardedArgs_1829_, v___x_1854_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 1, v___x_1855_);
v___x_1857_ = v___x_1850_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_leanOpts_1828_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v___x_1855_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v_opts_1837_);
lean_ctor_set(v_reuseFailAlloc_1861_, 3, v_rootDir_x3f_1839_);
lean_ctor_set(v_reuseFailAlloc_1861_, 4, v_setupFileName_x3f_1840_);
lean_ctor_set(v_reuseFailAlloc_1861_, 5, v_oleanFileName_x3f_1841_);
lean_ctor_set(v_reuseFailAlloc_1861_, 6, v_ileanFileName_x3f_1842_);
lean_ctor_set(v_reuseFailAlloc_1861_, 7, v_cFileName_x3f_1843_);
lean_ctor_set(v_reuseFailAlloc_1861_, 8, v_bcFileName_x3f_1844_);
lean_ctor_set(v_reuseFailAlloc_1861_, 9, v_errorOnKinds_1846_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*10 + 8, v_component_1830_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*10 + 9, v_printPrefix_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*10 + 10, v_printLibDir_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*10 + 11, v_useStdin_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*10 + 12, v_onlyDeps_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*10 + 13, v_onlySrcDeps_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*10 + 14, v_depsJson_1836_);
lean_ctor_set_uint32(v_reuseFailAlloc_1861_, sizeof(void*)*10 + 4, v_numThreads_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*10 + 15, v_jsonOutput_1845_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*10 + 16, v_printStats_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*10 + 17, v_run_1848_);
v___x_1857_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1859_; 
lean_ctor_set_uint32(v___x_1857_, sizeof(void*)*10, v___x_1852_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1857_);
v___x_1859_ = v___x_1817_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec(v___x_1822_);
lean_del_object(v___x_1817_);
lean_dec(v_a_1815_);
lean_dec_ref(v_opts_938_);
v___x_1863_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_1864_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1863_);
lean_dec_ref(v___x_1864_);
goto v___jp_1005_;
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_dec_ref(v_opts_938_);
v_a_1866_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1866_);
lean_dec_ref(v___x_1814_);
v___x_1870_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1871_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1870_);
lean_dec_ref(v___x_1871_);
goto v___jp_1867_;
v___jp_1867_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_io_error_to_string(v_a_1866_);
v___x_1869_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1868_);
lean_dec_ref(v___x_1869_);
goto v___jp_1002_;
}
}
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_1873_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1872_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1922_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1922_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1922_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1878_ = lean_unsigned_to_nat(0u);
v___x_1879_ = lean_string_utf8_byte_size(v_a_1874_);
lean_inc(v_a_1874_);
v___x_1880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1880_, 0, v_a_1874_);
lean_ctor_set(v___x_1880_, 1, v___x_1878_);
lean_ctor_set(v___x_1880_, 2, v___x_1879_);
v___x_1881_ = l_String_Slice_toNat_x3f(v___x_1880_);
lean_dec_ref(v___x_1880_);
if (lean_obj_tag(v___x_1881_) == 1)
{
lean_object* v_val_1882_; lean_object* v_leanOpts_1883_; lean_object* v_forwardedArgs_1884_; uint8_t v_component_1885_; uint8_t v_printPrefix_1886_; uint8_t v_printLibDir_1887_; uint8_t v_useStdin_1888_; uint8_t v_onlyDeps_1889_; uint8_t v_onlySrcDeps_1890_; uint8_t v_depsJson_1891_; lean_object* v_opts_1892_; uint32_t v_trustLevel_1893_; uint32_t v_numThreads_1894_; lean_object* v_rootDir_x3f_1895_; lean_object* v_setupFileName_x3f_1896_; lean_object* v_oleanFileName_x3f_1897_; lean_object* v_ileanFileName_x3f_1898_; lean_object* v_cFileName_x3f_1899_; lean_object* v_bcFileName_x3f_1900_; uint8_t v_jsonOutput_1901_; lean_object* v_errorOnKinds_1902_; uint8_t v_printStats_1903_; uint8_t v_run_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1919_; 
v_val_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_val_1882_);
lean_dec_ref(v___x_1881_);
v_leanOpts_1883_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1884_ = lean_ctor_get(v_opts_938_, 1);
v_component_1885_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1886_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1887_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1888_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1889_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1890_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1891_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1892_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1893_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1894_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1895_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1896_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1897_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1898_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1899_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1900_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1901_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1902_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1903_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1904_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1906_ = v_opts_938_;
v_isShared_1907_ = v_isSharedCheck_1919_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_errorOnKinds_1902_);
lean_inc(v_bcFileName_x3f_1900_);
lean_inc(v_cFileName_x3f_1899_);
lean_inc(v_ileanFileName_x3f_1898_);
lean_inc(v_oleanFileName_x3f_1897_);
lean_inc(v_setupFileName_x3f_1896_);
lean_inc(v_rootDir_x3f_1895_);
lean_inc(v_opts_1892_);
lean_inc(v_forwardedArgs_1884_);
lean_inc(v_leanOpts_1883_);
lean_dec(v_opts_938_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1919_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1908_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_1909_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_1883_, v___x_1908_, v_val_1882_);
v___x_1910_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_1911_ = lean_string_append(v___x_1910_, v_a_1874_);
lean_dec(v_a_1874_);
v___x_1912_ = lean_array_push(v_forwardedArgs_1884_, v___x_1911_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 1, v___x_1912_);
lean_ctor_set(v___x_1906_, 0, v___x_1909_);
v___x_1914_ = v___x_1906_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_opts_1892_);
lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_rootDir_x3f_1895_);
lean_ctor_set(v_reuseFailAlloc_1918_, 4, v_setupFileName_x3f_1896_);
lean_ctor_set(v_reuseFailAlloc_1918_, 5, v_oleanFileName_x3f_1897_);
lean_ctor_set(v_reuseFailAlloc_1918_, 6, v_ileanFileName_x3f_1898_);
lean_ctor_set(v_reuseFailAlloc_1918_, 7, v_cFileName_x3f_1899_);
lean_ctor_set(v_reuseFailAlloc_1918_, 8, v_bcFileName_x3f_1900_);
lean_ctor_set(v_reuseFailAlloc_1918_, 9, v_errorOnKinds_1902_);
lean_ctor_set_uint8(v_reuseFailAlloc_1918_, sizeof(void*)*10 + 8, v_component_1885_);
lean_ctor_set_uint8(v_reuseFailAlloc_1918_, sizeof(void*)*10 + 9, v_printPrefix_1886_);
lean_ctor_set_uint8(v_reuseFailAlloc_1918_, sizeof(void*)*10 + 10, v_printLibDir_1887_);
lean_ctor_set_uint8(v_reuseFailAlloc_1918_, sizeof(void*)*10 + 11, v_useStdin_1888_);
lean_ctor_set_uint8(v_reuseFailAlloc_1918_, sizeof(void*)*10 + 12, v_onlyDeps_1889_);
lean_ctor_set_uint8(v_reuseFailAlloc_1918_, sizeof(void*)*10 + 13, v_onlySrcDeps_1890_);
lean_ctor_set_uint8(v_reuseFailAlloc_1918_, sizeof(void*)*10 + 14, v_depsJson_1891_);
lean_ctor_set_uint32(v_reuseFailAlloc_1918_, sizeof(void*)*10, v_trustLevel_1893_);
lean_ctor_set_uint32(v_reuseFailAlloc_1918_, sizeof(void*)*10 + 4, v_numThreads_1894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1918_, sizeof(void*)*10 + 15, v_jsonOutput_1901_);
lean_ctor_set_uint8(v_reuseFailAlloc_1918_, sizeof(void*)*10 + 16, v_printStats_1903_);
lean_ctor_set_uint8(v_reuseFailAlloc_1918_, sizeof(void*)*10 + 17, v_run_1904_);
v___x_1914_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1916_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1914_);
v___x_1916_ = v___x_1876_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v___x_1881_);
lean_del_object(v___x_1876_);
lean_dec(v_a_1874_);
lean_dec_ref(v_opts_938_);
v___x_1920_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_1921_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1920_);
lean_dec_ref(v___x_1921_);
goto v___jp_1093_;
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_dec_ref(v_opts_938_);
v_a_1923_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1923_);
lean_dec_ref(v___x_1873_);
v___x_1927_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1928_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1927_);
lean_dec_ref(v___x_1928_);
goto v___jp_1924_;
v___jp_1924_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_io_error_to_string(v_a_1923_);
v___x_1926_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1925_);
lean_dec_ref(v___x_1926_);
goto v___jp_1099_;
}
}
}
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_1930_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1929_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1979_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1979_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1979_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = lean_string_utf8_byte_size(v_a_1931_);
lean_inc(v_a_1931_);
v___x_1937_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1937_, 0, v_a_1931_);
lean_ctor_set(v___x_1937_, 1, v___x_1935_);
lean_ctor_set(v___x_1937_, 2, v___x_1936_);
v___x_1938_ = l_String_Slice_toNat_x3f(v___x_1937_);
lean_dec_ref(v___x_1937_);
if (lean_obj_tag(v___x_1938_) == 1)
{
lean_object* v_val_1939_; lean_object* v_leanOpts_1940_; lean_object* v_forwardedArgs_1941_; uint8_t v_component_1942_; uint8_t v_printPrefix_1943_; uint8_t v_printLibDir_1944_; uint8_t v_useStdin_1945_; uint8_t v_onlyDeps_1946_; uint8_t v_onlySrcDeps_1947_; uint8_t v_depsJson_1948_; lean_object* v_opts_1949_; uint32_t v_trustLevel_1950_; uint32_t v_numThreads_1951_; lean_object* v_rootDir_x3f_1952_; lean_object* v_setupFileName_x3f_1953_; lean_object* v_oleanFileName_x3f_1954_; lean_object* v_ileanFileName_x3f_1955_; lean_object* v_cFileName_x3f_1956_; lean_object* v_bcFileName_x3f_1957_; uint8_t v_jsonOutput_1958_; lean_object* v_errorOnKinds_1959_; uint8_t v_printStats_1960_; uint8_t v_run_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1976_; 
v_val_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_val_1939_);
lean_dec_ref(v___x_1938_);
v_leanOpts_1940_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1941_ = lean_ctor_get(v_opts_938_, 1);
v_component_1942_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1943_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1944_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1945_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1946_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1947_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_1948_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_1949_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_1950_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_1951_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1952_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_1953_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_1954_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_1955_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_1956_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_1957_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_1958_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_1959_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_1960_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_1961_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1963_ = v_opts_938_;
v_isShared_1964_ = v_isSharedCheck_1976_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_errorOnKinds_1959_);
lean_inc(v_bcFileName_x3f_1957_);
lean_inc(v_cFileName_x3f_1956_);
lean_inc(v_ileanFileName_x3f_1955_);
lean_inc(v_oleanFileName_x3f_1954_);
lean_inc(v_setupFileName_x3f_1953_);
lean_inc(v_rootDir_x3f_1952_);
lean_inc(v_opts_1949_);
lean_inc(v_forwardedArgs_1941_);
lean_inc(v_leanOpts_1940_);
lean_dec(v_opts_938_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1976_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1965_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_1966_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_1940_, v___x_1965_, v_val_1939_);
v___x_1967_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_1968_ = lean_string_append(v___x_1967_, v_a_1931_);
lean_dec(v_a_1931_);
v___x_1969_ = lean_array_push(v_forwardedArgs_1941_, v___x_1968_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v___x_1969_);
lean_ctor_set(v___x_1963_, 0, v___x_1966_);
v___x_1971_ = v___x_1963_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1975_, 2, v_opts_1949_);
lean_ctor_set(v_reuseFailAlloc_1975_, 3, v_rootDir_x3f_1952_);
lean_ctor_set(v_reuseFailAlloc_1975_, 4, v_setupFileName_x3f_1953_);
lean_ctor_set(v_reuseFailAlloc_1975_, 5, v_oleanFileName_x3f_1954_);
lean_ctor_set(v_reuseFailAlloc_1975_, 6, v_ileanFileName_x3f_1955_);
lean_ctor_set(v_reuseFailAlloc_1975_, 7, v_cFileName_x3f_1956_);
lean_ctor_set(v_reuseFailAlloc_1975_, 8, v_bcFileName_x3f_1957_);
lean_ctor_set(v_reuseFailAlloc_1975_, 9, v_errorOnKinds_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*10 + 8, v_component_1942_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*10 + 9, v_printPrefix_1943_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*10 + 10, v_printLibDir_1944_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*10 + 11, v_useStdin_1945_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*10 + 12, v_onlyDeps_1946_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*10 + 13, v_onlySrcDeps_1947_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*10 + 14, v_depsJson_1948_);
lean_ctor_set_uint32(v_reuseFailAlloc_1975_, sizeof(void*)*10, v_trustLevel_1950_);
lean_ctor_set_uint32(v_reuseFailAlloc_1975_, sizeof(void*)*10 + 4, v_numThreads_1951_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*10 + 15, v_jsonOutput_1958_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*10 + 16, v_printStats_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*10 + 17, v_run_1961_);
v___x_1971_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1973_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1971_);
v___x_1973_ = v___x_1933_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1971_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_dec(v___x_1938_);
lean_del_object(v___x_1933_);
lean_dec(v_a_1931_);
lean_dec_ref(v_opts_938_);
v___x_1977_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_1978_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1977_);
lean_dec_ref(v___x_1978_);
goto v___jp_996_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec_ref(v_opts_938_);
v_a_1980_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1980_);
lean_dec_ref(v___x_1930_);
v___x_1984_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1985_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1984_);
lean_dec_ref(v___x_1985_);
goto v___jp_1981_;
v___jp_1981_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_io_error_to_string(v_a_1980_);
v___x_1983_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1982_);
lean_dec_ref(v___x_1983_);
goto v___jp_993_;
}
}
}
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_1987_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1986_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2028_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_2028_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2028_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v_leanOpts_1992_; lean_object* v_forwardedArgs_1993_; uint8_t v_component_1994_; uint8_t v_printPrefix_1995_; uint8_t v_printLibDir_1996_; uint8_t v_useStdin_1997_; uint8_t v_onlyDeps_1998_; uint8_t v_onlySrcDeps_1999_; uint8_t v_depsJson_2000_; lean_object* v_opts_2001_; uint32_t v_trustLevel_2002_; uint32_t v_numThreads_2003_; lean_object* v_setupFileName_x3f_2004_; lean_object* v_oleanFileName_x3f_2005_; lean_object* v_ileanFileName_x3f_2006_; lean_object* v_cFileName_x3f_2007_; lean_object* v_bcFileName_x3f_2008_; uint8_t v_jsonOutput_2009_; lean_object* v_errorOnKinds_2010_; uint8_t v_printStats_2011_; uint8_t v_run_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2026_; 
v_leanOpts_1992_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_1993_ = lean_ctor_get(v_opts_938_, 1);
v_component_1994_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_1995_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_1996_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_1997_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_1998_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1999_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_2000_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_2001_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_2002_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_2003_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_setupFileName_x3f_2004_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_2005_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_2006_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_2007_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_2008_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_2009_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_2010_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_2011_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_2012_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; 
v_unused_2027_ = lean_ctor_get(v_opts_938_, 3);
lean_dec(v_unused_2027_);
v___x_2014_ = v_opts_938_;
v_isShared_2015_ = v_isSharedCheck_2026_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_errorOnKinds_2010_);
lean_inc(v_bcFileName_x3f_2008_);
lean_inc(v_cFileName_x3f_2007_);
lean_inc(v_ileanFileName_x3f_2006_);
lean_inc(v_oleanFileName_x3f_2005_);
lean_inc(v_setupFileName_x3f_2004_);
lean_inc(v_opts_2001_);
lean_inc(v_forwardedArgs_1993_);
lean_inc(v_leanOpts_1992_);
lean_dec(v_opts_938_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2026_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2016_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2017_ = lean_string_append(v___x_2016_, v_a_1988_);
v___x_2018_ = lean_array_push(v_forwardedArgs_1993_, v___x_2017_);
v___x_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_a_1988_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 3, v___x_2019_);
lean_ctor_set(v___x_2014_, 1, v___x_2018_);
v___x_2021_ = v___x_2014_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_leanOpts_1992_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_opts_2001_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_setupFileName_x3f_2004_);
lean_ctor_set(v_reuseFailAlloc_2025_, 5, v_oleanFileName_x3f_2005_);
lean_ctor_set(v_reuseFailAlloc_2025_, 6, v_ileanFileName_x3f_2006_);
lean_ctor_set(v_reuseFailAlloc_2025_, 7, v_cFileName_x3f_2007_);
lean_ctor_set(v_reuseFailAlloc_2025_, 8, v_bcFileName_x3f_2008_);
lean_ctor_set(v_reuseFailAlloc_2025_, 9, v_errorOnKinds_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*10 + 8, v_component_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*10 + 9, v_printPrefix_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*10 + 10, v_printLibDir_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*10 + 11, v_useStdin_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*10 + 12, v_onlyDeps_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*10 + 13, v_onlySrcDeps_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*10 + 14, v_depsJson_2000_);
lean_ctor_set_uint32(v_reuseFailAlloc_2025_, sizeof(void*)*10, v_trustLevel_2002_);
lean_ctor_set_uint32(v_reuseFailAlloc_2025_, sizeof(void*)*10 + 4, v_numThreads_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*10 + 15, v_jsonOutput_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*10 + 16, v_printStats_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*10 + 17, v_run_2012_);
v___x_2021_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2023_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_2021_);
v___x_2023_ = v___x_1990_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec_ref(v_opts_938_);
v_a_2029_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_2029_);
lean_dec_ref(v___x_1987_);
v___x_2033_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2034_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2033_);
lean_dec_ref(v___x_2034_);
goto v___jp_2030_;
v___jp_2030_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_io_error_to_string(v_a_2029_);
v___x_2032_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2031_);
lean_dec_ref(v___x_2032_);
goto v___jp_1105_;
}
}
}
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2036_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2035_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2074_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2074_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2074_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v_leanOpts_2041_; lean_object* v_forwardedArgs_2042_; uint8_t v_component_2043_; uint8_t v_printPrefix_2044_; uint8_t v_printLibDir_2045_; uint8_t v_useStdin_2046_; uint8_t v_onlyDeps_2047_; uint8_t v_onlySrcDeps_2048_; uint8_t v_depsJson_2049_; lean_object* v_opts_2050_; uint32_t v_trustLevel_2051_; uint32_t v_numThreads_2052_; lean_object* v_rootDir_x3f_2053_; lean_object* v_setupFileName_x3f_2054_; lean_object* v_oleanFileName_x3f_2055_; lean_object* v_cFileName_x3f_2056_; lean_object* v_bcFileName_x3f_2057_; uint8_t v_jsonOutput_2058_; lean_object* v_errorOnKinds_2059_; uint8_t v_printStats_2060_; uint8_t v_run_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2072_; 
v_leanOpts_2041_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_2042_ = lean_ctor_get(v_opts_938_, 1);
v_component_2043_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_2044_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_2045_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_2046_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_2047_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2048_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_2049_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_2050_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_2051_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_2052_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2053_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_2054_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_2055_ = lean_ctor_get(v_opts_938_, 5);
v_cFileName_x3f_2056_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_2057_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_2058_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_2059_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_2060_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_2061_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v_opts_938_, 6);
lean_dec(v_unused_2073_);
v___x_2063_ = v_opts_938_;
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_errorOnKinds_2059_);
lean_inc(v_bcFileName_x3f_2057_);
lean_inc(v_cFileName_x3f_2056_);
lean_inc(v_oleanFileName_x3f_2055_);
lean_inc(v_setupFileName_x3f_2054_);
lean_inc(v_rootDir_x3f_2053_);
lean_inc(v_opts_2050_);
lean_inc(v_forwardedArgs_2042_);
lean_inc(v_leanOpts_2041_);
lean_dec(v_opts_938_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_a_2037_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 6, v___x_2065_);
v___x_2067_ = v___x_2063_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_leanOpts_2041_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_forwardedArgs_2042_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_opts_2050_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_rootDir_x3f_2053_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_setupFileName_x3f_2054_);
lean_ctor_set(v_reuseFailAlloc_2071_, 5, v_oleanFileName_x3f_2055_);
lean_ctor_set(v_reuseFailAlloc_2071_, 6, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2071_, 7, v_cFileName_x3f_2056_);
lean_ctor_set(v_reuseFailAlloc_2071_, 8, v_bcFileName_x3f_2057_);
lean_ctor_set(v_reuseFailAlloc_2071_, 9, v_errorOnKinds_2059_);
lean_ctor_set_uint8(v_reuseFailAlloc_2071_, sizeof(void*)*10 + 8, v_component_2043_);
lean_ctor_set_uint8(v_reuseFailAlloc_2071_, sizeof(void*)*10 + 9, v_printPrefix_2044_);
lean_ctor_set_uint8(v_reuseFailAlloc_2071_, sizeof(void*)*10 + 10, v_printLibDir_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2071_, sizeof(void*)*10 + 11, v_useStdin_2046_);
lean_ctor_set_uint8(v_reuseFailAlloc_2071_, sizeof(void*)*10 + 12, v_onlyDeps_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2071_, sizeof(void*)*10 + 13, v_onlySrcDeps_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2071_, sizeof(void*)*10 + 14, v_depsJson_2049_);
lean_ctor_set_uint32(v_reuseFailAlloc_2071_, sizeof(void*)*10, v_trustLevel_2051_);
lean_ctor_set_uint32(v_reuseFailAlloc_2071_, sizeof(void*)*10 + 4, v_numThreads_2052_);
lean_ctor_set_uint8(v_reuseFailAlloc_2071_, sizeof(void*)*10 + 15, v_jsonOutput_2058_);
lean_ctor_set_uint8(v_reuseFailAlloc_2071_, sizeof(void*)*10 + 16, v_printStats_2060_);
lean_ctor_set_uint8(v_reuseFailAlloc_2071_, sizeof(void*)*10 + 17, v_run_2061_);
v___x_2067_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2067_);
v___x_2069_ = v___x_2039_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_dec_ref(v_opts_938_);
v_a_2075_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2036_);
v___x_2079_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2080_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2079_);
lean_dec_ref(v___x_2080_);
goto v___jp_2076_;
v___jp_2076_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_io_error_to_string(v_a_2075_);
v___x_2078_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2077_);
lean_dec_ref(v___x_2078_);
goto v___jp_987_;
}
}
}
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2082_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2081_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2120_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2120_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2120_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v_leanOpts_2087_; lean_object* v_forwardedArgs_2088_; uint8_t v_component_2089_; uint8_t v_printPrefix_2090_; uint8_t v_printLibDir_2091_; uint8_t v_useStdin_2092_; uint8_t v_onlyDeps_2093_; uint8_t v_onlySrcDeps_2094_; uint8_t v_depsJson_2095_; lean_object* v_opts_2096_; uint32_t v_trustLevel_2097_; uint32_t v_numThreads_2098_; lean_object* v_rootDir_x3f_2099_; lean_object* v_setupFileName_x3f_2100_; lean_object* v_ileanFileName_x3f_2101_; lean_object* v_cFileName_x3f_2102_; lean_object* v_bcFileName_x3f_2103_; uint8_t v_jsonOutput_2104_; lean_object* v_errorOnKinds_2105_; uint8_t v_printStats_2106_; uint8_t v_run_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2118_; 
v_leanOpts_2087_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_2088_ = lean_ctor_get(v_opts_938_, 1);
v_component_2089_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_2090_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_2091_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_2092_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_2093_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2094_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_2095_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_2096_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_2097_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_2098_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2099_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_2100_ = lean_ctor_get(v_opts_938_, 4);
v_ileanFileName_x3f_2101_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_2102_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_2103_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_2104_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_2105_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_2106_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_2107_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; 
v_unused_2119_ = lean_ctor_get(v_opts_938_, 5);
lean_dec(v_unused_2119_);
v___x_2109_ = v_opts_938_;
v_isShared_2110_ = v_isSharedCheck_2118_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_errorOnKinds_2105_);
lean_inc(v_bcFileName_x3f_2103_);
lean_inc(v_cFileName_x3f_2102_);
lean_inc(v_ileanFileName_x3f_2101_);
lean_inc(v_setupFileName_x3f_2100_);
lean_inc(v_rootDir_x3f_2099_);
lean_inc(v_opts_2096_);
lean_inc(v_forwardedArgs_2088_);
lean_inc(v_leanOpts_2087_);
lean_dec(v_opts_938_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2118_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_a_2083_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 5, v___x_2111_);
v___x_2113_ = v___x_2109_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_leanOpts_2087_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_forwardedArgs_2088_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_opts_2096_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v_rootDir_x3f_2099_);
lean_ctor_set(v_reuseFailAlloc_2117_, 4, v_setupFileName_x3f_2100_);
lean_ctor_set(v_reuseFailAlloc_2117_, 5, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2117_, 6, v_ileanFileName_x3f_2101_);
lean_ctor_set(v_reuseFailAlloc_2117_, 7, v_cFileName_x3f_2102_);
lean_ctor_set(v_reuseFailAlloc_2117_, 8, v_bcFileName_x3f_2103_);
lean_ctor_set(v_reuseFailAlloc_2117_, 9, v_errorOnKinds_2105_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*10 + 8, v_component_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*10 + 9, v_printPrefix_2090_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*10 + 10, v_printLibDir_2091_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*10 + 11, v_useStdin_2092_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*10 + 12, v_onlyDeps_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*10 + 13, v_onlySrcDeps_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*10 + 14, v_depsJson_2095_);
lean_ctor_set_uint32(v_reuseFailAlloc_2117_, sizeof(void*)*10, v_trustLevel_2097_);
lean_ctor_set_uint32(v_reuseFailAlloc_2117_, sizeof(void*)*10 + 4, v_numThreads_2098_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*10 + 15, v_jsonOutput_2104_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*10 + 16, v_printStats_2106_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*10 + 17, v_run_2107_);
v___x_2113_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2113_);
v___x_2115_ = v___x_2085_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_dec_ref(v_opts_938_);
v_a_2121_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2082_);
v___x_2125_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2126_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2125_);
lean_dec_ref(v___x_2126_);
goto v___jp_2122_;
v___jp_2122_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = lean_io_error_to_string(v_a_2121_);
v___x_2124_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2123_);
lean_dec_ref(v___x_2124_);
goto v___jp_1111_;
}
}
}
}
else
{
lean_object* v_leanOpts_2127_; lean_object* v_forwardedArgs_2128_; uint8_t v_component_2129_; uint8_t v_printPrefix_2130_; uint8_t v_printLibDir_2131_; uint8_t v_useStdin_2132_; uint8_t v_onlyDeps_2133_; uint8_t v_onlySrcDeps_2134_; uint8_t v_depsJson_2135_; lean_object* v_opts_2136_; uint32_t v_trustLevel_2137_; uint32_t v_numThreads_2138_; lean_object* v_rootDir_x3f_2139_; lean_object* v_setupFileName_x3f_2140_; lean_object* v_oleanFileName_x3f_2141_; lean_object* v_ileanFileName_x3f_2142_; lean_object* v_cFileName_x3f_2143_; lean_object* v_bcFileName_x3f_2144_; uint8_t v_jsonOutput_2145_; lean_object* v_errorOnKinds_2146_; uint8_t v_printStats_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_optArg_x3f_940_);
v_leanOpts_2127_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_2128_ = lean_ctor_get(v_opts_938_, 1);
v_component_2129_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_2130_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_2131_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_2132_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_2133_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2134_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_2135_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_2136_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_2137_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_2138_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2139_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_2140_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_2141_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_2142_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_2143_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_2144_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_2145_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_2146_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_2147_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2149_ = v_opts_938_;
v_isShared_2150_ = v_isSharedCheck_2155_;
goto v_resetjp_2148_;
}
else
{
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
lean_dec(v_opts_938_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2155_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_leanOpts_2127_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_forwardedArgs_2128_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_opts_2136_);
lean_ctor_set(v_reuseFailAlloc_2154_, 3, v_rootDir_x3f_2139_);
lean_ctor_set(v_reuseFailAlloc_2154_, 4, v_setupFileName_x3f_2140_);
lean_ctor_set(v_reuseFailAlloc_2154_, 5, v_oleanFileName_x3f_2141_);
lean_ctor_set(v_reuseFailAlloc_2154_, 6, v_ileanFileName_x3f_2142_);
lean_ctor_set(v_reuseFailAlloc_2154_, 7, v_cFileName_x3f_2143_);
lean_ctor_set(v_reuseFailAlloc_2154_, 8, v_bcFileName_x3f_2144_);
lean_ctor_set(v_reuseFailAlloc_2154_, 9, v_errorOnKinds_2146_);
lean_ctor_set_uint8(v_reuseFailAlloc_2154_, sizeof(void*)*10 + 8, v_component_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2154_, sizeof(void*)*10 + 9, v_printPrefix_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2154_, sizeof(void*)*10 + 10, v_printLibDir_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2154_, sizeof(void*)*10 + 11, v_useStdin_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2154_, sizeof(void*)*10 + 12, v_onlyDeps_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2154_, sizeof(void*)*10 + 13, v_onlySrcDeps_2134_);
lean_ctor_set_uint8(v_reuseFailAlloc_2154_, sizeof(void*)*10 + 14, v_depsJson_2135_);
lean_ctor_set_uint32(v_reuseFailAlloc_2154_, sizeof(void*)*10, v_trustLevel_2137_);
lean_ctor_set_uint32(v_reuseFailAlloc_2154_, sizeof(void*)*10 + 4, v_numThreads_2138_);
lean_ctor_set_uint8(v_reuseFailAlloc_2154_, sizeof(void*)*10 + 15, v_jsonOutput_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2154_, sizeof(void*)*10 + 16, v_printStats_2147_);
v___x_2152_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; 
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*10 + 17, v___x_1161_);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_leanOpts_2156_; lean_object* v_forwardedArgs_2157_; uint8_t v_component_2158_; uint8_t v_printPrefix_2159_; uint8_t v_printLibDir_2160_; uint8_t v_onlyDeps_2161_; uint8_t v_onlySrcDeps_2162_; uint8_t v_depsJson_2163_; lean_object* v_opts_2164_; uint32_t v_trustLevel_2165_; uint32_t v_numThreads_2166_; lean_object* v_rootDir_x3f_2167_; lean_object* v_setupFileName_x3f_2168_; lean_object* v_oleanFileName_x3f_2169_; lean_object* v_ileanFileName_x3f_2170_; lean_object* v_cFileName_x3f_2171_; lean_object* v_bcFileName_x3f_2172_; uint8_t v_jsonOutput_2173_; lean_object* v_errorOnKinds_2174_; uint8_t v_printStats_2175_; uint8_t v_run_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v_optArg_x3f_940_);
v_leanOpts_2156_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_2157_ = lean_ctor_get(v_opts_938_, 1);
v_component_2158_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_2159_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_2160_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_onlyDeps_2161_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2162_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_2163_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_2164_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_2165_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_2166_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2167_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_2168_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_2169_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_2170_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_2171_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_2172_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_2173_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_2174_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_2175_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_2176_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2178_ = v_opts_938_;
v_isShared_2179_ = v_isSharedCheck_2184_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_errorOnKinds_2174_);
lean_inc(v_bcFileName_x3f_2172_);
lean_inc(v_cFileName_x3f_2171_);
lean_inc(v_ileanFileName_x3f_2170_);
lean_inc(v_oleanFileName_x3f_2169_);
lean_inc(v_setupFileName_x3f_2168_);
lean_inc(v_rootDir_x3f_2167_);
lean_inc(v_opts_2164_);
lean_inc(v_forwardedArgs_2157_);
lean_inc(v_leanOpts_2156_);
lean_dec(v_opts_938_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2184_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_leanOpts_2156_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_forwardedArgs_2157_);
lean_ctor_set(v_reuseFailAlloc_2183_, 2, v_opts_2164_);
lean_ctor_set(v_reuseFailAlloc_2183_, 3, v_rootDir_x3f_2167_);
lean_ctor_set(v_reuseFailAlloc_2183_, 4, v_setupFileName_x3f_2168_);
lean_ctor_set(v_reuseFailAlloc_2183_, 5, v_oleanFileName_x3f_2169_);
lean_ctor_set(v_reuseFailAlloc_2183_, 6, v_ileanFileName_x3f_2170_);
lean_ctor_set(v_reuseFailAlloc_2183_, 7, v_cFileName_x3f_2171_);
lean_ctor_set(v_reuseFailAlloc_2183_, 8, v_bcFileName_x3f_2172_);
lean_ctor_set(v_reuseFailAlloc_2183_, 9, v_errorOnKinds_2174_);
lean_ctor_set_uint8(v_reuseFailAlloc_2183_, sizeof(void*)*10 + 8, v_component_2158_);
lean_ctor_set_uint8(v_reuseFailAlloc_2183_, sizeof(void*)*10 + 9, v_printPrefix_2159_);
lean_ctor_set_uint8(v_reuseFailAlloc_2183_, sizeof(void*)*10 + 10, v_printLibDir_2160_);
lean_ctor_set_uint8(v_reuseFailAlloc_2183_, sizeof(void*)*10 + 12, v_onlyDeps_2161_);
lean_ctor_set_uint8(v_reuseFailAlloc_2183_, sizeof(void*)*10 + 13, v_onlySrcDeps_2162_);
lean_ctor_set_uint8(v_reuseFailAlloc_2183_, sizeof(void*)*10 + 14, v_depsJson_2163_);
lean_ctor_set_uint32(v_reuseFailAlloc_2183_, sizeof(void*)*10, v_trustLevel_2165_);
lean_ctor_set_uint32(v_reuseFailAlloc_2183_, sizeof(void*)*10 + 4, v_numThreads_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2183_, sizeof(void*)*10 + 15, v_jsonOutput_2173_);
lean_ctor_set_uint8(v_reuseFailAlloc_2183_, sizeof(void*)*10 + 16, v_printStats_2175_);
lean_ctor_set_uint8(v_reuseFailAlloc_2183_, sizeof(void*)*10 + 17, v_run_2176_);
v___x_2181_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
lean_object* v___x_2182_; 
lean_ctor_set_uint8(v___x_2181_, sizeof(void*)*10 + 11, v___x_1159_);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
return v___x_2182_;
}
}
}
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2186_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2185_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2245_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2245_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2245_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_string_utf8_byte_size(v_a_2187_);
lean_inc(v_a_2187_);
v___x_2193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2193_, 0, v_a_2187_);
lean_ctor_set(v___x_2193_, 1, v___x_2191_);
lean_ctor_set(v___x_2193_, 2, v___x_2192_);
v___x_2194_ = l_String_Slice_toNat_x3f(v___x_2193_);
lean_dec_ref(v___x_2193_);
if (lean_obj_tag(v___x_2194_) == 1)
{
lean_object* v_val_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; 
v_val_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_val_2195_);
lean_dec_ref(v___x_2194_);
v___x_2196_ = lean_unsigned_to_nat(4u);
v___x_2197_ = lean_unsigned_to_nat(2u);
v___x_2198_ = lean_nat_shiftr(v_val_2195_, v___x_2197_);
lean_dec(v_val_2195_);
v___x_2199_ = lean_nat_mul(v___x_2198_, v___x_2196_);
lean_dec(v___x_2198_);
v___x_2200_ = lean_unsigned_to_nat(1024u);
v___x_2201_ = lean_nat_mul(v___x_2199_, v___x_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25);
v___x_2203_ = lean_nat_dec_lt(v___x_2201_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec(v___x_2201_);
lean_del_object(v___x_2189_);
lean_dec(v_a_2187_);
lean_dec_ref(v_opts_938_);
v___x_2204_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2205_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2204_);
lean_dec_ref(v___x_2205_);
goto v___jp_981_;
}
else
{
size_t v___x_2206_; lean_object* v___x_2207_; lean_object* v_leanOpts_2208_; lean_object* v_forwardedArgs_2209_; uint8_t v_component_2210_; uint8_t v_printPrefix_2211_; uint8_t v_printLibDir_2212_; uint8_t v_useStdin_2213_; uint8_t v_onlyDeps_2214_; uint8_t v_onlySrcDeps_2215_; uint8_t v_depsJson_2216_; lean_object* v_opts_2217_; uint32_t v_trustLevel_2218_; uint32_t v_numThreads_2219_; lean_object* v_rootDir_x3f_2220_; lean_object* v_setupFileName_x3f_2221_; lean_object* v_oleanFileName_x3f_2222_; lean_object* v_ileanFileName_x3f_2223_; lean_object* v_cFileName_x3f_2224_; lean_object* v_bcFileName_x3f_2225_; uint8_t v_jsonOutput_2226_; lean_object* v_errorOnKinds_2227_; uint8_t v_printStats_2228_; uint8_t v_run_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2242_; 
v___x_2206_ = lean_usize_of_nat(v___x_2201_);
lean_dec(v___x_2201_);
v___x_2207_ = lean_internal_set_thread_stack_size(v___x_2206_);
v_leanOpts_2208_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_2209_ = lean_ctor_get(v_opts_938_, 1);
v_component_2210_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_2211_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_2212_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_2213_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_2214_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2215_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_2216_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_2217_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_2218_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_2219_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2220_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_2221_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_2222_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_2223_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_2224_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_2225_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_2226_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_2227_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_2228_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_2229_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2231_ = v_opts_938_;
v_isShared_2232_ = v_isSharedCheck_2242_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_errorOnKinds_2227_);
lean_inc(v_bcFileName_x3f_2225_);
lean_inc(v_cFileName_x3f_2224_);
lean_inc(v_ileanFileName_x3f_2223_);
lean_inc(v_oleanFileName_x3f_2222_);
lean_inc(v_setupFileName_x3f_2221_);
lean_inc(v_rootDir_x3f_2220_);
lean_inc(v_opts_2217_);
lean_inc(v_forwardedArgs_2209_);
lean_inc(v_leanOpts_2208_);
lean_dec(v_opts_938_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2242_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2233_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2234_ = lean_string_append(v___x_2233_, v_a_2187_);
lean_dec(v_a_2187_);
v___x_2235_ = lean_array_push(v_forwardedArgs_2209_, v___x_2234_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v___x_2235_);
v___x_2237_ = v___x_2231_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_leanOpts_2208_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_opts_2217_);
lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_rootDir_x3f_2220_);
lean_ctor_set(v_reuseFailAlloc_2241_, 4, v_setupFileName_x3f_2221_);
lean_ctor_set(v_reuseFailAlloc_2241_, 5, v_oleanFileName_x3f_2222_);
lean_ctor_set(v_reuseFailAlloc_2241_, 6, v_ileanFileName_x3f_2223_);
lean_ctor_set(v_reuseFailAlloc_2241_, 7, v_cFileName_x3f_2224_);
lean_ctor_set(v_reuseFailAlloc_2241_, 8, v_bcFileName_x3f_2225_);
lean_ctor_set(v_reuseFailAlloc_2241_, 9, v_errorOnKinds_2227_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*10 + 8, v_component_2210_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*10 + 9, v_printPrefix_2211_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*10 + 10, v_printLibDir_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*10 + 11, v_useStdin_2213_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*10 + 12, v_onlyDeps_2214_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*10 + 13, v_onlySrcDeps_2215_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*10 + 14, v_depsJson_2216_);
lean_ctor_set_uint32(v_reuseFailAlloc_2241_, sizeof(void*)*10, v_trustLevel_2218_);
lean_ctor_set_uint32(v_reuseFailAlloc_2241_, sizeof(void*)*10 + 4, v_numThreads_2219_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*10 + 15, v_jsonOutput_2226_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*10 + 16, v_printStats_2228_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*10 + 17, v_run_2229_);
v___x_2237_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
lean_object* v___x_2239_; 
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2237_);
v___x_2239_ = v___x_2189_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
lean_dec(v___x_2194_);
lean_del_object(v___x_2189_);
lean_dec(v_a_2187_);
lean_dec_ref(v_opts_938_);
v___x_2243_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28));
v___x_2244_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2243_);
lean_dec_ref(v___x_2244_);
goto v___jp_978_;
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_dec_ref(v_opts_938_);
v_a_2246_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2246_);
lean_dec_ref(v___x_2186_);
v___x_2250_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2251_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2250_);
lean_dec_ref(v___x_2251_);
goto v___jp_2247_;
v___jp_2247_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_io_error_to_string(v_a_2246_);
v___x_2249_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2248_);
lean_dec_ref(v___x_2249_);
goto v___jp_975_;
}
}
}
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2253_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2252_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2291_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2291_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2291_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_leanOpts_2258_; lean_object* v_forwardedArgs_2259_; uint8_t v_component_2260_; uint8_t v_printPrefix_2261_; uint8_t v_printLibDir_2262_; uint8_t v_useStdin_2263_; uint8_t v_onlyDeps_2264_; uint8_t v_onlySrcDeps_2265_; uint8_t v_depsJson_2266_; lean_object* v_opts_2267_; uint32_t v_trustLevel_2268_; uint32_t v_numThreads_2269_; lean_object* v_rootDir_x3f_2270_; lean_object* v_setupFileName_x3f_2271_; lean_object* v_oleanFileName_x3f_2272_; lean_object* v_ileanFileName_x3f_2273_; lean_object* v_cFileName_x3f_2274_; uint8_t v_jsonOutput_2275_; lean_object* v_errorOnKinds_2276_; uint8_t v_printStats_2277_; uint8_t v_run_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2289_; 
v_leanOpts_2258_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_2259_ = lean_ctor_get(v_opts_938_, 1);
v_component_2260_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_2261_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_2262_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_2263_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_2264_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2265_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_2266_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_2267_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_2268_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_2269_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2270_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_2271_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_2272_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_2273_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_2274_ = lean_ctor_get(v_opts_938_, 7);
v_jsonOutput_2275_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_2276_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_2277_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_2278_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; 
v_unused_2290_ = lean_ctor_get(v_opts_938_, 8);
lean_dec(v_unused_2290_);
v___x_2280_ = v_opts_938_;
v_isShared_2281_ = v_isSharedCheck_2289_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_errorOnKinds_2276_);
lean_inc(v_cFileName_x3f_2274_);
lean_inc(v_ileanFileName_x3f_2273_);
lean_inc(v_oleanFileName_x3f_2272_);
lean_inc(v_setupFileName_x3f_2271_);
lean_inc(v_rootDir_x3f_2270_);
lean_inc(v_opts_2267_);
lean_inc(v_forwardedArgs_2259_);
lean_inc(v_leanOpts_2258_);
lean_dec(v_opts_938_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2289_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2282_, 0, v_a_2254_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 8, v___x_2282_);
v___x_2284_ = v___x_2280_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_leanOpts_2258_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_forwardedArgs_2259_);
lean_ctor_set(v_reuseFailAlloc_2288_, 2, v_opts_2267_);
lean_ctor_set(v_reuseFailAlloc_2288_, 3, v_rootDir_x3f_2270_);
lean_ctor_set(v_reuseFailAlloc_2288_, 4, v_setupFileName_x3f_2271_);
lean_ctor_set(v_reuseFailAlloc_2288_, 5, v_oleanFileName_x3f_2272_);
lean_ctor_set(v_reuseFailAlloc_2288_, 6, v_ileanFileName_x3f_2273_);
lean_ctor_set(v_reuseFailAlloc_2288_, 7, v_cFileName_x3f_2274_);
lean_ctor_set(v_reuseFailAlloc_2288_, 8, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2288_, 9, v_errorOnKinds_2276_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*10 + 8, v_component_2260_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*10 + 9, v_printPrefix_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*10 + 10, v_printLibDir_2262_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*10 + 11, v_useStdin_2263_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*10 + 12, v_onlyDeps_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*10 + 13, v_onlySrcDeps_2265_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*10 + 14, v_depsJson_2266_);
lean_ctor_set_uint32(v_reuseFailAlloc_2288_, sizeof(void*)*10, v_trustLevel_2268_);
lean_ctor_set_uint32(v_reuseFailAlloc_2288_, sizeof(void*)*10 + 4, v_numThreads_2269_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*10 + 15, v_jsonOutput_2275_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*10 + 16, v_printStats_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*10 + 17, v_run_2278_);
v___x_2284_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2286_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v___x_2284_);
v___x_2286_ = v___x_2256_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_dec_ref(v_opts_938_);
v_a_2292_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2292_);
lean_dec_ref(v___x_2253_);
v___x_2296_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2297_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2296_);
lean_dec_ref(v___x_2297_);
goto v___jp_2293_;
v___jp_2293_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_io_error_to_string(v_a_2292_);
v___x_2295_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2294_);
lean_dec_ref(v___x_2295_);
goto v___jp_1117_;
}
}
}
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2299_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2298_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2337_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2337_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2337_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v_leanOpts_2304_; lean_object* v_forwardedArgs_2305_; uint8_t v_component_2306_; uint8_t v_printPrefix_2307_; uint8_t v_printLibDir_2308_; uint8_t v_useStdin_2309_; uint8_t v_onlyDeps_2310_; uint8_t v_onlySrcDeps_2311_; uint8_t v_depsJson_2312_; lean_object* v_opts_2313_; uint32_t v_trustLevel_2314_; uint32_t v_numThreads_2315_; lean_object* v_rootDir_x3f_2316_; lean_object* v_setupFileName_x3f_2317_; lean_object* v_oleanFileName_x3f_2318_; lean_object* v_ileanFileName_x3f_2319_; lean_object* v_bcFileName_x3f_2320_; uint8_t v_jsonOutput_2321_; lean_object* v_errorOnKinds_2322_; uint8_t v_printStats_2323_; uint8_t v_run_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2335_; 
v_leanOpts_2304_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_2305_ = lean_ctor_get(v_opts_938_, 1);
v_component_2306_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_2307_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_2308_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_2309_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_2310_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2311_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_2312_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_2313_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_2314_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_numThreads_2315_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2316_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_2317_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_2318_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_2319_ = lean_ctor_get(v_opts_938_, 6);
v_bcFileName_x3f_2320_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_2321_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_2322_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_2323_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_2324_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_2335_ == 0)
{
lean_object* v_unused_2336_; 
v_unused_2336_ = lean_ctor_get(v_opts_938_, 7);
lean_dec(v_unused_2336_);
v___x_2326_ = v_opts_938_;
v_isShared_2327_ = v_isSharedCheck_2335_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_errorOnKinds_2322_);
lean_inc(v_bcFileName_x3f_2320_);
lean_inc(v_ileanFileName_x3f_2319_);
lean_inc(v_oleanFileName_x3f_2318_);
lean_inc(v_setupFileName_x3f_2317_);
lean_inc(v_rootDir_x3f_2316_);
lean_inc(v_opts_2313_);
lean_inc(v_forwardedArgs_2305_);
lean_inc(v_leanOpts_2304_);
lean_dec(v_opts_938_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2335_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_a_2300_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 7, v___x_2328_);
v___x_2330_ = v___x_2326_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_leanOpts_2304_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_forwardedArgs_2305_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_opts_2313_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v_rootDir_x3f_2316_);
lean_ctor_set(v_reuseFailAlloc_2334_, 4, v_setupFileName_x3f_2317_);
lean_ctor_set(v_reuseFailAlloc_2334_, 5, v_oleanFileName_x3f_2318_);
lean_ctor_set(v_reuseFailAlloc_2334_, 6, v_ileanFileName_x3f_2319_);
lean_ctor_set(v_reuseFailAlloc_2334_, 7, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2334_, 8, v_bcFileName_x3f_2320_);
lean_ctor_set(v_reuseFailAlloc_2334_, 9, v_errorOnKinds_2322_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*10 + 8, v_component_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*10 + 9, v_printPrefix_2307_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*10 + 10, v_printLibDir_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*10 + 11, v_useStdin_2309_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*10 + 12, v_onlyDeps_2310_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*10 + 13, v_onlySrcDeps_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*10 + 14, v_depsJson_2312_);
lean_ctor_set_uint32(v_reuseFailAlloc_2334_, sizeof(void*)*10, v_trustLevel_2314_);
lean_ctor_set_uint32(v_reuseFailAlloc_2334_, sizeof(void*)*10 + 4, v_numThreads_2315_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*10 + 15, v_jsonOutput_2321_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*10 + 16, v_printStats_2323_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*10 + 17, v_run_2324_);
v___x_2330_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2332_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2330_);
v___x_2332_ = v___x_2302_;
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
lean_dec_ref(v_opts_938_);
v_a_2338_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2338_);
lean_dec_ref(v___x_2299_);
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
goto v___jp_969_;
}
}
}
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec(v_optArg_x3f_940_);
lean_dec_ref(v_opts_938_);
v___x_2344_ = l___private_Lean_Shell_0__Lean_featuresString;
v___x_2345_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2344_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2353_; 
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2353_ == 0)
{
lean_object* v_unused_2354_; 
v_unused_2354_ = lean_ctor_get(v___x_2345_, 0);
lean_dec(v_unused_2354_);
v___x_2347_ = v___x_2345_;
v_isShared_2348_ = v_isSharedCheck_2353_;
goto v_resetjp_2346_;
}
else
{
lean_dec(v___x_2345_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2353_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2349_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2348_ == 0)
{
lean_ctor_set_tag(v___x_2347_, 1);
lean_ctor_set(v___x_2347_, 0, v___x_2349_);
v___x_2351_ = v___x_2347_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_a_2355_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2355_);
lean_dec_ref(v___x_2345_);
v___x_2359_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2360_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2359_);
lean_dec_ref(v___x_2360_);
goto v___jp_2356_;
v___jp_2356_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_io_error_to_string(v_a_2355_);
v___x_2358_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2357_);
lean_dec_ref(v___x_2358_);
goto v___jp_1123_;
}
}
}
}
else
{
lean_object* v___x_2361_; 
lean_dec(v_optArg_x3f_940_);
lean_dec_ref(v_opts_938_);
v___x_2361_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1147_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2369_; 
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2369_ == 0)
{
lean_object* v_unused_2370_; 
v_unused_2370_ = lean_ctor_get(v___x_2361_, 0);
lean_dec(v_unused_2370_);
v___x_2363_ = v___x_2361_;
v_isShared_2364_ = v_isSharedCheck_2369_;
goto v_resetjp_2362_;
}
else
{
lean_dec(v___x_2361_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2369_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2365_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2364_ == 0)
{
lean_ctor_set_tag(v___x_2363_, 1);
lean_ctor_set(v___x_2363_, 0, v___x_2365_);
v___x_2367_ = v___x_2363_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v_a_2371_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2371_);
lean_dec_ref(v___x_2361_);
v___x_2375_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2376_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2375_);
lean_dec_ref(v___x_2376_);
goto v___jp_2372_;
v___jp_2372_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_io_error_to_string(v_a_2371_);
v___x_2374_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2373_);
lean_dec_ref(v___x_2374_);
goto v___jp_963_;
}
}
}
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_dec(v_optArg_x3f_940_);
lean_dec_ref(v_opts_938_);
v___x_2377_ = l_Lean_githash;
v___x_2378_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2377_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2386_; 
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2386_ == 0)
{
lean_object* v_unused_2387_; 
v_unused_2387_ = lean_ctor_get(v___x_2378_, 0);
lean_dec(v_unused_2387_);
v___x_2380_ = v___x_2378_;
v_isShared_2381_ = v_isSharedCheck_2386_;
goto v_resetjp_2379_;
}
else
{
lean_dec(v___x_2378_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2386_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2382_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2381_ == 0)
{
lean_ctor_set_tag(v___x_2380_, 1);
lean_ctor_set(v___x_2380_, 0, v___x_2382_);
v___x_2384_ = v___x_2380_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_a_2388_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2388_);
lean_dec_ref(v___x_2378_);
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
goto v___jp_1129_;
}
}
}
}
else
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
lean_dec(v_optArg_x3f_940_);
lean_dec_ref(v_opts_938_);
v___x_2394_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2395_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2394_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2403_; 
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; 
v_unused_2404_ = lean_ctor_get(v___x_2395_, 0);
lean_dec(v_unused_2404_);
v___x_2397_ = v___x_2395_;
v_isShared_2398_ = v_isSharedCheck_2403_;
goto v_resetjp_2396_;
}
else
{
lean_dec(v___x_2395_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2403_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2401_; 
v___x_2399_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2398_ == 0)
{
lean_ctor_set_tag(v___x_2397_, 1);
lean_ctor_set(v___x_2397_, 0, v___x_2399_);
v___x_2401_ = v___x_2397_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v_a_2405_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2405_);
lean_dec_ref(v___x_2395_);
v___x_2409_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2410_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2409_);
lean_dec_ref(v___x_2410_);
goto v___jp_2406_;
v___jp_2406_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_io_error_to_string(v_a_2405_);
v___x_2408_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2407_);
lean_dec_ref(v___x_2408_);
goto v___jp_957_;
}
}
}
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
lean_dec(v_optArg_x3f_940_);
lean_dec_ref(v_opts_938_);
v___x_2411_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2412_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2411_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2420_; 
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v___x_2412_, 0);
lean_dec(v_unused_2421_);
v___x_2414_ = v___x_2412_;
v_isShared_2415_ = v_isSharedCheck_2420_;
goto v_resetjp_2413_;
}
else
{
lean_dec(v___x_2412_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2420_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2416_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2415_ == 0)
{
lean_ctor_set_tag(v___x_2414_, 1);
lean_ctor_set(v___x_2414_, 0, v___x_2416_);
v___x_2418_ = v___x_2414_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v_a_2422_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2422_);
lean_dec_ref(v___x_2412_);
v___x_2426_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2427_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2426_);
lean_dec_ref(v___x_2427_);
goto v___jp_2423_;
v___jp_2423_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = lean_io_error_to_string(v_a_2422_);
v___x_2425_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2424_);
lean_dec_ref(v___x_2425_);
goto v___jp_1135_;
}
}
}
}
else
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2429_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2428_, v_optArg_x3f_940_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2480_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2480_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2480_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2434_ = lean_unsigned_to_nat(0u);
v___x_2435_ = lean_string_utf8_byte_size(v_a_2430_);
lean_inc(v_a_2430_);
v___x_2436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2436_, 0, v_a_2430_);
lean_ctor_set(v___x_2436_, 1, v___x_2434_);
lean_ctor_set(v___x_2436_, 2, v___x_2435_);
v___x_2437_ = l_String_Slice_toNat_x3f(v___x_2436_);
lean_dec_ref(v___x_2436_);
if (lean_obj_tag(v___x_2437_) == 1)
{
lean_object* v_val_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v_val_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_val_2438_);
lean_dec_ref(v___x_2437_);
v___x_2439_ = lean_cstr_to_nat("4294967296");
v___x_2440_ = lean_nat_dec_lt(v_val_2438_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_dec(v_val_2438_);
lean_del_object(v___x_2432_);
lean_dec(v_a_2430_);
lean_dec_ref(v_opts_938_);
v___x_2441_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2442_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2441_);
lean_dec_ref(v___x_2442_);
goto v___jp_951_;
}
else
{
lean_object* v_leanOpts_2443_; lean_object* v_forwardedArgs_2444_; uint8_t v_component_2445_; uint8_t v_printPrefix_2446_; uint8_t v_printLibDir_2447_; uint8_t v_useStdin_2448_; uint8_t v_onlyDeps_2449_; uint8_t v_onlySrcDeps_2450_; uint8_t v_depsJson_2451_; lean_object* v_opts_2452_; uint32_t v_trustLevel_2453_; lean_object* v_rootDir_x3f_2454_; lean_object* v_setupFileName_x3f_2455_; lean_object* v_oleanFileName_x3f_2456_; lean_object* v_ileanFileName_x3f_2457_; lean_object* v_cFileName_x3f_2458_; lean_object* v_bcFileName_x3f_2459_; uint8_t v_jsonOutput_2460_; lean_object* v_errorOnKinds_2461_; uint8_t v_printStats_2462_; uint8_t v_run_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2477_; 
v_leanOpts_2443_ = lean_ctor_get(v_opts_938_, 0);
v_forwardedArgs_2444_ = lean_ctor_get(v_opts_938_, 1);
v_component_2445_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 8);
v_printPrefix_2446_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 9);
v_printLibDir_2447_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 10);
v_useStdin_2448_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 11);
v_onlyDeps_2449_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2450_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 13);
v_depsJson_2451_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 14);
v_opts_2452_ = lean_ctor_get(v_opts_938_, 2);
v_trustLevel_2453_ = lean_ctor_get_uint32(v_opts_938_, sizeof(void*)*10);
v_rootDir_x3f_2454_ = lean_ctor_get(v_opts_938_, 3);
v_setupFileName_x3f_2455_ = lean_ctor_get(v_opts_938_, 4);
v_oleanFileName_x3f_2456_ = lean_ctor_get(v_opts_938_, 5);
v_ileanFileName_x3f_2457_ = lean_ctor_get(v_opts_938_, 6);
v_cFileName_x3f_2458_ = lean_ctor_get(v_opts_938_, 7);
v_bcFileName_x3f_2459_ = lean_ctor_get(v_opts_938_, 8);
v_jsonOutput_2460_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 15);
v_errorOnKinds_2461_ = lean_ctor_get(v_opts_938_, 9);
v_printStats_2462_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 16);
v_run_2463_ = lean_ctor_get_uint8(v_opts_938_, sizeof(void*)*10 + 17);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_opts_938_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2465_ = v_opts_938_;
v_isShared_2466_ = v_isSharedCheck_2477_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_errorOnKinds_2461_);
lean_inc(v_bcFileName_x3f_2459_);
lean_inc(v_cFileName_x3f_2458_);
lean_inc(v_ileanFileName_x3f_2457_);
lean_inc(v_oleanFileName_x3f_2456_);
lean_inc(v_setupFileName_x3f_2455_);
lean_inc(v_rootDir_x3f_2454_);
lean_inc(v_opts_2452_);
lean_inc(v_forwardedArgs_2444_);
lean_inc(v_leanOpts_2443_);
lean_dec(v_opts_938_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2477_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
uint32_t v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2467_ = lean_uint32_of_nat(v_val_2438_);
lean_dec(v_val_2438_);
v___x_2468_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2469_ = lean_string_append(v___x_2468_, v_a_2430_);
lean_dec(v_a_2430_);
v___x_2470_ = lean_array_push(v_forwardedArgs_2444_, v___x_2469_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 1, v___x_2470_);
v___x_2472_ = v___x_2465_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_leanOpts_2443_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v_opts_2452_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v_rootDir_x3f_2454_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v_setupFileName_x3f_2455_);
lean_ctor_set(v_reuseFailAlloc_2476_, 5, v_oleanFileName_x3f_2456_);
lean_ctor_set(v_reuseFailAlloc_2476_, 6, v_ileanFileName_x3f_2457_);
lean_ctor_set(v_reuseFailAlloc_2476_, 7, v_cFileName_x3f_2458_);
lean_ctor_set(v_reuseFailAlloc_2476_, 8, v_bcFileName_x3f_2459_);
lean_ctor_set(v_reuseFailAlloc_2476_, 9, v_errorOnKinds_2461_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*10 + 8, v_component_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*10 + 9, v_printPrefix_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*10 + 10, v_printLibDir_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*10 + 11, v_useStdin_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*10 + 12, v_onlyDeps_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*10 + 13, v_onlySrcDeps_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*10 + 14, v_depsJson_2451_);
lean_ctor_set_uint32(v_reuseFailAlloc_2476_, sizeof(void*)*10, v_trustLevel_2453_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*10 + 15, v_jsonOutput_2460_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*10 + 16, v_printStats_2462_);
lean_ctor_set_uint8(v_reuseFailAlloc_2476_, sizeof(void*)*10 + 17, v_run_2463_);
v___x_2472_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2474_; 
lean_ctor_set_uint32(v___x_2472_, sizeof(void*)*10 + 4, v___x_2467_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2472_);
v___x_2474_ = v___x_2432_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_dec(v___x_2437_);
lean_del_object(v___x_2432_);
lean_dec(v_a_2430_);
lean_dec_ref(v_opts_938_);
v___x_2478_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2479_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2478_);
lean_dec_ref(v___x_2479_);
goto v___jp_948_;
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref(v_opts_938_);
v_a_2481_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2481_);
lean_dec_ref(v___x_2429_);
v___x_2485_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2486_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2485_);
lean_dec_ref(v___x_2486_);
goto v___jp_2482_;
v___jp_2482_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_io_error_to_string(v_a_2481_);
v___x_2484_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2483_);
lean_dec_ref(v___x_2484_);
goto v___jp_945_;
}
}
}
}
else
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
lean_dec(v_optArg_x3f_940_);
v___x_2487_ = lean_internal_set_exit_on_panic(v___x_1139_);
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_opts_938_);
return v___x_2488_;
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
v___x_946_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_947_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_946_);
lean_dec_ref(v___x_947_);
goto v___jp_942_;
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
v___x_976_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_977_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_976_);
lean_dec_ref(v___x_977_);
goto v___jp_972_;
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
v___x_994_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_995_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_994_);
lean_dec_ref(v___x_995_);
goto v___jp_990_;
}
v___jp_996_:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
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
v___x_1003_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1004_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1003_);
lean_dec_ref(v___x_1004_);
goto v___jp_999_;
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
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_io_error_to_string(v___y_1042_);
v___x_1044_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1043_);
lean_dec_ref(v___x_1044_);
goto v___jp_1038_;
}
v___jp_1045_:
{
uint8_t v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = 1;
v___x_1047_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1046_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1055_; 
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; 
v_unused_1056_ = lean_ctor_get(v___x_1047_, 0);
lean_dec(v_unused_1056_);
v___x_1049_ = v___x_1047_;
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
else
{
lean_dec(v___x_1047_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1051_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 1);
lean_ctor_set(v___x_1049_, 0, v___x_1051_);
v___x_1053_ = v___x_1049_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_a_1057_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1057_);
lean_dec_ref(v___x_1047_);
v___x_1058_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1059_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1058_);
lean_dec_ref(v___x_1059_);
v___y_1042_ = v_a_1057_;
goto v___jp_1041_;
}
}
v___jp_1060_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
v___x_1062_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1061_);
lean_dec_ref(v___x_1062_);
goto v___jp_1045_;
}
v___jp_1063_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
v___jp_1066_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1068_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1067_);
lean_dec_ref(v___x_1068_);
goto v___jp_1063_;
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
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
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
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
return v___x_1104_;
}
v___jp_1105_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1107_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1106_);
lean_dec_ref(v___x_1107_);
goto v___jp_1102_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2489_, lean_object* v_opt_2490_, lean_object* v_optArg_x3f_2491_, lean_object* v_a_2492_){
_start:
{
uint32_t v_opt_boxed_2493_; lean_object* v_res_2494_; 
v_opt_boxed_2493_ = lean_unbox_uint32(v_opt_2490_);
lean_dec(v_opt_2490_);
v_res_2494_ = lean_shell_options_process(v_opts_2489_, v_opt_boxed_2493_, v_optArg_x3f_2491_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_opts_2495_, lean_object* v_opt_2496_){
_start:
{
lean_object* v_name_2497_; lean_object* v_defValue_2498_; lean_object* v_map_2499_; lean_object* v___x_2500_; 
v_name_2497_ = lean_ctor_get(v_opt_2496_, 0);
v_defValue_2498_ = lean_ctor_get(v_opt_2496_, 1);
v_map_2499_ = lean_ctor_get(v_opts_2495_, 0);
v___x_2500_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2499_, v_name_2497_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_inc(v_defValue_2498_);
return v_defValue_2498_;
}
else
{
lean_object* v_val_2501_; 
v_val_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_val_2501_);
lean_dec_ref(v___x_2500_);
if (lean_obj_tag(v_val_2501_) == 3)
{
lean_object* v_v_2502_; 
v_v_2502_ = lean_ctor_get(v_val_2501_, 0);
lean_inc(v_v_2502_);
lean_dec_ref(v_val_2501_);
return v_v_2502_;
}
else
{
lean_dec(v_val_2501_);
lean_inc(v_defValue_2498_);
return v_defValue_2498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_opts_2503_, lean_object* v_opt_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_opts_2503_, v_opt_2504_);
lean_dec_ref(v_opt_2504_);
lean_dec_ref(v_opts_2503_);
return v_res_2505_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2508_ = lean_string_utf8_byte_size(v___x_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2509_){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v___x_2510_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2511_ = lean_string_utf8_byte_size(v_s_2509_);
v___x_2512_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1);
v___x_2513_ = lean_nat_dec_le(v___x_2512_, v___x_2511_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; 
lean_dec_ref(v_s_2509_);
v___x_2514_ = lean_box(0);
return v___x_2514_;
}
else
{
lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2515_ = lean_unsigned_to_nat(0u);
v___x_2516_ = lean_string_memcmp(v_s_2509_, v___x_2510_, v___x_2515_, v___x_2515_, v___x_2512_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; 
lean_dec_ref(v_s_2509_);
v___x_2517_ = lean_box(0);
return v___x_2517_;
}
else
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_inc_ref(v_s_2509_);
v___x_2518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2518_, 0, v_s_2509_);
lean_ctor_set(v___x_2518_, 1, v___x_2515_);
lean_ctor_set(v___x_2518_, 2, v___x_2511_);
v___x_2519_ = l_String_Slice_pos_x21(v___x_2518_, v___x_2512_);
lean_dec_ref(v___x_2518_);
v___x_2520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2520_, 0, v_s_2509_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
lean_ctor_set(v___x_2520_, 2, v___x_2511_);
v___x_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2522_, lean_object* v_pat_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2522_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2525_, lean_object* v_pat_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2525_, v_pat_2526_);
lean_dec_ref(v_pat_2526_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v___x_2529_, lean_object* v___x_2530_, lean_object* v_mainModuleName_2531_, lean_object* v_a_2532_, lean_object* v___x_2533_, lean_object* v_fileName_2534_, lean_object* v___x_2535_, lean_object* v___x_2536_, lean_object* v___x_2537_, lean_object* v___x_2538_, lean_object* v___x_2539_, lean_object* v___x_2540_, lean_object* v___x_2541_, lean_object* v___x_2542_, uint8_t v_printLibDir_2543_){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v_env_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; lean_object* v_fileName_2554_; lean_object* v_fileMap_2555_; lean_object* v_currRecDepth_2556_; lean_object* v_ref_2557_; lean_object* v_currNamespace_2558_; lean_object* v_openDecls_2559_; lean_object* v_initHeartbeats_2560_; lean_object* v_maxHeartbeats_2561_; lean_object* v_quotContext_2562_; lean_object* v_currMacroScope_2563_; lean_object* v_cancelTk_x3f_2564_; uint8_t v_suppressElabErrors_2565_; lean_object* v_inheritedTraceOptions_2566_; lean_object* v___y_2567_; uint8_t v___y_2596_; uint8_t v___x_2616_; 
v___x_2545_ = lean_io_get_num_heartbeats();
v___x_2546_ = lean_st_mk_ref(v___x_2529_);
v___x_2547_ = l_Lean_inheritedTraceOptions;
v___x_2548_ = lean_st_ref_get(v___x_2547_);
v___x_2549_ = lean_st_ref_get(v___x_2546_);
v_env_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc_ref(v_env_2550_);
lean_dec(v___x_2549_);
v___x_2551_ = l_Lean_diagnostics;
v___x_2552_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v___x_2530_, v___x_2551_);
v___x_2616_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2550_);
lean_dec_ref(v_env_2550_);
if (v___x_2616_ == 0)
{
if (v___x_2552_ == 0)
{
lean_dec_ref(v___x_2533_);
lean_inc(v___x_2546_);
lean_inc(v___x_2538_);
v_fileName_2554_ = v_fileName_2534_;
v_fileMap_2555_ = v___x_2535_;
v_currRecDepth_2556_ = v___x_2536_;
v_ref_2557_ = v___x_2537_;
v_currNamespace_2558_ = v___x_2538_;
v_openDecls_2559_ = v___x_2539_;
v_initHeartbeats_2560_ = v___x_2545_;
v_maxHeartbeats_2561_ = v___x_2540_;
v_quotContext_2562_ = v___x_2538_;
v_currMacroScope_2563_ = v___x_2541_;
v_cancelTk_x3f_2564_ = v___x_2542_;
v_suppressElabErrors_2565_ = v_printLibDir_2543_;
v_inheritedTraceOptions_2566_ = v___x_2548_;
v___y_2567_ = v___x_2546_;
goto v___jp_2553_;
}
else
{
v___y_2596_ = v___x_2616_;
goto v___jp_2595_;
}
}
else
{
v___y_2596_ = v___x_2552_;
goto v___jp_2595_;
}
v___jp_2553_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2568_ = l_Lean_maxRecDepth;
v___x_2569_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_2530_, v___x_2568_);
v___x_2570_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2570_, 0, v_fileName_2554_);
lean_ctor_set(v___x_2570_, 1, v_fileMap_2555_);
lean_ctor_set(v___x_2570_, 2, v___x_2530_);
lean_ctor_set(v___x_2570_, 3, v_currRecDepth_2556_);
lean_ctor_set(v___x_2570_, 4, v___x_2569_);
lean_ctor_set(v___x_2570_, 5, v_ref_2557_);
lean_ctor_set(v___x_2570_, 6, v_currNamespace_2558_);
lean_ctor_set(v___x_2570_, 7, v_openDecls_2559_);
lean_ctor_set(v___x_2570_, 8, v_initHeartbeats_2560_);
lean_ctor_set(v___x_2570_, 9, v_maxHeartbeats_2561_);
lean_ctor_set(v___x_2570_, 10, v_quotContext_2562_);
lean_ctor_set(v___x_2570_, 11, v_currMacroScope_2563_);
lean_ctor_set(v___x_2570_, 12, v_cancelTk_x3f_2564_);
lean_ctor_set(v___x_2570_, 13, v_inheritedTraceOptions_2566_);
lean_ctor_set_uint8(v___x_2570_, sizeof(void*)*14, v___x_2552_);
lean_ctor_set_uint8(v___x_2570_, sizeof(void*)*14 + 1, v_suppressElabErrors_2565_);
v___x_2571_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2531_, v___x_2570_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___x_2570_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref(v___x_2571_);
v___x_2573_ = lean_st_ref_get(v___x_2546_);
lean_dec(v___x_2546_);
lean_dec(v___x_2573_);
v___x_2574_ = lean_string_to_utf8(v_a_2572_);
lean_dec(v_a_2572_);
v___x_2575_ = lean_io_prim_handle_write(v_a_2532_, v___x_2574_);
lean_dec_ref(v___x_2574_);
return v___x_2575_;
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2594_; 
lean_dec(v___x_2546_);
v_a_2576_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2578_ = v___x_2571_;
v_isShared_2579_ = v_isSharedCheck_2594_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2571_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2594_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
if (lean_obj_tag(v_a_2576_) == 0)
{
lean_object* v_msg_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2584_; 
v_msg_2580_ = lean_ctor_get(v_a_2576_, 1);
lean_inc_ref(v_msg_2580_);
lean_dec_ref(v_a_2576_);
v___x_2581_ = l_Lean_MessageData_toString(v_msg_2580_);
v___x_2582_ = lean_mk_io_user_error(v___x_2581_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v___x_2582_);
v___x_2584_ = v___x_2578_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
else
{
lean_object* v_id_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2592_; 
v_id_2586_ = lean_ctor_get(v_a_2576_, 0);
lean_inc(v_id_2586_);
lean_dec_ref(v_a_2576_);
v___x_2587_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0));
v___x_2588_ = l_Nat_reprFast(v_id_2586_);
v___x_2589_ = lean_string_append(v___x_2587_, v___x_2588_);
lean_dec_ref(v___x_2588_);
v___x_2590_ = lean_mk_io_user_error(v___x_2589_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v___x_2590_);
v___x_2592_ = v___x_2578_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
}
v___jp_2595_:
{
if (v___y_2596_ == 0)
{
lean_object* v___x_2597_; lean_object* v_env_2598_; lean_object* v_nextMacroScope_2599_; lean_object* v_ngen_2600_; lean_object* v_auxDeclNGen_2601_; lean_object* v_traceState_2602_; lean_object* v_messages_2603_; lean_object* v_infoState_2604_; lean_object* v_snapshotTasks_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2614_; 
v___x_2597_ = lean_st_ref_take(v___x_2546_);
v_env_2598_ = lean_ctor_get(v___x_2597_, 0);
v_nextMacroScope_2599_ = lean_ctor_get(v___x_2597_, 1);
v_ngen_2600_ = lean_ctor_get(v___x_2597_, 2);
v_auxDeclNGen_2601_ = lean_ctor_get(v___x_2597_, 3);
v_traceState_2602_ = lean_ctor_get(v___x_2597_, 4);
v_messages_2603_ = lean_ctor_get(v___x_2597_, 6);
v_infoState_2604_ = lean_ctor_get(v___x_2597_, 7);
v_snapshotTasks_2605_ = lean_ctor_get(v___x_2597_, 8);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v___x_2597_, 5);
lean_dec(v_unused_2615_);
v___x_2607_ = v___x_2597_;
v_isShared_2608_ = v_isSharedCheck_2614_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_snapshotTasks_2605_);
lean_inc(v_infoState_2604_);
lean_inc(v_messages_2603_);
lean_inc(v_traceState_2602_);
lean_inc(v_auxDeclNGen_2601_);
lean_inc(v_ngen_2600_);
lean_inc(v_nextMacroScope_2599_);
lean_inc(v_env_2598_);
lean_dec(v___x_2597_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2614_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2609_ = l_Lean_Kernel_enableDiag(v_env_2598_, v___x_2552_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 5, v___x_2533_);
lean_ctor_set(v___x_2607_, 0, v___x_2609_);
v___x_2611_ = v___x_2607_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2609_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_nextMacroScope_2599_);
lean_ctor_set(v_reuseFailAlloc_2613_, 2, v_ngen_2600_);
lean_ctor_set(v_reuseFailAlloc_2613_, 3, v_auxDeclNGen_2601_);
lean_ctor_set(v_reuseFailAlloc_2613_, 4, v_traceState_2602_);
lean_ctor_set(v_reuseFailAlloc_2613_, 5, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2613_, 6, v_messages_2603_);
lean_ctor_set(v_reuseFailAlloc_2613_, 7, v_infoState_2604_);
lean_ctor_set(v_reuseFailAlloc_2613_, 8, v_snapshotTasks_2605_);
v___x_2611_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_st_ref_set(v___x_2546_, v___x_2611_);
lean_inc(v___x_2546_);
lean_inc(v___x_2538_);
v_fileName_2554_ = v_fileName_2534_;
v_fileMap_2555_ = v___x_2535_;
v_currRecDepth_2556_ = v___x_2536_;
v_ref_2557_ = v___x_2537_;
v_currNamespace_2558_ = v___x_2538_;
v_openDecls_2559_ = v___x_2539_;
v_initHeartbeats_2560_ = v___x_2545_;
v_maxHeartbeats_2561_ = v___x_2540_;
v_quotContext_2562_ = v___x_2538_;
v_currMacroScope_2563_ = v___x_2541_;
v_cancelTk_x3f_2564_ = v___x_2542_;
v_suppressElabErrors_2565_ = v_printLibDir_2543_;
v_inheritedTraceOptions_2566_ = v___x_2548_;
v___y_2567_ = v___x_2546_;
goto v___jp_2553_;
}
}
}
else
{
lean_dec_ref(v___x_2533_);
lean_inc(v___x_2546_);
lean_inc(v___x_2538_);
v_fileName_2554_ = v_fileName_2534_;
v_fileMap_2555_ = v___x_2535_;
v_currRecDepth_2556_ = v___x_2536_;
v_ref_2557_ = v___x_2537_;
v_currNamespace_2558_ = v___x_2538_;
v_openDecls_2559_ = v___x_2539_;
v_initHeartbeats_2560_ = v___x_2545_;
v_maxHeartbeats_2561_ = v___x_2540_;
v_quotContext_2562_ = v___x_2538_;
v_currMacroScope_2563_ = v___x_2541_;
v_cancelTk_x3f_2564_ = v___x_2542_;
v_suppressElabErrors_2565_ = v_printLibDir_2543_;
v_inheritedTraceOptions_2566_ = v___x_2548_;
v___y_2567_ = v___x_2546_;
goto v___jp_2553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* v___x_2617_, lean_object* v___x_2618_, lean_object* v_mainModuleName_2619_, lean_object* v_a_2620_, lean_object* v___x_2621_, lean_object* v_fileName_2622_, lean_object* v___x_2623_, lean_object* v___x_2624_, lean_object* v___x_2625_, lean_object* v___x_2626_, lean_object* v___x_2627_, lean_object* v___x_2628_, lean_object* v___x_2629_, lean_object* v___x_2630_, lean_object* v_printLibDir_2631_, lean_object* v___y_2632_){
_start:
{
uint8_t v_printLibDir_boxed_2633_; lean_object* v_res_2634_; 
v_printLibDir_boxed_2633_ = lean_unbox(v_printLibDir_2631_);
v_res_2634_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v___x_2617_, v___x_2618_, v_mainModuleName_2619_, v_a_2620_, v___x_2621_, v_fileName_2622_, v___x_2623_, v___x_2624_, v___x_2625_, v___x_2626_, v___x_2627_, v___x_2628_, v___x_2629_, v___x_2630_, v_printLibDir_boxed_2633_);
lean_dec(v_a_2620_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_2635_, lean_object* v_a_2636_, lean_object* v_b_2637_){
_start:
{
lean_object* v_str_2638_; lean_object* v_startInclusive_2639_; lean_object* v_endExclusive_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v_str_2638_ = lean_ctor_get(v_val_2635_, 0);
v_startInclusive_2639_ = lean_ctor_get(v_val_2635_, 1);
v_endExclusive_2640_ = lean_ctor_get(v_val_2635_, 2);
v___x_2641_ = lean_nat_sub(v_endExclusive_2640_, v_startInclusive_2639_);
v___x_2642_ = lean_nat_dec_eq(v_a_2636_, v___x_2641_);
lean_dec(v___x_2641_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; uint32_t v___x_2644_; uint32_t v___x_2645_; uint8_t v___x_2646_; 
v___x_2643_ = lean_nat_add(v_startInclusive_2639_, v_a_2636_);
v___x_2644_ = lean_string_utf8_get_fast(v_str_2638_, v___x_2643_);
v___x_2645_ = 10;
v___x_2646_ = lean_uint32_dec_eq(v___x_2644_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_dec(v_a_2636_);
v___x_2647_ = lean_box(0);
v___x_2648_ = lean_string_utf8_next_fast(v_str_2638_, v___x_2643_);
lean_dec(v___x_2643_);
v___x_2649_ = lean_nat_sub(v___x_2648_, v_startInclusive_2639_);
v_a_2636_ = v___x_2649_;
v_b_2637_ = v___x_2647_;
goto _start;
}
else
{
lean_object* v___x_2651_; 
lean_dec(v___x_2643_);
v___x_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2651_, 0, v_a_2636_);
return v___x_2651_;
}
}
else
{
lean_dec(v_a_2636_);
lean_inc(v_b_2637_);
return v_b_2637_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_2652_, lean_object* v_a_2653_, lean_object* v_b_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_2652_, v_a_2653_, v_b_2654_);
lean_dec(v_b_2654_);
lean_dec_ref(v_val_2652_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_2656_){
_start:
{
uint32_t v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2658_ = 10;
v___x_2659_ = lean_string_push(v_s_2656_, v___x_2658_);
v___x_2660_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_2661_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_s_2664_){
_start:
{
uint32_t v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2666_ = 10;
v___x_2667_ = lean_string_push(v_s_2664_, v___x_2666_);
v___x_2668_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_s_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_s_2669_);
return v_res_2671_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0(void){
_start:
{
lean_object* v___x_2672_; uint8_t v___x_2673_; 
v___x_2672_ = lean_box(0);
v___x_2673_ = lean_internal_has_address_sanitizer(v___x_2672_);
return v___x_2673_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__3(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2676_ = l_Lean_Options_empty;
v___x_2677_ = l_Lean_Core_getMaxHeartbeats(v___x_2676_);
return v___x_2677_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = lean_unsigned_to_nat(1u);
v___x_2679_ = l_Lean_firstFrontendMacroScope;
v___x_2680_ = lean_nat_add(v___x_2679_, v___x_2678_);
return v___x_2680_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9(void){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2691_ = lean_unsigned_to_nat(32u);
v___x_2692_ = lean_mk_empty_array_with_capacity(v___x_2691_);
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
return v___x_2693_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10(void){
_start:
{
size_t v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2694_ = ((size_t)5ULL);
v___x_2695_ = lean_unsigned_to_nat(0u);
v___x_2696_ = lean_unsigned_to_nat(32u);
v___x_2697_ = lean_mk_empty_array_with_capacity(v___x_2696_);
v___x_2698_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9);
v___x_2699_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
lean_ctor_set(v___x_2699_, 1, v___x_2697_);
lean_ctor_set(v___x_2699_, 2, v___x_2695_);
lean_ctor_set(v___x_2699_, 3, v___x_2695_);
lean_ctor_set_usize(v___x_2699_, 4, v___x_2694_);
return v___x_2699_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11(void){
_start:
{
lean_object* v___x_2700_; uint64_t v___x_2701_; lean_object* v___x_2702_; 
v___x_2700_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_2701_ = 0ULL;
v___x_2702_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set_uint64(v___x_2702_, sizeof(void*)*1, v___x_2701_);
return v___x_2702_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12(void){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2703_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13(void){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__12, &l___private_Lean_Shell_0__Lean_shellMain___closed__12_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12);
v___x_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
return v___x_2705_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
return v___x_2707_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15(void){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2708_ = l_Lean_NameSet_empty;
v___x_2709_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_2710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
lean_ctor_set(v___x_2710_, 2, v___x_2708_);
return v___x_2710_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; lean_object* v___x_2714_; 
v___x_2711_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_2712_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_2713_ = 1;
v___x_2714_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2714_, 0, v___x_2712_);
lean_ctor_set(v___x_2714_, 1, v___x_2712_);
lean_ctor_set(v___x_2714_, 2, v___x_2711_);
lean_ctor_set_uint8(v___x_2714_, sizeof(void*)*3, v___x_2713_);
return v___x_2714_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__21(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___x_2721_ = lean_string_utf8_byte_size(v___x_2720_);
return v___x_2721_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2722_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__21, &l___private_Lean_Shell_0__Lean_shellMain___closed__21_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__21);
v___x_2723_ = lean_unsigned_to_nat(0u);
v___x_2724_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___x_2725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v___x_2723_);
lean_ctor_set(v___x_2725_, 2, v___x_2722_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* v_args_2729_, lean_object* v_opts_2730_){
_start:
{
lean_object* v___y_2736_; lean_object* v_fns_2753_; lean_object* v_leanOpts_2772_; lean_object* v_forwardedArgs_2773_; uint8_t v_component_2774_; uint8_t v_printPrefix_2775_; uint8_t v_printLibDir_2776_; uint8_t v_useStdin_2777_; uint8_t v_onlyDeps_2778_; uint8_t v_onlySrcDeps_2779_; uint8_t v_depsJson_2780_; uint32_t v_trustLevel_2781_; lean_object* v_rootDir_x3f_2782_; lean_object* v_setupFileName_x3f_2783_; lean_object* v_oleanFileName_x3f_2784_; lean_object* v_ileanFileName_x3f_2785_; lean_object* v_cFileName_x3f_2786_; lean_object* v_bcFileName_x3f_2787_; uint8_t v_jsonOutput_2788_; lean_object* v_errorOnKinds_2789_; uint8_t v_printStats_2790_; uint8_t v_run_2791_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; 
v_leanOpts_2772_ = lean_ctor_get(v_opts_2730_, 0);
lean_inc_ref(v_leanOpts_2772_);
v_forwardedArgs_2773_ = lean_ctor_get(v_opts_2730_, 1);
lean_inc_ref(v_forwardedArgs_2773_);
v_component_2774_ = lean_ctor_get_uint8(v_opts_2730_, sizeof(void*)*10 + 8);
v_printPrefix_2775_ = lean_ctor_get_uint8(v_opts_2730_, sizeof(void*)*10 + 9);
v_printLibDir_2776_ = lean_ctor_get_uint8(v_opts_2730_, sizeof(void*)*10 + 10);
v_useStdin_2777_ = lean_ctor_get_uint8(v_opts_2730_, sizeof(void*)*10 + 11);
v_onlyDeps_2778_ = lean_ctor_get_uint8(v_opts_2730_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2779_ = lean_ctor_get_uint8(v_opts_2730_, sizeof(void*)*10 + 13);
v_depsJson_2780_ = lean_ctor_get_uint8(v_opts_2730_, sizeof(void*)*10 + 14);
v_trustLevel_2781_ = lean_ctor_get_uint32(v_opts_2730_, sizeof(void*)*10);
v_rootDir_x3f_2782_ = lean_ctor_get(v_opts_2730_, 3);
lean_inc(v_rootDir_x3f_2782_);
v_setupFileName_x3f_2783_ = lean_ctor_get(v_opts_2730_, 4);
lean_inc(v_setupFileName_x3f_2783_);
v_oleanFileName_x3f_2784_ = lean_ctor_get(v_opts_2730_, 5);
lean_inc(v_oleanFileName_x3f_2784_);
v_ileanFileName_x3f_2785_ = lean_ctor_get(v_opts_2730_, 6);
lean_inc(v_ileanFileName_x3f_2785_);
v_cFileName_x3f_2786_ = lean_ctor_get(v_opts_2730_, 7);
lean_inc(v_cFileName_x3f_2786_);
v_bcFileName_x3f_2787_ = lean_ctor_get(v_opts_2730_, 8);
lean_inc(v_bcFileName_x3f_2787_);
v_jsonOutput_2788_ = lean_ctor_get_uint8(v_opts_2730_, sizeof(void*)*10 + 15);
v_errorOnKinds_2789_ = lean_ctor_get(v_opts_2730_, 9);
lean_inc_ref(v_errorOnKinds_2789_);
v_printStats_2790_ = lean_ctor_get_uint8(v_opts_2730_, sizeof(void*)*10 + 16);
v_run_2791_ = lean_ctor_get_uint8(v_opts_2730_, sizeof(void*)*10 + 17);
lean_dec_ref(v_opts_2730_);
if (v_printPrefix_2775_ == 0)
{
if (v_printLibDir_2776_ == 0)
{
uint8_t v___x_2818_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v_mainModuleName_2825_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v_contents_2925_; lean_object* v___y_2951_; lean_object* v_str_2952_; lean_object* v_startInclusive_2953_; lean_object* v_endExclusive_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v_fileName_3057_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v_fst_3095_; lean_object* v_snd_3096_; lean_object* v___x_3156_; lean_object* v_maxMemory_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_2818_ = 1;
v___x_3156_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3157_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_leanOpts_2772_, v___x_3156_);
v___x_3158_ = lean_unsigned_to_nat(0u);
v___x_3159_ = lean_nat_dec_eq(v_maxMemory_3157_, v___x_3158_);
if (v___x_3159_ == 0)
{
size_t v___x_3160_; size_t v___x_3161_; size_t v___x_3162_; size_t v___x_3163_; lean_object* v___x_3164_; 
v___x_3160_ = lean_usize_of_nat(v_maxMemory_3157_);
lean_dec(v_maxMemory_3157_);
v___x_3161_ = ((size_t)1024ULL);
v___x_3162_ = lean_usize_mul(v___x_3160_, v___x_3161_);
v___x_3163_ = lean_usize_mul(v___x_3162_, v___x_3161_);
v___x_3164_ = lean_internal_set_max_memory(v___x_3163_);
goto v___jp_3147_;
}
else
{
lean_dec(v_maxMemory_3157_);
goto v___jp_3147_;
}
v___jp_2819_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = lean_unsigned_to_nat(0u);
v___x_2827_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1));
lean_inc(v_mainModuleName_2825_);
lean_inc_ref(v_leanOpts_2772_);
v___x_2828_ = l_Lean_Elab_runFrontend(v___y_2822_, v_leanOpts_2772_, v___y_2823_, v_mainModuleName_2825_, v_trustLevel_2781_, v_oleanFileName_x3f_2784_, v_ileanFileName_x3f_2785_, v_jsonOutput_2788_, v_errorOnKinds_2789_, v___x_2827_, v_printStats_2790_, v___y_2821_);
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_ileanFileName_x3f_2785_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2895_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2831_ = v___x_2828_;
v_isShared_2832_ = v_isSharedCheck_2895_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2828_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2895_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
if (lean_obj_tag(v_a_2829_) == 1)
{
if (v_run_2791_ == 0)
{
lean_del_object(v___x_2831_);
lean_dec(v___y_2824_);
if (lean_obj_tag(v_cFileName_x3f_2786_) == 1)
{
lean_object* v_val_2833_; lean_object* v_val_2834_; uint8_t v___x_2835_; lean_object* v___x_2836_; 
v_val_2833_ = lean_ctor_get(v_a_2829_, 0);
lean_inc(v_val_2833_);
v_val_2834_ = lean_ctor_get(v_cFileName_x3f_2786_, 0);
lean_inc(v_val_2834_);
lean_dec_ref(v_cFileName_x3f_2786_);
v___x_2835_ = 1;
v___x_2836_ = lean_io_prim_handle_mk(v_val_2834_, v___x_2835_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___f_2856_; lean_object* v___x_2857_; 
lean_dec(v_val_2834_);
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref(v___x_2836_);
v___x_2838_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__2));
v___x_2839_ = l_Lean_instInhabitedFileMap_default;
v___x_2840_ = l_Lean_Options_empty;
v___x_2841_ = lean_box(0);
v___x_2842_ = lean_box(0);
v___x_2843_ = lean_box(0);
v___x_2844_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__3, &l___private_Lean_Shell_0__Lean_shellMain___closed__3_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__3);
v___x_2845_ = l_Lean_firstFrontendMacroScope;
v___x_2846_ = lean_box(0);
v___x_2847_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__4, &l___private_Lean_Shell_0__Lean_shellMain___closed__4_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4);
v___x_2848_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__7));
v___x_2849_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__8));
v___x_2850_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__11, &l___private_Lean_Shell_0__Lean_shellMain___closed__11_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11);
v___x_2851_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__14, &l___private_Lean_Shell_0__Lean_shellMain___closed__14_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14);
v___x_2852_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__15, &l___private_Lean_Shell_0__Lean_shellMain___closed__15_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15);
v___x_2853_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__16, &l___private_Lean_Shell_0__Lean_shellMain___closed__16_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16);
lean_inc(v_val_2833_);
v___x_2854_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2854_, 0, v_val_2833_);
lean_ctor_set(v___x_2854_, 1, v___x_2847_);
lean_ctor_set(v___x_2854_, 2, v___x_2848_);
lean_ctor_set(v___x_2854_, 3, v___x_2849_);
lean_ctor_set(v___x_2854_, 4, v___x_2850_);
lean_ctor_set(v___x_2854_, 5, v___x_2851_);
lean_ctor_set(v___x_2854_, 6, v___x_2852_);
lean_ctor_set(v___x_2854_, 7, v___x_2853_);
lean_ctor_set(v___x_2854_, 8, v___x_2827_);
v___x_2855_ = lean_box(v_printLibDir_2776_);
lean_inc(v_mainModuleName_2825_);
v___f_2856_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 16, 15);
lean_closure_set(v___f_2856_, 0, v___x_2854_);
lean_closure_set(v___f_2856_, 1, v___x_2840_);
lean_closure_set(v___f_2856_, 2, v_mainModuleName_2825_);
lean_closure_set(v___f_2856_, 3, v_a_2837_);
lean_closure_set(v___f_2856_, 4, v___x_2851_);
lean_closure_set(v___f_2856_, 5, v___y_2820_);
lean_closure_set(v___f_2856_, 6, v___x_2839_);
lean_closure_set(v___f_2856_, 7, v___x_2826_);
lean_closure_set(v___f_2856_, 8, v___x_2841_);
lean_closure_set(v___f_2856_, 9, v___x_2842_);
lean_closure_set(v___f_2856_, 10, v___x_2843_);
lean_closure_set(v___f_2856_, 11, v___x_2844_);
lean_closure_set(v___f_2856_, 12, v___x_2845_);
lean_closure_set(v___f_2856_, 13, v___x_2846_);
lean_closure_set(v___f_2856_, 14, v___x_2855_);
v___x_2857_ = l_Lean_profileitIOUnsafe___redArg(v___x_2838_, v_leanOpts_2772_, v___f_2856_, v___x_2842_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_dec_ref(v___x_2857_);
v___y_2793_ = v_val_2833_;
v___y_2794_ = v_a_2829_;
v___y_2795_ = v_mainModuleName_2825_;
goto v___jp_2792_;
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v_val_2833_);
lean_dec_ref(v_a_2829_);
lean_dec(v_mainModuleName_2825_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec_ref(v_leanOpts_2772_);
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
lean_dec_ref(v___x_2836_);
lean_dec(v_val_2833_);
lean_dec_ref(v_a_2829_);
lean_dec(v_mainModuleName_2825_);
lean_dec_ref(v___y_2820_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec_ref(v_leanOpts_2772_);
v___x_2866_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__17));
v___x_2867_ = lean_string_append(v___x_2866_, v_val_2834_);
lean_dec(v_val_2834_);
v___x_2868_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_2869_ = lean_string_append(v___x_2867_, v___x_2868_);
v___x_2870_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_2869_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2878_; 
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; 
v_unused_2879_ = lean_ctor_get(v___x_2870_, 0);
lean_dec(v_unused_2879_);
v___x_2872_ = v___x_2870_;
v_isShared_2873_ = v_isSharedCheck_2878_;
goto v_resetjp_2871_;
}
else
{
lean_dec(v___x_2870_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2878_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2874_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2874_);
v___x_2876_ = v___x_2872_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
v_a_2880_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2870_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2870_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
else
{
lean_object* v_val_2888_; 
lean_dec_ref(v___y_2820_);
lean_dec(v_cFileName_x3f_2786_);
v_val_2888_ = lean_ctor_get(v_a_2829_, 0);
lean_inc(v_val_2888_);
v___y_2793_ = v_val_2888_;
v___y_2794_ = v_a_2829_;
v___y_2795_ = v_mainModuleName_2825_;
goto v___jp_2792_;
}
}
else
{
lean_object* v_val_2889_; uint32_t v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2893_; 
lean_dec(v_mainModuleName_2825_);
lean_dec_ref(v___y_2820_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
v_val_2889_ = lean_ctor_get(v_a_2829_, 0);
lean_inc(v_val_2889_);
lean_dec_ref(v_a_2829_);
v___x_2890_ = lean_eval_main(v_val_2889_, v_leanOpts_2772_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec_ref(v_leanOpts_2772_);
lean_dec(v_val_2889_);
v___x_2891_ = lean_box_uint32(v___x_2890_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v___x_2891_);
v___x_2893_ = v___x_2831_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2891_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
else
{
lean_del_object(v___x_2831_);
lean_dec(v_mainModuleName_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2820_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec_ref(v_leanOpts_2772_);
v___y_2736_ = v_a_2829_;
goto v___jp_2735_;
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_mainModuleName_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2820_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec_ref(v_leanOpts_2772_);
v_a_2896_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2828_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2828_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
v___jp_2904_:
{
if (lean_obj_tag(v___y_2910_) == 0)
{
lean_object* v_a_2911_; 
v_a_2911_ = lean_ctor_get(v___y_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref(v___y_2910_);
v___y_2820_ = v___y_2905_;
v___y_2821_ = v___y_2906_;
v___y_2822_ = v___y_2907_;
v___y_2823_ = v___y_2908_;
v___y_2824_ = v___y_2909_;
v_mainModuleName_2825_ = v_a_2911_;
goto v___jp_2819_;
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec(v_ileanFileName_x3f_2785_);
lean_dec(v_oleanFileName_x3f_2784_);
lean_dec_ref(v_leanOpts_2772_);
v_a_2912_ = lean_ctor_get(v___y_2910_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___y_2910_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___y_2910_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___y_2910_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
v___jp_2920_:
{
if (lean_obj_tag(v_setupFileName_x3f_2783_) == 0)
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_box(0);
if (lean_obj_tag(v___y_2923_) == 1)
{
lean_object* v_val_2927_; lean_object* v___x_2928_; 
v_val_2927_ = lean_ctor_get(v___y_2923_, 0);
lean_inc(v_val_2927_);
lean_dec_ref(v___y_2923_);
v___x_2928_ = l_Lean_moduleNameOfFileName(v_val_2927_, v_rootDir_x3f_2782_);
if (lean_obj_tag(v___x_2928_) == 0)
{
v___y_2905_ = v___y_2921_;
v___y_2906_ = v___x_2926_;
v___y_2907_ = v_contents_2925_;
v___y_2908_ = v___y_2922_;
v___y_2909_ = v___y_2924_;
v___y_2910_ = v___x_2928_;
goto v___jp_2904_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_2784_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_2786_) == 0)
{
lean_object* v___x_2929_; 
lean_dec_ref(v___x_2928_);
v___x_2929_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__19));
v___y_2820_ = v___y_2921_;
v___y_2821_ = v___x_2926_;
v___y_2822_ = v_contents_2925_;
v___y_2823_ = v___y_2922_;
v___y_2824_ = v___y_2924_;
v_mainModuleName_2825_ = v___x_2929_;
goto v___jp_2819_;
}
else
{
v___y_2905_ = v___y_2921_;
v___y_2906_ = v___x_2926_;
v___y_2907_ = v_contents_2925_;
v___y_2908_ = v___y_2922_;
v___y_2909_ = v___y_2924_;
v___y_2910_ = v___x_2928_;
goto v___jp_2904_;
}
}
else
{
v___y_2905_ = v___y_2921_;
v___y_2906_ = v___x_2926_;
v___y_2907_ = v_contents_2925_;
v___y_2908_ = v___y_2922_;
v___y_2909_ = v___y_2924_;
v___y_2910_ = v___x_2928_;
goto v___jp_2904_;
}
}
}
else
{
lean_object* v___x_2930_; 
lean_dec(v___y_2923_);
lean_dec(v_rootDir_x3f_2782_);
v___x_2930_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__19));
v___y_2820_ = v___y_2921_;
v___y_2821_ = v___x_2926_;
v___y_2822_ = v_contents_2925_;
v___y_2823_ = v___y_2922_;
v___y_2824_ = v___y_2924_;
v_mainModuleName_2825_ = v___x_2930_;
goto v___jp_2819_;
}
}
else
{
lean_object* v_val_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2949_; 
lean_dec(v___y_2923_);
lean_dec(v_rootDir_x3f_2782_);
v_val_2931_ = lean_ctor_get(v_setupFileName_x3f_2783_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_setupFileName_x3f_2783_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2933_ = v_setupFileName_x3f_2783_;
v_isShared_2934_ = v_isSharedCheck_2949_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_val_2931_);
lean_dec(v_setupFileName_x3f_2783_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2949_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_ModuleSetup_load(v_val_2931_);
lean_dec(v_val_2931_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v_name_2937_; lean_object* v___x_2939_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref(v___x_2935_);
v_name_2937_ = lean_ctor_get(v_a_2936_, 0);
lean_inc(v_name_2937_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v_a_2936_);
v___x_2939_ = v___x_2933_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2936_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
v___y_2820_ = v___y_2921_;
v___y_2821_ = v___x_2939_;
v___y_2822_ = v_contents_2925_;
v___y_2823_ = v___y_2922_;
v___y_2824_ = v___y_2924_;
v_mainModuleName_2825_ = v_name_2937_;
goto v___jp_2819_;
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_del_object(v___x_2933_);
lean_dec_ref(v_contents_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec(v_ileanFileName_x3f_2785_);
lean_dec(v_oleanFileName_x3f_2784_);
lean_dec_ref(v_leanOpts_2772_);
v_a_2941_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2935_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2935_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
}
}
v___jp_2950_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2959_ = lean_nat_add(v_startInclusive_2953_, v___y_2958_);
lean_dec(v___y_2958_);
lean_inc(v___x_2959_);
lean_inc_ref(v_str_2952_);
v___x_2960_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2960_, 0, v_str_2952_);
lean_ctor_set(v___x_2960_, 1, v_startInclusive_2953_);
lean_ctor_set(v___x_2960_, 2, v___x_2959_);
v___x_2961_ = l_String_Slice_trimAscii(v___x_2960_);
v___x_2962_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__22, &l___private_Lean_Shell_0__Lean_shellMain___closed__22_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22);
v___x_2963_ = l_String_Slice_beq(v___x_2961_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
lean_dec(v___x_2959_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec(v_endExclusive_2954_);
lean_dec_ref(v_str_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec(v_ileanFileName_x3f_2785_);
lean_dec(v_oleanFileName_x3f_2784_);
lean_dec(v_setupFileName_x3f_2783_);
lean_dec(v_rootDir_x3f_2782_);
lean_dec_ref(v_leanOpts_2772_);
v___x_2964_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__23));
v___x_2965_ = l_String_Slice_toString(v___x_2961_);
lean_dec_ref(v___x_2961_);
v___x_2966_ = lean_string_append(v___x_2964_, v___x_2965_);
lean_dec_ref(v___x_2965_);
v___x_2967_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_2968_ = lean_string_append(v___x_2966_, v___x_2967_);
v___x_2969_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_2968_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2977_; 
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; 
v_unused_2978_ = lean_ctor_get(v___x_2969_, 0);
lean_dec(v_unused_2978_);
v___x_2971_ = v___x_2969_;
v_isShared_2972_ = v_isSharedCheck_2977_;
goto v_resetjp_2970_;
}
else
{
lean_dec(v___x_2969_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2977_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2973_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 0, v___x_2973_);
v___x_2975_ = v___x_2971_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
v_a_2979_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2969_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2969_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
else
{
lean_object* v___x_2987_; 
lean_dec_ref(v___x_2961_);
v___x_2987_ = lean_string_utf8_extract(v_str_2952_, v___x_2959_, v_endExclusive_2954_);
lean_dec(v_endExclusive_2954_);
lean_dec(v___x_2959_);
lean_dec_ref(v_str_2952_);
v___y_2921_ = v___y_2951_;
v___y_2922_ = v___y_2956_;
v___y_2923_ = v___y_2955_;
v___y_2924_ = v___y_2957_;
v_contents_2925_ = v___x_2987_;
goto v___jp_2920_;
}
}
v___jp_2988_:
{
if (lean_obj_tag(v___y_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2994_; 
v_a_2993_ = lean_ctor_get(v___y_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref(v___y_2992_);
v___x_2994_ = lean_decode_lossy_utf8(v_a_2993_);
lean_dec(v_a_2993_);
if (v_onlyDeps_2778_ == 0)
{
if (v_onlySrcDeps_2779_ == 0)
{
lean_object* v___x_2995_; 
lean_inc_ref(v___x_2994_);
v___x_2995_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_2994_);
if (lean_obj_tag(v___x_2995_) == 1)
{
lean_object* v_val_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
lean_dec_ref(v___x_2994_);
v_val_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_val_2996_);
lean_dec_ref(v___x_2995_);
v___x_2997_ = lean_unsigned_to_nat(0u);
v___x_2998_ = lean_box(0);
v___x_2999_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_2996_, v___x_2997_, v___x_2998_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_str_3000_; lean_object* v_startInclusive_3001_; lean_object* v_endExclusive_3002_; lean_object* v___x_3003_; 
v_str_3000_ = lean_ctor_get(v_val_2996_, 0);
lean_inc_ref(v_str_3000_);
v_startInclusive_3001_ = lean_ctor_get(v_val_2996_, 1);
lean_inc(v_startInclusive_3001_);
v_endExclusive_3002_ = lean_ctor_get(v_val_2996_, 2);
lean_inc(v_endExclusive_3002_);
lean_dec(v_val_2996_);
v___x_3003_ = lean_nat_sub(v_endExclusive_3002_, v_startInclusive_3001_);
lean_inc_ref(v___y_2990_);
v___y_2951_ = v___y_2990_;
v_str_2952_ = v_str_3000_;
v_startInclusive_2953_ = v_startInclusive_3001_;
v_endExclusive_2954_ = v_endExclusive_3002_;
v___y_2955_ = v___y_2989_;
v___y_2956_ = v___y_2990_;
v___y_2957_ = v___y_2991_;
v___y_2958_ = v___x_3003_;
goto v___jp_2950_;
}
else
{
lean_object* v_val_3004_; lean_object* v_str_3005_; lean_object* v_startInclusive_3006_; lean_object* v_endExclusive_3007_; 
v_val_3004_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_val_3004_);
lean_dec_ref(v___x_2999_);
v_str_3005_ = lean_ctor_get(v_val_2996_, 0);
lean_inc_ref(v_str_3005_);
v_startInclusive_3006_ = lean_ctor_get(v_val_2996_, 1);
lean_inc(v_startInclusive_3006_);
v_endExclusive_3007_ = lean_ctor_get(v_val_2996_, 2);
lean_inc(v_endExclusive_3007_);
lean_dec(v_val_2996_);
lean_inc_ref(v___y_2990_);
v___y_2951_ = v___y_2990_;
v_str_2952_ = v_str_3005_;
v_startInclusive_2953_ = v_startInclusive_3006_;
v_endExclusive_2954_ = v_endExclusive_3007_;
v___y_2955_ = v___y_2989_;
v___y_2956_ = v___y_2990_;
v___y_2957_ = v___y_2991_;
v___y_2958_ = v_val_3004_;
goto v___jp_2950_;
}
}
else
{
lean_dec(v___x_2995_);
lean_inc_ref(v___y_2990_);
v___y_2921_ = v___y_2990_;
v___y_2922_ = v___y_2990_;
v___y_2923_ = v___y_2989_;
v___y_2924_ = v___y_2991_;
v_contents_2925_ = v___x_2994_;
goto v___jp_2920_;
}
}
else
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec(v_ileanFileName_x3f_2785_);
lean_dec(v_oleanFileName_x3f_2784_);
lean_dec(v_setupFileName_x3f_2783_);
lean_dec(v_rootDir_x3f_2782_);
lean_dec_ref(v_leanOpts_2772_);
v___x_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___y_2990_);
v___x_3009_ = l_Lean_Elab_printImportSrcs(v___x_2994_, v___x_3008_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3017_; 
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v___x_3009_, 0);
lean_dec(v_unused_3018_);
v___x_3011_ = v___x_3009_;
v_isShared_3012_ = v_isSharedCheck_3017_;
goto v_resetjp_3010_;
}
else
{
lean_dec(v___x_3009_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3017_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3015_; 
v___x_3013_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 0, v___x_3013_);
v___x_3015_ = v___x_3011_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
v_a_3019_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3009_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3009_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
lean_dec(v___y_2991_);
lean_dec(v___y_2989_);
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec(v_ileanFileName_x3f_2785_);
lean_dec(v_oleanFileName_x3f_2784_);
lean_dec(v_setupFileName_x3f_2783_);
lean_dec(v_rootDir_x3f_2782_);
lean_dec_ref(v_leanOpts_2772_);
v___x_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3027_, 0, v___y_2990_);
v___x_3028_ = l_Lean_Elab_printImports(v___x_2994_, v___x_3027_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3036_; 
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3036_ == 0)
{
lean_object* v_unused_3037_; 
v_unused_3037_ = lean_ctor_get(v___x_3028_, 0);
lean_dec(v_unused_3037_);
v___x_3030_ = v___x_3028_;
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
else
{
lean_dec(v___x_3028_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3032_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v___x_3032_);
v___x_3034_ = v___x_3030_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
v_a_3038_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3028_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3028_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec(v_ileanFileName_x3f_2785_);
lean_dec(v_oleanFileName_x3f_2784_);
lean_dec(v_setupFileName_x3f_2783_);
lean_dec(v_rootDir_x3f_2782_);
lean_dec_ref(v_leanOpts_2772_);
v_a_3046_ = lean_ctor_get(v___y_2992_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___y_2992_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___y_2992_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___y_2992_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
v___jp_3054_:
{
if (v_useStdin_2777_ == 0)
{
lean_object* v___x_3058_; 
v___x_3058_ = l_IO_FS_readBinFile(v_fileName_3057_);
v___y_2989_ = v___y_3055_;
v___y_2990_ = v_fileName_3057_;
v___y_2991_ = v___y_3056_;
v___y_2992_ = v___x_3058_;
goto v___jp_2988_;
}
else
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = lean_get_stdin();
v___x_3060_ = l_IO_FS_Stream_readBinToEnd(v___x_3059_);
v___y_2989_ = v___y_3055_;
v___y_2990_ = v_fileName_3057_;
v___y_2991_ = v___y_3056_;
v___y_2992_ = v___x_3060_;
goto v___jp_2988_;
}
}
v___jp_3061_:
{
if (lean_obj_tag(v___y_3062_) == 1)
{
lean_object* v_val_3064_; 
v_val_3064_ = lean_ctor_get(v___y_3062_, 0);
lean_inc(v_val_3064_);
v___y_3055_ = v___y_3062_;
v___y_3056_ = v___y_3063_;
v_fileName_3057_ = v_val_3064_;
goto v___jp_3054_;
}
else
{
if (v_useStdin_2777_ == 0)
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_dec(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec(v_ileanFileName_x3f_2785_);
lean_dec(v_oleanFileName_x3f_2784_);
lean_dec(v_setupFileName_x3f_2783_);
lean_dec(v_rootDir_x3f_2782_);
lean_dec_ref(v_leanOpts_2772_);
v___x_3065_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__24));
v___x_3066_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3065_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v___x_3067_; 
lean_dec_ref(v___x_3066_);
v___x_3067_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_2818_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3075_; 
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3075_ == 0)
{
lean_object* v_unused_3076_; 
v_unused_3076_ = lean_ctor_get(v___x_3067_, 0);
lean_dec(v_unused_3076_);
v___x_3069_ = v___x_3067_;
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
else
{
lean_dec(v___x_3067_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3071_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3071_);
v___x_3073_ = v___x_3069_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
v_a_3077_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3067_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3067_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
v_a_3085_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3066_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3066_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v___x_3093_; 
v___x_3093_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__25));
v___y_3055_ = v___y_3062_;
v___y_3056_ = v___y_3063_;
v_fileName_3057_ = v___x_3093_;
goto v___jp_3054_;
}
}
}
v___jp_3094_:
{
if (v_run_2791_ == 0)
{
uint8_t v___x_3097_; 
v___x_3097_ = l_List_isEmpty___redArg(v_snd_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_dec(v_snd_3096_);
lean_dec(v_fst_3095_);
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec(v_ileanFileName_x3f_2785_);
lean_dec(v_oleanFileName_x3f_2784_);
lean_dec(v_setupFileName_x3f_2783_);
lean_dec(v_rootDir_x3f_2782_);
lean_dec_ref(v_leanOpts_2772_);
v___x_3098_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__24));
v___x_3099_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3098_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v___x_3100_; 
lean_dec_ref(v___x_3099_);
v___x_3100_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_2818_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3108_; 
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3108_ == 0)
{
lean_object* v_unused_3109_; 
v_unused_3109_ = lean_ctor_get(v___x_3100_, 0);
lean_dec(v_unused_3109_);
v___x_3102_ = v___x_3100_;
v_isShared_3103_ = v_isSharedCheck_3108_;
goto v_resetjp_3101_;
}
else
{
lean_dec(v___x_3100_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3108_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
v___x_3104_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3104_);
v___x_3106_ = v___x_3102_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
v_a_3110_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3100_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3100_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
v_a_3118_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3099_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3099_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
else
{
v___y_3062_ = v_fst_3095_;
v___y_3063_ = v_snd_3096_;
goto v___jp_3061_;
}
}
else
{
v___y_3062_ = v_fst_3095_;
v___y_3063_ = v_snd_3096_;
goto v___jp_3061_;
}
}
v___jp_3126_:
{
if (lean_obj_tag(v_args_2729_) == 0)
{
lean_object* v___x_3127_; 
v___x_3127_ = lean_box(0);
v_fst_3095_ = v___x_3127_;
v_snd_3096_ = v_args_2729_;
goto v___jp_3094_;
}
else
{
lean_object* v_head_3128_; lean_object* v_tail_3129_; lean_object* v___x_3130_; 
v_head_3128_ = lean_ctor_get(v_args_2729_, 0);
lean_inc(v_head_3128_);
v_tail_3129_ = lean_ctor_get(v_args_2729_, 1);
lean_inc(v_tail_3129_);
lean_dec_ref(v_args_2729_);
v___x_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3130_, 0, v_head_3128_);
v_fst_3095_ = v___x_3130_;
v_snd_3096_ = v_tail_3129_;
goto v___jp_3094_;
}
}
v___jp_3131_:
{
switch(v_component_2774_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_2773_);
if (v_onlyDeps_2778_ == 0)
{
goto v___jp_3126_;
}
else
{
if (v_depsJson_2780_ == 0)
{
goto v___jp_3126_;
}
else
{
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec(v_ileanFileName_x3f_2785_);
lean_dec(v_oleanFileName_x3f_2784_);
lean_dec(v_setupFileName_x3f_2783_);
lean_dec(v_rootDir_x3f_2782_);
lean_dec_ref(v_leanOpts_2772_);
if (v_useStdin_2777_ == 0)
{
lean_object* v___x_3132_; 
v___x_3132_ = lean_array_mk(v_args_2729_);
v_fns_2753_ = v___x_3132_;
goto v___jp_2752_;
}
else
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
lean_dec(v_args_2729_);
v___x_3133_ = lean_get_stdin();
v___x_3134_ = l_IO_FS_Stream_lines(v___x_3133_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref(v___x_3134_);
v_fns_2753_ = v_a_3135_;
goto v___jp_2752_;
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v_a_3136_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3134_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3134_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec(v_ileanFileName_x3f_2785_);
lean_dec(v_oleanFileName_x3f_2784_);
lean_dec(v_setupFileName_x3f_2783_);
lean_dec(v_rootDir_x3f_2782_);
lean_dec_ref(v_leanOpts_2772_);
lean_dec(v_args_2729_);
v___x_3144_ = lean_array_to_list(v_forwardedArgs_2773_);
v___x_3145_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3144_);
return v___x_3145_;
}
default: 
{
lean_object* v___x_3146_; 
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec(v_ileanFileName_x3f_2785_);
lean_dec(v_oleanFileName_x3f_2784_);
lean_dec(v_setupFileName_x3f_2783_);
lean_dec(v_rootDir_x3f_2782_);
lean_dec_ref(v_forwardedArgs_2773_);
lean_dec(v_args_2729_);
v___x_3146_ = l_Lean_Server_FileWorker_workerMain(v_leanOpts_2772_);
return v___x_3146_;
}
}
}
v___jp_3147_:
{
lean_object* v___x_3148_; lean_object* v_timeout_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; 
v___x_3148_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3149_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_leanOpts_2772_, v___x_3148_);
v___x_3150_ = lean_unsigned_to_nat(0u);
v___x_3151_ = lean_nat_dec_eq(v_timeout_3149_, v___x_3150_);
if (v___x_3151_ == 0)
{
size_t v___x_3152_; size_t v___x_3153_; size_t v___x_3154_; lean_object* v___x_3155_; 
v___x_3152_ = lean_usize_of_nat(v_timeout_3149_);
lean_dec(v_timeout_3149_);
v___x_3153_ = ((size_t)1000ULL);
v___x_3154_ = lean_usize_mul(v___x_3152_, v___x_3153_);
v___x_3155_ = lean_internal_set_max_heartbeat(v___x_3154_);
goto v___jp_3131_;
}
else
{
lean_dec(v_timeout_3149_);
goto v___jp_3131_;
}
}
}
else
{
lean_object* v___x_3165_; 
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec(v_ileanFileName_x3f_2785_);
lean_dec(v_oleanFileName_x3f_2784_);
lean_dec(v_setupFileName_x3f_2783_);
lean_dec(v_rootDir_x3f_2782_);
lean_dec_ref(v_forwardedArgs_2773_);
lean_dec_ref(v_leanOpts_2772_);
lean_dec(v_args_2729_);
v___x_3165_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v___x_3167_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref(v___x_3165_);
v___x_3167_ = l_Lean_getLibDir(v_a_3166_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3169_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref(v___x_3167_);
v___x_3169_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3168_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3177_; 
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; 
v_unused_3178_ = lean_ctor_get(v___x_3169_, 0);
lean_dec(v_unused_3178_);
v___x_3171_ = v___x_3169_;
v_isShared_3172_ = v_isSharedCheck_3177_;
goto v_resetjp_3170_;
}
else
{
lean_dec(v___x_3169_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3177_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3173_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 0, v___x_3173_);
v___x_3175_ = v___x_3171_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3173_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
v_a_3179_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3169_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3169_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
v_a_3187_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3167_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3167_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
v_a_3195_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3165_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3165_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
}
else
{
lean_object* v___x_3203_; 
lean_dec_ref(v_errorOnKinds_2789_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec(v_cFileName_x3f_2786_);
lean_dec(v_ileanFileName_x3f_2785_);
lean_dec(v_oleanFileName_x3f_2784_);
lean_dec(v_setupFileName_x3f_2783_);
lean_dec(v_rootDir_x3f_2782_);
lean_dec_ref(v_forwardedArgs_2773_);
lean_dec_ref(v_leanOpts_2772_);
lean_dec(v_args_2729_);
v___x_3203_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3205_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref(v___x_3203_);
v___x_3205_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3204_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3213_; 
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3213_ == 0)
{
lean_object* v_unused_3214_; 
v_unused_3214_ = lean_ctor_get(v___x_3205_, 0);
lean_dec(v_unused_3214_);
v___x_3207_ = v___x_3205_;
v_isShared_3208_ = v_isSharedCheck_3213_;
goto v_resetjp_3206_;
}
else
{
lean_dec(v___x_3205_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3213_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; lean_object* v___x_3211_; 
v___x_3209_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v___x_3209_);
v___x_3211_ = v___x_3207_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3209_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
v_a_3215_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3205_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3205_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
v_a_3223_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3203_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3203_);
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
v___jp_2732_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
return v___x_2734_;
}
v___jp_2735_:
{
lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2737_ = lean_display_cumulative_profiling_times();
v___x_2738_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__0, &l___private_Lean_Shell_0__Lean_shellMain___closed__0_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0);
if (v___x_2738_ == 0)
{
if (lean_obj_tag(v___y_2736_) == 0)
{
uint8_t v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = 1;
v___x_2740_ = lean_io_exit(v___x_2739_);
return v___x_2740_;
}
else
{
uint8_t v___x_2741_; lean_object* v___x_2742_; 
lean_dec_ref(v___y_2736_);
v___x_2741_ = 0;
v___x_2742_ = lean_io_exit(v___x_2741_);
return v___x_2742_;
}
}
else
{
if (lean_obj_tag(v___y_2736_) == 0)
{
goto v___jp_2732_;
}
else
{
lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2750_; 
v_isSharedCheck_2750_ = !lean_is_exclusive(v___y_2736_);
if (v_isSharedCheck_2750_ == 0)
{
lean_object* v_unused_2751_; 
v_unused_2751_ = lean_ctor_get(v___y_2736_, 0);
lean_dec(v_unused_2751_);
v___x_2744_ = v___y_2736_;
v_isShared_2745_ = v_isSharedCheck_2750_;
goto v_resetjp_2743_;
}
else
{
lean_dec(v___y_2736_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2750_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
if (v___x_2738_ == 0)
{
lean_del_object(v___x_2744_);
goto v___jp_2732_;
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2748_; 
v___x_2746_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2745_ == 0)
{
lean_ctor_set_tag(v___x_2744_, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2746_);
v___x_2748_ = v___x_2744_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
}
v___jp_2752_:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_printImportsJson(v_fns_2753_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2762_; 
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; 
v_unused_2763_ = lean_ctor_get(v___x_2754_, 0);
lean_dec(v_unused_2763_);
v___x_2756_ = v___x_2754_;
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
else
{
lean_dec(v___x_2754_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2758_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v___x_2758_);
v___x_2760_ = v___x_2756_;
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
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
v_a_2764_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2754_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2754_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
v___jp_2792_:
{
if (lean_obj_tag(v_bcFileName_x3f_2787_) == 1)
{
lean_object* v_val_2796_; lean_object* v___x_2797_; 
v_val_2796_ = lean_ctor_get(v_bcFileName_x3f_2787_, 0);
lean_inc(v_val_2796_);
lean_dec_ref(v_bcFileName_x3f_2787_);
v___x_2797_ = lean_init_llvm();
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
lean_dec_ref(v___x_2797_);
v___x_2798_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__1));
v___x_2799_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(v___x_2799_, 0, v___y_2793_);
lean_closure_set(v___x_2799_, 1, v___y_2795_);
lean_closure_set(v___x_2799_, 2, v_val_2796_);
v___x_2800_ = lean_box(0);
v___x_2801_ = l_Lean_profileitIOUnsafe___redArg(v___x_2798_, v_leanOpts_2772_, v___x_2799_, v___x_2800_);
lean_dec_ref(v_leanOpts_2772_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_dec_ref(v___x_2801_);
v___y_2736_ = v___y_2794_;
goto v___jp_2735_;
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v___y_2794_);
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_val_2796_);
lean_dec(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec_ref(v_leanOpts_2772_);
v_a_2810_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2797_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2797_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
else
{
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2793_);
lean_dec(v_bcFileName_x3f_2787_);
lean_dec_ref(v_leanOpts_2772_);
v___y_2736_ = v___y_2794_;
goto v___jp_2735_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3231_, lean_object* v_opts_3232_, lean_object* v_a_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = lean_shell_main(v_args_3231_, v_opts_3232_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3235_, lean_object* v_inst_3236_, lean_object* v_R_3237_, lean_object* v_a_3238_, lean_object* v_b_3239_, lean_object* v_c_3240_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3235_, v_a_3238_, v_b_3239_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3242_, lean_object* v_inst_3243_, lean_object* v_R_3244_, lean_object* v_a_3245_, lean_object* v_b_3246_, lean_object* v_c_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3242_, v_inst_3243_, v_R_3244_, v_a_3245_, v_b_3246_, v_c_3247_);
lean_dec(v_b_3246_);
lean_dec_ref(v_val_3242_);
return v_res_3248_;
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
