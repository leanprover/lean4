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
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
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
lean_object* lean_display_cumulative_profiling_times();
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
lean_object* v_defValue_354_; lean_object* v_descr_355_; lean_object* v_deprecation_x3f_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_defValue_354_ = lean_ctor_get(v_decl_351_, 0);
v_descr_355_ = lean_ctor_get(v_decl_351_, 1);
v_deprecation_x3f_356_ = lean_ctor_get(v_decl_351_, 2);
lean_inc(v_defValue_354_);
v___x_357_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_357_, 0, v_defValue_354_);
lean_inc(v_deprecation_x3f_356_);
lean_inc_ref(v_descr_355_);
lean_inc_n(v_name_350_, 2);
v___x_358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_358_, 0, v_name_350_);
lean_ctor_set(v___x_358_, 1, v_ref_352_);
lean_ctor_set(v___x_358_, 2, v___x_357_);
lean_ctor_set(v___x_358_, 3, v_descr_355_);
lean_ctor_set(v___x_358_, 4, v_deprecation_x3f_356_);
v___x_359_ = lean_register_option(v_name_350_, v___x_358_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_367_; 
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_367_ == 0)
{
lean_object* v_unused_368_; 
v_unused_368_ = lean_ctor_get(v___x_359_, 0);
lean_dec(v_unused_368_);
v___x_361_ = v___x_359_;
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
else
{
lean_dec(v___x_359_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
lean_inc(v_defValue_354_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_name_350_);
lean_ctor_set(v___x_363_, 1, v_defValue_354_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_363_);
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec(v_name_350_);
v_a_369_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_359_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_359_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_377_, lean_object* v_decl_378_, lean_object* v_ref_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v_name_377_, v_decl_378_, v_ref_379_);
lean_dec_ref(v_decl_378_);
return v_res_381_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_box(0);
v___x_386_ = lean_internal_get_default_max_memory(v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_387_ = lean_box(0);
v___x_388_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_389_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_388_);
lean_ctor_set(v___x_390_, 2, v___x_387_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_414_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_415_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_416_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_417_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_414_, v___x_415_, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2____boxed(lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
return v_res_419_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_box(0);
v___x_424_ = lean_internal_get_default_max_heartbeat(v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_425_ = lean_box(0);
v___x_426_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_427_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
lean_ctor_set(v___x_428_, 2, v___x_425_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_433_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_434_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_435_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_436_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_433_, v___x_434_, v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2____boxed(lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(lean_object* v_name_439_, lean_object* v_decl_440_, lean_object* v_ref_441_){
_start:
{
lean_object* v_defValue_443_; lean_object* v_descr_444_; lean_object* v_deprecation_x3f_445_; lean_object* v___x_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_defValue_443_ = lean_ctor_get(v_decl_440_, 0);
v_descr_444_ = lean_ctor_get(v_decl_440_, 1);
v_deprecation_x3f_445_ = lean_ctor_get(v_decl_440_, 2);
v___x_446_ = lean_alloc_ctor(1, 0, 1);
v___x_447_ = lean_unbox(v_defValue_443_);
lean_ctor_set_uint8(v___x_446_, 0, v___x_447_);
lean_inc(v_deprecation_x3f_445_);
lean_inc_ref(v_descr_444_);
lean_inc_n(v_name_439_, 2);
v___x_448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_448_, 0, v_name_439_);
lean_ctor_set(v___x_448_, 1, v_ref_441_);
lean_ctor_set(v___x_448_, 2, v___x_446_);
lean_ctor_set(v___x_448_, 3, v_descr_444_);
lean_ctor_set(v___x_448_, 4, v_deprecation_x3f_445_);
v___x_449_ = lean_register_option(v_name_439_, v___x_448_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_457_; 
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v___x_449_, 0);
lean_dec(v_unused_458_);
v___x_451_ = v___x_449_;
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
else
{
lean_dec(v___x_449_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
lean_inc(v_defValue_443_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_name_439_);
lean_ctor_set(v___x_453_, 1, v_defValue_443_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec(v_name_439_);
v_a_459_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_449_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_449_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_467_, lean_object* v_decl_468_, lean_object* v_ref_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v_name_467_, v_decl_468_, v_ref_469_);
lean_dec_ref(v_decl_468_);
return v_res_471_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_box(0);
v___x_476_ = lean_internal_get_default_verbose(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_477_ = lean_box(0);
v___x_478_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_479_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_480_ = lean_box(v___x_479_);
v___x_481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_478_);
lean_ctor_set(v___x_481_, 2, v___x_477_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_486_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_487_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_488_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_489_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v___x_486_, v___x_487_, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2____boxed(lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_();
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultOptions___boxed(lean_object* v_x_00___x40_Lean_Shell_2553953037____hygCtx___hyg_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = lean_internal_get_default_options(v_x_00___x40_Lean_Shell_2553953037____hygCtx___hyg_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBelieverTrustLevel___boxed(lean_object* v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_496_){
_start:
{
uint32_t v_res_497_; lean_object* v_r_498_; 
v_res_497_ = lean_internal_get_believer_trust_level(v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_496_);
v_r_498_ = lean_box_uint32(v_res_497_);
return v_r_498_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0(void){
_start:
{
lean_object* v___x_499_; uint32_t v___x_500_; 
v___x_499_ = lean_box(0);
v___x_500_ = lean_internal_get_believer_trust_level(v___x_499_);
return v___x_500_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1(void){
_start:
{
uint32_t v___x_501_; uint32_t v___x_502_; uint32_t v___x_503_; 
v___x_501_ = 1;
v___x_502_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0);
v___x_503_ = lean_uint32_add(v___x_502_, v___x_501_);
return v___x_503_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel(void){
_start:
{
uint32_t v___x_504_; 
v___x_504_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getHardwareCurrency___boxed(lean_object* v_x_00___x40_Lean_Shell_1910423346____hygCtx___hyg_506_){
_start:
{
uint32_t v_res_507_; lean_object* v_r_508_; 
v_res_507_ = lean_internal_get_hardware_concurrency(v_x_00___x40_Lean_Shell_1910423346____hygCtx___hyg_506_);
v_r_508_ = lean_box_uint32(v_res_507_);
return v_r_508_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0(void){
_start:
{
lean_object* v___x_509_; uint32_t v___x_510_; 
v___x_509_ = lean_box(0);
v___x_510_ = lean_internal_get_hardware_concurrency(v___x_509_);
return v___x_510_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads(void){
_start:
{
uint8_t v___x_511_; 
v___x_511_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__36, &l___private_Lean_Shell_0__Lean_displayHelp___closed__36_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36);
if (v___x_511_ == 0)
{
uint32_t v___x_512_; 
v___x_512_ = 0;
return v___x_512_;
}
else
{
uint32_t v___x_513_; 
v___x_513_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0, &l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0);
return v___x_513_;
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_box(0);
v___x_515_ = lean_internal_get_default_options(v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2(void){
_start:
{
lean_object* v___x_518_; uint32_t v___x_519_; uint32_t v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_518_ = lean_box(0);
v___x_519_ = l___private_Lean_Shell_0__Lean_defaultNumThreads;
v___x_520_ = l___private_Lean_Shell_0__Lean_defaultTrustLevel;
v___x_521_ = l_Lean_Options_empty;
v___x_522_ = 0;
v___x_523_ = 0;
v___x_524_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1));
v___x_525_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0);
v___x_526_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v___x_524_);
lean_ctor_set(v___x_526_, 2, v___x_521_);
lean_ctor_set(v___x_526_, 3, v___x_518_);
lean_ctor_set(v___x_526_, 4, v___x_518_);
lean_ctor_set(v___x_526_, 5, v___x_518_);
lean_ctor_set(v___x_526_, 6, v___x_518_);
lean_ctor_set(v___x_526_, 7, v___x_518_);
lean_ctor_set(v___x_526_, 8, v___x_518_);
lean_ctor_set(v___x_526_, 9, v___x_524_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*10 + 8, v___x_523_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*10 + 9, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*10 + 10, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*10 + 11, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*10 + 12, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*10 + 13, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*10 + 14, v___x_522_);
lean_ctor_set_uint32(v___x_526_, sizeof(void*)*10, v___x_520_);
lean_ctor_set_uint32(v___x_526_, sizeof(void*)*10 + 4, v___x_519_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*10 + 15, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*10 + 16, v___x_522_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*10 + 17, v___x_522_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object* v_x_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2);
return v___x_528_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_run(lean_object* v_opts_529_){
_start:
{
uint8_t v_run_530_; 
v_run_530_ = lean_ctor_get_uint8(v_opts_529_, sizeof(void*)*10 + 17);
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
lean_dec_ref(v___x_539_);
if (lean_obj_tag(v_val_541_) == 1)
{
uint8_t v_v_542_; 
v_v_542_ = lean_ctor_get_uint8(v_val_541_, 0);
lean_dec_ref(v_val_541_);
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
v_numThreads_556_ = lean_ctor_get_uint32(v_opts_555_, sizeof(void*)*10 + 4);
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
lean_dec_ref(v___x_665_);
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
lean_dec_ref(v___x_667_);
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
lean_dec_ref(v___x_641_);
v_val_644_ = lean_string_utf8_extract(v_arg_629_, v___x_642_, v___x_633_);
lean_dec_ref(v_arg_629_);
v___x_645_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_636_, v_name_643_);
lean_dec(v_a_636_);
if (lean_obj_tag(v___x_645_) == 1)
{
lean_object* v_val_646_; lean_object* v___x_647_; 
lean_del_object(v___x_638_);
v_val_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_val_646_);
lean_dec_ref(v___x_645_);
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
lean_dec_ref(v___x_727_);
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
lean_dec_ref(v___x_757_);
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
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = l_System_Platform_numBits;
v___x_918_ = lean_unsigned_to_nat(2u);
v___x_919_ = lean_nat_pow(v___x_918_, v___x_917_);
return v___x_919_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1(void){
_start:
{
uint32_t v___x_929_; lean_object* v___x_930_; 
v___x_929_ = 0;
v___x_930_ = lean_box_uint32(v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object* v_opts_931_, uint32_t v_opt_932_, lean_object* v_optArg_x3f_933_){
_start:
{
lean_object* v___y_1035_; uint32_t v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = 101;
v___x_1132_ = lean_uint32_dec_eq(v_opt_932_, v___x_1131_);
if (v___x_1132_ == 0)
{
uint32_t v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = 106;
v___x_1134_ = lean_uint32_dec_eq(v_opt_932_, v___x_1133_);
if (v___x_1134_ == 0)
{
uint32_t v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = 118;
v___x_1136_ = lean_uint32_dec_eq(v_opt_932_, v___x_1135_);
if (v___x_1136_ == 0)
{
uint32_t v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = 86;
v___x_1138_ = lean_uint32_dec_eq(v_opt_932_, v___x_1137_);
if (v___x_1138_ == 0)
{
uint32_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = 103;
v___x_1140_ = lean_uint32_dec_eq(v_opt_932_, v___x_1139_);
if (v___x_1140_ == 0)
{
uint32_t v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = 104;
v___x_1142_ = lean_uint32_dec_eq(v_opt_932_, v___x_1141_);
if (v___x_1142_ == 0)
{
uint32_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = 102;
v___x_1144_ = lean_uint32_dec_eq(v_opt_932_, v___x_1143_);
if (v___x_1144_ == 0)
{
uint32_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = 99;
v___x_1146_ = lean_uint32_dec_eq(v_opt_932_, v___x_1145_);
if (v___x_1146_ == 0)
{
uint32_t v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = 98;
v___x_1148_ = lean_uint32_dec_eq(v_opt_932_, v___x_1147_);
if (v___x_1148_ == 0)
{
uint32_t v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = 115;
v___x_1150_ = lean_uint32_dec_eq(v_opt_932_, v___x_1149_);
if (v___x_1150_ == 0)
{
uint32_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = 73;
v___x_1152_ = lean_uint32_dec_eq(v_opt_932_, v___x_1151_);
if (v___x_1152_ == 0)
{
uint32_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = 114;
v___x_1154_ = lean_uint32_dec_eq(v_opt_932_, v___x_1153_);
if (v___x_1154_ == 0)
{
uint32_t v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = 111;
v___x_1156_ = lean_uint32_dec_eq(v_opt_932_, v___x_1155_);
if (v___x_1156_ == 0)
{
uint32_t v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = 105;
v___x_1158_ = lean_uint32_dec_eq(v_opt_932_, v___x_1157_);
if (v___x_1158_ == 0)
{
uint32_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = 82;
v___x_1160_ = lean_uint32_dec_eq(v_opt_932_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint32_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = 77;
v___x_1162_ = lean_uint32_dec_eq(v_opt_932_, v___x_1161_);
if (v___x_1162_ == 0)
{
uint32_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = 84;
v___x_1164_ = lean_uint32_dec_eq(v_opt_932_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint32_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = 116;
v___x_1166_ = lean_uint32_dec_eq(v_opt_932_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint32_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = 113;
v___x_1168_ = lean_uint32_dec_eq(v_opt_932_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint32_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = 100;
v___x_1170_ = lean_uint32_dec_eq(v_opt_932_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint32_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = 79;
v___x_1172_ = lean_uint32_dec_eq(v_opt_932_, v___x_1171_);
if (v___x_1172_ == 0)
{
uint32_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 78;
v___x_1174_ = lean_uint32_dec_eq(v_opt_932_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint32_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = 74;
v___x_1176_ = lean_uint32_dec_eq(v_opt_932_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint32_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = 97;
v___x_1178_ = lean_uint32_dec_eq(v_opt_932_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint32_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = 120;
v___x_1180_ = lean_uint32_dec_eq(v_opt_932_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint32_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = 76;
v___x_1182_ = lean_uint32_dec_eq(v_opt_932_, v___x_1181_);
if (v___x_1182_ == 0)
{
uint32_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = 68;
v___x_1184_ = lean_uint32_dec_eq(v_opt_932_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint32_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = 83;
v___x_1186_ = lean_uint32_dec_eq(v_opt_932_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint32_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = 87;
v___x_1188_ = lean_uint32_dec_eq(v_opt_932_, v___x_1187_);
if (v___x_1188_ == 0)
{
uint32_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = 80;
v___x_1190_ = lean_uint32_dec_eq(v_opt_932_, v___x_1189_);
if (v___x_1190_ == 0)
{
uint32_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = 66;
v___x_1192_ = lean_uint32_dec_eq(v_opt_932_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint32_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = 112;
v___x_1194_ = lean_uint32_dec_eq(v_opt_932_, v___x_1193_);
if (v___x_1194_ == 0)
{
uint32_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = 108;
v___x_1196_ = lean_uint32_dec_eq(v_opt_932_, v___x_1195_);
if (v___x_1196_ == 0)
{
uint32_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = 117;
v___x_1198_ = lean_uint32_dec_eq(v_opt_932_, v___x_1197_);
if (v___x_1198_ == 0)
{
uint32_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 69;
v___x_1200_ = lean_uint32_dec_eq(v_opt_932_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
goto v___jp_1053_;
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1202_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1201_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1241_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1241_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1241_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v_leanOpts_1207_; lean_object* v_forwardedArgs_1208_; uint8_t v_component_1209_; uint8_t v_printPrefix_1210_; uint8_t v_printLibDir_1211_; uint8_t v_useStdin_1212_; uint8_t v_onlyDeps_1213_; uint8_t v_onlySrcDeps_1214_; uint8_t v_depsJson_1215_; lean_object* v_opts_1216_; uint32_t v_trustLevel_1217_; uint32_t v_numThreads_1218_; lean_object* v_rootDir_x3f_1219_; lean_object* v_setupFileName_x3f_1220_; lean_object* v_oleanFileName_x3f_1221_; lean_object* v_ileanFileName_x3f_1222_; lean_object* v_cFileName_x3f_1223_; lean_object* v_bcFileName_x3f_1224_; uint8_t v_jsonOutput_1225_; lean_object* v_errorOnKinds_1226_; uint8_t v_printStats_1227_; uint8_t v_run_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1240_; 
v_leanOpts_1207_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1208_ = lean_ctor_get(v_opts_931_, 1);
v_component_1209_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1210_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1211_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1212_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1213_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1214_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1215_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1216_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1217_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1218_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1219_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1220_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1221_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1222_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1223_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1224_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1225_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1226_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1227_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1228_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1230_ = v_opts_931_;
v_isShared_1231_ = v_isSharedCheck_1240_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_errorOnKinds_1226_);
lean_inc(v_bcFileName_x3f_1224_);
lean_inc(v_cFileName_x3f_1223_);
lean_inc(v_ileanFileName_x3f_1222_);
lean_inc(v_oleanFileName_x3f_1221_);
lean_inc(v_setupFileName_x3f_1220_);
lean_inc(v_rootDir_x3f_1219_);
lean_inc(v_opts_1216_);
lean_inc(v_forwardedArgs_1208_);
lean_inc(v_leanOpts_1207_);
lean_dec(v_opts_931_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1240_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1232_ = l_String_toName(v_a_1203_);
v___x_1233_ = lean_array_push(v_errorOnKinds_1226_, v___x_1232_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 9, v___x_1233_);
v___x_1235_ = v___x_1230_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_leanOpts_1207_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_forwardedArgs_1208_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_opts_1216_);
lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_rootDir_x3f_1219_);
lean_ctor_set(v_reuseFailAlloc_1239_, 4, v_setupFileName_x3f_1220_);
lean_ctor_set(v_reuseFailAlloc_1239_, 5, v_oleanFileName_x3f_1221_);
lean_ctor_set(v_reuseFailAlloc_1239_, 6, v_ileanFileName_x3f_1222_);
lean_ctor_set(v_reuseFailAlloc_1239_, 7, v_cFileName_x3f_1223_);
lean_ctor_set(v_reuseFailAlloc_1239_, 8, v_bcFileName_x3f_1224_);
lean_ctor_set(v_reuseFailAlloc_1239_, 9, v___x_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1239_, sizeof(void*)*10 + 8, v_component_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1239_, sizeof(void*)*10 + 9, v_printPrefix_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1239_, sizeof(void*)*10 + 10, v_printLibDir_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1239_, sizeof(void*)*10 + 11, v_useStdin_1212_);
lean_ctor_set_uint8(v_reuseFailAlloc_1239_, sizeof(void*)*10 + 12, v_onlyDeps_1213_);
lean_ctor_set_uint8(v_reuseFailAlloc_1239_, sizeof(void*)*10 + 13, v_onlySrcDeps_1214_);
lean_ctor_set_uint8(v_reuseFailAlloc_1239_, sizeof(void*)*10 + 14, v_depsJson_1215_);
lean_ctor_set_uint32(v_reuseFailAlloc_1239_, sizeof(void*)*10, v_trustLevel_1217_);
lean_ctor_set_uint32(v_reuseFailAlloc_1239_, sizeof(void*)*10 + 4, v_numThreads_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1239_, sizeof(void*)*10 + 15, v_jsonOutput_1225_);
lean_ctor_set_uint8(v_reuseFailAlloc_1239_, sizeof(void*)*10 + 16, v_printStats_1227_);
lean_ctor_set_uint8(v_reuseFailAlloc_1239_, sizeof(void*)*10 + 17, v_run_1228_);
v___x_1235_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1237_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1235_);
v___x_1237_ = v___x_1205_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec_ref(v_opts_931_);
v_a_1242_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1242_);
lean_dec_ref(v___x_1202_);
v___x_1246_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1247_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1246_);
lean_dec_ref(v___x_1247_);
goto v___jp_1243_;
v___jp_1243_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_io_error_to_string(v_a_1242_);
v___x_1245_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1244_);
lean_dec_ref(v___x_1245_);
goto v___jp_1059_;
}
}
}
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1249_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1248_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1287_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1287_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1287_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_leanOpts_1254_; lean_object* v_forwardedArgs_1255_; uint8_t v_component_1256_; uint8_t v_printPrefix_1257_; uint8_t v_printLibDir_1258_; uint8_t v_useStdin_1259_; uint8_t v_onlyDeps_1260_; uint8_t v_onlySrcDeps_1261_; uint8_t v_depsJson_1262_; lean_object* v_opts_1263_; uint32_t v_trustLevel_1264_; uint32_t v_numThreads_1265_; lean_object* v_rootDir_x3f_1266_; lean_object* v_oleanFileName_x3f_1267_; lean_object* v_ileanFileName_x3f_1268_; lean_object* v_cFileName_x3f_1269_; lean_object* v_bcFileName_x3f_1270_; uint8_t v_jsonOutput_1271_; lean_object* v_errorOnKinds_1272_; uint8_t v_printStats_1273_; uint8_t v_run_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1285_; 
v_leanOpts_1254_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1255_ = lean_ctor_get(v_opts_931_, 1);
v_component_1256_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1257_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1258_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1259_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1260_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1261_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1262_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1263_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1264_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1265_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1266_ = lean_ctor_get(v_opts_931_, 3);
v_oleanFileName_x3f_1267_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1268_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1269_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1270_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1271_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1272_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1273_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1274_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v_opts_931_, 4);
lean_dec(v_unused_1286_);
v___x_1276_ = v_opts_931_;
v_isShared_1277_ = v_isSharedCheck_1285_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_errorOnKinds_1272_);
lean_inc(v_bcFileName_x3f_1270_);
lean_inc(v_cFileName_x3f_1269_);
lean_inc(v_ileanFileName_x3f_1268_);
lean_inc(v_oleanFileName_x3f_1267_);
lean_inc(v_rootDir_x3f_1266_);
lean_inc(v_opts_1263_);
lean_inc(v_forwardedArgs_1255_);
lean_inc(v_leanOpts_1254_);
lean_dec(v_opts_931_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1285_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1278_, 0, v_a_1250_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 4, v___x_1278_);
v___x_1280_ = v___x_1276_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_leanOpts_1254_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_forwardedArgs_1255_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_opts_1263_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_rootDir_x3f_1266_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1284_, 5, v_oleanFileName_x3f_1267_);
lean_ctor_set(v_reuseFailAlloc_1284_, 6, v_ileanFileName_x3f_1268_);
lean_ctor_set(v_reuseFailAlloc_1284_, 7, v_cFileName_x3f_1269_);
lean_ctor_set(v_reuseFailAlloc_1284_, 8, v_bcFileName_x3f_1270_);
lean_ctor_set(v_reuseFailAlloc_1284_, 9, v_errorOnKinds_1272_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*10 + 8, v_component_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*10 + 9, v_printPrefix_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*10 + 10, v_printLibDir_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*10 + 11, v_useStdin_1259_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*10 + 12, v_onlyDeps_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*10 + 13, v_onlySrcDeps_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*10 + 14, v_depsJson_1262_);
lean_ctor_set_uint32(v_reuseFailAlloc_1284_, sizeof(void*)*10, v_trustLevel_1264_);
lean_ctor_set_uint32(v_reuseFailAlloc_1284_, sizeof(void*)*10 + 4, v_numThreads_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*10 + 15, v_jsonOutput_1271_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*10 + 16, v_printStats_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1284_, sizeof(void*)*10 + 17, v_run_1274_);
v___x_1280_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1282_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1280_);
v___x_1282_ = v___x_1252_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_dec_ref(v_opts_931_);
v_a_1288_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1288_);
lean_dec_ref(v___x_1249_);
v___x_1292_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1293_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1292_);
lean_dec_ref(v___x_1293_);
goto v___jp_1289_;
v___jp_1289_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_io_error_to_string(v_a_1288_);
v___x_1291_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1290_);
lean_dec_ref(v___x_1291_);
goto v___jp_1025_;
}
}
}
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1295_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1294_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1297_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc_n(v_a_1296_, 2);
lean_dec_ref(v___x_1295_);
v___x_1297_ = lean_load_dynlib(v_a_1296_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1336_; 
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v___x_1297_, 0);
lean_dec(v_unused_1337_);
v___x_1299_ = v___x_1297_;
v_isShared_1300_ = v_isSharedCheck_1336_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v___x_1297_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1336_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v_leanOpts_1301_; lean_object* v_forwardedArgs_1302_; uint8_t v_component_1303_; uint8_t v_printPrefix_1304_; uint8_t v_printLibDir_1305_; uint8_t v_useStdin_1306_; uint8_t v_onlyDeps_1307_; uint8_t v_onlySrcDeps_1308_; uint8_t v_depsJson_1309_; lean_object* v_opts_1310_; uint32_t v_trustLevel_1311_; uint32_t v_numThreads_1312_; lean_object* v_rootDir_x3f_1313_; lean_object* v_setupFileName_x3f_1314_; lean_object* v_oleanFileName_x3f_1315_; lean_object* v_ileanFileName_x3f_1316_; lean_object* v_cFileName_x3f_1317_; lean_object* v_bcFileName_x3f_1318_; uint8_t v_jsonOutput_1319_; lean_object* v_errorOnKinds_1320_; uint8_t v_printStats_1321_; uint8_t v_run_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1335_; 
v_leanOpts_1301_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1302_ = lean_ctor_get(v_opts_931_, 1);
v_component_1303_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1304_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1305_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1306_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1307_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1308_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1309_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1310_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1311_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1312_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1313_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1314_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1315_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1316_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1317_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1318_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1319_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1320_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1321_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1322_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1324_ = v_opts_931_;
v_isShared_1325_ = v_isSharedCheck_1335_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_errorOnKinds_1320_);
lean_inc(v_bcFileName_x3f_1318_);
lean_inc(v_cFileName_x3f_1317_);
lean_inc(v_ileanFileName_x3f_1316_);
lean_inc(v_oleanFileName_x3f_1315_);
lean_inc(v_setupFileName_x3f_1314_);
lean_inc(v_rootDir_x3f_1313_);
lean_inc(v_opts_1310_);
lean_inc(v_forwardedArgs_1302_);
lean_inc(v_leanOpts_1301_);
lean_dec(v_opts_931_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1335_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1326_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1327_ = lean_string_append(v___x_1326_, v_a_1296_);
lean_dec(v_a_1296_);
v___x_1328_ = lean_array_push(v_forwardedArgs_1302_, v___x_1327_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v___x_1328_);
v___x_1330_ = v___x_1324_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_leanOpts_1301_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_opts_1310_);
lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_rootDir_x3f_1313_);
lean_ctor_set(v_reuseFailAlloc_1334_, 4, v_setupFileName_x3f_1314_);
lean_ctor_set(v_reuseFailAlloc_1334_, 5, v_oleanFileName_x3f_1315_);
lean_ctor_set(v_reuseFailAlloc_1334_, 6, v_ileanFileName_x3f_1316_);
lean_ctor_set(v_reuseFailAlloc_1334_, 7, v_cFileName_x3f_1317_);
lean_ctor_set(v_reuseFailAlloc_1334_, 8, v_bcFileName_x3f_1318_);
lean_ctor_set(v_reuseFailAlloc_1334_, 9, v_errorOnKinds_1320_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*10 + 8, v_component_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*10 + 9, v_printPrefix_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*10 + 10, v_printLibDir_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*10 + 11, v_useStdin_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*10 + 12, v_onlyDeps_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*10 + 13, v_onlySrcDeps_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*10 + 14, v_depsJson_1309_);
lean_ctor_set_uint32(v_reuseFailAlloc_1334_, sizeof(void*)*10, v_trustLevel_1311_);
lean_ctor_set_uint32(v_reuseFailAlloc_1334_, sizeof(void*)*10 + 4, v_numThreads_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*10 + 15, v_jsonOutput_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*10 + 16, v_printStats_1321_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*10 + 17, v_run_1322_);
v___x_1330_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1332_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1330_);
v___x_1332_ = v___x_1299_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec(v_a_1296_);
lean_dec_ref(v_opts_931_);
v_a_1338_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1297_);
v___x_1342_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1343_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1342_);
lean_dec_ref(v___x_1343_);
goto v___jp_1339_;
v___jp_1339_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_io_error_to_string(v_a_1338_);
v___x_1341_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1340_);
lean_dec_ref(v___x_1341_);
goto v___jp_1065_;
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec_ref(v_opts_931_);
v_a_1344_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1295_);
v___x_1348_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1349_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1348_);
lean_dec_ref(v___x_1349_);
goto v___jp_1345_;
v___jp_1345_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_io_error_to_string(v_a_1344_);
v___x_1347_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1346_);
lean_dec_ref(v___x_1347_);
goto v___jp_1019_;
}
}
}
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1351_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1350_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1353_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc_n(v_a_1352_, 2);
lean_dec_ref(v___x_1351_);
v___x_1353_ = lean_load_plugin(v_a_1352_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1392_; 
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v___x_1353_, 0);
lean_dec(v_unused_1393_);
v___x_1355_ = v___x_1353_;
v_isShared_1356_ = v_isSharedCheck_1392_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v___x_1353_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1392_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v_leanOpts_1357_; lean_object* v_forwardedArgs_1358_; uint8_t v_component_1359_; uint8_t v_printPrefix_1360_; uint8_t v_printLibDir_1361_; uint8_t v_useStdin_1362_; uint8_t v_onlyDeps_1363_; uint8_t v_onlySrcDeps_1364_; uint8_t v_depsJson_1365_; lean_object* v_opts_1366_; uint32_t v_trustLevel_1367_; uint32_t v_numThreads_1368_; lean_object* v_rootDir_x3f_1369_; lean_object* v_setupFileName_x3f_1370_; lean_object* v_oleanFileName_x3f_1371_; lean_object* v_ileanFileName_x3f_1372_; lean_object* v_cFileName_x3f_1373_; lean_object* v_bcFileName_x3f_1374_; uint8_t v_jsonOutput_1375_; lean_object* v_errorOnKinds_1376_; uint8_t v_printStats_1377_; uint8_t v_run_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1391_; 
v_leanOpts_1357_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1358_ = lean_ctor_get(v_opts_931_, 1);
v_component_1359_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1360_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1361_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1362_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1363_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1364_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1365_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1366_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1367_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1368_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1369_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1370_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1371_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1372_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1373_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1374_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1375_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1376_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1377_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1378_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1380_ = v_opts_931_;
v_isShared_1381_ = v_isSharedCheck_1391_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_errorOnKinds_1376_);
lean_inc(v_bcFileName_x3f_1374_);
lean_inc(v_cFileName_x3f_1373_);
lean_inc(v_ileanFileName_x3f_1372_);
lean_inc(v_oleanFileName_x3f_1371_);
lean_inc(v_setupFileName_x3f_1370_);
lean_inc(v_rootDir_x3f_1369_);
lean_inc(v_opts_1366_);
lean_inc(v_forwardedArgs_1358_);
lean_inc(v_leanOpts_1357_);
lean_dec(v_opts_931_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1391_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1382_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1383_ = lean_string_append(v___x_1382_, v_a_1352_);
lean_dec(v_a_1352_);
v___x_1384_ = lean_array_push(v_forwardedArgs_1358_, v___x_1383_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v___x_1384_);
v___x_1386_ = v___x_1380_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_leanOpts_1357_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_opts_1366_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_rootDir_x3f_1369_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_setupFileName_x3f_1370_);
lean_ctor_set(v_reuseFailAlloc_1390_, 5, v_oleanFileName_x3f_1371_);
lean_ctor_set(v_reuseFailAlloc_1390_, 6, v_ileanFileName_x3f_1372_);
lean_ctor_set(v_reuseFailAlloc_1390_, 7, v_cFileName_x3f_1373_);
lean_ctor_set(v_reuseFailAlloc_1390_, 8, v_bcFileName_x3f_1374_);
lean_ctor_set(v_reuseFailAlloc_1390_, 9, v_errorOnKinds_1376_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*10 + 8, v_component_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*10 + 9, v_printPrefix_1360_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*10 + 10, v_printLibDir_1361_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*10 + 11, v_useStdin_1362_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*10 + 12, v_onlyDeps_1363_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*10 + 13, v_onlySrcDeps_1364_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*10 + 14, v_depsJson_1365_);
lean_ctor_set_uint32(v_reuseFailAlloc_1390_, sizeof(void*)*10, v_trustLevel_1367_);
lean_ctor_set_uint32(v_reuseFailAlloc_1390_, sizeof(void*)*10 + 4, v_numThreads_1368_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*10 + 15, v_jsonOutput_1375_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*10 + 16, v_printStats_1377_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*10 + 17, v_run_1378_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1386_);
v___x_1388_ = v___x_1355_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec(v_a_1352_);
lean_dec_ref(v_opts_931_);
v_a_1394_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1394_);
lean_dec_ref(v___x_1353_);
v___x_1398_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1399_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1398_);
lean_dec_ref(v___x_1399_);
goto v___jp_1395_;
v___jp_1395_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_io_error_to_string(v_a_1394_);
v___x_1397_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1396_);
lean_dec_ref(v___x_1397_);
goto v___jp_1071_;
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec_ref(v_opts_931_);
v_a_1400_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1400_);
lean_dec_ref(v___x_1351_);
v___x_1404_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1405_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1404_);
lean_dec_ref(v___x_1405_);
goto v___jp_1401_;
v___jp_1401_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_io_error_to_string(v_a_1400_);
v___x_1403_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1402_);
lean_dec_ref(v___x_1403_);
goto v___jp_1013_;
}
}
}
}
else
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__12, &l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12);
if (v___x_1406_ == 0)
{
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
goto v___jp_1053_;
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1408_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1407_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1417_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1417_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1417_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1413_ = lean_internal_enable_debug(v_a_1409_);
lean_dec(v_a_1409_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v_opts_931_);
v___x_1415_ = v___x_1411_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_opts_931_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref(v_opts_931_);
v_a_1418_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1408_);
v___x_1422_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1423_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1422_);
lean_dec_ref(v___x_1423_);
goto v___jp_1419_;
v___jp_1419_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = lean_io_error_to_string(v_a_1418_);
v___x_1421_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1420_);
lean_dec_ref(v___x_1421_);
goto v___jp_1077_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1424_; lean_object* v_forwardedArgs_1425_; uint8_t v_component_1426_; uint8_t v_printPrefix_1427_; uint8_t v_printLibDir_1428_; uint8_t v_useStdin_1429_; uint8_t v_onlyDeps_1430_; uint8_t v_onlySrcDeps_1431_; uint8_t v_depsJson_1432_; lean_object* v_opts_1433_; uint32_t v_trustLevel_1434_; uint32_t v_numThreads_1435_; lean_object* v_rootDir_x3f_1436_; lean_object* v_setupFileName_x3f_1437_; lean_object* v_oleanFileName_x3f_1438_; lean_object* v_ileanFileName_x3f_1439_; lean_object* v_cFileName_x3f_1440_; lean_object* v_bcFileName_x3f_1441_; uint8_t v_jsonOutput_1442_; lean_object* v_errorOnKinds_1443_; uint8_t v_printStats_1444_; uint8_t v_run_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1424_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1425_ = lean_ctor_get(v_opts_931_, 1);
v_component_1426_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1427_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1428_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1429_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1430_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1431_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1432_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1433_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1434_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1435_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1436_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1437_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1438_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1439_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1440_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1441_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1442_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1443_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1444_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1445_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1447_ = v_opts_931_;
v_isShared_1448_ = v_isSharedCheck_1455_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_errorOnKinds_1443_);
lean_inc(v_bcFileName_x3f_1441_);
lean_inc(v_cFileName_x3f_1440_);
lean_inc(v_ileanFileName_x3f_1439_);
lean_inc(v_oleanFileName_x3f_1438_);
lean_inc(v_setupFileName_x3f_1437_);
lean_inc(v_rootDir_x3f_1436_);
lean_inc(v_opts_1433_);
lean_inc(v_forwardedArgs_1425_);
lean_inc(v_leanOpts_1424_);
lean_dec(v_opts_931_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1455_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1449_ = l_Lean_profiler;
v___x_1450_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1424_, v___x_1449_, v___x_1190_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1450_);
v___x_1452_ = v___x_1447_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_forwardedArgs_1425_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_opts_1433_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v_rootDir_x3f_1436_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v_setupFileName_x3f_1437_);
lean_ctor_set(v_reuseFailAlloc_1454_, 5, v_oleanFileName_x3f_1438_);
lean_ctor_set(v_reuseFailAlloc_1454_, 6, v_ileanFileName_x3f_1439_);
lean_ctor_set(v_reuseFailAlloc_1454_, 7, v_cFileName_x3f_1440_);
lean_ctor_set(v_reuseFailAlloc_1454_, 8, v_bcFileName_x3f_1441_);
lean_ctor_set(v_reuseFailAlloc_1454_, 9, v_errorOnKinds_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*10 + 8, v_component_1426_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*10 + 9, v_printPrefix_1427_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*10 + 10, v_printLibDir_1428_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*10 + 11, v_useStdin_1429_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*10 + 12, v_onlyDeps_1430_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*10 + 13, v_onlySrcDeps_1431_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*10 + 14, v_depsJson_1432_);
lean_ctor_set_uint32(v_reuseFailAlloc_1454_, sizeof(void*)*10, v_trustLevel_1434_);
lean_ctor_set_uint32(v_reuseFailAlloc_1454_, sizeof(void*)*10 + 4, v_numThreads_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*10 + 15, v_jsonOutput_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*10 + 16, v_printStats_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*10 + 17, v_run_1445_);
v___x_1452_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
}
}
}
else
{
lean_object* v_leanOpts_1456_; lean_object* v_forwardedArgs_1457_; uint8_t v_printPrefix_1458_; uint8_t v_printLibDir_1459_; uint8_t v_useStdin_1460_; uint8_t v_onlyDeps_1461_; uint8_t v_onlySrcDeps_1462_; uint8_t v_depsJson_1463_; lean_object* v_opts_1464_; uint32_t v_trustLevel_1465_; uint32_t v_numThreads_1466_; lean_object* v_rootDir_x3f_1467_; lean_object* v_setupFileName_x3f_1468_; lean_object* v_oleanFileName_x3f_1469_; lean_object* v_ileanFileName_x3f_1470_; lean_object* v_cFileName_x3f_1471_; lean_object* v_bcFileName_x3f_1472_; uint8_t v_jsonOutput_1473_; lean_object* v_errorOnKinds_1474_; uint8_t v_printStats_1475_; uint8_t v_run_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1456_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1457_ = lean_ctor_get(v_opts_931_, 1);
v_printPrefix_1458_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1459_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1460_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1461_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1462_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1463_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1464_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1465_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1466_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1467_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1468_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1469_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1470_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1471_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1472_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1473_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1474_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1475_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1476_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1478_ = v_opts_931_;
v_isShared_1479_ = v_isSharedCheck_1485_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_errorOnKinds_1474_);
lean_inc(v_bcFileName_x3f_1472_);
lean_inc(v_cFileName_x3f_1471_);
lean_inc(v_ileanFileName_x3f_1470_);
lean_inc(v_oleanFileName_x3f_1469_);
lean_inc(v_setupFileName_x3f_1468_);
lean_inc(v_rootDir_x3f_1467_);
lean_inc(v_opts_1464_);
lean_inc(v_forwardedArgs_1457_);
lean_inc(v_leanOpts_1456_);
lean_dec(v_opts_931_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1485_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
uint8_t v___x_1480_; lean_object* v___x_1482_; 
v___x_1480_ = 2;
if (v_isShared_1479_ == 0)
{
v___x_1482_ = v___x_1478_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_leanOpts_1456_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_forwardedArgs_1457_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_opts_1464_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_rootDir_x3f_1467_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_setupFileName_x3f_1468_);
lean_ctor_set(v_reuseFailAlloc_1484_, 5, v_oleanFileName_x3f_1469_);
lean_ctor_set(v_reuseFailAlloc_1484_, 6, v_ileanFileName_x3f_1470_);
lean_ctor_set(v_reuseFailAlloc_1484_, 7, v_cFileName_x3f_1471_);
lean_ctor_set(v_reuseFailAlloc_1484_, 8, v_bcFileName_x3f_1472_);
lean_ctor_set(v_reuseFailAlloc_1484_, 9, v_errorOnKinds_1474_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*10 + 9, v_printPrefix_1458_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*10 + 10, v_printLibDir_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*10 + 11, v_useStdin_1460_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*10 + 12, v_onlyDeps_1461_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*10 + 13, v_onlySrcDeps_1462_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*10 + 14, v_depsJson_1463_);
lean_ctor_set_uint32(v_reuseFailAlloc_1484_, sizeof(void*)*10, v_trustLevel_1465_);
lean_ctor_set_uint32(v_reuseFailAlloc_1484_, sizeof(void*)*10 + 4, v_numThreads_1466_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*10 + 15, v_jsonOutput_1473_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*10 + 16, v_printStats_1475_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*10 + 17, v_run_1476_);
v___x_1482_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1483_; 
lean_ctor_set_uint8(v___x_1482_, sizeof(void*)*10 + 8, v___x_1480_);
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
}
}
}
else
{
lean_object* v_leanOpts_1486_; lean_object* v_forwardedArgs_1487_; uint8_t v_printPrefix_1488_; uint8_t v_printLibDir_1489_; uint8_t v_useStdin_1490_; uint8_t v_onlyDeps_1491_; uint8_t v_onlySrcDeps_1492_; uint8_t v_depsJson_1493_; lean_object* v_opts_1494_; uint32_t v_trustLevel_1495_; uint32_t v_numThreads_1496_; lean_object* v_rootDir_x3f_1497_; lean_object* v_setupFileName_x3f_1498_; lean_object* v_oleanFileName_x3f_1499_; lean_object* v_ileanFileName_x3f_1500_; lean_object* v_cFileName_x3f_1501_; lean_object* v_bcFileName_x3f_1502_; uint8_t v_jsonOutput_1503_; lean_object* v_errorOnKinds_1504_; uint8_t v_printStats_1505_; uint8_t v_run_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1486_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1487_ = lean_ctor_get(v_opts_931_, 1);
v_printPrefix_1488_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1489_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1490_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1491_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1492_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1493_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1494_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1495_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1496_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1497_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1498_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1499_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1500_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1501_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1502_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1503_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1504_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1505_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1506_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1508_ = v_opts_931_;
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_errorOnKinds_1504_);
lean_inc(v_bcFileName_x3f_1502_);
lean_inc(v_cFileName_x3f_1501_);
lean_inc(v_ileanFileName_x3f_1500_);
lean_inc(v_oleanFileName_x3f_1499_);
lean_inc(v_setupFileName_x3f_1498_);
lean_inc(v_rootDir_x3f_1497_);
lean_inc(v_opts_1494_);
lean_inc(v_forwardedArgs_1487_);
lean_inc(v_leanOpts_1486_);
lean_dec(v_opts_931_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
uint8_t v___x_1510_; lean_object* v___x_1512_; 
v___x_1510_ = 1;
if (v_isShared_1509_ == 0)
{
v___x_1512_ = v___x_1508_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_leanOpts_1486_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_forwardedArgs_1487_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_opts_1494_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_rootDir_x3f_1497_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_setupFileName_x3f_1498_);
lean_ctor_set(v_reuseFailAlloc_1514_, 5, v_oleanFileName_x3f_1499_);
lean_ctor_set(v_reuseFailAlloc_1514_, 6, v_ileanFileName_x3f_1500_);
lean_ctor_set(v_reuseFailAlloc_1514_, 7, v_cFileName_x3f_1501_);
lean_ctor_set(v_reuseFailAlloc_1514_, 8, v_bcFileName_x3f_1502_);
lean_ctor_set(v_reuseFailAlloc_1514_, 9, v_errorOnKinds_1504_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*10 + 9, v_printPrefix_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*10 + 10, v_printLibDir_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*10 + 11, v_useStdin_1490_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*10 + 12, v_onlyDeps_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*10 + 13, v_onlySrcDeps_1492_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*10 + 14, v_depsJson_1493_);
lean_ctor_set_uint32(v_reuseFailAlloc_1514_, sizeof(void*)*10, v_trustLevel_1495_);
lean_ctor_set_uint32(v_reuseFailAlloc_1514_, sizeof(void*)*10 + 4, v_numThreads_1496_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*10 + 15, v_jsonOutput_1503_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*10 + 16, v_printStats_1505_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*10 + 17, v_run_1506_);
v___x_1512_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; 
lean_ctor_set_uint8(v___x_1512_, sizeof(void*)*10 + 8, v___x_1510_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
}
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1517_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1516_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v_leanOpts_1519_; lean_object* v_forwardedArgs_1520_; uint8_t v_component_1521_; uint8_t v_printPrefix_1522_; uint8_t v_printLibDir_1523_; uint8_t v_useStdin_1524_; uint8_t v_onlyDeps_1525_; uint8_t v_onlySrcDeps_1526_; uint8_t v_depsJson_1527_; lean_object* v_opts_1528_; uint32_t v_trustLevel_1529_; uint32_t v_numThreads_1530_; lean_object* v_rootDir_x3f_1531_; lean_object* v_setupFileName_x3f_1532_; lean_object* v_oleanFileName_x3f_1533_; lean_object* v_ileanFileName_x3f_1534_; lean_object* v_cFileName_x3f_1535_; lean_object* v_bcFileName_x3f_1536_; uint8_t v_jsonOutput_1537_; lean_object* v_errorOnKinds_1538_; uint8_t v_printStats_1539_; uint8_t v_run_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1565_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref(v___x_1517_);
v_leanOpts_1519_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1520_ = lean_ctor_get(v_opts_931_, 1);
v_component_1521_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1522_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1523_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1524_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1525_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1526_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1527_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1528_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1529_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1530_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1531_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1532_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1533_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1534_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1535_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1536_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1537_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1538_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1539_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1540_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1542_ = v_opts_931_;
v_isShared_1543_ = v_isSharedCheck_1565_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_errorOnKinds_1538_);
lean_inc(v_bcFileName_x3f_1536_);
lean_inc(v_cFileName_x3f_1535_);
lean_inc(v_ileanFileName_x3f_1534_);
lean_inc(v_oleanFileName_x3f_1533_);
lean_inc(v_setupFileName_x3f_1532_);
lean_inc(v_rootDir_x3f_1531_);
lean_inc(v_opts_1528_);
lean_inc(v_forwardedArgs_1520_);
lean_inc(v_leanOpts_1519_);
lean_dec(v_opts_931_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1565_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; 
lean_inc(v_a_1518_);
v___x_1544_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1519_, v_a_1518_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1558_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1558_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1558_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1549_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1550_ = lean_string_append(v___x_1549_, v_a_1518_);
lean_dec(v_a_1518_);
v___x_1551_ = lean_array_push(v_forwardedArgs_1520_, v___x_1550_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 1, v___x_1551_);
lean_ctor_set(v___x_1542_, 0, v_a_1545_);
v___x_1553_ = v___x_1542_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1545_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1557_, 2, v_opts_1528_);
lean_ctor_set(v_reuseFailAlloc_1557_, 3, v_rootDir_x3f_1531_);
lean_ctor_set(v_reuseFailAlloc_1557_, 4, v_setupFileName_x3f_1532_);
lean_ctor_set(v_reuseFailAlloc_1557_, 5, v_oleanFileName_x3f_1533_);
lean_ctor_set(v_reuseFailAlloc_1557_, 6, v_ileanFileName_x3f_1534_);
lean_ctor_set(v_reuseFailAlloc_1557_, 7, v_cFileName_x3f_1535_);
lean_ctor_set(v_reuseFailAlloc_1557_, 8, v_bcFileName_x3f_1536_);
lean_ctor_set(v_reuseFailAlloc_1557_, 9, v_errorOnKinds_1538_);
lean_ctor_set_uint8(v_reuseFailAlloc_1557_, sizeof(void*)*10 + 8, v_component_1521_);
lean_ctor_set_uint8(v_reuseFailAlloc_1557_, sizeof(void*)*10 + 9, v_printPrefix_1522_);
lean_ctor_set_uint8(v_reuseFailAlloc_1557_, sizeof(void*)*10 + 10, v_printLibDir_1523_);
lean_ctor_set_uint8(v_reuseFailAlloc_1557_, sizeof(void*)*10 + 11, v_useStdin_1524_);
lean_ctor_set_uint8(v_reuseFailAlloc_1557_, sizeof(void*)*10 + 12, v_onlyDeps_1525_);
lean_ctor_set_uint8(v_reuseFailAlloc_1557_, sizeof(void*)*10 + 13, v_onlySrcDeps_1526_);
lean_ctor_set_uint8(v_reuseFailAlloc_1557_, sizeof(void*)*10 + 14, v_depsJson_1527_);
lean_ctor_set_uint32(v_reuseFailAlloc_1557_, sizeof(void*)*10, v_trustLevel_1529_);
lean_ctor_set_uint32(v_reuseFailAlloc_1557_, sizeof(void*)*10 + 4, v_numThreads_1530_);
lean_ctor_set_uint8(v_reuseFailAlloc_1557_, sizeof(void*)*10 + 15, v_jsonOutput_1537_);
lean_ctor_set_uint8(v_reuseFailAlloc_1557_, sizeof(void*)*10 + 16, v_printStats_1539_);
lean_ctor_set_uint8(v_reuseFailAlloc_1557_, sizeof(void*)*10 + 17, v_run_1540_);
v___x_1553_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1555_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1553_);
v___x_1555_ = v___x_1547_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_del_object(v___x_1542_);
lean_dec_ref(v_errorOnKinds_1538_);
lean_dec(v_bcFileName_x3f_1536_);
lean_dec(v_cFileName_x3f_1535_);
lean_dec(v_ileanFileName_x3f_1534_);
lean_dec(v_oleanFileName_x3f_1533_);
lean_dec(v_setupFileName_x3f_1532_);
lean_dec(v_rootDir_x3f_1531_);
lean_dec_ref(v_opts_1528_);
lean_dec_ref(v_forwardedArgs_1520_);
lean_dec(v_a_1518_);
v_a_1559_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1559_);
lean_dec_ref(v___x_1544_);
v___x_1563_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1564_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1563_);
lean_dec_ref(v___x_1564_);
goto v___jp_1560_;
v___jp_1560_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_io_error_to_string(v_a_1559_);
v___x_1562_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1561_);
lean_dec_ref(v___x_1562_);
goto v___jp_1007_;
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec_ref(v_opts_931_);
v_a_1566_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v___x_1517_);
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
goto v___jp_1083_;
}
}
}
}
else
{
lean_object* v_leanOpts_1572_; lean_object* v_forwardedArgs_1573_; uint8_t v_component_1574_; uint8_t v_printPrefix_1575_; uint8_t v_useStdin_1576_; uint8_t v_onlyDeps_1577_; uint8_t v_onlySrcDeps_1578_; uint8_t v_depsJson_1579_; lean_object* v_opts_1580_; uint32_t v_trustLevel_1581_; uint32_t v_numThreads_1582_; lean_object* v_rootDir_x3f_1583_; lean_object* v_setupFileName_x3f_1584_; lean_object* v_oleanFileName_x3f_1585_; lean_object* v_ileanFileName_x3f_1586_; lean_object* v_cFileName_x3f_1587_; lean_object* v_bcFileName_x3f_1588_; uint8_t v_jsonOutput_1589_; lean_object* v_errorOnKinds_1590_; uint8_t v_printStats_1591_; uint8_t v_run_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1600_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1572_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1573_ = lean_ctor_get(v_opts_931_, 1);
v_component_1574_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1575_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_useStdin_1576_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1577_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1578_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1579_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1580_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1581_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1582_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1583_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1584_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1585_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1586_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1587_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1588_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1589_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1590_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1591_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1592_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1594_ = v_opts_931_;
v_isShared_1595_ = v_isSharedCheck_1600_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_errorOnKinds_1590_);
lean_inc(v_bcFileName_x3f_1588_);
lean_inc(v_cFileName_x3f_1587_);
lean_inc(v_ileanFileName_x3f_1586_);
lean_inc(v_oleanFileName_x3f_1585_);
lean_inc(v_setupFileName_x3f_1584_);
lean_inc(v_rootDir_x3f_1583_);
lean_inc(v_opts_1580_);
lean_inc(v_forwardedArgs_1573_);
lean_inc(v_leanOpts_1572_);
lean_dec(v_opts_931_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1600_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_leanOpts_1572_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_forwardedArgs_1573_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_opts_1580_);
lean_ctor_set(v_reuseFailAlloc_1599_, 3, v_rootDir_x3f_1583_);
lean_ctor_set(v_reuseFailAlloc_1599_, 4, v_setupFileName_x3f_1584_);
lean_ctor_set(v_reuseFailAlloc_1599_, 5, v_oleanFileName_x3f_1585_);
lean_ctor_set(v_reuseFailAlloc_1599_, 6, v_ileanFileName_x3f_1586_);
lean_ctor_set(v_reuseFailAlloc_1599_, 7, v_cFileName_x3f_1587_);
lean_ctor_set(v_reuseFailAlloc_1599_, 8, v_bcFileName_x3f_1588_);
lean_ctor_set(v_reuseFailAlloc_1599_, 9, v_errorOnKinds_1590_);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, sizeof(void*)*10 + 8, v_component_1574_);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, sizeof(void*)*10 + 9, v_printPrefix_1575_);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, sizeof(void*)*10 + 11, v_useStdin_1576_);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, sizeof(void*)*10 + 12, v_onlyDeps_1577_);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, sizeof(void*)*10 + 13, v_onlySrcDeps_1578_);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, sizeof(void*)*10 + 14, v_depsJson_1579_);
lean_ctor_set_uint32(v_reuseFailAlloc_1599_, sizeof(void*)*10, v_trustLevel_1581_);
lean_ctor_set_uint32(v_reuseFailAlloc_1599_, sizeof(void*)*10 + 4, v_numThreads_1582_);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, sizeof(void*)*10 + 15, v_jsonOutput_1589_);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, sizeof(void*)*10 + 16, v_printStats_1591_);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, sizeof(void*)*10 + 17, v_run_1592_);
v___x_1597_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; 
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*10 + 10, v___x_1182_);
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
return v___x_1598_;
}
}
}
}
else
{
lean_object* v_leanOpts_1601_; lean_object* v_forwardedArgs_1602_; uint8_t v_component_1603_; uint8_t v_printLibDir_1604_; uint8_t v_useStdin_1605_; uint8_t v_onlyDeps_1606_; uint8_t v_onlySrcDeps_1607_; uint8_t v_depsJson_1608_; lean_object* v_opts_1609_; uint32_t v_trustLevel_1610_; uint32_t v_numThreads_1611_; lean_object* v_rootDir_x3f_1612_; lean_object* v_setupFileName_x3f_1613_; lean_object* v_oleanFileName_x3f_1614_; lean_object* v_ileanFileName_x3f_1615_; lean_object* v_cFileName_x3f_1616_; lean_object* v_bcFileName_x3f_1617_; uint8_t v_jsonOutput_1618_; lean_object* v_errorOnKinds_1619_; uint8_t v_printStats_1620_; uint8_t v_run_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1601_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1602_ = lean_ctor_get(v_opts_931_, 1);
v_component_1603_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printLibDir_1604_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1605_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1606_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1607_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1608_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1609_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1610_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1611_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1612_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1613_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1614_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1615_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1616_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1617_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1618_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1619_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1620_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1621_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1623_ = v_opts_931_;
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_errorOnKinds_1619_);
lean_inc(v_bcFileName_x3f_1617_);
lean_inc(v_cFileName_x3f_1616_);
lean_inc(v_ileanFileName_x3f_1615_);
lean_inc(v_oleanFileName_x3f_1614_);
lean_inc(v_setupFileName_x3f_1613_);
lean_inc(v_rootDir_x3f_1612_);
lean_inc(v_opts_1609_);
lean_inc(v_forwardedArgs_1602_);
lean_inc(v_leanOpts_1601_);
lean_dec(v_opts_931_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_leanOpts_1601_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_forwardedArgs_1602_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_opts_1609_);
lean_ctor_set(v_reuseFailAlloc_1628_, 3, v_rootDir_x3f_1612_);
lean_ctor_set(v_reuseFailAlloc_1628_, 4, v_setupFileName_x3f_1613_);
lean_ctor_set(v_reuseFailAlloc_1628_, 5, v_oleanFileName_x3f_1614_);
lean_ctor_set(v_reuseFailAlloc_1628_, 6, v_ileanFileName_x3f_1615_);
lean_ctor_set(v_reuseFailAlloc_1628_, 7, v_cFileName_x3f_1616_);
lean_ctor_set(v_reuseFailAlloc_1628_, 8, v_bcFileName_x3f_1617_);
lean_ctor_set(v_reuseFailAlloc_1628_, 9, v_errorOnKinds_1619_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*10 + 8, v_component_1603_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*10 + 10, v_printLibDir_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*10 + 11, v_useStdin_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*10 + 12, v_onlyDeps_1606_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*10 + 13, v_onlySrcDeps_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*10 + 14, v_depsJson_1608_);
lean_ctor_set_uint32(v_reuseFailAlloc_1628_, sizeof(void*)*10, v_trustLevel_1610_);
lean_ctor_set_uint32(v_reuseFailAlloc_1628_, sizeof(void*)*10 + 4, v_numThreads_1611_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*10 + 15, v_jsonOutput_1618_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*10 + 16, v_printStats_1620_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*10 + 17, v_run_1621_);
v___x_1626_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; 
lean_ctor_set_uint8(v___x_1626_, sizeof(void*)*10 + 9, v___x_1180_);
v___x_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_leanOpts_1630_; lean_object* v_forwardedArgs_1631_; uint8_t v_component_1632_; uint8_t v_printPrefix_1633_; uint8_t v_printLibDir_1634_; uint8_t v_useStdin_1635_; uint8_t v_onlyDeps_1636_; uint8_t v_onlySrcDeps_1637_; uint8_t v_depsJson_1638_; lean_object* v_opts_1639_; uint32_t v_trustLevel_1640_; uint32_t v_numThreads_1641_; lean_object* v_rootDir_x3f_1642_; lean_object* v_setupFileName_x3f_1643_; lean_object* v_oleanFileName_x3f_1644_; lean_object* v_ileanFileName_x3f_1645_; lean_object* v_cFileName_x3f_1646_; lean_object* v_bcFileName_x3f_1647_; uint8_t v_jsonOutput_1648_; lean_object* v_errorOnKinds_1649_; uint8_t v_run_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1630_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1631_ = lean_ctor_get(v_opts_931_, 1);
v_component_1632_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1633_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1634_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1635_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1636_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1637_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1638_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1639_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1640_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1641_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1642_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1643_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1644_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1645_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1646_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1647_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1648_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1649_ = lean_ctor_get(v_opts_931_, 9);
v_run_1650_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1652_ = v_opts_931_;
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_errorOnKinds_1649_);
lean_inc(v_bcFileName_x3f_1647_);
lean_inc(v_cFileName_x3f_1646_);
lean_inc(v_ileanFileName_x3f_1645_);
lean_inc(v_oleanFileName_x3f_1644_);
lean_inc(v_setupFileName_x3f_1643_);
lean_inc(v_rootDir_x3f_1642_);
lean_inc(v_opts_1639_);
lean_inc(v_forwardedArgs_1631_);
lean_inc(v_leanOpts_1630_);
lean_dec(v_opts_931_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_leanOpts_1630_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_forwardedArgs_1631_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_opts_1639_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_rootDir_x3f_1642_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v_setupFileName_x3f_1643_);
lean_ctor_set(v_reuseFailAlloc_1657_, 5, v_oleanFileName_x3f_1644_);
lean_ctor_set(v_reuseFailAlloc_1657_, 6, v_ileanFileName_x3f_1645_);
lean_ctor_set(v_reuseFailAlloc_1657_, 7, v_cFileName_x3f_1646_);
lean_ctor_set(v_reuseFailAlloc_1657_, 8, v_bcFileName_x3f_1647_);
lean_ctor_set(v_reuseFailAlloc_1657_, 9, v_errorOnKinds_1649_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*10 + 8, v_component_1632_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*10 + 9, v_printPrefix_1633_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*10 + 10, v_printLibDir_1634_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*10 + 11, v_useStdin_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*10 + 12, v_onlyDeps_1636_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*10 + 13, v_onlySrcDeps_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*10 + 14, v_depsJson_1638_);
lean_ctor_set_uint32(v_reuseFailAlloc_1657_, sizeof(void*)*10, v_trustLevel_1640_);
lean_ctor_set_uint32(v_reuseFailAlloc_1657_, sizeof(void*)*10 + 4, v_numThreads_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*10 + 15, v_jsonOutput_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*10 + 17, v_run_1650_);
v___x_1655_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; 
lean_ctor_set_uint8(v___x_1655_, sizeof(void*)*10 + 16, v___x_1178_);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
return v___x_1656_;
}
}
}
}
else
{
lean_object* v_leanOpts_1659_; lean_object* v_forwardedArgs_1660_; uint8_t v_component_1661_; uint8_t v_printPrefix_1662_; uint8_t v_printLibDir_1663_; uint8_t v_useStdin_1664_; uint8_t v_onlyDeps_1665_; uint8_t v_onlySrcDeps_1666_; uint8_t v_depsJson_1667_; lean_object* v_opts_1668_; uint32_t v_trustLevel_1669_; uint32_t v_numThreads_1670_; lean_object* v_rootDir_x3f_1671_; lean_object* v_setupFileName_x3f_1672_; lean_object* v_oleanFileName_x3f_1673_; lean_object* v_ileanFileName_x3f_1674_; lean_object* v_cFileName_x3f_1675_; lean_object* v_bcFileName_x3f_1676_; lean_object* v_errorOnKinds_1677_; uint8_t v_printStats_1678_; uint8_t v_run_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1659_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1660_ = lean_ctor_get(v_opts_931_, 1);
v_component_1661_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1662_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1663_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1664_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1665_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1666_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1667_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1668_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1669_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1670_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1671_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1672_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1673_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1674_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1675_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1676_ = lean_ctor_get(v_opts_931_, 8);
v_errorOnKinds_1677_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1678_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1679_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1681_ = v_opts_931_;
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_errorOnKinds_1677_);
lean_inc(v_bcFileName_x3f_1676_);
lean_inc(v_cFileName_x3f_1675_);
lean_inc(v_ileanFileName_x3f_1674_);
lean_inc(v_oleanFileName_x3f_1673_);
lean_inc(v_setupFileName_x3f_1672_);
lean_inc(v_rootDir_x3f_1671_);
lean_inc(v_opts_1668_);
lean_inc(v_forwardedArgs_1660_);
lean_inc(v_leanOpts_1659_);
lean_dec(v_opts_931_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_leanOpts_1659_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_forwardedArgs_1660_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_opts_1668_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v_rootDir_x3f_1671_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v_setupFileName_x3f_1672_);
lean_ctor_set(v_reuseFailAlloc_1686_, 5, v_oleanFileName_x3f_1673_);
lean_ctor_set(v_reuseFailAlloc_1686_, 6, v_ileanFileName_x3f_1674_);
lean_ctor_set(v_reuseFailAlloc_1686_, 7, v_cFileName_x3f_1675_);
lean_ctor_set(v_reuseFailAlloc_1686_, 8, v_bcFileName_x3f_1676_);
lean_ctor_set(v_reuseFailAlloc_1686_, 9, v_errorOnKinds_1677_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*10 + 8, v_component_1661_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*10 + 9, v_printPrefix_1662_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*10 + 10, v_printLibDir_1663_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*10 + 11, v_useStdin_1664_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*10 + 12, v_onlyDeps_1665_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*10 + 13, v_onlySrcDeps_1666_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*10 + 14, v_depsJson_1667_);
lean_ctor_set_uint32(v_reuseFailAlloc_1686_, sizeof(void*)*10, v_trustLevel_1669_);
lean_ctor_set_uint32(v_reuseFailAlloc_1686_, sizeof(void*)*10 + 4, v_numThreads_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*10 + 16, v_printStats_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*10 + 17, v_run_1679_);
v___x_1684_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; 
lean_ctor_set_uint8(v___x_1684_, sizeof(void*)*10 + 15, v___x_1176_);
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_leanOpts_1688_; lean_object* v_forwardedArgs_1689_; uint8_t v_component_1690_; uint8_t v_printPrefix_1691_; uint8_t v_printLibDir_1692_; uint8_t v_useStdin_1693_; uint8_t v_onlySrcDeps_1694_; lean_object* v_opts_1695_; uint32_t v_trustLevel_1696_; uint32_t v_numThreads_1697_; lean_object* v_rootDir_x3f_1698_; lean_object* v_setupFileName_x3f_1699_; lean_object* v_oleanFileName_x3f_1700_; lean_object* v_ileanFileName_x3f_1701_; lean_object* v_cFileName_x3f_1702_; lean_object* v_bcFileName_x3f_1703_; uint8_t v_jsonOutput_1704_; lean_object* v_errorOnKinds_1705_; uint8_t v_printStats_1706_; uint8_t v_run_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1688_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1689_ = lean_ctor_get(v_opts_931_, 1);
v_component_1690_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1691_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1692_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1693_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlySrcDeps_1694_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_opts_1695_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1696_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1697_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1698_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1699_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1700_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1701_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1702_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1703_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1704_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1705_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1706_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1707_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1709_ = v_opts_931_;
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_errorOnKinds_1705_);
lean_inc(v_bcFileName_x3f_1703_);
lean_inc(v_cFileName_x3f_1702_);
lean_inc(v_ileanFileName_x3f_1701_);
lean_inc(v_oleanFileName_x3f_1700_);
lean_inc(v_setupFileName_x3f_1699_);
lean_inc(v_rootDir_x3f_1698_);
lean_inc(v_opts_1695_);
lean_inc(v_forwardedArgs_1689_);
lean_inc(v_leanOpts_1688_);
lean_dec(v_opts_931_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_leanOpts_1688_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_forwardedArgs_1689_);
lean_ctor_set(v_reuseFailAlloc_1714_, 2, v_opts_1695_);
lean_ctor_set(v_reuseFailAlloc_1714_, 3, v_rootDir_x3f_1698_);
lean_ctor_set(v_reuseFailAlloc_1714_, 4, v_setupFileName_x3f_1699_);
lean_ctor_set(v_reuseFailAlloc_1714_, 5, v_oleanFileName_x3f_1700_);
lean_ctor_set(v_reuseFailAlloc_1714_, 6, v_ileanFileName_x3f_1701_);
lean_ctor_set(v_reuseFailAlloc_1714_, 7, v_cFileName_x3f_1702_);
lean_ctor_set(v_reuseFailAlloc_1714_, 8, v_bcFileName_x3f_1703_);
lean_ctor_set(v_reuseFailAlloc_1714_, 9, v_errorOnKinds_1705_);
lean_ctor_set_uint8(v_reuseFailAlloc_1714_, sizeof(void*)*10 + 8, v_component_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1714_, sizeof(void*)*10 + 9, v_printPrefix_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1714_, sizeof(void*)*10 + 10, v_printLibDir_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1714_, sizeof(void*)*10 + 11, v_useStdin_1693_);
lean_ctor_set_uint8(v_reuseFailAlloc_1714_, sizeof(void*)*10 + 13, v_onlySrcDeps_1694_);
lean_ctor_set_uint32(v_reuseFailAlloc_1714_, sizeof(void*)*10, v_trustLevel_1696_);
lean_ctor_set_uint32(v_reuseFailAlloc_1714_, sizeof(void*)*10 + 4, v_numThreads_1697_);
lean_ctor_set_uint8(v_reuseFailAlloc_1714_, sizeof(void*)*10 + 15, v_jsonOutput_1704_);
lean_ctor_set_uint8(v_reuseFailAlloc_1714_, sizeof(void*)*10 + 16, v_printStats_1706_);
lean_ctor_set_uint8(v_reuseFailAlloc_1714_, sizeof(void*)*10 + 17, v_run_1707_);
v___x_1712_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1713_; 
lean_ctor_set_uint8(v___x_1712_, sizeof(void*)*10 + 12, v___x_1174_);
lean_ctor_set_uint8(v___x_1712_, sizeof(void*)*10 + 14, v___x_1174_);
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
return v___x_1713_;
}
}
}
}
else
{
lean_object* v_leanOpts_1716_; lean_object* v_forwardedArgs_1717_; uint8_t v_component_1718_; uint8_t v_printPrefix_1719_; uint8_t v_printLibDir_1720_; uint8_t v_useStdin_1721_; uint8_t v_onlyDeps_1722_; uint8_t v_depsJson_1723_; lean_object* v_opts_1724_; uint32_t v_trustLevel_1725_; uint32_t v_numThreads_1726_; lean_object* v_rootDir_x3f_1727_; lean_object* v_setupFileName_x3f_1728_; lean_object* v_oleanFileName_x3f_1729_; lean_object* v_ileanFileName_x3f_1730_; lean_object* v_cFileName_x3f_1731_; lean_object* v_bcFileName_x3f_1732_; uint8_t v_jsonOutput_1733_; lean_object* v_errorOnKinds_1734_; uint8_t v_printStats_1735_; uint8_t v_run_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1716_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1717_ = lean_ctor_get(v_opts_931_, 1);
v_component_1718_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1719_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1720_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1721_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1722_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_depsJson_1723_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1724_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1725_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1726_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1727_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1728_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1729_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1730_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1731_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1732_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1733_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1734_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1735_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1736_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1738_ = v_opts_931_;
v_isShared_1739_ = v_isSharedCheck_1744_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_errorOnKinds_1734_);
lean_inc(v_bcFileName_x3f_1732_);
lean_inc(v_cFileName_x3f_1731_);
lean_inc(v_ileanFileName_x3f_1730_);
lean_inc(v_oleanFileName_x3f_1729_);
lean_inc(v_setupFileName_x3f_1728_);
lean_inc(v_rootDir_x3f_1727_);
lean_inc(v_opts_1724_);
lean_inc(v_forwardedArgs_1717_);
lean_inc(v_leanOpts_1716_);
lean_dec(v_opts_931_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1744_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_leanOpts_1716_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_forwardedArgs_1717_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_opts_1724_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v_rootDir_x3f_1727_);
lean_ctor_set(v_reuseFailAlloc_1743_, 4, v_setupFileName_x3f_1728_);
lean_ctor_set(v_reuseFailAlloc_1743_, 5, v_oleanFileName_x3f_1729_);
lean_ctor_set(v_reuseFailAlloc_1743_, 6, v_ileanFileName_x3f_1730_);
lean_ctor_set(v_reuseFailAlloc_1743_, 7, v_cFileName_x3f_1731_);
lean_ctor_set(v_reuseFailAlloc_1743_, 8, v_bcFileName_x3f_1732_);
lean_ctor_set(v_reuseFailAlloc_1743_, 9, v_errorOnKinds_1734_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*10 + 8, v_component_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*10 + 9, v_printPrefix_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*10 + 10, v_printLibDir_1720_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*10 + 11, v_useStdin_1721_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*10 + 12, v_onlyDeps_1722_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*10 + 14, v_depsJson_1723_);
lean_ctor_set_uint32(v_reuseFailAlloc_1743_, sizeof(void*)*10, v_trustLevel_1725_);
lean_ctor_set_uint32(v_reuseFailAlloc_1743_, sizeof(void*)*10 + 4, v_numThreads_1726_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*10 + 15, v_jsonOutput_1733_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*10 + 16, v_printStats_1735_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*10 + 17, v_run_1736_);
v___x_1741_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; 
lean_ctor_set_uint8(v___x_1741_, sizeof(void*)*10 + 13, v___x_1172_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_leanOpts_1745_; lean_object* v_forwardedArgs_1746_; uint8_t v_component_1747_; uint8_t v_printPrefix_1748_; uint8_t v_printLibDir_1749_; uint8_t v_useStdin_1750_; uint8_t v_onlySrcDeps_1751_; uint8_t v_depsJson_1752_; lean_object* v_opts_1753_; uint32_t v_trustLevel_1754_; uint32_t v_numThreads_1755_; lean_object* v_rootDir_x3f_1756_; lean_object* v_setupFileName_x3f_1757_; lean_object* v_oleanFileName_x3f_1758_; lean_object* v_ileanFileName_x3f_1759_; lean_object* v_cFileName_x3f_1760_; lean_object* v_bcFileName_x3f_1761_; uint8_t v_jsonOutput_1762_; lean_object* v_errorOnKinds_1763_; uint8_t v_printStats_1764_; uint8_t v_run_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1773_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1745_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1746_ = lean_ctor_get(v_opts_931_, 1);
v_component_1747_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1748_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1749_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1750_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlySrcDeps_1751_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1752_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1753_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1754_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1755_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1756_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1757_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1758_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1759_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1760_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1761_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1762_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1763_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1764_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1765_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1767_ = v_opts_931_;
v_isShared_1768_ = v_isSharedCheck_1773_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_errorOnKinds_1763_);
lean_inc(v_bcFileName_x3f_1761_);
lean_inc(v_cFileName_x3f_1760_);
lean_inc(v_ileanFileName_x3f_1759_);
lean_inc(v_oleanFileName_x3f_1758_);
lean_inc(v_setupFileName_x3f_1757_);
lean_inc(v_rootDir_x3f_1756_);
lean_inc(v_opts_1753_);
lean_inc(v_forwardedArgs_1746_);
lean_inc(v_leanOpts_1745_);
lean_dec(v_opts_931_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1773_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_leanOpts_1745_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_forwardedArgs_1746_);
lean_ctor_set(v_reuseFailAlloc_1772_, 2, v_opts_1753_);
lean_ctor_set(v_reuseFailAlloc_1772_, 3, v_rootDir_x3f_1756_);
lean_ctor_set(v_reuseFailAlloc_1772_, 4, v_setupFileName_x3f_1757_);
lean_ctor_set(v_reuseFailAlloc_1772_, 5, v_oleanFileName_x3f_1758_);
lean_ctor_set(v_reuseFailAlloc_1772_, 6, v_ileanFileName_x3f_1759_);
lean_ctor_set(v_reuseFailAlloc_1772_, 7, v_cFileName_x3f_1760_);
lean_ctor_set(v_reuseFailAlloc_1772_, 8, v_bcFileName_x3f_1761_);
lean_ctor_set(v_reuseFailAlloc_1772_, 9, v_errorOnKinds_1763_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, sizeof(void*)*10 + 8, v_component_1747_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, sizeof(void*)*10 + 9, v_printPrefix_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, sizeof(void*)*10 + 10, v_printLibDir_1749_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, sizeof(void*)*10 + 11, v_useStdin_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, sizeof(void*)*10 + 13, v_onlySrcDeps_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, sizeof(void*)*10 + 14, v_depsJson_1752_);
lean_ctor_set_uint32(v_reuseFailAlloc_1772_, sizeof(void*)*10, v_trustLevel_1754_);
lean_ctor_set_uint32(v_reuseFailAlloc_1772_, sizeof(void*)*10 + 4, v_numThreads_1755_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, sizeof(void*)*10 + 15, v_jsonOutput_1762_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, sizeof(void*)*10 + 16, v_printStats_1764_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, sizeof(void*)*10 + 17, v_run_1765_);
v___x_1770_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1771_; 
lean_ctor_set_uint8(v___x_1770_, sizeof(void*)*10 + 12, v___x_1170_);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
return v___x_1771_;
}
}
}
}
else
{
lean_object* v_leanOpts_1774_; lean_object* v_forwardedArgs_1775_; uint8_t v_component_1776_; uint8_t v_printPrefix_1777_; uint8_t v_printLibDir_1778_; uint8_t v_useStdin_1779_; uint8_t v_onlyDeps_1780_; uint8_t v_onlySrcDeps_1781_; uint8_t v_depsJson_1782_; lean_object* v_opts_1783_; uint32_t v_trustLevel_1784_; uint32_t v_numThreads_1785_; lean_object* v_rootDir_x3f_1786_; lean_object* v_setupFileName_x3f_1787_; lean_object* v_oleanFileName_x3f_1788_; lean_object* v_ileanFileName_x3f_1789_; lean_object* v_cFileName_x3f_1790_; lean_object* v_bcFileName_x3f_1791_; uint8_t v_jsonOutput_1792_; lean_object* v_errorOnKinds_1793_; uint8_t v_printStats_1794_; uint8_t v_run_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1774_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1775_ = lean_ctor_get(v_opts_931_, 1);
v_component_1776_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1777_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1778_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1779_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1780_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1781_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1782_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1783_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1784_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1785_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1786_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1787_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1788_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1789_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1790_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1791_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1792_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1793_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1794_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1795_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1797_ = v_opts_931_;
v_isShared_1798_ = v_isSharedCheck_1805_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_errorOnKinds_1793_);
lean_inc(v_bcFileName_x3f_1791_);
lean_inc(v_cFileName_x3f_1790_);
lean_inc(v_ileanFileName_x3f_1789_);
lean_inc(v_oleanFileName_x3f_1788_);
lean_inc(v_setupFileName_x3f_1787_);
lean_inc(v_rootDir_x3f_1786_);
lean_inc(v_opts_1783_);
lean_inc(v_forwardedArgs_1775_);
lean_inc(v_leanOpts_1774_);
lean_dec(v_opts_931_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1805_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1799_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_1800_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1774_, v___x_1799_, v___x_1166_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1800_);
v___x_1802_ = v___x_1797_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_forwardedArgs_1775_);
lean_ctor_set(v_reuseFailAlloc_1804_, 2, v_opts_1783_);
lean_ctor_set(v_reuseFailAlloc_1804_, 3, v_rootDir_x3f_1786_);
lean_ctor_set(v_reuseFailAlloc_1804_, 4, v_setupFileName_x3f_1787_);
lean_ctor_set(v_reuseFailAlloc_1804_, 5, v_oleanFileName_x3f_1788_);
lean_ctor_set(v_reuseFailAlloc_1804_, 6, v_ileanFileName_x3f_1789_);
lean_ctor_set(v_reuseFailAlloc_1804_, 7, v_cFileName_x3f_1790_);
lean_ctor_set(v_reuseFailAlloc_1804_, 8, v_bcFileName_x3f_1791_);
lean_ctor_set(v_reuseFailAlloc_1804_, 9, v_errorOnKinds_1793_);
lean_ctor_set_uint8(v_reuseFailAlloc_1804_, sizeof(void*)*10 + 8, v_component_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1804_, sizeof(void*)*10 + 9, v_printPrefix_1777_);
lean_ctor_set_uint8(v_reuseFailAlloc_1804_, sizeof(void*)*10 + 10, v_printLibDir_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1804_, sizeof(void*)*10 + 11, v_useStdin_1779_);
lean_ctor_set_uint8(v_reuseFailAlloc_1804_, sizeof(void*)*10 + 12, v_onlyDeps_1780_);
lean_ctor_set_uint8(v_reuseFailAlloc_1804_, sizeof(void*)*10 + 13, v_onlySrcDeps_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1804_, sizeof(void*)*10 + 14, v_depsJson_1782_);
lean_ctor_set_uint32(v_reuseFailAlloc_1804_, sizeof(void*)*10, v_trustLevel_1784_);
lean_ctor_set_uint32(v_reuseFailAlloc_1804_, sizeof(void*)*10 + 4, v_numThreads_1785_);
lean_ctor_set_uint8(v_reuseFailAlloc_1804_, sizeof(void*)*10 + 15, v_jsonOutput_1792_);
lean_ctor_set_uint8(v_reuseFailAlloc_1804_, sizeof(void*)*10 + 16, v_printStats_1794_);
lean_ctor_set_uint8(v_reuseFailAlloc_1804_, sizeof(void*)*10 + 17, v_run_1795_);
v___x_1802_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
return v___x_1803_;
}
}
}
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1807_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1806_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1858_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1858_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1858_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = lean_string_utf8_byte_size(v_a_1808_);
lean_inc(v_a_1808_);
v___x_1814_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1814_, 0, v_a_1808_);
lean_ctor_set(v___x_1814_, 1, v___x_1812_);
lean_ctor_set(v___x_1814_, 2, v___x_1813_);
v___x_1815_ = l_String_Slice_toNat_x3f(v___x_1814_);
lean_dec_ref(v___x_1814_);
if (lean_obj_tag(v___x_1815_) == 1)
{
lean_object* v_val_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v_val_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_val_1816_);
lean_dec_ref(v___x_1815_);
v___x_1817_ = lean_cstr_to_nat("4294967296");
v___x_1818_ = lean_nat_dec_lt(v_val_1816_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec(v_val_1816_);
lean_del_object(v___x_1810_);
lean_dec(v_a_1808_);
lean_dec_ref(v_opts_931_);
v___x_1819_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1820_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1819_);
lean_dec_ref(v___x_1820_);
goto v___jp_1001_;
}
else
{
lean_object* v_leanOpts_1821_; lean_object* v_forwardedArgs_1822_; uint8_t v_component_1823_; uint8_t v_printPrefix_1824_; uint8_t v_printLibDir_1825_; uint8_t v_useStdin_1826_; uint8_t v_onlyDeps_1827_; uint8_t v_onlySrcDeps_1828_; uint8_t v_depsJson_1829_; lean_object* v_opts_1830_; uint32_t v_numThreads_1831_; lean_object* v_rootDir_x3f_1832_; lean_object* v_setupFileName_x3f_1833_; lean_object* v_oleanFileName_x3f_1834_; lean_object* v_ileanFileName_x3f_1835_; lean_object* v_cFileName_x3f_1836_; lean_object* v_bcFileName_x3f_1837_; uint8_t v_jsonOutput_1838_; lean_object* v_errorOnKinds_1839_; uint8_t v_printStats_1840_; uint8_t v_run_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1855_; 
v_leanOpts_1821_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1822_ = lean_ctor_get(v_opts_931_, 1);
v_component_1823_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1824_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1825_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1826_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1827_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1828_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1829_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1830_ = lean_ctor_get(v_opts_931_, 2);
v_numThreads_1831_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1832_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1833_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1834_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1835_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1836_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1837_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1838_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1839_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1840_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1841_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1843_ = v_opts_931_;
v_isShared_1844_ = v_isSharedCheck_1855_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_errorOnKinds_1839_);
lean_inc(v_bcFileName_x3f_1837_);
lean_inc(v_cFileName_x3f_1836_);
lean_inc(v_ileanFileName_x3f_1835_);
lean_inc(v_oleanFileName_x3f_1834_);
lean_inc(v_setupFileName_x3f_1833_);
lean_inc(v_rootDir_x3f_1832_);
lean_inc(v_opts_1830_);
lean_inc(v_forwardedArgs_1822_);
lean_inc(v_leanOpts_1821_);
lean_dec(v_opts_931_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1855_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
uint32_t v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1845_ = lean_uint32_of_nat(v_val_1816_);
lean_dec(v_val_1816_);
v___x_1846_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1847_ = lean_string_append(v___x_1846_, v_a_1808_);
lean_dec(v_a_1808_);
v___x_1848_ = lean_array_push(v_forwardedArgs_1822_, v___x_1847_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v___x_1848_);
v___x_1850_ = v___x_1843_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_leanOpts_1821_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_opts_1830_);
lean_ctor_set(v_reuseFailAlloc_1854_, 3, v_rootDir_x3f_1832_);
lean_ctor_set(v_reuseFailAlloc_1854_, 4, v_setupFileName_x3f_1833_);
lean_ctor_set(v_reuseFailAlloc_1854_, 5, v_oleanFileName_x3f_1834_);
lean_ctor_set(v_reuseFailAlloc_1854_, 6, v_ileanFileName_x3f_1835_);
lean_ctor_set(v_reuseFailAlloc_1854_, 7, v_cFileName_x3f_1836_);
lean_ctor_set(v_reuseFailAlloc_1854_, 8, v_bcFileName_x3f_1837_);
lean_ctor_set(v_reuseFailAlloc_1854_, 9, v_errorOnKinds_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1854_, sizeof(void*)*10 + 8, v_component_1823_);
lean_ctor_set_uint8(v_reuseFailAlloc_1854_, sizeof(void*)*10 + 9, v_printPrefix_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1854_, sizeof(void*)*10 + 10, v_printLibDir_1825_);
lean_ctor_set_uint8(v_reuseFailAlloc_1854_, sizeof(void*)*10 + 11, v_useStdin_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1854_, sizeof(void*)*10 + 12, v_onlyDeps_1827_);
lean_ctor_set_uint8(v_reuseFailAlloc_1854_, sizeof(void*)*10 + 13, v_onlySrcDeps_1828_);
lean_ctor_set_uint8(v_reuseFailAlloc_1854_, sizeof(void*)*10 + 14, v_depsJson_1829_);
lean_ctor_set_uint32(v_reuseFailAlloc_1854_, sizeof(void*)*10 + 4, v_numThreads_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1854_, sizeof(void*)*10 + 15, v_jsonOutput_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1854_, sizeof(void*)*10 + 16, v_printStats_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1854_, sizeof(void*)*10 + 17, v_run_1841_);
v___x_1850_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1852_; 
lean_ctor_set_uint32(v___x_1850_, sizeof(void*)*10, v___x_1845_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1850_);
v___x_1852_ = v___x_1810_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec(v___x_1815_);
lean_del_object(v___x_1810_);
lean_dec(v_a_1808_);
lean_dec_ref(v_opts_931_);
v___x_1856_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_1857_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1856_);
lean_dec_ref(v___x_1857_);
goto v___jp_998_;
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec_ref(v_opts_931_);
v_a_1859_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1807_);
v___x_1863_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1864_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1863_);
lean_dec_ref(v___x_1864_);
goto v___jp_1860_;
v___jp_1860_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = lean_io_error_to_string(v_a_1859_);
v___x_1862_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1861_);
lean_dec_ref(v___x_1862_);
goto v___jp_995_;
}
}
}
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_1866_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1865_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1915_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1915_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1915_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1871_ = lean_unsigned_to_nat(0u);
v___x_1872_ = lean_string_utf8_byte_size(v_a_1867_);
lean_inc(v_a_1867_);
v___x_1873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1873_, 0, v_a_1867_);
lean_ctor_set(v___x_1873_, 1, v___x_1871_);
lean_ctor_set(v___x_1873_, 2, v___x_1872_);
v___x_1874_ = l_String_Slice_toNat_x3f(v___x_1873_);
lean_dec_ref(v___x_1873_);
if (lean_obj_tag(v___x_1874_) == 1)
{
lean_object* v_val_1875_; lean_object* v_leanOpts_1876_; lean_object* v_forwardedArgs_1877_; uint8_t v_component_1878_; uint8_t v_printPrefix_1879_; uint8_t v_printLibDir_1880_; uint8_t v_useStdin_1881_; uint8_t v_onlyDeps_1882_; uint8_t v_onlySrcDeps_1883_; uint8_t v_depsJson_1884_; lean_object* v_opts_1885_; uint32_t v_trustLevel_1886_; uint32_t v_numThreads_1887_; lean_object* v_rootDir_x3f_1888_; lean_object* v_setupFileName_x3f_1889_; lean_object* v_oleanFileName_x3f_1890_; lean_object* v_ileanFileName_x3f_1891_; lean_object* v_cFileName_x3f_1892_; lean_object* v_bcFileName_x3f_1893_; uint8_t v_jsonOutput_1894_; lean_object* v_errorOnKinds_1895_; uint8_t v_printStats_1896_; uint8_t v_run_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1912_; 
v_val_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_val_1875_);
lean_dec_ref(v___x_1874_);
v_leanOpts_1876_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1877_ = lean_ctor_get(v_opts_931_, 1);
v_component_1878_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1879_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1880_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1881_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1882_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1883_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1884_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1885_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1886_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1887_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1888_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1889_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1890_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1891_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1892_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1893_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1894_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1895_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1896_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1897_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1899_ = v_opts_931_;
v_isShared_1900_ = v_isSharedCheck_1912_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_errorOnKinds_1895_);
lean_inc(v_bcFileName_x3f_1893_);
lean_inc(v_cFileName_x3f_1892_);
lean_inc(v_ileanFileName_x3f_1891_);
lean_inc(v_oleanFileName_x3f_1890_);
lean_inc(v_setupFileName_x3f_1889_);
lean_inc(v_rootDir_x3f_1888_);
lean_inc(v_opts_1885_);
lean_inc(v_forwardedArgs_1877_);
lean_inc(v_leanOpts_1876_);
lean_dec(v_opts_931_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1912_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1901_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_1902_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_1876_, v___x_1901_, v_val_1875_);
v___x_1903_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_1904_ = lean_string_append(v___x_1903_, v_a_1867_);
lean_dec(v_a_1867_);
v___x_1905_ = lean_array_push(v_forwardedArgs_1877_, v___x_1904_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v___x_1905_);
lean_ctor_set(v___x_1899_, 0, v___x_1902_);
v___x_1907_ = v___x_1899_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1902_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_opts_1885_);
lean_ctor_set(v_reuseFailAlloc_1911_, 3, v_rootDir_x3f_1888_);
lean_ctor_set(v_reuseFailAlloc_1911_, 4, v_setupFileName_x3f_1889_);
lean_ctor_set(v_reuseFailAlloc_1911_, 5, v_oleanFileName_x3f_1890_);
lean_ctor_set(v_reuseFailAlloc_1911_, 6, v_ileanFileName_x3f_1891_);
lean_ctor_set(v_reuseFailAlloc_1911_, 7, v_cFileName_x3f_1892_);
lean_ctor_set(v_reuseFailAlloc_1911_, 8, v_bcFileName_x3f_1893_);
lean_ctor_set(v_reuseFailAlloc_1911_, 9, v_errorOnKinds_1895_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*10 + 8, v_component_1878_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*10 + 9, v_printPrefix_1879_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*10 + 10, v_printLibDir_1880_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*10 + 11, v_useStdin_1881_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*10 + 12, v_onlyDeps_1882_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*10 + 13, v_onlySrcDeps_1883_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*10 + 14, v_depsJson_1884_);
lean_ctor_set_uint32(v_reuseFailAlloc_1911_, sizeof(void*)*10, v_trustLevel_1886_);
lean_ctor_set_uint32(v_reuseFailAlloc_1911_, sizeof(void*)*10 + 4, v_numThreads_1887_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*10 + 15, v_jsonOutput_1894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*10 + 16, v_printStats_1896_);
lean_ctor_set_uint8(v_reuseFailAlloc_1911_, sizeof(void*)*10 + 17, v_run_1897_);
v___x_1907_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1909_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1907_);
v___x_1909_ = v___x_1869_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_dec(v___x_1874_);
lean_del_object(v___x_1869_);
lean_dec(v_a_1867_);
lean_dec_ref(v_opts_931_);
v___x_1913_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_1914_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1913_);
lean_dec_ref(v___x_1914_);
goto v___jp_1086_;
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec_ref(v_opts_931_);
v_a_1916_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1866_);
v___x_1920_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1921_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1920_);
lean_dec_ref(v___x_1921_);
goto v___jp_1917_;
v___jp_1917_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_io_error_to_string(v_a_1916_);
v___x_1919_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1918_);
lean_dec_ref(v___x_1919_);
goto v___jp_1092_;
}
}
}
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_1923_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1922_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1972_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1972_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1972_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1928_ = lean_unsigned_to_nat(0u);
v___x_1929_ = lean_string_utf8_byte_size(v_a_1924_);
lean_inc(v_a_1924_);
v___x_1930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1930_, 0, v_a_1924_);
lean_ctor_set(v___x_1930_, 1, v___x_1928_);
lean_ctor_set(v___x_1930_, 2, v___x_1929_);
v___x_1931_ = l_String_Slice_toNat_x3f(v___x_1930_);
lean_dec_ref(v___x_1930_);
if (lean_obj_tag(v___x_1931_) == 1)
{
lean_object* v_val_1932_; lean_object* v_leanOpts_1933_; lean_object* v_forwardedArgs_1934_; uint8_t v_component_1935_; uint8_t v_printPrefix_1936_; uint8_t v_printLibDir_1937_; uint8_t v_useStdin_1938_; uint8_t v_onlyDeps_1939_; uint8_t v_onlySrcDeps_1940_; uint8_t v_depsJson_1941_; lean_object* v_opts_1942_; uint32_t v_trustLevel_1943_; uint32_t v_numThreads_1944_; lean_object* v_rootDir_x3f_1945_; lean_object* v_setupFileName_x3f_1946_; lean_object* v_oleanFileName_x3f_1947_; lean_object* v_ileanFileName_x3f_1948_; lean_object* v_cFileName_x3f_1949_; lean_object* v_bcFileName_x3f_1950_; uint8_t v_jsonOutput_1951_; lean_object* v_errorOnKinds_1952_; uint8_t v_printStats_1953_; uint8_t v_run_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1969_; 
v_val_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_val_1932_);
lean_dec_ref(v___x_1931_);
v_leanOpts_1933_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1934_ = lean_ctor_get(v_opts_931_, 1);
v_component_1935_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1936_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1937_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1938_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1939_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1940_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1941_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1942_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1943_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1944_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1945_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1946_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1947_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1948_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1949_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1950_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1951_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1952_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1953_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1954_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1956_ = v_opts_931_;
v_isShared_1957_ = v_isSharedCheck_1969_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_errorOnKinds_1952_);
lean_inc(v_bcFileName_x3f_1950_);
lean_inc(v_cFileName_x3f_1949_);
lean_inc(v_ileanFileName_x3f_1948_);
lean_inc(v_oleanFileName_x3f_1947_);
lean_inc(v_setupFileName_x3f_1946_);
lean_inc(v_rootDir_x3f_1945_);
lean_inc(v_opts_1942_);
lean_inc(v_forwardedArgs_1934_);
lean_inc(v_leanOpts_1933_);
lean_dec(v_opts_931_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1969_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1958_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_1959_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_1933_, v___x_1958_, v_val_1932_);
v___x_1960_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_1961_ = lean_string_append(v___x_1960_, v_a_1924_);
lean_dec(v_a_1924_);
v___x_1962_ = lean_array_push(v_forwardedArgs_1934_, v___x_1961_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v___x_1962_);
lean_ctor_set(v___x_1956_, 0, v___x_1959_);
v___x_1964_ = v___x_1956_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1968_, 2, v_opts_1942_);
lean_ctor_set(v_reuseFailAlloc_1968_, 3, v_rootDir_x3f_1945_);
lean_ctor_set(v_reuseFailAlloc_1968_, 4, v_setupFileName_x3f_1946_);
lean_ctor_set(v_reuseFailAlloc_1968_, 5, v_oleanFileName_x3f_1947_);
lean_ctor_set(v_reuseFailAlloc_1968_, 6, v_ileanFileName_x3f_1948_);
lean_ctor_set(v_reuseFailAlloc_1968_, 7, v_cFileName_x3f_1949_);
lean_ctor_set(v_reuseFailAlloc_1968_, 8, v_bcFileName_x3f_1950_);
lean_ctor_set(v_reuseFailAlloc_1968_, 9, v_errorOnKinds_1952_);
lean_ctor_set_uint8(v_reuseFailAlloc_1968_, sizeof(void*)*10 + 8, v_component_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1968_, sizeof(void*)*10 + 9, v_printPrefix_1936_);
lean_ctor_set_uint8(v_reuseFailAlloc_1968_, sizeof(void*)*10 + 10, v_printLibDir_1937_);
lean_ctor_set_uint8(v_reuseFailAlloc_1968_, sizeof(void*)*10 + 11, v_useStdin_1938_);
lean_ctor_set_uint8(v_reuseFailAlloc_1968_, sizeof(void*)*10 + 12, v_onlyDeps_1939_);
lean_ctor_set_uint8(v_reuseFailAlloc_1968_, sizeof(void*)*10 + 13, v_onlySrcDeps_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1968_, sizeof(void*)*10 + 14, v_depsJson_1941_);
lean_ctor_set_uint32(v_reuseFailAlloc_1968_, sizeof(void*)*10, v_trustLevel_1943_);
lean_ctor_set_uint32(v_reuseFailAlloc_1968_, sizeof(void*)*10 + 4, v_numThreads_1944_);
lean_ctor_set_uint8(v_reuseFailAlloc_1968_, sizeof(void*)*10 + 15, v_jsonOutput_1951_);
lean_ctor_set_uint8(v_reuseFailAlloc_1968_, sizeof(void*)*10 + 16, v_printStats_1953_);
lean_ctor_set_uint8(v_reuseFailAlloc_1968_, sizeof(void*)*10 + 17, v_run_1954_);
v___x_1964_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1966_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1964_);
v___x_1966_ = v___x_1926_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec(v___x_1931_);
lean_del_object(v___x_1926_);
lean_dec(v_a_1924_);
lean_dec_ref(v_opts_931_);
v___x_1970_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_1971_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1970_);
lean_dec_ref(v___x_1971_);
goto v___jp_989_;
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_dec_ref(v_opts_931_);
v_a_1973_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1973_);
lean_dec_ref(v___x_1923_);
v___x_1977_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1978_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1977_);
lean_dec_ref(v___x_1978_);
goto v___jp_1974_;
v___jp_1974_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_io_error_to_string(v_a_1973_);
v___x_1976_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1975_);
lean_dec_ref(v___x_1976_);
goto v___jp_986_;
}
}
}
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_1980_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1979_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2021_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_2021_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2021_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_leanOpts_1985_; lean_object* v_forwardedArgs_1986_; uint8_t v_component_1987_; uint8_t v_printPrefix_1988_; uint8_t v_printLibDir_1989_; uint8_t v_useStdin_1990_; uint8_t v_onlyDeps_1991_; uint8_t v_onlySrcDeps_1992_; uint8_t v_depsJson_1993_; lean_object* v_opts_1994_; uint32_t v_trustLevel_1995_; uint32_t v_numThreads_1996_; lean_object* v_setupFileName_x3f_1997_; lean_object* v_oleanFileName_x3f_1998_; lean_object* v_ileanFileName_x3f_1999_; lean_object* v_cFileName_x3f_2000_; lean_object* v_bcFileName_x3f_2001_; uint8_t v_jsonOutput_2002_; lean_object* v_errorOnKinds_2003_; uint8_t v_printStats_2004_; uint8_t v_run_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2019_; 
v_leanOpts_1985_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1986_ = lean_ctor_get(v_opts_931_, 1);
v_component_1987_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1988_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1989_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1990_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1991_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1992_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1993_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1994_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1995_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1996_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_setupFileName_x3f_1997_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1998_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1999_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2000_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2001_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2002_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2003_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2004_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2005_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v_opts_931_, 3);
lean_dec(v_unused_2020_);
v___x_2007_ = v_opts_931_;
v_isShared_2008_ = v_isSharedCheck_2019_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_errorOnKinds_2003_);
lean_inc(v_bcFileName_x3f_2001_);
lean_inc(v_cFileName_x3f_2000_);
lean_inc(v_ileanFileName_x3f_1999_);
lean_inc(v_oleanFileName_x3f_1998_);
lean_inc(v_setupFileName_x3f_1997_);
lean_inc(v_opts_1994_);
lean_inc(v_forwardedArgs_1986_);
lean_inc(v_leanOpts_1985_);
lean_dec(v_opts_931_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2019_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2009_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2010_ = lean_string_append(v___x_2009_, v_a_1981_);
v___x_2011_ = lean_array_push(v_forwardedArgs_1986_, v___x_2010_);
v___x_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2012_, 0, v_a_1981_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 3, v___x_2012_);
lean_ctor_set(v___x_2007_, 1, v___x_2011_);
v___x_2014_ = v___x_2007_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_leanOpts_1985_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_opts_1994_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2018_, 4, v_setupFileName_x3f_1997_);
lean_ctor_set(v_reuseFailAlloc_2018_, 5, v_oleanFileName_x3f_1998_);
lean_ctor_set(v_reuseFailAlloc_2018_, 6, v_ileanFileName_x3f_1999_);
lean_ctor_set(v_reuseFailAlloc_2018_, 7, v_cFileName_x3f_2000_);
lean_ctor_set(v_reuseFailAlloc_2018_, 8, v_bcFileName_x3f_2001_);
lean_ctor_set(v_reuseFailAlloc_2018_, 9, v_errorOnKinds_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*10 + 8, v_component_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*10 + 9, v_printPrefix_1988_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*10 + 10, v_printLibDir_1989_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*10 + 11, v_useStdin_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*10 + 12, v_onlyDeps_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*10 + 13, v_onlySrcDeps_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*10 + 14, v_depsJson_1993_);
lean_ctor_set_uint32(v_reuseFailAlloc_2018_, sizeof(void*)*10, v_trustLevel_1995_);
lean_ctor_set_uint32(v_reuseFailAlloc_2018_, sizeof(void*)*10 + 4, v_numThreads_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*10 + 15, v_jsonOutput_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*10 + 16, v_printStats_2004_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*10 + 17, v_run_2005_);
v___x_2014_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2016_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_2014_);
v___x_2016_ = v___x_1983_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec_ref(v_opts_931_);
v_a_2022_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_2022_);
lean_dec_ref(v___x_1980_);
v___x_2026_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2027_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2026_);
lean_dec_ref(v___x_2027_);
goto v___jp_2023_;
v___jp_2023_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_io_error_to_string(v_a_2022_);
v___x_2025_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2024_);
lean_dec_ref(v___x_2025_);
goto v___jp_1098_;
}
}
}
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2029_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2028_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2067_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2067_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2067_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v_leanOpts_2034_; lean_object* v_forwardedArgs_2035_; uint8_t v_component_2036_; uint8_t v_printPrefix_2037_; uint8_t v_printLibDir_2038_; uint8_t v_useStdin_2039_; uint8_t v_onlyDeps_2040_; uint8_t v_onlySrcDeps_2041_; uint8_t v_depsJson_2042_; lean_object* v_opts_2043_; uint32_t v_trustLevel_2044_; uint32_t v_numThreads_2045_; lean_object* v_rootDir_x3f_2046_; lean_object* v_setupFileName_x3f_2047_; lean_object* v_oleanFileName_x3f_2048_; lean_object* v_cFileName_x3f_2049_; lean_object* v_bcFileName_x3f_2050_; uint8_t v_jsonOutput_2051_; lean_object* v_errorOnKinds_2052_; uint8_t v_printStats_2053_; uint8_t v_run_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2065_; 
v_leanOpts_2034_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2035_ = lean_ctor_get(v_opts_931_, 1);
v_component_2036_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2037_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2038_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2039_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2040_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2041_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2042_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2043_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2044_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2045_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2046_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2047_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2048_ = lean_ctor_get(v_opts_931_, 5);
v_cFileName_x3f_2049_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2050_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2051_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2052_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2053_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2054_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v_opts_931_, 6);
lean_dec(v_unused_2066_);
v___x_2056_ = v_opts_931_;
v_isShared_2057_ = v_isSharedCheck_2065_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_errorOnKinds_2052_);
lean_inc(v_bcFileName_x3f_2050_);
lean_inc(v_cFileName_x3f_2049_);
lean_inc(v_oleanFileName_x3f_2048_);
lean_inc(v_setupFileName_x3f_2047_);
lean_inc(v_rootDir_x3f_2046_);
lean_inc(v_opts_2043_);
lean_inc(v_forwardedArgs_2035_);
lean_inc(v_leanOpts_2034_);
lean_dec(v_opts_931_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2065_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_a_2030_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 6, v___x_2058_);
v___x_2060_ = v___x_2056_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_leanOpts_2034_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_forwardedArgs_2035_);
lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_opts_2043_);
lean_ctor_set(v_reuseFailAlloc_2064_, 3, v_rootDir_x3f_2046_);
lean_ctor_set(v_reuseFailAlloc_2064_, 4, v_setupFileName_x3f_2047_);
lean_ctor_set(v_reuseFailAlloc_2064_, 5, v_oleanFileName_x3f_2048_);
lean_ctor_set(v_reuseFailAlloc_2064_, 6, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2064_, 7, v_cFileName_x3f_2049_);
lean_ctor_set(v_reuseFailAlloc_2064_, 8, v_bcFileName_x3f_2050_);
lean_ctor_set(v_reuseFailAlloc_2064_, 9, v_errorOnKinds_2052_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 8, v_component_2036_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 9, v_printPrefix_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 10, v_printLibDir_2038_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 11, v_useStdin_2039_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 12, v_onlyDeps_2040_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 13, v_onlySrcDeps_2041_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 14, v_depsJson_2042_);
lean_ctor_set_uint32(v_reuseFailAlloc_2064_, sizeof(void*)*10, v_trustLevel_2044_);
lean_ctor_set_uint32(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 4, v_numThreads_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 15, v_jsonOutput_2051_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 16, v_printStats_2053_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 17, v_run_2054_);
v___x_2060_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2062_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2060_);
v___x_2062_ = v___x_2032_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec_ref(v_opts_931_);
v_a_2068_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2068_);
lean_dec_ref(v___x_2029_);
v___x_2072_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2073_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2072_);
lean_dec_ref(v___x_2073_);
goto v___jp_2069_;
v___jp_2069_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = lean_io_error_to_string(v_a_2068_);
v___x_2071_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2070_);
lean_dec_ref(v___x_2071_);
goto v___jp_980_;
}
}
}
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2075_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2074_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2113_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2113_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2113_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v_leanOpts_2080_; lean_object* v_forwardedArgs_2081_; uint8_t v_component_2082_; uint8_t v_printPrefix_2083_; uint8_t v_printLibDir_2084_; uint8_t v_useStdin_2085_; uint8_t v_onlyDeps_2086_; uint8_t v_onlySrcDeps_2087_; uint8_t v_depsJson_2088_; lean_object* v_opts_2089_; uint32_t v_trustLevel_2090_; uint32_t v_numThreads_2091_; lean_object* v_rootDir_x3f_2092_; lean_object* v_setupFileName_x3f_2093_; lean_object* v_ileanFileName_x3f_2094_; lean_object* v_cFileName_x3f_2095_; lean_object* v_bcFileName_x3f_2096_; uint8_t v_jsonOutput_2097_; lean_object* v_errorOnKinds_2098_; uint8_t v_printStats_2099_; uint8_t v_run_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2111_; 
v_leanOpts_2080_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2081_ = lean_ctor_get(v_opts_931_, 1);
v_component_2082_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2083_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2084_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2085_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2086_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2087_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2088_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2089_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2090_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2091_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2092_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2093_ = lean_ctor_get(v_opts_931_, 4);
v_ileanFileName_x3f_2094_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2095_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2096_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2097_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2098_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2099_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2100_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v_opts_931_, 5);
lean_dec(v_unused_2112_);
v___x_2102_ = v_opts_931_;
v_isShared_2103_ = v_isSharedCheck_2111_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_errorOnKinds_2098_);
lean_inc(v_bcFileName_x3f_2096_);
lean_inc(v_cFileName_x3f_2095_);
lean_inc(v_ileanFileName_x3f_2094_);
lean_inc(v_setupFileName_x3f_2093_);
lean_inc(v_rootDir_x3f_2092_);
lean_inc(v_opts_2089_);
lean_inc(v_forwardedArgs_2081_);
lean_inc(v_leanOpts_2080_);
lean_dec(v_opts_931_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2111_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2104_, 0, v_a_2076_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 5, v___x_2104_);
v___x_2106_ = v___x_2102_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_leanOpts_2080_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_forwardedArgs_2081_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_opts_2089_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_rootDir_x3f_2092_);
lean_ctor_set(v_reuseFailAlloc_2110_, 4, v_setupFileName_x3f_2093_);
lean_ctor_set(v_reuseFailAlloc_2110_, 5, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2110_, 6, v_ileanFileName_x3f_2094_);
lean_ctor_set(v_reuseFailAlloc_2110_, 7, v_cFileName_x3f_2095_);
lean_ctor_set(v_reuseFailAlloc_2110_, 8, v_bcFileName_x3f_2096_);
lean_ctor_set(v_reuseFailAlloc_2110_, 9, v_errorOnKinds_2098_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*10 + 8, v_component_2082_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*10 + 9, v_printPrefix_2083_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*10 + 10, v_printLibDir_2084_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*10 + 11, v_useStdin_2085_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*10 + 12, v_onlyDeps_2086_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*10 + 13, v_onlySrcDeps_2087_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*10 + 14, v_depsJson_2088_);
lean_ctor_set_uint32(v_reuseFailAlloc_2110_, sizeof(void*)*10, v_trustLevel_2090_);
lean_ctor_set_uint32(v_reuseFailAlloc_2110_, sizeof(void*)*10 + 4, v_numThreads_2091_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*10 + 15, v_jsonOutput_2097_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*10 + 16, v_printStats_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*10 + 17, v_run_2100_);
v___x_2106_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2106_);
v___x_2108_ = v___x_2078_;
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
lean_object* v_a_2114_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_dec_ref(v_opts_931_);
v_a_2114_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2114_);
lean_dec_ref(v___x_2075_);
v___x_2118_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2119_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2118_);
lean_dec_ref(v___x_2119_);
goto v___jp_2115_;
v___jp_2115_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_io_error_to_string(v_a_2114_);
v___x_2117_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2116_);
lean_dec_ref(v___x_2117_);
goto v___jp_1104_;
}
}
}
}
else
{
lean_object* v_leanOpts_2120_; lean_object* v_forwardedArgs_2121_; uint8_t v_component_2122_; uint8_t v_printPrefix_2123_; uint8_t v_printLibDir_2124_; uint8_t v_useStdin_2125_; uint8_t v_onlyDeps_2126_; uint8_t v_onlySrcDeps_2127_; uint8_t v_depsJson_2128_; lean_object* v_opts_2129_; uint32_t v_trustLevel_2130_; uint32_t v_numThreads_2131_; lean_object* v_rootDir_x3f_2132_; lean_object* v_setupFileName_x3f_2133_; lean_object* v_oleanFileName_x3f_2134_; lean_object* v_ileanFileName_x3f_2135_; lean_object* v_cFileName_x3f_2136_; lean_object* v_bcFileName_x3f_2137_; uint8_t v_jsonOutput_2138_; lean_object* v_errorOnKinds_2139_; uint8_t v_printStats_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2150_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_2120_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2121_ = lean_ctor_get(v_opts_931_, 1);
v_component_2122_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2123_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2124_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2125_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2126_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2127_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2128_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2129_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2130_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2131_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2132_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2133_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2134_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_2135_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2136_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2137_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2138_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2139_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2140_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2142_ = v_opts_931_;
v_isShared_2143_ = v_isSharedCheck_2150_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_errorOnKinds_2139_);
lean_inc(v_bcFileName_x3f_2137_);
lean_inc(v_cFileName_x3f_2136_);
lean_inc(v_ileanFileName_x3f_2135_);
lean_inc(v_oleanFileName_x3f_2134_);
lean_inc(v_setupFileName_x3f_2133_);
lean_inc(v_rootDir_x3f_2132_);
lean_inc(v_opts_2129_);
lean_inc(v_forwardedArgs_2121_);
lean_inc(v_leanOpts_2120_);
lean_dec(v_opts_931_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2150_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2144_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2145_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2120_, v___x_2144_, v___x_1152_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2145_);
v___x_2147_ = v___x_2142_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_forwardedArgs_2121_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_opts_2129_);
lean_ctor_set(v_reuseFailAlloc_2149_, 3, v_rootDir_x3f_2132_);
lean_ctor_set(v_reuseFailAlloc_2149_, 4, v_setupFileName_x3f_2133_);
lean_ctor_set(v_reuseFailAlloc_2149_, 5, v_oleanFileName_x3f_2134_);
lean_ctor_set(v_reuseFailAlloc_2149_, 6, v_ileanFileName_x3f_2135_);
lean_ctor_set(v_reuseFailAlloc_2149_, 7, v_cFileName_x3f_2136_);
lean_ctor_set(v_reuseFailAlloc_2149_, 8, v_bcFileName_x3f_2137_);
lean_ctor_set(v_reuseFailAlloc_2149_, 9, v_errorOnKinds_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2149_, sizeof(void*)*10 + 8, v_component_2122_);
lean_ctor_set_uint8(v_reuseFailAlloc_2149_, sizeof(void*)*10 + 9, v_printPrefix_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2149_, sizeof(void*)*10 + 10, v_printLibDir_2124_);
lean_ctor_set_uint8(v_reuseFailAlloc_2149_, sizeof(void*)*10 + 11, v_useStdin_2125_);
lean_ctor_set_uint8(v_reuseFailAlloc_2149_, sizeof(void*)*10 + 12, v_onlyDeps_2126_);
lean_ctor_set_uint8(v_reuseFailAlloc_2149_, sizeof(void*)*10 + 13, v_onlySrcDeps_2127_);
lean_ctor_set_uint8(v_reuseFailAlloc_2149_, sizeof(void*)*10 + 14, v_depsJson_2128_);
lean_ctor_set_uint32(v_reuseFailAlloc_2149_, sizeof(void*)*10, v_trustLevel_2130_);
lean_ctor_set_uint32(v_reuseFailAlloc_2149_, sizeof(void*)*10 + 4, v_numThreads_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2149_, sizeof(void*)*10 + 15, v_jsonOutput_2138_);
lean_ctor_set_uint8(v_reuseFailAlloc_2149_, sizeof(void*)*10 + 16, v_printStats_2140_);
v___x_2147_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2148_; 
lean_ctor_set_uint8(v___x_2147_, sizeof(void*)*10 + 17, v___x_1154_);
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_leanOpts_2151_; lean_object* v_forwardedArgs_2152_; uint8_t v_component_2153_; uint8_t v_printPrefix_2154_; uint8_t v_printLibDir_2155_; uint8_t v_onlyDeps_2156_; uint8_t v_onlySrcDeps_2157_; uint8_t v_depsJson_2158_; lean_object* v_opts_2159_; uint32_t v_trustLevel_2160_; uint32_t v_numThreads_2161_; lean_object* v_rootDir_x3f_2162_; lean_object* v_setupFileName_x3f_2163_; lean_object* v_oleanFileName_x3f_2164_; lean_object* v_ileanFileName_x3f_2165_; lean_object* v_cFileName_x3f_2166_; lean_object* v_bcFileName_x3f_2167_; uint8_t v_jsonOutput_2168_; lean_object* v_errorOnKinds_2169_; uint8_t v_printStats_2170_; uint8_t v_run_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_2151_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2152_ = lean_ctor_get(v_opts_931_, 1);
v_component_2153_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2154_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2155_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_onlyDeps_2156_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2157_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2158_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2159_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2160_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2161_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2162_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2163_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2164_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_2165_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2166_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2167_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2168_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2169_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2170_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2171_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2173_ = v_opts_931_;
v_isShared_2174_ = v_isSharedCheck_2179_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_errorOnKinds_2169_);
lean_inc(v_bcFileName_x3f_2167_);
lean_inc(v_cFileName_x3f_2166_);
lean_inc(v_ileanFileName_x3f_2165_);
lean_inc(v_oleanFileName_x3f_2164_);
lean_inc(v_setupFileName_x3f_2163_);
lean_inc(v_rootDir_x3f_2162_);
lean_inc(v_opts_2159_);
lean_inc(v_forwardedArgs_2152_);
lean_inc(v_leanOpts_2151_);
lean_dec(v_opts_931_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2179_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_leanOpts_2151_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_forwardedArgs_2152_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_opts_2159_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v_rootDir_x3f_2162_);
lean_ctor_set(v_reuseFailAlloc_2178_, 4, v_setupFileName_x3f_2163_);
lean_ctor_set(v_reuseFailAlloc_2178_, 5, v_oleanFileName_x3f_2164_);
lean_ctor_set(v_reuseFailAlloc_2178_, 6, v_ileanFileName_x3f_2165_);
lean_ctor_set(v_reuseFailAlloc_2178_, 7, v_cFileName_x3f_2166_);
lean_ctor_set(v_reuseFailAlloc_2178_, 8, v_bcFileName_x3f_2167_);
lean_ctor_set(v_reuseFailAlloc_2178_, 9, v_errorOnKinds_2169_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*10 + 8, v_component_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*10 + 9, v_printPrefix_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*10 + 10, v_printLibDir_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*10 + 12, v_onlyDeps_2156_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*10 + 13, v_onlySrcDeps_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*10 + 14, v_depsJson_2158_);
lean_ctor_set_uint32(v_reuseFailAlloc_2178_, sizeof(void*)*10, v_trustLevel_2160_);
lean_ctor_set_uint32(v_reuseFailAlloc_2178_, sizeof(void*)*10 + 4, v_numThreads_2161_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*10 + 15, v_jsonOutput_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*10 + 16, v_printStats_2170_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*10 + 17, v_run_2171_);
v___x_2176_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2177_; 
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*10 + 11, v___x_1152_);
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
return v___x_2177_;
}
}
}
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2181_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2180_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2240_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2240_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2240_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = lean_string_utf8_byte_size(v_a_2182_);
lean_inc(v_a_2182_);
v___x_2188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2188_, 0, v_a_2182_);
lean_ctor_set(v___x_2188_, 1, v___x_2186_);
lean_ctor_set(v___x_2188_, 2, v___x_2187_);
v___x_2189_ = l_String_Slice_toNat_x3f(v___x_2188_);
lean_dec_ref(v___x_2188_);
if (lean_obj_tag(v___x_2189_) == 1)
{
lean_object* v_val_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v_val_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_val_2190_);
lean_dec_ref(v___x_2189_);
v___x_2191_ = lean_unsigned_to_nat(4u);
v___x_2192_ = lean_unsigned_to_nat(2u);
v___x_2193_ = lean_nat_shiftr(v_val_2190_, v___x_2192_);
lean_dec(v_val_2190_);
v___x_2194_ = lean_nat_mul(v___x_2193_, v___x_2191_);
lean_dec(v___x_2193_);
v___x_2195_ = lean_unsigned_to_nat(1024u);
v___x_2196_ = lean_nat_mul(v___x_2194_, v___x_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25);
v___x_2198_ = lean_nat_dec_lt(v___x_2196_, v___x_2197_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec(v___x_2196_);
lean_del_object(v___x_2184_);
lean_dec(v_a_2182_);
lean_dec_ref(v_opts_931_);
v___x_2199_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2200_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2199_);
lean_dec_ref(v___x_2200_);
goto v___jp_974_;
}
else
{
size_t v___x_2201_; lean_object* v___x_2202_; lean_object* v_leanOpts_2203_; lean_object* v_forwardedArgs_2204_; uint8_t v_component_2205_; uint8_t v_printPrefix_2206_; uint8_t v_printLibDir_2207_; uint8_t v_useStdin_2208_; uint8_t v_onlyDeps_2209_; uint8_t v_onlySrcDeps_2210_; uint8_t v_depsJson_2211_; lean_object* v_opts_2212_; uint32_t v_trustLevel_2213_; uint32_t v_numThreads_2214_; lean_object* v_rootDir_x3f_2215_; lean_object* v_setupFileName_x3f_2216_; lean_object* v_oleanFileName_x3f_2217_; lean_object* v_ileanFileName_x3f_2218_; lean_object* v_cFileName_x3f_2219_; lean_object* v_bcFileName_x3f_2220_; uint8_t v_jsonOutput_2221_; lean_object* v_errorOnKinds_2222_; uint8_t v_printStats_2223_; uint8_t v_run_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2237_; 
v___x_2201_ = lean_usize_of_nat(v___x_2196_);
lean_dec(v___x_2196_);
v___x_2202_ = lean_internal_set_thread_stack_size(v___x_2201_);
v_leanOpts_2203_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2204_ = lean_ctor_get(v_opts_931_, 1);
v_component_2205_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2206_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2207_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2208_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2209_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2210_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2211_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2212_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2213_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2214_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2215_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2216_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2217_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_2218_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2219_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2220_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2221_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2222_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2223_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2224_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2226_ = v_opts_931_;
v_isShared_2227_ = v_isSharedCheck_2237_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_errorOnKinds_2222_);
lean_inc(v_bcFileName_x3f_2220_);
lean_inc(v_cFileName_x3f_2219_);
lean_inc(v_ileanFileName_x3f_2218_);
lean_inc(v_oleanFileName_x3f_2217_);
lean_inc(v_setupFileName_x3f_2216_);
lean_inc(v_rootDir_x3f_2215_);
lean_inc(v_opts_2212_);
lean_inc(v_forwardedArgs_2204_);
lean_inc(v_leanOpts_2203_);
lean_dec(v_opts_931_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2237_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2228_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2229_ = lean_string_append(v___x_2228_, v_a_2182_);
lean_dec(v_a_2182_);
v___x_2230_ = lean_array_push(v_forwardedArgs_2204_, v___x_2229_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 1, v___x_2230_);
v___x_2232_ = v___x_2226_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_leanOpts_2203_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_opts_2212_);
lean_ctor_set(v_reuseFailAlloc_2236_, 3, v_rootDir_x3f_2215_);
lean_ctor_set(v_reuseFailAlloc_2236_, 4, v_setupFileName_x3f_2216_);
lean_ctor_set(v_reuseFailAlloc_2236_, 5, v_oleanFileName_x3f_2217_);
lean_ctor_set(v_reuseFailAlloc_2236_, 6, v_ileanFileName_x3f_2218_);
lean_ctor_set(v_reuseFailAlloc_2236_, 7, v_cFileName_x3f_2219_);
lean_ctor_set(v_reuseFailAlloc_2236_, 8, v_bcFileName_x3f_2220_);
lean_ctor_set(v_reuseFailAlloc_2236_, 9, v_errorOnKinds_2222_);
lean_ctor_set_uint8(v_reuseFailAlloc_2236_, sizeof(void*)*10 + 8, v_component_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2236_, sizeof(void*)*10 + 9, v_printPrefix_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2236_, sizeof(void*)*10 + 10, v_printLibDir_2207_);
lean_ctor_set_uint8(v_reuseFailAlloc_2236_, sizeof(void*)*10 + 11, v_useStdin_2208_);
lean_ctor_set_uint8(v_reuseFailAlloc_2236_, sizeof(void*)*10 + 12, v_onlyDeps_2209_);
lean_ctor_set_uint8(v_reuseFailAlloc_2236_, sizeof(void*)*10 + 13, v_onlySrcDeps_2210_);
lean_ctor_set_uint8(v_reuseFailAlloc_2236_, sizeof(void*)*10 + 14, v_depsJson_2211_);
lean_ctor_set_uint32(v_reuseFailAlloc_2236_, sizeof(void*)*10, v_trustLevel_2213_);
lean_ctor_set_uint32(v_reuseFailAlloc_2236_, sizeof(void*)*10 + 4, v_numThreads_2214_);
lean_ctor_set_uint8(v_reuseFailAlloc_2236_, sizeof(void*)*10 + 15, v_jsonOutput_2221_);
lean_ctor_set_uint8(v_reuseFailAlloc_2236_, sizeof(void*)*10 + 16, v_printStats_2223_);
lean_ctor_set_uint8(v_reuseFailAlloc_2236_, sizeof(void*)*10 + 17, v_run_2224_);
v___x_2232_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2234_; 
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2232_);
v___x_2234_ = v___x_2184_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec(v___x_2189_);
lean_del_object(v___x_2184_);
lean_dec(v_a_2182_);
lean_dec_ref(v_opts_931_);
v___x_2238_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28));
v___x_2239_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2238_);
lean_dec_ref(v___x_2239_);
goto v___jp_971_;
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec_ref(v_opts_931_);
v_a_2241_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2241_);
lean_dec_ref(v___x_2181_);
v___x_2245_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2246_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2245_);
lean_dec_ref(v___x_2246_);
goto v___jp_2242_;
v___jp_2242_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = lean_io_error_to_string(v_a_2241_);
v___x_2244_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2243_);
lean_dec_ref(v___x_2244_);
goto v___jp_968_;
}
}
}
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2248_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2247_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2286_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2286_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2286_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v_leanOpts_2253_; lean_object* v_forwardedArgs_2254_; uint8_t v_component_2255_; uint8_t v_printPrefix_2256_; uint8_t v_printLibDir_2257_; uint8_t v_useStdin_2258_; uint8_t v_onlyDeps_2259_; uint8_t v_onlySrcDeps_2260_; uint8_t v_depsJson_2261_; lean_object* v_opts_2262_; uint32_t v_trustLevel_2263_; uint32_t v_numThreads_2264_; lean_object* v_rootDir_x3f_2265_; lean_object* v_setupFileName_x3f_2266_; lean_object* v_oleanFileName_x3f_2267_; lean_object* v_ileanFileName_x3f_2268_; lean_object* v_cFileName_x3f_2269_; uint8_t v_jsonOutput_2270_; lean_object* v_errorOnKinds_2271_; uint8_t v_printStats_2272_; uint8_t v_run_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2284_; 
v_leanOpts_2253_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2254_ = lean_ctor_get(v_opts_931_, 1);
v_component_2255_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2256_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2257_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2258_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2259_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2260_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2261_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2262_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2263_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2264_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2265_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2266_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2267_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_2268_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2269_ = lean_ctor_get(v_opts_931_, 7);
v_jsonOutput_2270_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2271_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2272_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2273_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2284_ == 0)
{
lean_object* v_unused_2285_; 
v_unused_2285_ = lean_ctor_get(v_opts_931_, 8);
lean_dec(v_unused_2285_);
v___x_2275_ = v_opts_931_;
v_isShared_2276_ = v_isSharedCheck_2284_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_errorOnKinds_2271_);
lean_inc(v_cFileName_x3f_2269_);
lean_inc(v_ileanFileName_x3f_2268_);
lean_inc(v_oleanFileName_x3f_2267_);
lean_inc(v_setupFileName_x3f_2266_);
lean_inc(v_rootDir_x3f_2265_);
lean_inc(v_opts_2262_);
lean_inc(v_forwardedArgs_2254_);
lean_inc(v_leanOpts_2253_);
lean_dec(v_opts_931_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2284_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2277_, 0, v_a_2249_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 8, v___x_2277_);
v___x_2279_ = v___x_2275_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_leanOpts_2253_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_forwardedArgs_2254_);
lean_ctor_set(v_reuseFailAlloc_2283_, 2, v_opts_2262_);
lean_ctor_set(v_reuseFailAlloc_2283_, 3, v_rootDir_x3f_2265_);
lean_ctor_set(v_reuseFailAlloc_2283_, 4, v_setupFileName_x3f_2266_);
lean_ctor_set(v_reuseFailAlloc_2283_, 5, v_oleanFileName_x3f_2267_);
lean_ctor_set(v_reuseFailAlloc_2283_, 6, v_ileanFileName_x3f_2268_);
lean_ctor_set(v_reuseFailAlloc_2283_, 7, v_cFileName_x3f_2269_);
lean_ctor_set(v_reuseFailAlloc_2283_, 8, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2283_, 9, v_errorOnKinds_2271_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*10 + 8, v_component_2255_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*10 + 9, v_printPrefix_2256_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*10 + 10, v_printLibDir_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*10 + 11, v_useStdin_2258_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*10 + 12, v_onlyDeps_2259_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*10 + 13, v_onlySrcDeps_2260_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*10 + 14, v_depsJson_2261_);
lean_ctor_set_uint32(v_reuseFailAlloc_2283_, sizeof(void*)*10, v_trustLevel_2263_);
lean_ctor_set_uint32(v_reuseFailAlloc_2283_, sizeof(void*)*10 + 4, v_numThreads_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*10 + 15, v_jsonOutput_2270_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*10 + 16, v_printStats_2272_);
lean_ctor_set_uint8(v_reuseFailAlloc_2283_, sizeof(void*)*10 + 17, v_run_2273_);
v___x_2279_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2281_; 
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2279_);
v___x_2281_ = v___x_2251_;
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
lean_dec_ref(v_opts_931_);
v_a_2287_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2287_);
lean_dec_ref(v___x_2248_);
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
goto v___jp_1110_;
}
}
}
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2294_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2293_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2332_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2332_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2332_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_leanOpts_2299_; lean_object* v_forwardedArgs_2300_; uint8_t v_component_2301_; uint8_t v_printPrefix_2302_; uint8_t v_printLibDir_2303_; uint8_t v_useStdin_2304_; uint8_t v_onlyDeps_2305_; uint8_t v_onlySrcDeps_2306_; uint8_t v_depsJson_2307_; lean_object* v_opts_2308_; uint32_t v_trustLevel_2309_; uint32_t v_numThreads_2310_; lean_object* v_rootDir_x3f_2311_; lean_object* v_setupFileName_x3f_2312_; lean_object* v_oleanFileName_x3f_2313_; lean_object* v_ileanFileName_x3f_2314_; lean_object* v_bcFileName_x3f_2315_; uint8_t v_jsonOutput_2316_; lean_object* v_errorOnKinds_2317_; uint8_t v_printStats_2318_; uint8_t v_run_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2330_; 
v_leanOpts_2299_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2300_ = lean_ctor_get(v_opts_931_, 1);
v_component_2301_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2302_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2303_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2304_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2305_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2306_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2307_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2308_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2309_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2310_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2311_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2312_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2313_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_2314_ = lean_ctor_get(v_opts_931_, 6);
v_bcFileName_x3f_2315_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2316_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2317_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2318_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2319_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; 
v_unused_2331_ = lean_ctor_get(v_opts_931_, 7);
lean_dec(v_unused_2331_);
v___x_2321_ = v_opts_931_;
v_isShared_2322_ = v_isSharedCheck_2330_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_errorOnKinds_2317_);
lean_inc(v_bcFileName_x3f_2315_);
lean_inc(v_ileanFileName_x3f_2314_);
lean_inc(v_oleanFileName_x3f_2313_);
lean_inc(v_setupFileName_x3f_2312_);
lean_inc(v_rootDir_x3f_2311_);
lean_inc(v_opts_2308_);
lean_inc(v_forwardedArgs_2300_);
lean_inc(v_leanOpts_2299_);
lean_dec(v_opts_931_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2330_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2323_, 0, v_a_2295_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 7, v___x_2323_);
v___x_2325_ = v___x_2321_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_leanOpts_2299_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_forwardedArgs_2300_);
lean_ctor_set(v_reuseFailAlloc_2329_, 2, v_opts_2308_);
lean_ctor_set(v_reuseFailAlloc_2329_, 3, v_rootDir_x3f_2311_);
lean_ctor_set(v_reuseFailAlloc_2329_, 4, v_setupFileName_x3f_2312_);
lean_ctor_set(v_reuseFailAlloc_2329_, 5, v_oleanFileName_x3f_2313_);
lean_ctor_set(v_reuseFailAlloc_2329_, 6, v_ileanFileName_x3f_2314_);
lean_ctor_set(v_reuseFailAlloc_2329_, 7, v___x_2323_);
lean_ctor_set(v_reuseFailAlloc_2329_, 8, v_bcFileName_x3f_2315_);
lean_ctor_set(v_reuseFailAlloc_2329_, 9, v_errorOnKinds_2317_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*10 + 8, v_component_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*10 + 9, v_printPrefix_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*10 + 10, v_printLibDir_2303_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*10 + 11, v_useStdin_2304_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*10 + 12, v_onlyDeps_2305_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*10 + 13, v_onlySrcDeps_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*10 + 14, v_depsJson_2307_);
lean_ctor_set_uint32(v_reuseFailAlloc_2329_, sizeof(void*)*10, v_trustLevel_2309_);
lean_ctor_set_uint32(v_reuseFailAlloc_2329_, sizeof(void*)*10 + 4, v_numThreads_2310_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*10 + 15, v_jsonOutput_2316_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*10 + 16, v_printStats_2318_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*10 + 17, v_run_2319_);
v___x_2325_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2327_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2325_);
v___x_2327_ = v___x_2297_;
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
lean_dec_ref(v_opts_931_);
v_a_2333_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2294_);
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
goto v___jp_962_;
}
}
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
v___x_2339_ = l___private_Lean_Shell_0__Lean_featuresString;
v___x_2340_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2339_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2348_; 
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2348_ == 0)
{
lean_object* v_unused_2349_; 
v_unused_2349_ = lean_ctor_get(v___x_2340_, 0);
lean_dec(v_unused_2349_);
v___x_2342_ = v___x_2340_;
v_isShared_2343_ = v_isSharedCheck_2348_;
goto v_resetjp_2341_;
}
else
{
lean_dec(v___x_2340_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2348_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; lean_object* v___x_2346_; 
v___x_2344_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2343_ == 0)
{
lean_ctor_set_tag(v___x_2342_, 1);
lean_ctor_set(v___x_2342_, 0, v___x_2344_);
v___x_2346_ = v___x_2342_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_a_2350_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2340_);
v___x_2354_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2355_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2354_);
lean_dec_ref(v___x_2355_);
goto v___jp_2351_;
v___jp_2351_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_io_error_to_string(v_a_2350_);
v___x_2353_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2352_);
lean_dec_ref(v___x_2353_);
goto v___jp_1116_;
}
}
}
}
else
{
lean_object* v___x_2356_; 
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
v___x_2356_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1140_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2364_; 
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; 
v_unused_2365_ = lean_ctor_get(v___x_2356_, 0);
lean_dec(v_unused_2365_);
v___x_2358_ = v___x_2356_;
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
else
{
lean_dec(v___x_2356_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2360_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2359_ == 0)
{
lean_ctor_set_tag(v___x_2358_, 1);
lean_ctor_set(v___x_2358_, 0, v___x_2360_);
v___x_2362_ = v___x_2358_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v_a_2366_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2366_);
lean_dec_ref(v___x_2356_);
v___x_2370_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2371_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2370_);
lean_dec_ref(v___x_2371_);
goto v___jp_2367_;
v___jp_2367_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_io_error_to_string(v_a_2366_);
v___x_2369_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2368_);
lean_dec_ref(v___x_2369_);
goto v___jp_956_;
}
}
}
}
else
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
v___x_2372_ = l_Lean_githash;
v___x_2373_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2372_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2381_; 
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; 
v_unused_2382_ = lean_ctor_get(v___x_2373_, 0);
lean_dec(v_unused_2382_);
v___x_2375_ = v___x_2373_;
v_isShared_2376_ = v_isSharedCheck_2381_;
goto v_resetjp_2374_;
}
else
{
lean_dec(v___x_2373_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2381_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2377_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2376_ == 0)
{
lean_ctor_set_tag(v___x_2375_, 1);
lean_ctor_set(v___x_2375_, 0, v___x_2377_);
v___x_2379_ = v___x_2375_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_2383_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_a_2383_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2383_);
lean_dec_ref(v___x_2373_);
v___x_2387_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2388_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2387_);
lean_dec_ref(v___x_2388_);
goto v___jp_2384_;
v___jp_2384_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_io_error_to_string(v_a_2383_);
v___x_2386_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2385_);
lean_dec_ref(v___x_2386_);
goto v___jp_1122_;
}
}
}
}
else
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
v___x_2389_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2390_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2389_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2398_; 
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v___x_2390_, 0);
lean_dec(v_unused_2399_);
v___x_2392_ = v___x_2390_;
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
else
{
lean_dec(v___x_2390_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2394_; lean_object* v___x_2396_; 
v___x_2394_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2393_ == 0)
{
lean_ctor_set_tag(v___x_2392_, 1);
lean_ctor_set(v___x_2392_, 0, v___x_2394_);
v___x_2396_ = v___x_2392_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_a_2400_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2400_);
lean_dec_ref(v___x_2390_);
v___x_2404_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2405_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2404_);
lean_dec_ref(v___x_2405_);
goto v___jp_2401_;
v___jp_2401_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = lean_io_error_to_string(v_a_2400_);
v___x_2403_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2402_);
lean_dec_ref(v___x_2403_);
goto v___jp_950_;
}
}
}
}
else
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
v___x_2406_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2407_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2406_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2415_; 
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; 
v_unused_2416_ = lean_ctor_get(v___x_2407_, 0);
lean_dec(v_unused_2416_);
v___x_2409_ = v___x_2407_;
v_isShared_2410_ = v_isSharedCheck_2415_;
goto v_resetjp_2408_;
}
else
{
lean_dec(v___x_2407_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2415_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2411_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2410_ == 0)
{
lean_ctor_set_tag(v___x_2409_, 1);
lean_ctor_set(v___x_2409_, 0, v___x_2411_);
v___x_2413_ = v___x_2409_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v_a_2417_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2417_);
lean_dec_ref(v___x_2407_);
v___x_2421_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2422_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2421_);
lean_dec_ref(v___x_2422_);
goto v___jp_2418_;
v___jp_2418_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_io_error_to_string(v_a_2417_);
v___x_2420_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2419_);
lean_dec_ref(v___x_2420_);
goto v___jp_1128_;
}
}
}
}
else
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2424_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2423_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2475_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2475_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2475_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2429_ = lean_unsigned_to_nat(0u);
v___x_2430_ = lean_string_utf8_byte_size(v_a_2425_);
lean_inc(v_a_2425_);
v___x_2431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2431_, 0, v_a_2425_);
lean_ctor_set(v___x_2431_, 1, v___x_2429_);
lean_ctor_set(v___x_2431_, 2, v___x_2430_);
v___x_2432_ = l_String_Slice_toNat_x3f(v___x_2431_);
lean_dec_ref(v___x_2431_);
if (lean_obj_tag(v___x_2432_) == 1)
{
lean_object* v_val_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v_val_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_val_2433_);
lean_dec_ref(v___x_2432_);
v___x_2434_ = lean_cstr_to_nat("4294967296");
v___x_2435_ = lean_nat_dec_lt(v_val_2433_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_dec(v_val_2433_);
lean_del_object(v___x_2427_);
lean_dec(v_a_2425_);
lean_dec_ref(v_opts_931_);
v___x_2436_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2437_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2436_);
lean_dec_ref(v___x_2437_);
goto v___jp_944_;
}
else
{
lean_object* v_leanOpts_2438_; lean_object* v_forwardedArgs_2439_; uint8_t v_component_2440_; uint8_t v_printPrefix_2441_; uint8_t v_printLibDir_2442_; uint8_t v_useStdin_2443_; uint8_t v_onlyDeps_2444_; uint8_t v_onlySrcDeps_2445_; uint8_t v_depsJson_2446_; lean_object* v_opts_2447_; uint32_t v_trustLevel_2448_; lean_object* v_rootDir_x3f_2449_; lean_object* v_setupFileName_x3f_2450_; lean_object* v_oleanFileName_x3f_2451_; lean_object* v_ileanFileName_x3f_2452_; lean_object* v_cFileName_x3f_2453_; lean_object* v_bcFileName_x3f_2454_; uint8_t v_jsonOutput_2455_; lean_object* v_errorOnKinds_2456_; uint8_t v_printStats_2457_; uint8_t v_run_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2472_; 
v_leanOpts_2438_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2439_ = lean_ctor_get(v_opts_931_, 1);
v_component_2440_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2441_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2442_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2443_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2444_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2445_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2446_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2447_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2448_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_rootDir_x3f_2449_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2450_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2451_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_2452_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2453_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2454_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2455_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2456_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2457_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2458_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2460_ = v_opts_931_;
v_isShared_2461_ = v_isSharedCheck_2472_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_errorOnKinds_2456_);
lean_inc(v_bcFileName_x3f_2454_);
lean_inc(v_cFileName_x3f_2453_);
lean_inc(v_ileanFileName_x3f_2452_);
lean_inc(v_oleanFileName_x3f_2451_);
lean_inc(v_setupFileName_x3f_2450_);
lean_inc(v_rootDir_x3f_2449_);
lean_inc(v_opts_2447_);
lean_inc(v_forwardedArgs_2439_);
lean_inc(v_leanOpts_2438_);
lean_dec(v_opts_931_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2472_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
uint32_t v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2462_ = lean_uint32_of_nat(v_val_2433_);
lean_dec(v_val_2433_);
v___x_2463_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2464_ = lean_string_append(v___x_2463_, v_a_2425_);
lean_dec(v_a_2425_);
v___x_2465_ = lean_array_push(v_forwardedArgs_2439_, v___x_2464_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 1, v___x_2465_);
v___x_2467_ = v___x_2460_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_leanOpts_2438_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v_opts_2447_);
lean_ctor_set(v_reuseFailAlloc_2471_, 3, v_rootDir_x3f_2449_);
lean_ctor_set(v_reuseFailAlloc_2471_, 4, v_setupFileName_x3f_2450_);
lean_ctor_set(v_reuseFailAlloc_2471_, 5, v_oleanFileName_x3f_2451_);
lean_ctor_set(v_reuseFailAlloc_2471_, 6, v_ileanFileName_x3f_2452_);
lean_ctor_set(v_reuseFailAlloc_2471_, 7, v_cFileName_x3f_2453_);
lean_ctor_set(v_reuseFailAlloc_2471_, 8, v_bcFileName_x3f_2454_);
lean_ctor_set(v_reuseFailAlloc_2471_, 9, v_errorOnKinds_2456_);
lean_ctor_set_uint8(v_reuseFailAlloc_2471_, sizeof(void*)*10 + 8, v_component_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2471_, sizeof(void*)*10 + 9, v_printPrefix_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2471_, sizeof(void*)*10 + 10, v_printLibDir_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2471_, sizeof(void*)*10 + 11, v_useStdin_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2471_, sizeof(void*)*10 + 12, v_onlyDeps_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2471_, sizeof(void*)*10 + 13, v_onlySrcDeps_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2471_, sizeof(void*)*10 + 14, v_depsJson_2446_);
lean_ctor_set_uint32(v_reuseFailAlloc_2471_, sizeof(void*)*10, v_trustLevel_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2471_, sizeof(void*)*10 + 15, v_jsonOutput_2455_);
lean_ctor_set_uint8(v_reuseFailAlloc_2471_, sizeof(void*)*10 + 16, v_printStats_2457_);
lean_ctor_set_uint8(v_reuseFailAlloc_2471_, sizeof(void*)*10 + 17, v_run_2458_);
v___x_2467_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2469_; 
lean_ctor_set_uint32(v___x_2467_, sizeof(void*)*10 + 4, v___x_2462_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2467_);
v___x_2469_ = v___x_2427_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
else
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
lean_dec(v___x_2432_);
lean_del_object(v___x_2427_);
lean_dec(v_a_2425_);
lean_dec_ref(v_opts_931_);
v___x_2473_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2474_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2473_);
lean_dec_ref(v___x_2474_);
goto v___jp_941_;
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec_ref(v_opts_931_);
v_a_2476_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2476_);
lean_dec_ref(v___x_2424_);
v___x_2480_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2481_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2480_);
lean_dec_ref(v___x_2481_);
goto v___jp_2477_;
v___jp_2477_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = lean_io_error_to_string(v_a_2476_);
v___x_2479_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2478_);
lean_dec_ref(v___x_2479_);
goto v___jp_938_;
}
}
}
}
else
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec(v_optArg_x3f_933_);
v___x_2482_ = lean_internal_set_exit_on_panic(v___x_1132_);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_opts_931_);
return v___x_2483_;
}
v___jp_935_:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
v___jp_938_:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_940_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_939_);
lean_dec_ref(v___x_940_);
goto v___jp_935_;
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
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_io_error_to_string(v___y_1035_);
v___x_1037_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1036_);
lean_dec_ref(v___x_1037_);
goto v___jp_1031_;
}
v___jp_1038_:
{
uint8_t v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = 1;
v___x_1040_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1039_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1048_; 
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v___x_1040_, 0);
lean_dec(v_unused_1049_);
v___x_1042_ = v___x_1040_;
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
else
{
lean_dec(v___x_1040_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_1043_ == 0)
{
lean_ctor_set_tag(v___x_1042_, 1);
lean_ctor_set(v___x_1042_, 0, v___x_1044_);
v___x_1046_ = v___x_1042_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_a_1050_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1050_);
lean_dec_ref(v___x_1040_);
v___x_1051_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1052_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1051_);
lean_dec_ref(v___x_1052_);
v___y_1035_ = v_a_1050_;
goto v___jp_1034_;
}
}
v___jp_1053_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
v___x_1055_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1054_);
lean_dec_ref(v___x_1055_);
goto v___jp_1038_;
}
v___jp_1056_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
v___jp_1059_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1061_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1060_);
lean_dec_ref(v___x_1061_);
goto v___jp_1056_;
}
v___jp_1062_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
v___jp_1065_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1067_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1066_);
lean_dec_ref(v___x_1067_);
goto v___jp_1062_;
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
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
v___jp_1098_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1100_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1099_);
lean_dec_ref(v___x_1100_);
goto v___jp_1095_;
}
v___jp_1101_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
v___jp_1104_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1106_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1105_);
lean_dec_ref(v___x_1106_);
goto v___jp_1101_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2484_, lean_object* v_opt_2485_, lean_object* v_optArg_x3f_2486_, lean_object* v_a_2487_){
_start:
{
uint32_t v_opt_boxed_2488_; lean_object* v_res_2489_; 
v_opt_boxed_2488_ = lean_unbox_uint32(v_opt_2485_);
lean_dec(v_opt_2485_);
v_res_2489_ = lean_shell_options_process(v_opts_2484_, v_opt_boxed_2488_, v_optArg_x3f_2486_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_opts_2490_, lean_object* v_opt_2491_){
_start:
{
lean_object* v_name_2492_; lean_object* v_defValue_2493_; lean_object* v_map_2494_; lean_object* v___x_2495_; 
v_name_2492_ = lean_ctor_get(v_opt_2491_, 0);
v_defValue_2493_ = lean_ctor_get(v_opt_2491_, 1);
v_map_2494_ = lean_ctor_get(v_opts_2490_, 0);
v___x_2495_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2494_, v_name_2492_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_inc(v_defValue_2493_);
return v_defValue_2493_;
}
else
{
lean_object* v_val_2496_; 
v_val_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_val_2496_);
lean_dec_ref(v___x_2495_);
if (lean_obj_tag(v_val_2496_) == 3)
{
lean_object* v_v_2497_; 
v_v_2497_ = lean_ctor_get(v_val_2496_, 0);
lean_inc(v_v_2497_);
lean_dec_ref(v_val_2496_);
return v_v_2497_;
}
else
{
lean_dec(v_val_2496_);
lean_inc(v_defValue_2493_);
return v_defValue_2493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_opts_2498_, lean_object* v_opt_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_opts_2498_, v_opt_2499_);
lean_dec_ref(v_opt_2499_);
lean_dec_ref(v_opts_2498_);
return v_res_2500_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2503_ = lean_string_utf8_byte_size(v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2504_){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2505_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2506_ = lean_string_utf8_byte_size(v_s_2504_);
v___x_2507_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1);
v___x_2508_ = lean_nat_dec_le(v___x_2507_, v___x_2506_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; 
lean_dec_ref(v_s_2504_);
v___x_2509_ = lean_box(0);
return v___x_2509_;
}
else
{
lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2510_ = lean_unsigned_to_nat(0u);
v___x_2511_ = lean_string_memcmp(v_s_2504_, v___x_2505_, v___x_2510_, v___x_2510_, v___x_2507_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; 
lean_dec_ref(v_s_2504_);
v___x_2512_ = lean_box(0);
return v___x_2512_;
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
lean_inc_ref(v_s_2504_);
v___x_2513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2513_, 0, v_s_2504_);
lean_ctor_set(v___x_2513_, 1, v___x_2510_);
lean_ctor_set(v___x_2513_, 2, v___x_2506_);
v___x_2514_ = l_String_Slice_pos_x21(v___x_2513_, v___x_2507_);
lean_dec_ref(v___x_2513_);
v___x_2515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2515_, 0, v_s_2504_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
lean_ctor_set(v___x_2515_, 2, v___x_2506_);
v___x_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
return v___x_2516_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2517_, lean_object* v_pat_2518_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2517_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2520_, lean_object* v_pat_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2520_, v_pat_2521_);
lean_dec_ref(v_pat_2521_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v___x_2524_, lean_object* v___x_2525_, lean_object* v_mainModuleName_2526_, lean_object* v_a_2527_, lean_object* v___x_2528_, lean_object* v_fileName_2529_, lean_object* v___x_2530_, lean_object* v___x_2531_, lean_object* v___x_2532_, lean_object* v___x_2533_, lean_object* v___x_2534_, lean_object* v___x_2535_, lean_object* v___x_2536_, lean_object* v___x_2537_, uint8_t v_run_2538_){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v_env_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; lean_object* v_fileName_2549_; lean_object* v_fileMap_2550_; lean_object* v_currRecDepth_2551_; lean_object* v_ref_2552_; lean_object* v_currNamespace_2553_; lean_object* v_openDecls_2554_; lean_object* v_initHeartbeats_2555_; lean_object* v_maxHeartbeats_2556_; lean_object* v_quotContext_2557_; lean_object* v_currMacroScope_2558_; lean_object* v_cancelTk_x3f_2559_; uint8_t v_suppressElabErrors_2560_; lean_object* v_inheritedTraceOptions_2561_; lean_object* v___y_2562_; uint8_t v___y_2591_; uint8_t v___x_2611_; 
v___x_2540_ = lean_io_get_num_heartbeats();
v___x_2541_ = lean_st_mk_ref(v___x_2524_);
v___x_2542_ = l_Lean_inheritedTraceOptions;
v___x_2543_ = lean_st_ref_get(v___x_2542_);
v___x_2544_ = lean_st_ref_get(v___x_2541_);
v_env_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc_ref(v_env_2545_);
lean_dec(v___x_2544_);
v___x_2546_ = l_Lean_diagnostics;
v___x_2547_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v___x_2525_, v___x_2546_);
v___x_2611_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2545_);
lean_dec_ref(v_env_2545_);
if (v___x_2611_ == 0)
{
if (v___x_2547_ == 0)
{
lean_dec_ref(v___x_2528_);
lean_inc(v___x_2541_);
lean_inc(v___x_2533_);
v_fileName_2549_ = v_fileName_2529_;
v_fileMap_2550_ = v___x_2530_;
v_currRecDepth_2551_ = v___x_2531_;
v_ref_2552_ = v___x_2532_;
v_currNamespace_2553_ = v___x_2533_;
v_openDecls_2554_ = v___x_2534_;
v_initHeartbeats_2555_ = v___x_2540_;
v_maxHeartbeats_2556_ = v___x_2535_;
v_quotContext_2557_ = v___x_2533_;
v_currMacroScope_2558_ = v___x_2536_;
v_cancelTk_x3f_2559_ = v___x_2537_;
v_suppressElabErrors_2560_ = v_run_2538_;
v_inheritedTraceOptions_2561_ = v___x_2543_;
v___y_2562_ = v___x_2541_;
goto v___jp_2548_;
}
else
{
v___y_2591_ = v___x_2611_;
goto v___jp_2590_;
}
}
else
{
v___y_2591_ = v___x_2547_;
goto v___jp_2590_;
}
v___jp_2548_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2563_ = l_Lean_maxRecDepth;
v___x_2564_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_2525_, v___x_2563_);
v___x_2565_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2565_, 0, v_fileName_2549_);
lean_ctor_set(v___x_2565_, 1, v_fileMap_2550_);
lean_ctor_set(v___x_2565_, 2, v___x_2525_);
lean_ctor_set(v___x_2565_, 3, v_currRecDepth_2551_);
lean_ctor_set(v___x_2565_, 4, v___x_2564_);
lean_ctor_set(v___x_2565_, 5, v_ref_2552_);
lean_ctor_set(v___x_2565_, 6, v_currNamespace_2553_);
lean_ctor_set(v___x_2565_, 7, v_openDecls_2554_);
lean_ctor_set(v___x_2565_, 8, v_initHeartbeats_2555_);
lean_ctor_set(v___x_2565_, 9, v_maxHeartbeats_2556_);
lean_ctor_set(v___x_2565_, 10, v_quotContext_2557_);
lean_ctor_set(v___x_2565_, 11, v_currMacroScope_2558_);
lean_ctor_set(v___x_2565_, 12, v_cancelTk_x3f_2559_);
lean_ctor_set(v___x_2565_, 13, v_inheritedTraceOptions_2561_);
lean_ctor_set_uint8(v___x_2565_, sizeof(void*)*14, v___x_2547_);
lean_ctor_set_uint8(v___x_2565_, sizeof(void*)*14 + 1, v_suppressElabErrors_2560_);
v___x_2566_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2526_, v___x_2565_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___x_2565_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref(v___x_2566_);
v___x_2568_ = lean_st_ref_get(v___x_2541_);
lean_dec(v___x_2541_);
lean_dec(v___x_2568_);
v___x_2569_ = lean_string_to_utf8(v_a_2567_);
lean_dec(v_a_2567_);
v___x_2570_ = lean_io_prim_handle_write(v_a_2527_, v___x_2569_);
lean_dec_ref(v___x_2569_);
return v___x_2570_;
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2589_; 
lean_dec(v___x_2541_);
v_a_2571_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2573_ = v___x_2566_;
v_isShared_2574_ = v_isSharedCheck_2589_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2566_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2589_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
if (lean_obj_tag(v_a_2571_) == 0)
{
lean_object* v_msg_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
v_msg_2575_ = lean_ctor_get(v_a_2571_, 1);
lean_inc_ref(v_msg_2575_);
lean_dec_ref(v_a_2571_);
v___x_2576_ = l_Lean_MessageData_toString(v_msg_2575_);
v___x_2577_ = lean_mk_io_user_error(v___x_2576_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2577_);
v___x_2579_ = v___x_2573_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
else
{
lean_object* v_id_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
v_id_2581_ = lean_ctor_get(v_a_2571_, 0);
lean_inc(v_id_2581_);
lean_dec_ref(v_a_2571_);
v___x_2582_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0));
v___x_2583_ = l_Nat_reprFast(v_id_2581_);
v___x_2584_ = lean_string_append(v___x_2582_, v___x_2583_);
lean_dec_ref(v___x_2583_);
v___x_2585_ = lean_mk_io_user_error(v___x_2584_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2585_);
v___x_2587_ = v___x_2573_;
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
}
}
}
v___jp_2590_:
{
if (v___y_2591_ == 0)
{
lean_object* v___x_2592_; lean_object* v_env_2593_; lean_object* v_nextMacroScope_2594_; lean_object* v_ngen_2595_; lean_object* v_auxDeclNGen_2596_; lean_object* v_traceState_2597_; lean_object* v_messages_2598_; lean_object* v_infoState_2599_; lean_object* v_snapshotTasks_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2609_; 
v___x_2592_ = lean_st_ref_take(v___x_2541_);
v_env_2593_ = lean_ctor_get(v___x_2592_, 0);
v_nextMacroScope_2594_ = lean_ctor_get(v___x_2592_, 1);
v_ngen_2595_ = lean_ctor_get(v___x_2592_, 2);
v_auxDeclNGen_2596_ = lean_ctor_get(v___x_2592_, 3);
v_traceState_2597_ = lean_ctor_get(v___x_2592_, 4);
v_messages_2598_ = lean_ctor_get(v___x_2592_, 6);
v_infoState_2599_ = lean_ctor_get(v___x_2592_, 7);
v_snapshotTasks_2600_ = lean_ctor_get(v___x_2592_, 8);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2609_ == 0)
{
lean_object* v_unused_2610_; 
v_unused_2610_ = lean_ctor_get(v___x_2592_, 5);
lean_dec(v_unused_2610_);
v___x_2602_ = v___x_2592_;
v_isShared_2603_ = v_isSharedCheck_2609_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_snapshotTasks_2600_);
lean_inc(v_infoState_2599_);
lean_inc(v_messages_2598_);
lean_inc(v_traceState_2597_);
lean_inc(v_auxDeclNGen_2596_);
lean_inc(v_ngen_2595_);
lean_inc(v_nextMacroScope_2594_);
lean_inc(v_env_2593_);
lean_dec(v___x_2592_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2609_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2604_ = l_Lean_Kernel_enableDiag(v_env_2593_, v___x_2547_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 5, v___x_2528_);
lean_ctor_set(v___x_2602_, 0, v___x_2604_);
v___x_2606_ = v___x_2602_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2604_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_nextMacroScope_2594_);
lean_ctor_set(v_reuseFailAlloc_2608_, 2, v_ngen_2595_);
lean_ctor_set(v_reuseFailAlloc_2608_, 3, v_auxDeclNGen_2596_);
lean_ctor_set(v_reuseFailAlloc_2608_, 4, v_traceState_2597_);
lean_ctor_set(v_reuseFailAlloc_2608_, 5, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2608_, 6, v_messages_2598_);
lean_ctor_set(v_reuseFailAlloc_2608_, 7, v_infoState_2599_);
lean_ctor_set(v_reuseFailAlloc_2608_, 8, v_snapshotTasks_2600_);
v___x_2606_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
lean_object* v___x_2607_; 
v___x_2607_ = lean_st_ref_set(v___x_2541_, v___x_2606_);
lean_inc(v___x_2541_);
lean_inc(v___x_2533_);
v_fileName_2549_ = v_fileName_2529_;
v_fileMap_2550_ = v___x_2530_;
v_currRecDepth_2551_ = v___x_2531_;
v_ref_2552_ = v___x_2532_;
v_currNamespace_2553_ = v___x_2533_;
v_openDecls_2554_ = v___x_2534_;
v_initHeartbeats_2555_ = v___x_2540_;
v_maxHeartbeats_2556_ = v___x_2535_;
v_quotContext_2557_ = v___x_2533_;
v_currMacroScope_2558_ = v___x_2536_;
v_cancelTk_x3f_2559_ = v___x_2537_;
v_suppressElabErrors_2560_ = v_run_2538_;
v_inheritedTraceOptions_2561_ = v___x_2543_;
v___y_2562_ = v___x_2541_;
goto v___jp_2548_;
}
}
}
else
{
lean_dec_ref(v___x_2528_);
lean_inc(v___x_2541_);
lean_inc(v___x_2533_);
v_fileName_2549_ = v_fileName_2529_;
v_fileMap_2550_ = v___x_2530_;
v_currRecDepth_2551_ = v___x_2531_;
v_ref_2552_ = v___x_2532_;
v_currNamespace_2553_ = v___x_2533_;
v_openDecls_2554_ = v___x_2534_;
v_initHeartbeats_2555_ = v___x_2540_;
v_maxHeartbeats_2556_ = v___x_2535_;
v_quotContext_2557_ = v___x_2533_;
v_currMacroScope_2558_ = v___x_2536_;
v_cancelTk_x3f_2559_ = v___x_2537_;
v_suppressElabErrors_2560_ = v_run_2538_;
v_inheritedTraceOptions_2561_ = v___x_2543_;
v___y_2562_ = v___x_2541_;
goto v___jp_2548_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* v___x_2612_, lean_object* v___x_2613_, lean_object* v_mainModuleName_2614_, lean_object* v_a_2615_, lean_object* v___x_2616_, lean_object* v_fileName_2617_, lean_object* v___x_2618_, lean_object* v___x_2619_, lean_object* v___x_2620_, lean_object* v___x_2621_, lean_object* v___x_2622_, lean_object* v___x_2623_, lean_object* v___x_2624_, lean_object* v___x_2625_, lean_object* v_run_2626_, lean_object* v___y_2627_){
_start:
{
uint8_t v_run_boxed_2628_; lean_object* v_res_2629_; 
v_run_boxed_2628_ = lean_unbox(v_run_2626_);
v_res_2629_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v___x_2612_, v___x_2613_, v_mainModuleName_2614_, v_a_2615_, v___x_2616_, v_fileName_2617_, v___x_2618_, v___x_2619_, v___x_2620_, v___x_2621_, v___x_2622_, v___x_2623_, v___x_2624_, v___x_2625_, v_run_boxed_2628_);
lean_dec(v_a_2615_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_2630_, lean_object* v_a_2631_, lean_object* v_b_2632_){
_start:
{
lean_object* v_str_2633_; lean_object* v_startInclusive_2634_; lean_object* v_endExclusive_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; 
v_str_2633_ = lean_ctor_get(v_val_2630_, 0);
v_startInclusive_2634_ = lean_ctor_get(v_val_2630_, 1);
v_endExclusive_2635_ = lean_ctor_get(v_val_2630_, 2);
v___x_2636_ = lean_nat_sub(v_endExclusive_2635_, v_startInclusive_2634_);
v___x_2637_ = lean_nat_dec_eq(v_a_2631_, v___x_2636_);
lean_dec(v___x_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; uint32_t v___x_2639_; uint32_t v___x_2640_; uint8_t v___x_2641_; 
v___x_2638_ = lean_nat_add(v_startInclusive_2634_, v_a_2631_);
v___x_2639_ = lean_string_utf8_get_fast(v_str_2633_, v___x_2638_);
v___x_2640_ = 10;
v___x_2641_ = lean_uint32_dec_eq(v___x_2639_, v___x_2640_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_dec(v_a_2631_);
v___x_2642_ = lean_box(0);
v___x_2643_ = lean_string_utf8_next_fast(v_str_2633_, v___x_2638_);
lean_dec(v___x_2638_);
v___x_2644_ = lean_nat_sub(v___x_2643_, v_startInclusive_2634_);
v_a_2631_ = v___x_2644_;
v_b_2632_ = v___x_2642_;
goto _start;
}
else
{
lean_object* v___x_2646_; 
lean_dec(v___x_2638_);
v___x_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2646_, 0, v_a_2631_);
return v___x_2646_;
}
}
else
{
lean_dec(v_a_2631_);
lean_inc(v_b_2632_);
return v_b_2632_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_2647_, lean_object* v_a_2648_, lean_object* v_b_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_2647_, v_a_2648_, v_b_2649_);
lean_dec(v_b_2649_);
lean_dec_ref(v_val_2647_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_2651_){
_start:
{
uint32_t v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = 10;
v___x_2654_ = lean_string_push(v_s_2651_, v___x_2653_);
v___x_2655_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_2656_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_s_2659_){
_start:
{
uint32_t v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2661_ = 10;
v___x_2662_ = lean_string_push(v_s_2659_, v___x_2661_);
v___x_2663_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_s_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_s_2664_);
return v_res_2666_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0(void){
_start:
{
lean_object* v___x_2667_; uint8_t v___x_2668_; 
v___x_2667_ = lean_box(0);
v___x_2668_ = lean_internal_has_address_sanitizer(v___x_2667_);
return v___x_2668_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__3(void){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = l_Lean_Options_empty;
v___x_2672_ = l_Lean_Core_getMaxHeartbeats(v___x_2671_);
return v___x_2672_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2673_ = lean_unsigned_to_nat(1u);
v___x_2674_ = l_Lean_firstFrontendMacroScope;
v___x_2675_ = lean_nat_add(v___x_2674_, v___x_2673_);
return v___x_2675_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = lean_unsigned_to_nat(32u);
v___x_2687_ = lean_mk_empty_array_with_capacity(v___x_2686_);
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
return v___x_2688_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10(void){
_start:
{
size_t v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2689_ = ((size_t)5ULL);
v___x_2690_ = lean_unsigned_to_nat(0u);
v___x_2691_ = lean_unsigned_to_nat(32u);
v___x_2692_ = lean_mk_empty_array_with_capacity(v___x_2691_);
v___x_2693_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9);
v___x_2694_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
lean_ctor_set(v___x_2694_, 1, v___x_2692_);
lean_ctor_set(v___x_2694_, 2, v___x_2690_);
lean_ctor_set(v___x_2694_, 3, v___x_2690_);
lean_ctor_set_usize(v___x_2694_, 4, v___x_2689_);
return v___x_2694_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11(void){
_start:
{
lean_object* v___x_2695_; uint64_t v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_2696_ = 0ULL;
v___x_2697_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set_uint64(v___x_2697_, sizeof(void*)*1, v___x_2696_);
return v___x_2697_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12(void){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2698_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__12, &l___private_Lean_Shell_0__Lean_shellMain___closed__12_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12);
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
return v___x_2702_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = l_Lean_NameSet_empty;
v___x_2704_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_2705_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
lean_ctor_set(v___x_2705_, 2, v___x_2703_);
return v___x_2705_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; lean_object* v___x_2709_; 
v___x_2706_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_2707_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_2708_ = 1;
v___x_2709_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2707_);
lean_ctor_set(v___x_2709_, 2, v___x_2706_);
lean_ctor_set_uint8(v___x_2709_, sizeof(void*)*3, v___x_2708_);
return v___x_2709_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__21(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___x_2716_ = lean_string_utf8_byte_size(v___x_2715_);
return v___x_2716_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2717_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__21, &l___private_Lean_Shell_0__Lean_shellMain___closed__21_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__21);
v___x_2718_ = lean_unsigned_to_nat(0u);
v___x_2719_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___x_2720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v___x_2718_);
lean_ctor_set(v___x_2720_, 2, v___x_2717_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* v_args_2724_, lean_object* v_opts_2725_){
_start:
{
lean_object* v___y_2734_; lean_object* v_fns_2749_; lean_object* v_leanOpts_2768_; lean_object* v_forwardedArgs_2769_; uint8_t v_component_2770_; uint8_t v_printPrefix_2771_; uint8_t v_printLibDir_2772_; uint8_t v_useStdin_2773_; uint8_t v_onlyDeps_2774_; uint8_t v_onlySrcDeps_2775_; uint8_t v_depsJson_2776_; uint32_t v_trustLevel_2777_; lean_object* v_rootDir_x3f_2778_; lean_object* v_setupFileName_x3f_2779_; lean_object* v_oleanFileName_x3f_2780_; lean_object* v_ileanFileName_x3f_2781_; lean_object* v_cFileName_x3f_2782_; lean_object* v_bcFileName_x3f_2783_; uint8_t v_jsonOutput_2784_; lean_object* v_errorOnKinds_2785_; uint8_t v_printStats_2786_; uint8_t v_run_2787_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; 
v_leanOpts_2768_ = lean_ctor_get(v_opts_2725_, 0);
lean_inc_ref(v_leanOpts_2768_);
v_forwardedArgs_2769_ = lean_ctor_get(v_opts_2725_, 1);
lean_inc_ref(v_forwardedArgs_2769_);
v_component_2770_ = lean_ctor_get_uint8(v_opts_2725_, sizeof(void*)*10 + 8);
v_printPrefix_2771_ = lean_ctor_get_uint8(v_opts_2725_, sizeof(void*)*10 + 9);
v_printLibDir_2772_ = lean_ctor_get_uint8(v_opts_2725_, sizeof(void*)*10 + 10);
v_useStdin_2773_ = lean_ctor_get_uint8(v_opts_2725_, sizeof(void*)*10 + 11);
v_onlyDeps_2774_ = lean_ctor_get_uint8(v_opts_2725_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2775_ = lean_ctor_get_uint8(v_opts_2725_, sizeof(void*)*10 + 13);
v_depsJson_2776_ = lean_ctor_get_uint8(v_opts_2725_, sizeof(void*)*10 + 14);
v_trustLevel_2777_ = lean_ctor_get_uint32(v_opts_2725_, sizeof(void*)*10);
v_rootDir_x3f_2778_ = lean_ctor_get(v_opts_2725_, 3);
lean_inc(v_rootDir_x3f_2778_);
v_setupFileName_x3f_2779_ = lean_ctor_get(v_opts_2725_, 4);
lean_inc(v_setupFileName_x3f_2779_);
v_oleanFileName_x3f_2780_ = lean_ctor_get(v_opts_2725_, 5);
lean_inc(v_oleanFileName_x3f_2780_);
v_ileanFileName_x3f_2781_ = lean_ctor_get(v_opts_2725_, 6);
lean_inc(v_ileanFileName_x3f_2781_);
v_cFileName_x3f_2782_ = lean_ctor_get(v_opts_2725_, 7);
lean_inc(v_cFileName_x3f_2782_);
v_bcFileName_x3f_2783_ = lean_ctor_get(v_opts_2725_, 8);
lean_inc(v_bcFileName_x3f_2783_);
v_jsonOutput_2784_ = lean_ctor_get_uint8(v_opts_2725_, sizeof(void*)*10 + 15);
v_errorOnKinds_2785_ = lean_ctor_get(v_opts_2725_, 9);
lean_inc_ref(v_errorOnKinds_2785_);
v_printStats_2786_ = lean_ctor_get_uint8(v_opts_2725_, sizeof(void*)*10 + 16);
v_run_2787_ = lean_ctor_get_uint8(v_opts_2725_, sizeof(void*)*10 + 17);
lean_dec_ref(v_opts_2725_);
if (v_printPrefix_2771_ == 0)
{
if (v_printLibDir_2772_ == 0)
{
uint8_t v___x_2814_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v_mainModuleName_2821_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v_contents_2921_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v_str_2951_; lean_object* v_startInclusive_2952_; lean_object* v_endExclusive_2953_; lean_object* v___y_2954_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v_fileName_3053_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3091_; lean_object* v___y_3092_; uint8_t v___y_3123_; lean_object* v_fst_3124_; lean_object* v_snd_3125_; uint8_t v___y_3127_; lean_object* v___x_3157_; lean_object* v_maxMemory_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; 
v___x_2814_ = 1;
v___x_3157_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3158_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_leanOpts_2768_, v___x_3157_);
v___x_3159_ = lean_unsigned_to_nat(0u);
v___x_3160_ = lean_nat_dec_eq(v_maxMemory_3158_, v___x_3159_);
if (v___x_3160_ == 0)
{
size_t v___x_3161_; size_t v___x_3162_; size_t v___x_3163_; size_t v___x_3164_; lean_object* v___x_3165_; 
v___x_3161_ = lean_usize_of_nat(v_maxMemory_3158_);
lean_dec(v_maxMemory_3158_);
v___x_3162_ = ((size_t)1024ULL);
v___x_3163_ = lean_usize_mul(v___x_3161_, v___x_3162_);
v___x_3164_ = lean_usize_mul(v___x_3163_, v___x_3162_);
v___x_3165_ = lean_internal_set_max_memory(v___x_3164_);
goto v___jp_3148_;
}
else
{
lean_dec(v_maxMemory_3158_);
goto v___jp_3148_;
}
v___jp_2815_:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2822_ = lean_unsigned_to_nat(0u);
v___x_2823_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1));
lean_inc(v_mainModuleName_2821_);
lean_inc_ref(v_leanOpts_2768_);
v___x_2824_ = l_Lean_Elab_runFrontend(v___y_2819_, v_leanOpts_2768_, v___y_2820_, v_mainModuleName_2821_, v_trustLevel_2777_, v_oleanFileName_x3f_2780_, v_ileanFileName_x3f_2781_, v_jsonOutput_2784_, v_errorOnKinds_2785_, v___x_2823_, v_printStats_2786_, v___y_2817_);
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_ileanFileName_x3f_2781_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2891_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2827_ = v___x_2824_;
v_isShared_2828_ = v_isSharedCheck_2891_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2824_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2891_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
if (lean_obj_tag(v_a_2825_) == 1)
{
if (v_run_2787_ == 0)
{
lean_del_object(v___x_2827_);
lean_dec(v___y_2818_);
if (lean_obj_tag(v_cFileName_x3f_2782_) == 1)
{
lean_object* v_val_2829_; lean_object* v_val_2830_; uint8_t v___x_2831_; lean_object* v___x_2832_; 
v_val_2829_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_val_2829_);
v_val_2830_ = lean_ctor_get(v_cFileName_x3f_2782_, 0);
lean_inc(v_val_2830_);
lean_dec_ref(v_cFileName_x3f_2782_);
v___x_2831_ = 1;
v___x_2832_ = lean_io_prim_handle_mk(v_val_2830_, v___x_2831_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___f_2852_; lean_object* v___x_2853_; 
lean_dec(v_val_2830_);
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref(v___x_2832_);
v___x_2834_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__2));
v___x_2835_ = l_Lean_instInhabitedFileMap_default;
v___x_2836_ = l_Lean_Options_empty;
v___x_2837_ = lean_box(0);
v___x_2838_ = lean_box(0);
v___x_2839_ = lean_box(0);
v___x_2840_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__3, &l___private_Lean_Shell_0__Lean_shellMain___closed__3_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__3);
v___x_2841_ = l_Lean_firstFrontendMacroScope;
v___x_2842_ = lean_box(0);
v___x_2843_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__4, &l___private_Lean_Shell_0__Lean_shellMain___closed__4_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4);
v___x_2844_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__7));
v___x_2845_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__8));
v___x_2846_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__11, &l___private_Lean_Shell_0__Lean_shellMain___closed__11_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11);
v___x_2847_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__14, &l___private_Lean_Shell_0__Lean_shellMain___closed__14_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14);
v___x_2848_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__15, &l___private_Lean_Shell_0__Lean_shellMain___closed__15_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15);
v___x_2849_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__16, &l___private_Lean_Shell_0__Lean_shellMain___closed__16_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16);
lean_inc(v_val_2829_);
v___x_2850_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2850_, 0, v_val_2829_);
lean_ctor_set(v___x_2850_, 1, v___x_2843_);
lean_ctor_set(v___x_2850_, 2, v___x_2844_);
lean_ctor_set(v___x_2850_, 3, v___x_2845_);
lean_ctor_set(v___x_2850_, 4, v___x_2846_);
lean_ctor_set(v___x_2850_, 5, v___x_2847_);
lean_ctor_set(v___x_2850_, 6, v___x_2848_);
lean_ctor_set(v___x_2850_, 7, v___x_2849_);
lean_ctor_set(v___x_2850_, 8, v___x_2823_);
v___x_2851_ = lean_box(v_run_2787_);
lean_inc(v_mainModuleName_2821_);
v___f_2852_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 16, 15);
lean_closure_set(v___f_2852_, 0, v___x_2850_);
lean_closure_set(v___f_2852_, 1, v___x_2836_);
lean_closure_set(v___f_2852_, 2, v_mainModuleName_2821_);
lean_closure_set(v___f_2852_, 3, v_a_2833_);
lean_closure_set(v___f_2852_, 4, v___x_2847_);
lean_closure_set(v___f_2852_, 5, v___y_2816_);
lean_closure_set(v___f_2852_, 6, v___x_2835_);
lean_closure_set(v___f_2852_, 7, v___x_2822_);
lean_closure_set(v___f_2852_, 8, v___x_2837_);
lean_closure_set(v___f_2852_, 9, v___x_2838_);
lean_closure_set(v___f_2852_, 10, v___x_2839_);
lean_closure_set(v___f_2852_, 11, v___x_2840_);
lean_closure_set(v___f_2852_, 12, v___x_2841_);
lean_closure_set(v___f_2852_, 13, v___x_2842_);
lean_closure_set(v___f_2852_, 14, v___x_2851_);
v___x_2853_ = l_Lean_profileitIOUnsafe___redArg(v___x_2834_, v_leanOpts_2768_, v___f_2852_, v___x_2838_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_dec_ref(v___x_2853_);
v___y_2789_ = v_a_2825_;
v___y_2790_ = v_mainModuleName_2821_;
v___y_2791_ = v_val_2829_;
goto v___jp_2788_;
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec(v_val_2829_);
lean_dec_ref(v_a_2825_);
lean_dec(v_mainModuleName_2821_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec_ref(v_leanOpts_2768_);
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
lean_dec_ref(v___x_2832_);
lean_dec(v_val_2829_);
lean_dec_ref(v_a_2825_);
lean_dec(v_mainModuleName_2821_);
lean_dec_ref(v___y_2816_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec_ref(v_leanOpts_2768_);
v___x_2862_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__17));
v___x_2863_ = lean_string_append(v___x_2862_, v_val_2830_);
lean_dec(v_val_2830_);
v___x_2864_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_2865_ = lean_string_append(v___x_2863_, v___x_2864_);
v___x_2866_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_2865_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2874_; 
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2874_ == 0)
{
lean_object* v_unused_2875_; 
v_unused_2875_ = lean_ctor_get(v___x_2866_, 0);
lean_dec(v_unused_2875_);
v___x_2868_ = v___x_2866_;
v_isShared_2869_ = v_isSharedCheck_2874_;
goto v_resetjp_2867_;
}
else
{
lean_dec(v___x_2866_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2874_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2872_; 
v___x_2870_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2870_);
v___x_2872_ = v___x_2868_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
v_a_2876_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2866_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2866_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
else
{
lean_object* v_val_2884_; 
lean_dec_ref(v___y_2816_);
lean_dec(v_cFileName_x3f_2782_);
v_val_2884_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_val_2884_);
v___y_2789_ = v_a_2825_;
v___y_2790_ = v_mainModuleName_2821_;
v___y_2791_ = v_val_2884_;
goto v___jp_2788_;
}
}
else
{
lean_object* v_val_2885_; uint32_t v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
lean_dec(v_mainModuleName_2821_);
lean_dec_ref(v___y_2816_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
v_val_2885_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_val_2885_);
lean_dec_ref(v_a_2825_);
v___x_2886_ = lean_eval_main(v_val_2885_, v_leanOpts_2768_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v_leanOpts_2768_);
lean_dec(v_val_2885_);
v___x_2887_ = lean_box_uint32(v___x_2886_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v___x_2887_);
v___x_2889_ = v___x_2827_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
else
{
lean_del_object(v___x_2827_);
lean_dec(v_mainModuleName_2821_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2816_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec_ref(v_leanOpts_2768_);
v___y_2734_ = v_a_2825_;
goto v___jp_2733_;
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v_mainModuleName_2821_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2816_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec_ref(v_leanOpts_2768_);
v_a_2892_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2824_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2824_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
v___jp_2900_:
{
if (lean_obj_tag(v___y_2906_) == 0)
{
lean_object* v_a_2907_; 
v_a_2907_ = lean_ctor_get(v___y_2906_, 0);
lean_inc(v_a_2907_);
lean_dec_ref(v___y_2906_);
v___y_2816_ = v___y_2901_;
v___y_2817_ = v___y_2902_;
v___y_2818_ = v___y_2904_;
v___y_2819_ = v___y_2903_;
v___y_2820_ = v___y_2905_;
v_mainModuleName_2821_ = v_a_2907_;
goto v___jp_2815_;
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec(v_ileanFileName_x3f_2781_);
lean_dec(v_oleanFileName_x3f_2780_);
lean_dec_ref(v_leanOpts_2768_);
v_a_2908_ = lean_ctor_get(v___y_2906_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___y_2906_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___y_2906_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___y_2906_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
v___jp_2916_:
{
if (lean_obj_tag(v_setupFileName_x3f_2779_) == 0)
{
lean_object* v___x_2922_; 
v___x_2922_ = lean_box(0);
if (lean_obj_tag(v___y_2920_) == 1)
{
lean_object* v_val_2923_; lean_object* v___x_2924_; 
v_val_2923_ = lean_ctor_get(v___y_2920_, 0);
lean_inc(v_val_2923_);
lean_dec_ref(v___y_2920_);
v___x_2924_ = l_Lean_moduleNameOfFileName(v_val_2923_, v_rootDir_x3f_2778_);
if (lean_obj_tag(v___x_2924_) == 0)
{
v___y_2901_ = v___y_2917_;
v___y_2902_ = v___x_2922_;
v___y_2903_ = v_contents_2921_;
v___y_2904_ = v___y_2918_;
v___y_2905_ = v___y_2919_;
v___y_2906_ = v___x_2924_;
goto v___jp_2900_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_2780_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_2782_) == 0)
{
lean_object* v___x_2925_; 
lean_dec_ref(v___x_2924_);
v___x_2925_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__19));
v___y_2816_ = v___y_2917_;
v___y_2817_ = v___x_2922_;
v___y_2818_ = v___y_2918_;
v___y_2819_ = v_contents_2921_;
v___y_2820_ = v___y_2919_;
v_mainModuleName_2821_ = v___x_2925_;
goto v___jp_2815_;
}
else
{
v___y_2901_ = v___y_2917_;
v___y_2902_ = v___x_2922_;
v___y_2903_ = v_contents_2921_;
v___y_2904_ = v___y_2918_;
v___y_2905_ = v___y_2919_;
v___y_2906_ = v___x_2924_;
goto v___jp_2900_;
}
}
else
{
v___y_2901_ = v___y_2917_;
v___y_2902_ = v___x_2922_;
v___y_2903_ = v_contents_2921_;
v___y_2904_ = v___y_2918_;
v___y_2905_ = v___y_2919_;
v___y_2906_ = v___x_2924_;
goto v___jp_2900_;
}
}
}
else
{
lean_object* v___x_2926_; 
lean_dec(v___y_2920_);
lean_dec(v_rootDir_x3f_2778_);
v___x_2926_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__19));
v___y_2816_ = v___y_2917_;
v___y_2817_ = v___x_2922_;
v___y_2818_ = v___y_2918_;
v___y_2819_ = v_contents_2921_;
v___y_2820_ = v___y_2919_;
v_mainModuleName_2821_ = v___x_2926_;
goto v___jp_2815_;
}
}
else
{
lean_object* v_val_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v___y_2920_);
lean_dec(v_rootDir_x3f_2778_);
v_val_2927_ = lean_ctor_get(v_setupFileName_x3f_2779_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_setupFileName_x3f_2779_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2929_ = v_setupFileName_x3f_2779_;
v_isShared_2930_ = v_isSharedCheck_2945_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_val_2927_);
lean_dec(v_setupFileName_x3f_2779_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2945_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_ModuleSetup_load(v_val_2927_);
lean_dec(v_val_2927_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v_name_2933_; lean_object* v___x_2935_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref(v___x_2931_);
v_name_2933_ = lean_ctor_get(v_a_2932_, 0);
lean_inc(v_name_2933_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v_a_2932_);
v___x_2935_ = v___x_2929_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2932_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
v___y_2816_ = v___y_2917_;
v___y_2817_ = v___x_2935_;
v___y_2818_ = v___y_2918_;
v___y_2819_ = v_contents_2921_;
v___y_2820_ = v___y_2919_;
v_mainModuleName_2821_ = v_name_2933_;
goto v___jp_2815_;
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_del_object(v___x_2929_);
lean_dec_ref(v_contents_2921_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec(v_ileanFileName_x3f_2781_);
lean_dec(v_oleanFileName_x3f_2780_);
lean_dec_ref(v_leanOpts_2768_);
v_a_2937_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2931_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2931_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
}
v___jp_2946_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; uint8_t v___x_2959_; 
v___x_2955_ = lean_nat_add(v_startInclusive_2952_, v___y_2954_);
lean_dec(v___y_2954_);
lean_inc(v___x_2955_);
lean_inc_ref(v_str_2951_);
v___x_2956_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2956_, 0, v_str_2951_);
lean_ctor_set(v___x_2956_, 1, v_startInclusive_2952_);
lean_ctor_set(v___x_2956_, 2, v___x_2955_);
v___x_2957_ = l_String_Slice_trimAscii(v___x_2956_);
v___x_2958_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__22, &l___private_Lean_Shell_0__Lean_shellMain___closed__22_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22);
v___x_2959_ = l_String_Slice_beq(v___x_2957_, v___x_2958_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec(v___x_2955_);
lean_dec(v_endExclusive_2953_);
lean_dec_ref(v_str_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec(v_ileanFileName_x3f_2781_);
lean_dec(v_oleanFileName_x3f_2780_);
lean_dec(v_setupFileName_x3f_2779_);
lean_dec(v_rootDir_x3f_2778_);
lean_dec_ref(v_leanOpts_2768_);
v___x_2960_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__23));
v___x_2961_ = l_String_Slice_toString(v___x_2957_);
lean_dec_ref(v___x_2957_);
v___x_2962_ = lean_string_append(v___x_2960_, v___x_2961_);
lean_dec_ref(v___x_2961_);
v___x_2963_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_2964_ = lean_string_append(v___x_2962_, v___x_2963_);
v___x_2965_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_2964_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2973_; 
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2973_ == 0)
{
lean_object* v_unused_2974_; 
v_unused_2974_ = lean_ctor_get(v___x_2965_, 0);
lean_dec(v_unused_2974_);
v___x_2967_ = v___x_2965_;
v_isShared_2968_ = v_isSharedCheck_2973_;
goto v_resetjp_2966_;
}
else
{
lean_dec(v___x_2965_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2973_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2971_; 
v___x_2969_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 0, v___x_2969_);
v___x_2971_ = v___x_2967_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
v_a_2975_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2965_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2965_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_object* v___x_2983_; 
lean_dec_ref(v___x_2957_);
v___x_2983_ = lean_string_utf8_extract(v_str_2951_, v___x_2955_, v_endExclusive_2953_);
lean_dec(v_endExclusive_2953_);
lean_dec(v___x_2955_);
lean_dec_ref(v_str_2951_);
v___y_2917_ = v___y_2947_;
v___y_2918_ = v___y_2948_;
v___y_2919_ = v___y_2949_;
v___y_2920_ = v___y_2950_;
v_contents_2921_ = v___x_2983_;
goto v___jp_2916_;
}
}
v___jp_2984_:
{
if (lean_obj_tag(v___y_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v___x_2990_; 
v_a_2989_ = lean_ctor_get(v___y_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref(v___y_2988_);
v___x_2990_ = lean_decode_lossy_utf8(v_a_2989_);
lean_dec(v_a_2989_);
if (v_onlyDeps_2774_ == 0)
{
if (v_onlySrcDeps_2775_ == 0)
{
lean_object* v___x_2991_; 
lean_inc_ref(v___x_2990_);
v___x_2991_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_2990_);
if (lean_obj_tag(v___x_2991_) == 1)
{
lean_object* v_val_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
lean_dec_ref(v___x_2990_);
v_val_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_val_2992_);
lean_dec_ref(v___x_2991_);
v___x_2993_ = lean_unsigned_to_nat(0u);
v___x_2994_ = lean_box(0);
v___x_2995_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_2992_, v___x_2993_, v___x_2994_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_str_2996_; lean_object* v_startInclusive_2997_; lean_object* v_endExclusive_2998_; lean_object* v___x_2999_; 
v_str_2996_ = lean_ctor_get(v_val_2992_, 0);
lean_inc_ref(v_str_2996_);
v_startInclusive_2997_ = lean_ctor_get(v_val_2992_, 1);
lean_inc(v_startInclusive_2997_);
v_endExclusive_2998_ = lean_ctor_get(v_val_2992_, 2);
lean_inc(v_endExclusive_2998_);
lean_dec(v_val_2992_);
v___x_2999_ = lean_nat_sub(v_endExclusive_2998_, v_startInclusive_2997_);
lean_inc_ref(v___y_2986_);
v___y_2947_ = v___y_2986_;
v___y_2948_ = v___y_2985_;
v___y_2949_ = v___y_2986_;
v___y_2950_ = v___y_2987_;
v_str_2951_ = v_str_2996_;
v_startInclusive_2952_ = v_startInclusive_2997_;
v_endExclusive_2953_ = v_endExclusive_2998_;
v___y_2954_ = v___x_2999_;
goto v___jp_2946_;
}
else
{
lean_object* v_val_3000_; lean_object* v_str_3001_; lean_object* v_startInclusive_3002_; lean_object* v_endExclusive_3003_; 
v_val_3000_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_val_3000_);
lean_dec_ref(v___x_2995_);
v_str_3001_ = lean_ctor_get(v_val_2992_, 0);
lean_inc_ref(v_str_3001_);
v_startInclusive_3002_ = lean_ctor_get(v_val_2992_, 1);
lean_inc(v_startInclusive_3002_);
v_endExclusive_3003_ = lean_ctor_get(v_val_2992_, 2);
lean_inc(v_endExclusive_3003_);
lean_dec(v_val_2992_);
lean_inc_ref(v___y_2986_);
v___y_2947_ = v___y_2986_;
v___y_2948_ = v___y_2985_;
v___y_2949_ = v___y_2986_;
v___y_2950_ = v___y_2987_;
v_str_2951_ = v_str_3001_;
v_startInclusive_2952_ = v_startInclusive_3002_;
v_endExclusive_2953_ = v_endExclusive_3003_;
v___y_2954_ = v_val_3000_;
goto v___jp_2946_;
}
}
else
{
lean_dec(v___x_2991_);
lean_inc_ref(v___y_2986_);
v___y_2917_ = v___y_2986_;
v___y_2918_ = v___y_2985_;
v___y_2919_ = v___y_2986_;
v___y_2920_ = v___y_2987_;
v_contents_2921_ = v___x_2990_;
goto v___jp_2916_;
}
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec(v_ileanFileName_x3f_2781_);
lean_dec(v_oleanFileName_x3f_2780_);
lean_dec(v_setupFileName_x3f_2779_);
lean_dec(v_rootDir_x3f_2778_);
lean_dec_ref(v_leanOpts_2768_);
v___x_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___y_2986_);
v___x_3005_ = l_Lean_Elab_printImportSrcs(v___x_2990_, v___x_3004_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3013_; 
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3013_ == 0)
{
lean_object* v_unused_3014_; 
v_unused_3014_ = lean_ctor_get(v___x_3005_, 0);
lean_dec(v_unused_3014_);
v___x_3007_ = v___x_3005_;
v_isShared_3008_ = v_isSharedCheck_3013_;
goto v_resetjp_3006_;
}
else
{
lean_dec(v___x_3005_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3013_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v___x_3011_; 
v___x_3009_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v___x_3009_);
v___x_3011_ = v___x_3007_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
v_a_3015_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3005_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3005_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
lean_dec(v___y_2987_);
lean_dec(v___y_2985_);
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec(v_ileanFileName_x3f_2781_);
lean_dec(v_oleanFileName_x3f_2780_);
lean_dec(v_setupFileName_x3f_2779_);
lean_dec(v_rootDir_x3f_2778_);
lean_dec_ref(v_leanOpts_2768_);
v___x_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3023_, 0, v___y_2986_);
v___x_3024_ = l_Lean_Elab_printImports(v___x_2990_, v___x_3023_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3032_; 
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3032_ == 0)
{
lean_object* v_unused_3033_; 
v_unused_3033_ = lean_ctor_get(v___x_3024_, 0);
lean_dec(v_unused_3033_);
v___x_3026_ = v___x_3024_;
v_isShared_3027_ = v_isSharedCheck_3032_;
goto v_resetjp_3025_;
}
else
{
lean_dec(v___x_3024_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3032_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3028_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3028_);
v___x_3030_ = v___x_3026_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
v_a_3034_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3024_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3024_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec(v_ileanFileName_x3f_2781_);
lean_dec(v_oleanFileName_x3f_2780_);
lean_dec(v_setupFileName_x3f_2779_);
lean_dec(v_rootDir_x3f_2778_);
lean_dec_ref(v_leanOpts_2768_);
v_a_3042_ = lean_ctor_get(v___y_2988_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___y_2988_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___y_2988_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___y_2988_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
v___jp_3050_:
{
if (v_useStdin_2773_ == 0)
{
lean_object* v___x_3054_; 
v___x_3054_ = l_IO_FS_readBinFile(v_fileName_3053_);
v___y_2985_ = v___y_3051_;
v___y_2986_ = v_fileName_3053_;
v___y_2987_ = v___y_3052_;
v___y_2988_ = v___x_3054_;
goto v___jp_2984_;
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_get_stdin();
v___x_3056_ = l_IO_FS_Stream_readBinToEnd(v___x_3055_);
v___y_2985_ = v___y_3051_;
v___y_2986_ = v_fileName_3053_;
v___y_2987_ = v___y_3052_;
v___y_2988_ = v___x_3056_;
goto v___jp_2984_;
}
}
v___jp_3057_:
{
if (lean_obj_tag(v___y_3059_) == 1)
{
lean_object* v_val_3060_; 
v_val_3060_ = lean_ctor_get(v___y_3059_, 0);
lean_inc(v_val_3060_);
v___y_3051_ = v___y_3058_;
v___y_3052_ = v___y_3059_;
v_fileName_3053_ = v_val_3060_;
goto v___jp_3050_;
}
else
{
if (v_useStdin_2773_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
lean_dec(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec(v_ileanFileName_x3f_2781_);
lean_dec(v_oleanFileName_x3f_2780_);
lean_dec(v_setupFileName_x3f_2779_);
lean_dec(v_rootDir_x3f_2778_);
lean_dec_ref(v_leanOpts_2768_);
v___x_3061_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__24));
v___x_3062_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3061_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v___x_3063_; 
lean_dec_ref(v___x_3062_);
v___x_3063_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_2814_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3071_; 
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3071_ == 0)
{
lean_object* v_unused_3072_; 
v_unused_3072_ = lean_ctor_get(v___x_3063_, 0);
lean_dec(v_unused_3072_);
v___x_3065_ = v___x_3063_;
v_isShared_3066_ = v_isSharedCheck_3071_;
goto v_resetjp_3064_;
}
else
{
lean_dec(v___x_3063_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3071_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3067_; lean_object* v___x_3069_; 
v___x_3067_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v___x_3067_);
v___x_3069_ = v___x_3065_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3067_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
v_a_3073_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3063_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3063_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
v_a_3081_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3062_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3062_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
else
{
lean_object* v___x_3089_; 
v___x_3089_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__25));
v___y_3051_ = v___y_3058_;
v___y_3052_ = v___y_3059_;
v_fileName_3053_ = v___x_3089_;
goto v___jp_3050_;
}
}
}
v___jp_3090_:
{
uint8_t v___x_3093_; 
v___x_3093_ = l_List_isEmpty___redArg(v___y_3091_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_dec(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec(v_ileanFileName_x3f_2781_);
lean_dec(v_oleanFileName_x3f_2780_);
lean_dec(v_setupFileName_x3f_2779_);
lean_dec(v_rootDir_x3f_2778_);
lean_dec_ref(v_leanOpts_2768_);
v___x_3094_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__24));
v___x_3095_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3094_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v___x_3096_; 
lean_dec_ref(v___x_3095_);
v___x_3096_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_2814_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3104_; 
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3104_ == 0)
{
lean_object* v_unused_3105_; 
v_unused_3105_ = lean_ctor_get(v___x_3096_, 0);
lean_dec(v_unused_3105_);
v___x_3098_ = v___x_3096_;
v_isShared_3099_ = v_isSharedCheck_3104_;
goto v_resetjp_3097_;
}
else
{
lean_dec(v___x_3096_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3104_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3100_; lean_object* v___x_3102_; 
v___x_3100_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v___x_3100_);
v___x_3102_ = v___x_3098_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3100_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
v_a_3106_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3096_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3096_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
v_a_3114_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3095_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3095_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
else
{
v___y_3058_ = v___y_3091_;
v___y_3059_ = v___y_3092_;
goto v___jp_3057_;
}
}
v___jp_3122_:
{
if (v_run_2787_ == 0)
{
v___y_3091_ = v_snd_3125_;
v___y_3092_ = v_fst_3124_;
goto v___jp_3090_;
}
else
{
if (v___y_3123_ == 0)
{
v___y_3058_ = v_snd_3125_;
v___y_3059_ = v_fst_3124_;
goto v___jp_3057_;
}
else
{
v___y_3091_ = v_snd_3125_;
v___y_3092_ = v_fst_3124_;
goto v___jp_3090_;
}
}
}
v___jp_3126_:
{
if (lean_obj_tag(v_args_2724_) == 0)
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_box(0);
v___y_3123_ = v___y_3127_;
v_fst_3124_ = v___x_3128_;
v_snd_3125_ = v_args_2724_;
goto v___jp_3122_;
}
else
{
lean_object* v_head_3129_; lean_object* v_tail_3130_; lean_object* v___x_3131_; 
v_head_3129_ = lean_ctor_get(v_args_2724_, 0);
lean_inc(v_head_3129_);
v_tail_3130_ = lean_ctor_get(v_args_2724_, 1);
lean_inc(v_tail_3130_);
lean_dec_ref(v_args_2724_);
v___x_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3131_, 0, v_head_3129_);
v___y_3123_ = v___y_3127_;
v_fst_3124_ = v___x_3131_;
v_snd_3125_ = v_tail_3130_;
goto v___jp_3122_;
}
}
v___jp_3132_:
{
switch(v_component_2770_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_2769_);
if (v_onlyDeps_2774_ == 0)
{
v___y_3127_ = v_onlyDeps_2774_;
goto v___jp_3126_;
}
else
{
if (v_depsJson_2776_ == 0)
{
v___y_3127_ = v_depsJson_2776_;
goto v___jp_3126_;
}
else
{
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec(v_ileanFileName_x3f_2781_);
lean_dec(v_oleanFileName_x3f_2780_);
lean_dec(v_setupFileName_x3f_2779_);
lean_dec(v_rootDir_x3f_2778_);
lean_dec_ref(v_leanOpts_2768_);
if (v_useStdin_2773_ == 0)
{
lean_object* v___x_3133_; 
v___x_3133_ = lean_array_mk(v_args_2724_);
v_fns_2749_ = v___x_3133_;
goto v___jp_2748_;
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_dec(v_args_2724_);
v___x_3134_ = lean_get_stdin();
v___x_3135_ = l_IO_FS_Stream_lines(v___x_3134_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref(v___x_3135_);
v_fns_2749_ = v_a_3136_;
goto v___jp_2748_;
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
v_a_3137_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3135_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3135_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec(v_ileanFileName_x3f_2781_);
lean_dec(v_oleanFileName_x3f_2780_);
lean_dec(v_setupFileName_x3f_2779_);
lean_dec(v_rootDir_x3f_2778_);
lean_dec_ref(v_leanOpts_2768_);
lean_dec(v_args_2724_);
v___x_3145_ = lean_array_to_list(v_forwardedArgs_2769_);
v___x_3146_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3145_);
return v___x_3146_;
}
default: 
{
lean_object* v___x_3147_; 
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec(v_ileanFileName_x3f_2781_);
lean_dec(v_oleanFileName_x3f_2780_);
lean_dec(v_setupFileName_x3f_2779_);
lean_dec(v_rootDir_x3f_2778_);
lean_dec_ref(v_forwardedArgs_2769_);
lean_dec(v_args_2724_);
v___x_3147_ = l_Lean_Server_FileWorker_workerMain(v_leanOpts_2768_);
return v___x_3147_;
}
}
}
v___jp_3148_:
{
lean_object* v___x_3149_; lean_object* v_timeout_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v___x_3149_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3150_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_leanOpts_2768_, v___x_3149_);
v___x_3151_ = lean_unsigned_to_nat(0u);
v___x_3152_ = lean_nat_dec_eq(v_timeout_3150_, v___x_3151_);
if (v___x_3152_ == 0)
{
size_t v___x_3153_; size_t v___x_3154_; size_t v___x_3155_; lean_object* v___x_3156_; 
v___x_3153_ = lean_usize_of_nat(v_timeout_3150_);
lean_dec(v_timeout_3150_);
v___x_3154_ = ((size_t)1000ULL);
v___x_3155_ = lean_usize_mul(v___x_3153_, v___x_3154_);
v___x_3156_ = lean_internal_set_max_heartbeat(v___x_3155_);
goto v___jp_3132_;
}
else
{
lean_dec(v_timeout_3150_);
goto v___jp_3132_;
}
}
}
else
{
lean_object* v___x_3166_; 
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec(v_ileanFileName_x3f_2781_);
lean_dec(v_oleanFileName_x3f_2780_);
lean_dec(v_setupFileName_x3f_2779_);
lean_dec(v_rootDir_x3f_2778_);
lean_dec_ref(v_forwardedArgs_2769_);
lean_dec_ref(v_leanOpts_2768_);
lean_dec(v_args_2724_);
v___x_3166_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3168_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
lean_inc(v_a_3167_);
lean_dec_ref(v___x_3166_);
v___x_3168_ = l_Lean_getLibDir(v_a_3167_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3170_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref(v___x_3168_);
v___x_3170_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3169_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3178_; 
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; 
v_unused_3179_ = lean_ctor_get(v___x_3170_, 0);
lean_dec(v_unused_3179_);
v___x_3172_ = v___x_3170_;
v_isShared_3173_ = v_isSharedCheck_3178_;
goto v_resetjp_3171_;
}
else
{
lean_dec(v___x_3170_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3178_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3176_; 
v___x_3174_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3174_);
v___x_3176_ = v___x_3172_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3174_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
v_a_3180_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3170_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3170_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
v_a_3188_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3168_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3168_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
v_a_3196_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3166_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3166_);
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
lean_object* v___x_3204_; 
lean_dec_ref(v_errorOnKinds_2785_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec(v_cFileName_x3f_2782_);
lean_dec(v_ileanFileName_x3f_2781_);
lean_dec(v_oleanFileName_x3f_2780_);
lean_dec(v_setupFileName_x3f_2779_);
lean_dec(v_rootDir_x3f_2778_);
lean_dec_ref(v_forwardedArgs_2769_);
lean_dec_ref(v_leanOpts_2768_);
lean_dec(v_args_2724_);
v___x_3204_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v___x_3206_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref(v___x_3204_);
v___x_3206_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3205_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3214_; 
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; 
v_unused_3215_ = lean_ctor_get(v___x_3206_, 0);
lean_dec(v_unused_3215_);
v___x_3208_ = v___x_3206_;
v_isShared_3209_ = v_isSharedCheck_3214_;
goto v_resetjp_3207_;
}
else
{
lean_dec(v___x_3206_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3214_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3210_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3210_);
v___x_3212_ = v___x_3208_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
v_a_3216_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3206_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3206_);
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
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
v_a_3224_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3204_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3204_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
v___jp_2727_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
return v___x_2729_;
}
v___jp_2730_:
{
uint8_t v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = 0;
v___x_2732_ = lean_io_exit(v___x_2731_);
return v___x_2732_;
}
v___jp_2733_:
{
lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2735_ = lean_display_cumulative_profiling_times();
v___x_2736_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__0, &l___private_Lean_Shell_0__Lean_shellMain___closed__0_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0);
if (v___x_2736_ == 0)
{
if (lean_obj_tag(v___y_2734_) == 0)
{
if (v___x_2736_ == 0)
{
uint8_t v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = 1;
v___x_2738_ = lean_io_exit(v___x_2737_);
return v___x_2738_;
}
else
{
goto v___jp_2730_;
}
}
else
{
lean_dec_ref(v___y_2734_);
goto v___jp_2730_;
}
}
else
{
if (lean_obj_tag(v___y_2734_) == 0)
{
goto v___jp_2727_;
}
else
{
lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2746_; 
v_isSharedCheck_2746_ = !lean_is_exclusive(v___y_2734_);
if (v_isSharedCheck_2746_ == 0)
{
lean_object* v_unused_2747_; 
v_unused_2747_ = lean_ctor_get(v___y_2734_, 0);
lean_dec(v_unused_2747_);
v___x_2740_ = v___y_2734_;
v_isShared_2741_ = v_isSharedCheck_2746_;
goto v_resetjp_2739_;
}
else
{
lean_dec(v___y_2734_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2746_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
if (v___x_2736_ == 0)
{
lean_del_object(v___x_2740_);
goto v___jp_2727_;
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2742_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2741_ == 0)
{
lean_ctor_set_tag(v___x_2740_, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2742_);
v___x_2744_ = v___x_2740_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
}
v___jp_2748_:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_printImportsJson(v_fns_2749_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2758_; 
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2758_ == 0)
{
lean_object* v_unused_2759_; 
v_unused_2759_ = lean_ctor_get(v___x_2750_, 0);
lean_dec(v_unused_2759_);
v___x_2752_ = v___x_2750_;
v_isShared_2753_ = v_isSharedCheck_2758_;
goto v_resetjp_2751_;
}
else
{
lean_dec(v___x_2750_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2758_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2754_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2754_);
v___x_2756_ = v___x_2752_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2754_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
v_a_2760_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2750_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2750_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
v___jp_2788_:
{
if (lean_obj_tag(v_bcFileName_x3f_2783_) == 1)
{
lean_object* v_val_2792_; lean_object* v___x_2793_; 
v_val_2792_ = lean_ctor_get(v_bcFileName_x3f_2783_, 0);
lean_inc(v_val_2792_);
lean_dec_ref(v_bcFileName_x3f_2783_);
v___x_2793_ = lean_init_llvm();
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
lean_dec_ref(v___x_2793_);
v___x_2794_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__1));
v___x_2795_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(v___x_2795_, 0, v___y_2791_);
lean_closure_set(v___x_2795_, 1, v___y_2790_);
lean_closure_set(v___x_2795_, 2, v_val_2792_);
v___x_2796_ = lean_box(0);
v___x_2797_ = l_Lean_profileitIOUnsafe___redArg(v___x_2794_, v_leanOpts_2768_, v___x_2795_, v___x_2796_);
lean_dec_ref(v_leanOpts_2768_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_dec_ref(v___x_2797_);
v___y_2734_ = v___y_2789_;
goto v___jp_2733_;
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_dec(v___y_2789_);
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2797_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2797_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec(v_val_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v_leanOpts_2768_);
v_a_2806_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2793_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2793_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
else
{
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec(v_bcFileName_x3f_2783_);
lean_dec_ref(v_leanOpts_2768_);
v___y_2734_ = v___y_2789_;
goto v___jp_2733_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3232_, lean_object* v_opts_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = lean_shell_main(v_args_3232_, v_opts_3233_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3236_, lean_object* v_inst_3237_, lean_object* v_R_3238_, lean_object* v_a_3239_, lean_object* v_b_3240_, lean_object* v_c_3241_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3236_, v_a_3239_, v_b_3240_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3243_, lean_object* v_inst_3244_, lean_object* v_R_3245_, lean_object* v_a_3246_, lean_object* v_b_3247_, lean_object* v_c_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3243_, v_inst_3244_, v_R_3245_, v_a_3246_, v_b_3247_, v_c_3248_);
lean_dec(v_b_3247_);
lean_dec_ref(v_val_3243_);
return v_res_3249_;
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
