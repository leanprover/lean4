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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
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
static const lean_string_object l___private_Lean_Shell_0__Lean_displayHelp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "      --plugin=file[:fn] load and initialize Lean shared library for registering linters etc."};
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__4(lean_object* v_o_818_, lean_object* v_k_819_, lean_object* v_v_820_){
_start:
{
lean_object* v_map_821_; uint8_t v_hasTrace_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_836_; 
v_map_821_ = lean_ctor_get(v_o_818_, 0);
v_hasTrace_822_ = lean_ctor_get_uint8(v_o_818_, sizeof(void*)*1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_o_818_);
if (v_isSharedCheck_836_ == 0)
{
v___x_824_ = v_o_818_;
v_isShared_825_ = v_isSharedCheck_836_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_map_821_);
lean_dec(v_o_818_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_836_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_826_, 0, v_v_820_);
lean_inc(v_k_819_);
v___x_827_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_819_, v___x_826_, v_map_821_);
if (v_hasTrace_822_ == 0)
{
lean_object* v___x_828_; uint8_t v___x_829_; lean_object* v___x_831_; 
v___x_828_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_829_ = l_Lean_Name_isPrefixOf(v___x_828_, v_k_819_);
lean_dec(v_k_819_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_827_);
v___x_831_ = v___x_824_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_827_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*1, v___x_829_);
return v___x_831_;
}
}
else
{
lean_object* v___x_834_; 
lean_dec(v_k_819_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_827_);
v___x_834_ = v___x_824_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_827_);
lean_ctor_set_uint8(v_reuseFailAlloc_835_, sizeof(void*)*1, v_hasTrace_822_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object* v_opts_837_, lean_object* v_opt_838_, lean_object* v_val_839_){
_start:
{
lean_object* v_name_840_; lean_object* v___x_841_; 
v_name_840_ = lean_ctor_get(v_opt_838_, 0);
lean_inc(v_name_840_);
lean_dec_ref(v_opt_838_);
v___x_841_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__4(v_opts_837_, v_name_840_, v_val_839_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4_spec__6(lean_object* v_s_842_){
_start:
{
lean_object* v___x_844_; lean_object* v_putStr_845_; lean_object* v___x_846_; 
v___x_844_ = lean_get_stdout();
v_putStr_845_ = lean_ctor_get(v___x_844_, 4);
lean_inc_ref(v_putStr_845_);
lean_dec_ref(v___x_844_);
v___x_846_ = lean_apply_2(v_putStr_845_, v_s_842_, lean_box(0));
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4_spec__6___boxed(lean_object* v_s_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4_spec__6(v_s_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4(lean_object* v_s_850_){
_start:
{
uint32_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = 10;
v___x_853_ = lean_string_push(v_s_850_, v___x_852_);
v___x_854_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4_spec__6(v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4___boxed(lean_object* v_s_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4(v_s_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__2(lean_object* v_o_858_, lean_object* v_k_859_, uint8_t v_v_860_){
_start:
{
lean_object* v_map_861_; uint8_t v_hasTrace_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_876_; 
v_map_861_ = lean_ctor_get(v_o_858_, 0);
v_hasTrace_862_ = lean_ctor_get_uint8(v_o_858_, sizeof(void*)*1);
v_isSharedCheck_876_ = !lean_is_exclusive(v_o_858_);
if (v_isSharedCheck_876_ == 0)
{
v___x_864_ = v_o_858_;
v_isShared_865_ = v_isSharedCheck_876_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_map_861_);
lean_dec(v_o_858_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_876_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_866_, 0, v_v_860_);
lean_inc(v_k_859_);
v___x_867_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_859_, v___x_866_, v_map_861_);
if (v_hasTrace_862_ == 0)
{
lean_object* v___x_868_; uint8_t v___x_869_; lean_object* v___x_871_; 
v___x_868_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_869_ = l_Lean_Name_isPrefixOf(v___x_868_, v_k_859_);
lean_dec(v_k_859_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_867_);
v___x_871_ = v___x_864_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_867_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*1, v___x_869_);
return v___x_871_;
}
}
else
{
lean_object* v___x_874_; 
lean_dec(v_k_859_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_867_);
v___x_874_ = v___x_864_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*1, v_hasTrace_862_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__2___boxed(lean_object* v_o_877_, lean_object* v_k_878_, lean_object* v_v_879_){
_start:
{
uint8_t v_v_boxed_880_; lean_object* v_res_881_; 
v_v_boxed_880_ = lean_unbox(v_v_879_);
v_res_881_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__2(v_o_877_, v_k_878_, v_v_boxed_880_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object* v_opts_882_, lean_object* v_opt_883_, uint8_t v_val_884_){
_start:
{
lean_object* v_name_885_; lean_object* v___x_886_; 
v_name_885_ = lean_ctor_get(v_opt_883_, 0);
lean_inc(v_name_885_);
lean_dec_ref(v_opt_883_);
v___x_886_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__2(v_opts_882_, v_name_885_, v_val_884_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2___boxed(lean_object* v_opts_887_, lean_object* v_opt_888_, lean_object* v_val_889_){
_start:
{
uint8_t v_val_boxed_890_; lean_object* v_res_891_; 
v_val_boxed_890_ = lean_unbox(v_val_889_);
v_res_891_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_opts_887_, v_opt_888_, v_val_boxed_890_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___redArg(lean_object* v___x_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_b_895_){
_start:
{
lean_object* v_startInclusive_896_; lean_object* v_endExclusive_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_startInclusive_896_ = lean_ctor_get(v___x_892_, 1);
v_endExclusive_897_ = lean_ctor_get(v___x_892_, 2);
v___x_898_ = lean_nat_sub(v_endExclusive_897_, v_startInclusive_896_);
v___x_899_ = lean_nat_dec_eq(v_a_894_, v___x_898_);
lean_dec(v___x_898_);
if (v___x_899_ == 0)
{
uint32_t v___x_900_; uint32_t v___x_901_; uint8_t v___x_902_; 
v___x_900_ = lean_string_utf8_get_fast(v_a_893_, v_a_894_);
v___x_901_ = 58;
v___x_902_ = lean_uint32_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_box(0);
v___x_904_ = lean_string_utf8_next_fast(v_a_893_, v_a_894_);
lean_dec(v_a_894_);
v_a_894_ = v___x_904_;
v_b_895_ = v___x_903_;
goto _start;
}
else
{
lean_object* v___x_906_; 
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v_a_894_);
return v___x_906_;
}
}
else
{
lean_dec(v_a_894_);
lean_inc(v_b_895_);
return v_b_895_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___redArg___boxed(lean_object* v___x_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_b_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___redArg(v___x_907_, v_a_908_, v_a_909_, v_b_910_);
lean_dec(v_b_910_);
lean_dec_ref(v_a_908_);
lean_dec_ref(v___x_907_);
return v_res_911_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = l_System_Platform_numBits;
v___x_938_ = lean_unsigned_to_nat(2u);
v___x_939_ = lean_nat_pow(v___x_938_, v___x_937_);
return v___x_939_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1(void){
_start:
{
uint32_t v___x_949_; lean_object* v___x_950_; 
v___x_949_ = 0;
v___x_950_ = lean_box_uint32(v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object* v_opts_951_, uint32_t v_opt_952_, lean_object* v_optArg_x3f_953_){
_start:
{
lean_object* v___y_1055_; lean_object* v___y_1095_; uint32_t v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = 101;
v___x_1156_ = lean_uint32_dec_eq(v_opt_952_, v___x_1155_);
if (v___x_1156_ == 0)
{
uint32_t v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = 106;
v___x_1158_ = lean_uint32_dec_eq(v_opt_952_, v___x_1157_);
if (v___x_1158_ == 0)
{
uint32_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = 118;
v___x_1160_ = lean_uint32_dec_eq(v_opt_952_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint32_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = 86;
v___x_1162_ = lean_uint32_dec_eq(v_opt_952_, v___x_1161_);
if (v___x_1162_ == 0)
{
uint32_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = 103;
v___x_1164_ = lean_uint32_dec_eq(v_opt_952_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint32_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = 104;
v___x_1166_ = lean_uint32_dec_eq(v_opt_952_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint32_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = 102;
v___x_1168_ = lean_uint32_dec_eq(v_opt_952_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint32_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = 99;
v___x_1170_ = lean_uint32_dec_eq(v_opt_952_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint32_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = 98;
v___x_1172_ = lean_uint32_dec_eq(v_opt_952_, v___x_1171_);
if (v___x_1172_ == 0)
{
uint32_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 115;
v___x_1174_ = lean_uint32_dec_eq(v_opt_952_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint32_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = 73;
v___x_1176_ = lean_uint32_dec_eq(v_opt_952_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint32_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = 114;
v___x_1178_ = lean_uint32_dec_eq(v_opt_952_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint32_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = 111;
v___x_1180_ = lean_uint32_dec_eq(v_opt_952_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint32_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = 105;
v___x_1182_ = lean_uint32_dec_eq(v_opt_952_, v___x_1181_);
if (v___x_1182_ == 0)
{
uint32_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = 82;
v___x_1184_ = lean_uint32_dec_eq(v_opt_952_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint32_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = 77;
v___x_1186_ = lean_uint32_dec_eq(v_opt_952_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint32_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = 84;
v___x_1188_ = lean_uint32_dec_eq(v_opt_952_, v___x_1187_);
if (v___x_1188_ == 0)
{
uint32_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = 116;
v___x_1190_ = lean_uint32_dec_eq(v_opt_952_, v___x_1189_);
if (v___x_1190_ == 0)
{
uint32_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = 113;
v___x_1192_ = lean_uint32_dec_eq(v_opt_952_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint32_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = 100;
v___x_1194_ = lean_uint32_dec_eq(v_opt_952_, v___x_1193_);
if (v___x_1194_ == 0)
{
uint32_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = 79;
v___x_1196_ = lean_uint32_dec_eq(v_opt_952_, v___x_1195_);
if (v___x_1196_ == 0)
{
uint32_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = 78;
v___x_1198_ = lean_uint32_dec_eq(v_opt_952_, v___x_1197_);
if (v___x_1198_ == 0)
{
uint32_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 74;
v___x_1200_ = lean_uint32_dec_eq(v_opt_952_, v___x_1199_);
if (v___x_1200_ == 0)
{
uint32_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = 97;
v___x_1202_ = lean_uint32_dec_eq(v_opt_952_, v___x_1201_);
if (v___x_1202_ == 0)
{
uint32_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = 120;
v___x_1204_ = lean_uint32_dec_eq(v_opt_952_, v___x_1203_);
if (v___x_1204_ == 0)
{
uint32_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = 76;
v___x_1206_ = lean_uint32_dec_eq(v_opt_952_, v___x_1205_);
if (v___x_1206_ == 0)
{
uint32_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = 68;
v___x_1208_ = lean_uint32_dec_eq(v_opt_952_, v___x_1207_);
if (v___x_1208_ == 0)
{
uint32_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = 83;
v___x_1210_ = lean_uint32_dec_eq(v_opt_952_, v___x_1209_);
if (v___x_1210_ == 0)
{
uint32_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = 87;
v___x_1212_ = lean_uint32_dec_eq(v_opt_952_, v___x_1211_);
if (v___x_1212_ == 0)
{
uint32_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = 80;
v___x_1214_ = lean_uint32_dec_eq(v_opt_952_, v___x_1213_);
if (v___x_1214_ == 0)
{
uint32_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = 66;
v___x_1216_ = lean_uint32_dec_eq(v_opt_952_, v___x_1215_);
if (v___x_1216_ == 0)
{
uint32_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = 112;
v___x_1218_ = lean_uint32_dec_eq(v_opt_952_, v___x_1217_);
if (v___x_1218_ == 0)
{
uint32_t v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = 108;
v___x_1220_ = lean_uint32_dec_eq(v_opt_952_, v___x_1219_);
if (v___x_1220_ == 0)
{
uint32_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = 117;
v___x_1222_ = lean_uint32_dec_eq(v_opt_952_, v___x_1221_);
if (v___x_1222_ == 0)
{
uint32_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = 69;
v___x_1224_ = lean_uint32_dec_eq(v_opt_952_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_dec(v_optArg_x3f_953_);
lean_dec_ref(v_opts_951_);
goto v___jp_1073_;
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1226_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1225_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1265_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1265_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1265_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v_leanOpts_1231_; lean_object* v_forwardedArgs_1232_; uint8_t v_component_1233_; uint8_t v_printPrefix_1234_; uint8_t v_printLibDir_1235_; uint8_t v_useStdin_1236_; uint8_t v_onlyDeps_1237_; uint8_t v_onlySrcDeps_1238_; uint8_t v_depsJson_1239_; lean_object* v_opts_1240_; uint32_t v_trustLevel_1241_; uint32_t v_numThreads_1242_; lean_object* v_rootDir_x3f_1243_; lean_object* v_setupFileName_x3f_1244_; lean_object* v_oleanFileName_x3f_1245_; lean_object* v_ileanFileName_x3f_1246_; lean_object* v_cFileName_x3f_1247_; lean_object* v_bcFileName_x3f_1248_; uint8_t v_jsonOutput_1249_; lean_object* v_errorOnKinds_1250_; uint8_t v_printStats_1251_; uint8_t v_run_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1264_; 
v_leanOpts_1231_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1232_ = lean_ctor_get(v_opts_951_, 1);
v_component_1233_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1234_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1235_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1236_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1237_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1238_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1239_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1240_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1241_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1242_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1243_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1244_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1245_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1246_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1247_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1248_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1249_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1250_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1251_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1252_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1254_ = v_opts_951_;
v_isShared_1255_ = v_isSharedCheck_1264_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_errorOnKinds_1250_);
lean_inc(v_bcFileName_x3f_1248_);
lean_inc(v_cFileName_x3f_1247_);
lean_inc(v_ileanFileName_x3f_1246_);
lean_inc(v_oleanFileName_x3f_1245_);
lean_inc(v_setupFileName_x3f_1244_);
lean_inc(v_rootDir_x3f_1243_);
lean_inc(v_opts_1240_);
lean_inc(v_forwardedArgs_1232_);
lean_inc(v_leanOpts_1231_);
lean_dec(v_opts_951_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1264_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1256_ = l_String_toName(v_a_1227_);
v___x_1257_ = lean_array_push(v_errorOnKinds_1250_, v___x_1256_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 9, v___x_1257_);
v___x_1259_ = v___x_1254_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_leanOpts_1231_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_forwardedArgs_1232_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_opts_1240_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_rootDir_x3f_1243_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v_setupFileName_x3f_1244_);
lean_ctor_set(v_reuseFailAlloc_1263_, 5, v_oleanFileName_x3f_1245_);
lean_ctor_set(v_reuseFailAlloc_1263_, 6, v_ileanFileName_x3f_1246_);
lean_ctor_set(v_reuseFailAlloc_1263_, 7, v_cFileName_x3f_1247_);
lean_ctor_set(v_reuseFailAlloc_1263_, 8, v_bcFileName_x3f_1248_);
lean_ctor_set(v_reuseFailAlloc_1263_, 9, v___x_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*10 + 8, v_component_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*10 + 9, v_printPrefix_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*10 + 10, v_printLibDir_1235_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*10 + 11, v_useStdin_1236_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*10 + 12, v_onlyDeps_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*10 + 13, v_onlySrcDeps_1238_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*10 + 14, v_depsJson_1239_);
lean_ctor_set_uint32(v_reuseFailAlloc_1263_, sizeof(void*)*10, v_trustLevel_1241_);
lean_ctor_set_uint32(v_reuseFailAlloc_1263_, sizeof(void*)*10 + 4, v_numThreads_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*10 + 15, v_jsonOutput_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*10 + 16, v_printStats_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*10 + 17, v_run_1252_);
v___x_1259_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1261_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1259_);
v___x_1261_ = v___x_1229_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v_opts_951_);
v_a_1266_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1266_);
lean_dec_ref(v___x_1226_);
v___x_1270_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1271_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1270_);
lean_dec_ref(v___x_1271_);
goto v___jp_1267_;
v___jp_1267_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_io_error_to_string(v_a_1266_);
v___x_1269_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1268_);
lean_dec_ref(v___x_1269_);
goto v___jp_1079_;
}
}
}
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1273_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1272_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1311_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1311_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1311_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v_leanOpts_1278_; lean_object* v_forwardedArgs_1279_; uint8_t v_component_1280_; uint8_t v_printPrefix_1281_; uint8_t v_printLibDir_1282_; uint8_t v_useStdin_1283_; uint8_t v_onlyDeps_1284_; uint8_t v_onlySrcDeps_1285_; uint8_t v_depsJson_1286_; lean_object* v_opts_1287_; uint32_t v_trustLevel_1288_; uint32_t v_numThreads_1289_; lean_object* v_rootDir_x3f_1290_; lean_object* v_oleanFileName_x3f_1291_; lean_object* v_ileanFileName_x3f_1292_; lean_object* v_cFileName_x3f_1293_; lean_object* v_bcFileName_x3f_1294_; uint8_t v_jsonOutput_1295_; lean_object* v_errorOnKinds_1296_; uint8_t v_printStats_1297_; uint8_t v_run_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1309_; 
v_leanOpts_1278_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1279_ = lean_ctor_get(v_opts_951_, 1);
v_component_1280_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1281_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1282_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1283_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1284_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1285_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1286_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1287_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1288_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1289_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1290_ = lean_ctor_get(v_opts_951_, 3);
v_oleanFileName_x3f_1291_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1292_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1293_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1294_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1295_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1296_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1297_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1298_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v_opts_951_, 4);
lean_dec(v_unused_1310_);
v___x_1300_ = v_opts_951_;
v_isShared_1301_ = v_isSharedCheck_1309_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_errorOnKinds_1296_);
lean_inc(v_bcFileName_x3f_1294_);
lean_inc(v_cFileName_x3f_1293_);
lean_inc(v_ileanFileName_x3f_1292_);
lean_inc(v_oleanFileName_x3f_1291_);
lean_inc(v_rootDir_x3f_1290_);
lean_inc(v_opts_1287_);
lean_inc(v_forwardedArgs_1279_);
lean_inc(v_leanOpts_1278_);
lean_dec(v_opts_951_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1309_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_a_1274_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 4, v___x_1302_);
v___x_1304_ = v___x_1300_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_leanOpts_1278_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_forwardedArgs_1279_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v_opts_1287_);
lean_ctor_set(v_reuseFailAlloc_1308_, 3, v_rootDir_x3f_1290_);
lean_ctor_set(v_reuseFailAlloc_1308_, 4, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1308_, 5, v_oleanFileName_x3f_1291_);
lean_ctor_set(v_reuseFailAlloc_1308_, 6, v_ileanFileName_x3f_1292_);
lean_ctor_set(v_reuseFailAlloc_1308_, 7, v_cFileName_x3f_1293_);
lean_ctor_set(v_reuseFailAlloc_1308_, 8, v_bcFileName_x3f_1294_);
lean_ctor_set(v_reuseFailAlloc_1308_, 9, v_errorOnKinds_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1308_, sizeof(void*)*10 + 8, v_component_1280_);
lean_ctor_set_uint8(v_reuseFailAlloc_1308_, sizeof(void*)*10 + 9, v_printPrefix_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1308_, sizeof(void*)*10 + 10, v_printLibDir_1282_);
lean_ctor_set_uint8(v_reuseFailAlloc_1308_, sizeof(void*)*10 + 11, v_useStdin_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1308_, sizeof(void*)*10 + 12, v_onlyDeps_1284_);
lean_ctor_set_uint8(v_reuseFailAlloc_1308_, sizeof(void*)*10 + 13, v_onlySrcDeps_1285_);
lean_ctor_set_uint8(v_reuseFailAlloc_1308_, sizeof(void*)*10 + 14, v_depsJson_1286_);
lean_ctor_set_uint32(v_reuseFailAlloc_1308_, sizeof(void*)*10, v_trustLevel_1288_);
lean_ctor_set_uint32(v_reuseFailAlloc_1308_, sizeof(void*)*10 + 4, v_numThreads_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1308_, sizeof(void*)*10 + 15, v_jsonOutput_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1308_, sizeof(void*)*10 + 16, v_printStats_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1308_, sizeof(void*)*10 + 17, v_run_1298_);
v___x_1304_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1306_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1304_);
v___x_1306_ = v___x_1276_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec_ref(v_opts_951_);
v_a_1312_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1312_);
lean_dec_ref(v___x_1273_);
v___x_1316_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1317_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1316_);
lean_dec_ref(v___x_1317_);
goto v___jp_1313_;
v___jp_1313_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_io_error_to_string(v_a_1312_);
v___x_1315_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1314_);
lean_dec_ref(v___x_1315_);
goto v___jp_1045_;
}
}
}
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1319_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1318_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc_n(v_a_1320_, 2);
lean_dec_ref(v___x_1319_);
v___x_1321_ = lean_load_dynlib(v_a_1320_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1360_; 
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; 
v_unused_1361_ = lean_ctor_get(v___x_1321_, 0);
lean_dec(v_unused_1361_);
v___x_1323_ = v___x_1321_;
v_isShared_1324_ = v_isSharedCheck_1360_;
goto v_resetjp_1322_;
}
else
{
lean_dec(v___x_1321_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1360_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_leanOpts_1325_; lean_object* v_forwardedArgs_1326_; uint8_t v_component_1327_; uint8_t v_printPrefix_1328_; uint8_t v_printLibDir_1329_; uint8_t v_useStdin_1330_; uint8_t v_onlyDeps_1331_; uint8_t v_onlySrcDeps_1332_; uint8_t v_depsJson_1333_; lean_object* v_opts_1334_; uint32_t v_trustLevel_1335_; uint32_t v_numThreads_1336_; lean_object* v_rootDir_x3f_1337_; lean_object* v_setupFileName_x3f_1338_; lean_object* v_oleanFileName_x3f_1339_; lean_object* v_ileanFileName_x3f_1340_; lean_object* v_cFileName_x3f_1341_; lean_object* v_bcFileName_x3f_1342_; uint8_t v_jsonOutput_1343_; lean_object* v_errorOnKinds_1344_; uint8_t v_printStats_1345_; uint8_t v_run_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1359_; 
v_leanOpts_1325_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1326_ = lean_ctor_get(v_opts_951_, 1);
v_component_1327_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1328_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1329_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1330_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1331_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1332_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1333_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1334_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1335_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1336_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1337_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1338_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1339_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1340_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1341_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1342_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1343_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1344_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1345_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1346_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1348_ = v_opts_951_;
v_isShared_1349_ = v_isSharedCheck_1359_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_errorOnKinds_1344_);
lean_inc(v_bcFileName_x3f_1342_);
lean_inc(v_cFileName_x3f_1341_);
lean_inc(v_ileanFileName_x3f_1340_);
lean_inc(v_oleanFileName_x3f_1339_);
lean_inc(v_setupFileName_x3f_1338_);
lean_inc(v_rootDir_x3f_1337_);
lean_inc(v_opts_1334_);
lean_inc(v_forwardedArgs_1326_);
lean_inc(v_leanOpts_1325_);
lean_dec(v_opts_951_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1359_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1350_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1351_ = lean_string_append(v___x_1350_, v_a_1320_);
lean_dec(v_a_1320_);
v___x_1352_ = lean_array_push(v_forwardedArgs_1326_, v___x_1351_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v___x_1352_);
v___x_1354_ = v___x_1348_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_leanOpts_1325_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_opts_1334_);
lean_ctor_set(v_reuseFailAlloc_1358_, 3, v_rootDir_x3f_1337_);
lean_ctor_set(v_reuseFailAlloc_1358_, 4, v_setupFileName_x3f_1338_);
lean_ctor_set(v_reuseFailAlloc_1358_, 5, v_oleanFileName_x3f_1339_);
lean_ctor_set(v_reuseFailAlloc_1358_, 6, v_ileanFileName_x3f_1340_);
lean_ctor_set(v_reuseFailAlloc_1358_, 7, v_cFileName_x3f_1341_);
lean_ctor_set(v_reuseFailAlloc_1358_, 8, v_bcFileName_x3f_1342_);
lean_ctor_set(v_reuseFailAlloc_1358_, 9, v_errorOnKinds_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*10 + 8, v_component_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*10 + 9, v_printPrefix_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*10 + 10, v_printLibDir_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*10 + 11, v_useStdin_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*10 + 12, v_onlyDeps_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*10 + 13, v_onlySrcDeps_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*10 + 14, v_depsJson_1333_);
lean_ctor_set_uint32(v_reuseFailAlloc_1358_, sizeof(void*)*10, v_trustLevel_1335_);
lean_ctor_set_uint32(v_reuseFailAlloc_1358_, sizeof(void*)*10 + 4, v_numThreads_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*10 + 15, v_jsonOutput_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*10 + 16, v_printStats_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1358_, sizeof(void*)*10 + 17, v_run_1346_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1354_);
v___x_1356_ = v___x_1323_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec(v_a_1320_);
lean_dec_ref(v_opts_951_);
v_a_1362_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v___x_1321_);
v___x_1366_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1367_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1366_);
lean_dec_ref(v___x_1367_);
goto v___jp_1363_;
v___jp_1363_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_io_error_to_string(v_a_1362_);
v___x_1365_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1364_);
lean_dec_ref(v___x_1365_);
goto v___jp_1085_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec_ref(v_opts_951_);
v_a_1368_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1368_);
lean_dec_ref(v___x_1319_);
v___x_1372_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1373_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1372_);
lean_dec_ref(v___x_1373_);
goto v___jp_1369_;
v___jp_1369_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_io_error_to_string(v_a_1368_);
v___x_1371_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1370_);
lean_dec_ref(v___x_1371_);
goto v___jp_1039_;
}
}
}
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1375_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1374_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1445_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1445_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1445_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v_fst_1381_; lean_object* v_snd_1382_; lean_object* v___y_1428_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = lean_string_utf8_byte_size(v_a_1376_);
lean_inc(v_a_1376_);
v___x_1441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1441_, 0, v_a_1376_);
lean_ctor_set(v___x_1441_, 1, v___x_1439_);
lean_ctor_set(v___x_1441_, 2, v___x_1440_);
v___x_1442_ = lean_box(0);
v___x_1443_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___redArg(v___x_1441_, v_a_1376_, v___x_1439_, v___x_1442_);
lean_dec_ref(v___x_1441_);
if (lean_obj_tag(v___x_1443_) == 0)
{
v___y_1428_ = v___x_1440_;
goto v___jp_1427_;
}
else
{
lean_object* v_val_1444_; 
v_val_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_val_1444_);
lean_dec_ref(v___x_1443_);
v___y_1428_ = v_val_1444_;
goto v___jp_1427_;
}
v___jp_1380_:
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_load_plugin(v_fst_1381_, v_snd_1382_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1422_; 
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v___x_1383_, 0);
lean_dec(v_unused_1423_);
v___x_1385_ = v___x_1383_;
v_isShared_1386_ = v_isSharedCheck_1422_;
goto v_resetjp_1384_;
}
else
{
lean_dec(v___x_1383_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1422_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v_leanOpts_1387_; lean_object* v_forwardedArgs_1388_; uint8_t v_component_1389_; uint8_t v_printPrefix_1390_; uint8_t v_printLibDir_1391_; uint8_t v_useStdin_1392_; uint8_t v_onlyDeps_1393_; uint8_t v_onlySrcDeps_1394_; uint8_t v_depsJson_1395_; lean_object* v_opts_1396_; uint32_t v_trustLevel_1397_; uint32_t v_numThreads_1398_; lean_object* v_rootDir_x3f_1399_; lean_object* v_setupFileName_x3f_1400_; lean_object* v_oleanFileName_x3f_1401_; lean_object* v_ileanFileName_x3f_1402_; lean_object* v_cFileName_x3f_1403_; lean_object* v_bcFileName_x3f_1404_; uint8_t v_jsonOutput_1405_; lean_object* v_errorOnKinds_1406_; uint8_t v_printStats_1407_; uint8_t v_run_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1421_; 
v_leanOpts_1387_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1388_ = lean_ctor_get(v_opts_951_, 1);
v_component_1389_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1390_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1391_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1392_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1393_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1394_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1395_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1396_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1397_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1398_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1399_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1400_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1401_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1402_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1403_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1404_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1405_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1406_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1407_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1408_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1410_ = v_opts_951_;
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_errorOnKinds_1406_);
lean_inc(v_bcFileName_x3f_1404_);
lean_inc(v_cFileName_x3f_1403_);
lean_inc(v_ileanFileName_x3f_1402_);
lean_inc(v_oleanFileName_x3f_1401_);
lean_inc(v_setupFileName_x3f_1400_);
lean_inc(v_rootDir_x3f_1399_);
lean_inc(v_opts_1396_);
lean_inc(v_forwardedArgs_1388_);
lean_inc(v_leanOpts_1387_);
lean_dec(v_opts_951_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1412_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1413_ = lean_string_append(v___x_1412_, v_a_1376_);
lean_dec(v_a_1376_);
v___x_1414_ = lean_array_push(v_forwardedArgs_1388_, v___x_1413_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v___x_1414_);
v___x_1416_ = v___x_1410_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_leanOpts_1387_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_opts_1396_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_rootDir_x3f_1399_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_setupFileName_x3f_1400_);
lean_ctor_set(v_reuseFailAlloc_1420_, 5, v_oleanFileName_x3f_1401_);
lean_ctor_set(v_reuseFailAlloc_1420_, 6, v_ileanFileName_x3f_1402_);
lean_ctor_set(v_reuseFailAlloc_1420_, 7, v_cFileName_x3f_1403_);
lean_ctor_set(v_reuseFailAlloc_1420_, 8, v_bcFileName_x3f_1404_);
lean_ctor_set(v_reuseFailAlloc_1420_, 9, v_errorOnKinds_1406_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*10 + 8, v_component_1389_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*10 + 9, v_printPrefix_1390_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*10 + 10, v_printLibDir_1391_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*10 + 11, v_useStdin_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*10 + 12, v_onlyDeps_1393_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*10 + 13, v_onlySrcDeps_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*10 + 14, v_depsJson_1395_);
lean_ctor_set_uint32(v_reuseFailAlloc_1420_, sizeof(void*)*10, v_trustLevel_1397_);
lean_ctor_set_uint32(v_reuseFailAlloc_1420_, sizeof(void*)*10 + 4, v_numThreads_1398_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*10 + 15, v_jsonOutput_1405_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*10 + 16, v_printStats_1407_);
lean_ctor_set_uint8(v_reuseFailAlloc_1420_, sizeof(void*)*10 + 17, v_run_1408_);
v___x_1416_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; 
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1416_);
v___x_1418_ = v___x_1385_;
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
lean_object* v_a_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_951_);
v_a_1424_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1424_);
lean_dec_ref(v___x_1383_);
v___x_1425_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1426_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1425_);
lean_dec_ref(v___x_1426_);
v___y_1095_ = v_a_1424_;
goto v___jp_1094_;
}
}
v___jp_1427_:
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = lean_string_utf8_byte_size(v_a_1376_);
v___x_1430_ = lean_nat_dec_eq(v___y_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = lean_string_utf8_next_fast(v_a_1376_, v___y_1428_);
v___x_1433_ = lean_string_utf8_extract(v_a_1376_, v___x_1431_, v___y_1428_);
lean_dec(v___y_1428_);
v___x_1434_ = lean_string_utf8_extract(v_a_1376_, v___x_1432_, v___x_1429_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set_tag(v___x_1378_, 1);
lean_ctor_set(v___x_1378_, 0, v___x_1434_);
v___x_1436_ = v___x_1378_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
v_fst_1381_ = v___x_1433_;
v_snd_1382_ = v___x_1436_;
goto v___jp_1380_;
}
}
else
{
lean_object* v___x_1438_; 
lean_dec(v___y_1428_);
lean_del_object(v___x_1378_);
v___x_1438_ = lean_box(0);
lean_inc(v_a_1376_);
v_fst_1381_ = v_a_1376_;
v_snd_1382_ = v___x_1438_;
goto v___jp_1380_;
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_dec_ref(v_opts_951_);
v_a_1446_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1446_);
lean_dec_ref(v___x_1375_);
v___x_1450_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1451_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1450_);
lean_dec_ref(v___x_1451_);
goto v___jp_1447_;
v___jp_1447_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_io_error_to_string(v_a_1446_);
v___x_1449_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1448_);
lean_dec_ref(v___x_1449_);
goto v___jp_1033_;
}
}
}
}
else
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__12, &l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12);
if (v___x_1452_ == 0)
{
lean_dec(v_optArg_x3f_953_);
lean_dec_ref(v_opts_951_);
goto v___jp_1073_;
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1454_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1453_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1463_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1459_ = lean_internal_enable_debug(v_a_1455_);
lean_dec(v_a_1455_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v_opts_951_);
v___x_1461_ = v___x_1457_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_opts_951_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec_ref(v_opts_951_);
v_a_1464_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1464_);
lean_dec_ref(v___x_1454_);
v___x_1468_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1469_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1468_);
lean_dec_ref(v___x_1469_);
goto v___jp_1465_;
v___jp_1465_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_io_error_to_string(v_a_1464_);
v___x_1467_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1466_);
lean_dec_ref(v___x_1467_);
goto v___jp_1101_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1470_; lean_object* v_forwardedArgs_1471_; uint8_t v_component_1472_; uint8_t v_printPrefix_1473_; uint8_t v_printLibDir_1474_; uint8_t v_useStdin_1475_; uint8_t v_onlyDeps_1476_; uint8_t v_onlySrcDeps_1477_; uint8_t v_depsJson_1478_; lean_object* v_opts_1479_; uint32_t v_trustLevel_1480_; uint32_t v_numThreads_1481_; lean_object* v_rootDir_x3f_1482_; lean_object* v_setupFileName_x3f_1483_; lean_object* v_oleanFileName_x3f_1484_; lean_object* v_ileanFileName_x3f_1485_; lean_object* v_cFileName_x3f_1486_; lean_object* v_bcFileName_x3f_1487_; uint8_t v_jsonOutput_1488_; lean_object* v_errorOnKinds_1489_; uint8_t v_printStats_1490_; uint8_t v_run_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1501_; 
lean_dec(v_optArg_x3f_953_);
v_leanOpts_1470_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1471_ = lean_ctor_get(v_opts_951_, 1);
v_component_1472_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1473_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1474_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1475_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1476_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1477_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1478_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1479_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1480_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1481_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1482_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1483_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1484_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1485_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1486_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1487_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1488_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1489_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1490_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1491_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1493_ = v_opts_951_;
v_isShared_1494_ = v_isSharedCheck_1501_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_errorOnKinds_1489_);
lean_inc(v_bcFileName_x3f_1487_);
lean_inc(v_cFileName_x3f_1486_);
lean_inc(v_ileanFileName_x3f_1485_);
lean_inc(v_oleanFileName_x3f_1484_);
lean_inc(v_setupFileName_x3f_1483_);
lean_inc(v_rootDir_x3f_1482_);
lean_inc(v_opts_1479_);
lean_inc(v_forwardedArgs_1471_);
lean_inc(v_leanOpts_1470_);
lean_dec(v_opts_951_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1501_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1495_ = l_Lean_profiler;
v___x_1496_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_1470_, v___x_1495_, v___x_1214_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1496_);
v___x_1498_ = v___x_1493_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_forwardedArgs_1471_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_opts_1479_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_rootDir_x3f_1482_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_setupFileName_x3f_1483_);
lean_ctor_set(v_reuseFailAlloc_1500_, 5, v_oleanFileName_x3f_1484_);
lean_ctor_set(v_reuseFailAlloc_1500_, 6, v_ileanFileName_x3f_1485_);
lean_ctor_set(v_reuseFailAlloc_1500_, 7, v_cFileName_x3f_1486_);
lean_ctor_set(v_reuseFailAlloc_1500_, 8, v_bcFileName_x3f_1487_);
lean_ctor_set(v_reuseFailAlloc_1500_, 9, v_errorOnKinds_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*10 + 8, v_component_1472_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*10 + 9, v_printPrefix_1473_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*10 + 10, v_printLibDir_1474_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*10 + 11, v_useStdin_1475_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*10 + 12, v_onlyDeps_1476_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*10 + 13, v_onlySrcDeps_1477_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*10 + 14, v_depsJson_1478_);
lean_ctor_set_uint32(v_reuseFailAlloc_1500_, sizeof(void*)*10, v_trustLevel_1480_);
lean_ctor_set_uint32(v_reuseFailAlloc_1500_, sizeof(void*)*10 + 4, v_numThreads_1481_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*10 + 15, v_jsonOutput_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*10 + 16, v_printStats_1490_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*10 + 17, v_run_1491_);
v___x_1498_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
return v___x_1499_;
}
}
}
}
else
{
lean_object* v_leanOpts_1502_; lean_object* v_forwardedArgs_1503_; uint8_t v_printPrefix_1504_; uint8_t v_printLibDir_1505_; uint8_t v_useStdin_1506_; uint8_t v_onlyDeps_1507_; uint8_t v_onlySrcDeps_1508_; uint8_t v_depsJson_1509_; lean_object* v_opts_1510_; uint32_t v_trustLevel_1511_; uint32_t v_numThreads_1512_; lean_object* v_rootDir_x3f_1513_; lean_object* v_setupFileName_x3f_1514_; lean_object* v_oleanFileName_x3f_1515_; lean_object* v_ileanFileName_x3f_1516_; lean_object* v_cFileName_x3f_1517_; lean_object* v_bcFileName_x3f_1518_; uint8_t v_jsonOutput_1519_; lean_object* v_errorOnKinds_1520_; uint8_t v_printStats_1521_; uint8_t v_run_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1531_; 
lean_dec(v_optArg_x3f_953_);
v_leanOpts_1502_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1503_ = lean_ctor_get(v_opts_951_, 1);
v_printPrefix_1504_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1505_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1506_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1507_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1508_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1509_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1510_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1511_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1512_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1513_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1514_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1515_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1516_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1517_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1518_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1519_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1520_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1521_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1522_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1524_ = v_opts_951_;
v_isShared_1525_ = v_isSharedCheck_1531_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_errorOnKinds_1520_);
lean_inc(v_bcFileName_x3f_1518_);
lean_inc(v_cFileName_x3f_1517_);
lean_inc(v_ileanFileName_x3f_1516_);
lean_inc(v_oleanFileName_x3f_1515_);
lean_inc(v_setupFileName_x3f_1514_);
lean_inc(v_rootDir_x3f_1513_);
lean_inc(v_opts_1510_);
lean_inc(v_forwardedArgs_1503_);
lean_inc(v_leanOpts_1502_);
lean_dec(v_opts_951_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1531_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
uint8_t v___x_1526_; lean_object* v___x_1528_; 
v___x_1526_ = 2;
if (v_isShared_1525_ == 0)
{
v___x_1528_ = v___x_1524_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_leanOpts_1502_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_forwardedArgs_1503_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_opts_1510_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_rootDir_x3f_1513_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_setupFileName_x3f_1514_);
lean_ctor_set(v_reuseFailAlloc_1530_, 5, v_oleanFileName_x3f_1515_);
lean_ctor_set(v_reuseFailAlloc_1530_, 6, v_ileanFileName_x3f_1516_);
lean_ctor_set(v_reuseFailAlloc_1530_, 7, v_cFileName_x3f_1517_);
lean_ctor_set(v_reuseFailAlloc_1530_, 8, v_bcFileName_x3f_1518_);
lean_ctor_set(v_reuseFailAlloc_1530_, 9, v_errorOnKinds_1520_);
lean_ctor_set_uint8(v_reuseFailAlloc_1530_, sizeof(void*)*10 + 9, v_printPrefix_1504_);
lean_ctor_set_uint8(v_reuseFailAlloc_1530_, sizeof(void*)*10 + 10, v_printLibDir_1505_);
lean_ctor_set_uint8(v_reuseFailAlloc_1530_, sizeof(void*)*10 + 11, v_useStdin_1506_);
lean_ctor_set_uint8(v_reuseFailAlloc_1530_, sizeof(void*)*10 + 12, v_onlyDeps_1507_);
lean_ctor_set_uint8(v_reuseFailAlloc_1530_, sizeof(void*)*10 + 13, v_onlySrcDeps_1508_);
lean_ctor_set_uint8(v_reuseFailAlloc_1530_, sizeof(void*)*10 + 14, v_depsJson_1509_);
lean_ctor_set_uint32(v_reuseFailAlloc_1530_, sizeof(void*)*10, v_trustLevel_1511_);
lean_ctor_set_uint32(v_reuseFailAlloc_1530_, sizeof(void*)*10 + 4, v_numThreads_1512_);
lean_ctor_set_uint8(v_reuseFailAlloc_1530_, sizeof(void*)*10 + 15, v_jsonOutput_1519_);
lean_ctor_set_uint8(v_reuseFailAlloc_1530_, sizeof(void*)*10 + 16, v_printStats_1521_);
lean_ctor_set_uint8(v_reuseFailAlloc_1530_, sizeof(void*)*10 + 17, v_run_1522_);
v___x_1528_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; 
lean_ctor_set_uint8(v___x_1528_, sizeof(void*)*10 + 8, v___x_1526_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
}
}
}
else
{
lean_object* v_leanOpts_1532_; lean_object* v_forwardedArgs_1533_; uint8_t v_printPrefix_1534_; uint8_t v_printLibDir_1535_; uint8_t v_useStdin_1536_; uint8_t v_onlyDeps_1537_; uint8_t v_onlySrcDeps_1538_; uint8_t v_depsJson_1539_; lean_object* v_opts_1540_; uint32_t v_trustLevel_1541_; uint32_t v_numThreads_1542_; lean_object* v_rootDir_x3f_1543_; lean_object* v_setupFileName_x3f_1544_; lean_object* v_oleanFileName_x3f_1545_; lean_object* v_ileanFileName_x3f_1546_; lean_object* v_cFileName_x3f_1547_; lean_object* v_bcFileName_x3f_1548_; uint8_t v_jsonOutput_1549_; lean_object* v_errorOnKinds_1550_; uint8_t v_printStats_1551_; uint8_t v_run_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1561_; 
lean_dec(v_optArg_x3f_953_);
v_leanOpts_1532_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1533_ = lean_ctor_get(v_opts_951_, 1);
v_printPrefix_1534_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1535_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1536_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1537_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1538_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1539_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1540_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1541_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1542_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1543_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1544_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1545_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1546_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1547_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1548_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1549_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1550_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1551_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1552_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1554_ = v_opts_951_;
v_isShared_1555_ = v_isSharedCheck_1561_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_errorOnKinds_1550_);
lean_inc(v_bcFileName_x3f_1548_);
lean_inc(v_cFileName_x3f_1547_);
lean_inc(v_ileanFileName_x3f_1546_);
lean_inc(v_oleanFileName_x3f_1545_);
lean_inc(v_setupFileName_x3f_1544_);
lean_inc(v_rootDir_x3f_1543_);
lean_inc(v_opts_1540_);
lean_inc(v_forwardedArgs_1533_);
lean_inc(v_leanOpts_1532_);
lean_dec(v_opts_951_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1561_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
uint8_t v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = 1;
if (v_isShared_1555_ == 0)
{
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_leanOpts_1532_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_forwardedArgs_1533_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v_opts_1540_);
lean_ctor_set(v_reuseFailAlloc_1560_, 3, v_rootDir_x3f_1543_);
lean_ctor_set(v_reuseFailAlloc_1560_, 4, v_setupFileName_x3f_1544_);
lean_ctor_set(v_reuseFailAlloc_1560_, 5, v_oleanFileName_x3f_1545_);
lean_ctor_set(v_reuseFailAlloc_1560_, 6, v_ileanFileName_x3f_1546_);
lean_ctor_set(v_reuseFailAlloc_1560_, 7, v_cFileName_x3f_1547_);
lean_ctor_set(v_reuseFailAlloc_1560_, 8, v_bcFileName_x3f_1548_);
lean_ctor_set(v_reuseFailAlloc_1560_, 9, v_errorOnKinds_1550_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*10 + 9, v_printPrefix_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*10 + 10, v_printLibDir_1535_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*10 + 11, v_useStdin_1536_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*10 + 12, v_onlyDeps_1537_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*10 + 13, v_onlySrcDeps_1538_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*10 + 14, v_depsJson_1539_);
lean_ctor_set_uint32(v_reuseFailAlloc_1560_, sizeof(void*)*10, v_trustLevel_1541_);
lean_ctor_set_uint32(v_reuseFailAlloc_1560_, sizeof(void*)*10 + 4, v_numThreads_1542_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*10 + 15, v_jsonOutput_1549_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*10 + 16, v_printStats_1551_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*10 + 17, v_run_1552_);
v___x_1558_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1559_; 
lean_ctor_set_uint8(v___x_1558_, sizeof(void*)*10 + 8, v___x_1556_);
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
}
}
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1563_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1562_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v_leanOpts_1565_; lean_object* v_forwardedArgs_1566_; uint8_t v_component_1567_; uint8_t v_printPrefix_1568_; uint8_t v_printLibDir_1569_; uint8_t v_useStdin_1570_; uint8_t v_onlyDeps_1571_; uint8_t v_onlySrcDeps_1572_; uint8_t v_depsJson_1573_; lean_object* v_opts_1574_; uint32_t v_trustLevel_1575_; uint32_t v_numThreads_1576_; lean_object* v_rootDir_x3f_1577_; lean_object* v_setupFileName_x3f_1578_; lean_object* v_oleanFileName_x3f_1579_; lean_object* v_ileanFileName_x3f_1580_; lean_object* v_cFileName_x3f_1581_; lean_object* v_bcFileName_x3f_1582_; uint8_t v_jsonOutput_1583_; lean_object* v_errorOnKinds_1584_; uint8_t v_printStats_1585_; uint8_t v_run_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1611_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref(v___x_1563_);
v_leanOpts_1565_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1566_ = lean_ctor_get(v_opts_951_, 1);
v_component_1567_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1568_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1569_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1570_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1571_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1572_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1573_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1574_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1575_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1576_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1577_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1578_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1579_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1580_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1581_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1582_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1583_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1584_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1585_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1586_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1588_ = v_opts_951_;
v_isShared_1589_ = v_isSharedCheck_1611_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_errorOnKinds_1584_);
lean_inc(v_bcFileName_x3f_1582_);
lean_inc(v_cFileName_x3f_1581_);
lean_inc(v_ileanFileName_x3f_1580_);
lean_inc(v_oleanFileName_x3f_1579_);
lean_inc(v_setupFileName_x3f_1578_);
lean_inc(v_rootDir_x3f_1577_);
lean_inc(v_opts_1574_);
lean_inc(v_forwardedArgs_1566_);
lean_inc(v_leanOpts_1565_);
lean_dec(v_opts_951_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1611_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; 
lean_inc(v_a_1564_);
v___x_1590_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1565_, v_a_1564_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1604_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1604_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1604_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1595_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1596_ = lean_string_append(v___x_1595_, v_a_1564_);
lean_dec(v_a_1564_);
v___x_1597_ = lean_array_push(v_forwardedArgs_1566_, v___x_1596_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v___x_1597_);
lean_ctor_set(v___x_1588_, 0, v_a_1591_);
v___x_1599_ = v___x_1588_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1591_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_opts_1574_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_rootDir_x3f_1577_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_setupFileName_x3f_1578_);
lean_ctor_set(v_reuseFailAlloc_1603_, 5, v_oleanFileName_x3f_1579_);
lean_ctor_set(v_reuseFailAlloc_1603_, 6, v_ileanFileName_x3f_1580_);
lean_ctor_set(v_reuseFailAlloc_1603_, 7, v_cFileName_x3f_1581_);
lean_ctor_set(v_reuseFailAlloc_1603_, 8, v_bcFileName_x3f_1582_);
lean_ctor_set(v_reuseFailAlloc_1603_, 9, v_errorOnKinds_1584_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*10 + 8, v_component_1567_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*10 + 9, v_printPrefix_1568_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*10 + 10, v_printLibDir_1569_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*10 + 11, v_useStdin_1570_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*10 + 12, v_onlyDeps_1571_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*10 + 13, v_onlySrcDeps_1572_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*10 + 14, v_depsJson_1573_);
lean_ctor_set_uint32(v_reuseFailAlloc_1603_, sizeof(void*)*10, v_trustLevel_1575_);
lean_ctor_set_uint32(v_reuseFailAlloc_1603_, sizeof(void*)*10 + 4, v_numThreads_1576_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*10 + 15, v_jsonOutput_1583_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*10 + 16, v_printStats_1585_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*10 + 17, v_run_1586_);
v___x_1599_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1601_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1599_);
v___x_1601_ = v___x_1593_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_del_object(v___x_1588_);
lean_dec_ref(v_errorOnKinds_1584_);
lean_dec(v_bcFileName_x3f_1582_);
lean_dec(v_cFileName_x3f_1581_);
lean_dec(v_ileanFileName_x3f_1580_);
lean_dec(v_oleanFileName_x3f_1579_);
lean_dec(v_setupFileName_x3f_1578_);
lean_dec(v_rootDir_x3f_1577_);
lean_dec_ref(v_opts_1574_);
lean_dec_ref(v_forwardedArgs_1566_);
lean_dec(v_a_1564_);
v_a_1605_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v___x_1590_);
v___x_1609_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1610_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1609_);
lean_dec_ref(v___x_1610_);
goto v___jp_1606_;
v___jp_1606_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_io_error_to_string(v_a_1605_);
v___x_1608_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1607_);
lean_dec_ref(v___x_1608_);
goto v___jp_1027_;
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v_opts_951_);
v_a_1612_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1612_);
lean_dec_ref(v___x_1563_);
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
goto v___jp_1107_;
}
}
}
}
else
{
lean_object* v_leanOpts_1618_; lean_object* v_forwardedArgs_1619_; uint8_t v_component_1620_; uint8_t v_printPrefix_1621_; uint8_t v_useStdin_1622_; uint8_t v_onlyDeps_1623_; uint8_t v_onlySrcDeps_1624_; uint8_t v_depsJson_1625_; lean_object* v_opts_1626_; uint32_t v_trustLevel_1627_; uint32_t v_numThreads_1628_; lean_object* v_rootDir_x3f_1629_; lean_object* v_setupFileName_x3f_1630_; lean_object* v_oleanFileName_x3f_1631_; lean_object* v_ileanFileName_x3f_1632_; lean_object* v_cFileName_x3f_1633_; lean_object* v_bcFileName_x3f_1634_; uint8_t v_jsonOutput_1635_; lean_object* v_errorOnKinds_1636_; uint8_t v_printStats_1637_; uint8_t v_run_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v_optArg_x3f_953_);
v_leanOpts_1618_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1619_ = lean_ctor_get(v_opts_951_, 1);
v_component_1620_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1621_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_useStdin_1622_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1623_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1624_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1625_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1626_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1627_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1628_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1629_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1630_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1631_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1632_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1633_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1634_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1635_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1636_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1637_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1638_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1640_ = v_opts_951_;
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_errorOnKinds_1636_);
lean_inc(v_bcFileName_x3f_1634_);
lean_inc(v_cFileName_x3f_1633_);
lean_inc(v_ileanFileName_x3f_1632_);
lean_inc(v_oleanFileName_x3f_1631_);
lean_inc(v_setupFileName_x3f_1630_);
lean_inc(v_rootDir_x3f_1629_);
lean_inc(v_opts_1626_);
lean_inc(v_forwardedArgs_1619_);
lean_inc(v_leanOpts_1618_);
lean_dec(v_opts_951_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_leanOpts_1618_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_forwardedArgs_1619_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_opts_1626_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_rootDir_x3f_1629_);
lean_ctor_set(v_reuseFailAlloc_1645_, 4, v_setupFileName_x3f_1630_);
lean_ctor_set(v_reuseFailAlloc_1645_, 5, v_oleanFileName_x3f_1631_);
lean_ctor_set(v_reuseFailAlloc_1645_, 6, v_ileanFileName_x3f_1632_);
lean_ctor_set(v_reuseFailAlloc_1645_, 7, v_cFileName_x3f_1633_);
lean_ctor_set(v_reuseFailAlloc_1645_, 8, v_bcFileName_x3f_1634_);
lean_ctor_set(v_reuseFailAlloc_1645_, 9, v_errorOnKinds_1636_);
lean_ctor_set_uint8(v_reuseFailAlloc_1645_, sizeof(void*)*10 + 8, v_component_1620_);
lean_ctor_set_uint8(v_reuseFailAlloc_1645_, sizeof(void*)*10 + 9, v_printPrefix_1621_);
lean_ctor_set_uint8(v_reuseFailAlloc_1645_, sizeof(void*)*10 + 11, v_useStdin_1622_);
lean_ctor_set_uint8(v_reuseFailAlloc_1645_, sizeof(void*)*10 + 12, v_onlyDeps_1623_);
lean_ctor_set_uint8(v_reuseFailAlloc_1645_, sizeof(void*)*10 + 13, v_onlySrcDeps_1624_);
lean_ctor_set_uint8(v_reuseFailAlloc_1645_, sizeof(void*)*10 + 14, v_depsJson_1625_);
lean_ctor_set_uint32(v_reuseFailAlloc_1645_, sizeof(void*)*10, v_trustLevel_1627_);
lean_ctor_set_uint32(v_reuseFailAlloc_1645_, sizeof(void*)*10 + 4, v_numThreads_1628_);
lean_ctor_set_uint8(v_reuseFailAlloc_1645_, sizeof(void*)*10 + 15, v_jsonOutput_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1645_, sizeof(void*)*10 + 16, v_printStats_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1645_, sizeof(void*)*10 + 17, v_run_1638_);
v___x_1643_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1644_; 
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*10 + 10, v___x_1206_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
return v___x_1644_;
}
}
}
}
else
{
lean_object* v_leanOpts_1647_; lean_object* v_forwardedArgs_1648_; uint8_t v_component_1649_; uint8_t v_printLibDir_1650_; uint8_t v_useStdin_1651_; uint8_t v_onlyDeps_1652_; uint8_t v_onlySrcDeps_1653_; uint8_t v_depsJson_1654_; lean_object* v_opts_1655_; uint32_t v_trustLevel_1656_; uint32_t v_numThreads_1657_; lean_object* v_rootDir_x3f_1658_; lean_object* v_setupFileName_x3f_1659_; lean_object* v_oleanFileName_x3f_1660_; lean_object* v_ileanFileName_x3f_1661_; lean_object* v_cFileName_x3f_1662_; lean_object* v_bcFileName_x3f_1663_; uint8_t v_jsonOutput_1664_; lean_object* v_errorOnKinds_1665_; uint8_t v_printStats_1666_; uint8_t v_run_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v_optArg_x3f_953_);
v_leanOpts_1647_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1648_ = lean_ctor_get(v_opts_951_, 1);
v_component_1649_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printLibDir_1650_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1651_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1652_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1653_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1654_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1655_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1656_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1657_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1658_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1659_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1660_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1661_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1662_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1663_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1664_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1665_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1666_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1667_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1669_ = v_opts_951_;
v_isShared_1670_ = v_isSharedCheck_1675_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_errorOnKinds_1665_);
lean_inc(v_bcFileName_x3f_1663_);
lean_inc(v_cFileName_x3f_1662_);
lean_inc(v_ileanFileName_x3f_1661_);
lean_inc(v_oleanFileName_x3f_1660_);
lean_inc(v_setupFileName_x3f_1659_);
lean_inc(v_rootDir_x3f_1658_);
lean_inc(v_opts_1655_);
lean_inc(v_forwardedArgs_1648_);
lean_inc(v_leanOpts_1647_);
lean_dec(v_opts_951_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1675_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_leanOpts_1647_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_forwardedArgs_1648_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_opts_1655_);
lean_ctor_set(v_reuseFailAlloc_1674_, 3, v_rootDir_x3f_1658_);
lean_ctor_set(v_reuseFailAlloc_1674_, 4, v_setupFileName_x3f_1659_);
lean_ctor_set(v_reuseFailAlloc_1674_, 5, v_oleanFileName_x3f_1660_);
lean_ctor_set(v_reuseFailAlloc_1674_, 6, v_ileanFileName_x3f_1661_);
lean_ctor_set(v_reuseFailAlloc_1674_, 7, v_cFileName_x3f_1662_);
lean_ctor_set(v_reuseFailAlloc_1674_, 8, v_bcFileName_x3f_1663_);
lean_ctor_set(v_reuseFailAlloc_1674_, 9, v_errorOnKinds_1665_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*10 + 8, v_component_1649_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*10 + 10, v_printLibDir_1650_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*10 + 11, v_useStdin_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*10 + 12, v_onlyDeps_1652_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*10 + 13, v_onlySrcDeps_1653_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*10 + 14, v_depsJson_1654_);
lean_ctor_set_uint32(v_reuseFailAlloc_1674_, sizeof(void*)*10, v_trustLevel_1656_);
lean_ctor_set_uint32(v_reuseFailAlloc_1674_, sizeof(void*)*10 + 4, v_numThreads_1657_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*10 + 15, v_jsonOutput_1664_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*10 + 16, v_printStats_1666_);
lean_ctor_set_uint8(v_reuseFailAlloc_1674_, sizeof(void*)*10 + 17, v_run_1667_);
v___x_1672_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; 
lean_ctor_set_uint8(v___x_1672_, sizeof(void*)*10 + 9, v___x_1204_);
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
return v___x_1673_;
}
}
}
}
else
{
lean_object* v_leanOpts_1676_; lean_object* v_forwardedArgs_1677_; uint8_t v_component_1678_; uint8_t v_printPrefix_1679_; uint8_t v_printLibDir_1680_; uint8_t v_useStdin_1681_; uint8_t v_onlyDeps_1682_; uint8_t v_onlySrcDeps_1683_; uint8_t v_depsJson_1684_; lean_object* v_opts_1685_; uint32_t v_trustLevel_1686_; uint32_t v_numThreads_1687_; lean_object* v_rootDir_x3f_1688_; lean_object* v_setupFileName_x3f_1689_; lean_object* v_oleanFileName_x3f_1690_; lean_object* v_ileanFileName_x3f_1691_; lean_object* v_cFileName_x3f_1692_; lean_object* v_bcFileName_x3f_1693_; uint8_t v_jsonOutput_1694_; lean_object* v_errorOnKinds_1695_; uint8_t v_run_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v_optArg_x3f_953_);
v_leanOpts_1676_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1677_ = lean_ctor_get(v_opts_951_, 1);
v_component_1678_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1679_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1680_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1681_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1682_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1683_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1684_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1685_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1686_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1687_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1688_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1689_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1690_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1691_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1692_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1693_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1694_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1695_ = lean_ctor_get(v_opts_951_, 9);
v_run_1696_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1698_ = v_opts_951_;
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_errorOnKinds_1695_);
lean_inc(v_bcFileName_x3f_1693_);
lean_inc(v_cFileName_x3f_1692_);
lean_inc(v_ileanFileName_x3f_1691_);
lean_inc(v_oleanFileName_x3f_1690_);
lean_inc(v_setupFileName_x3f_1689_);
lean_inc(v_rootDir_x3f_1688_);
lean_inc(v_opts_1685_);
lean_inc(v_forwardedArgs_1677_);
lean_inc(v_leanOpts_1676_);
lean_dec(v_opts_951_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_leanOpts_1676_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_forwardedArgs_1677_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_opts_1685_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v_rootDir_x3f_1688_);
lean_ctor_set(v_reuseFailAlloc_1703_, 4, v_setupFileName_x3f_1689_);
lean_ctor_set(v_reuseFailAlloc_1703_, 5, v_oleanFileName_x3f_1690_);
lean_ctor_set(v_reuseFailAlloc_1703_, 6, v_ileanFileName_x3f_1691_);
lean_ctor_set(v_reuseFailAlloc_1703_, 7, v_cFileName_x3f_1692_);
lean_ctor_set(v_reuseFailAlloc_1703_, 8, v_bcFileName_x3f_1693_);
lean_ctor_set(v_reuseFailAlloc_1703_, 9, v_errorOnKinds_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*10 + 8, v_component_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*10 + 9, v_printPrefix_1679_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*10 + 10, v_printLibDir_1680_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*10 + 11, v_useStdin_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*10 + 12, v_onlyDeps_1682_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*10 + 13, v_onlySrcDeps_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*10 + 14, v_depsJson_1684_);
lean_ctor_set_uint32(v_reuseFailAlloc_1703_, sizeof(void*)*10, v_trustLevel_1686_);
lean_ctor_set_uint32(v_reuseFailAlloc_1703_, sizeof(void*)*10 + 4, v_numThreads_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*10 + 15, v_jsonOutput_1694_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*10 + 17, v_run_1696_);
v___x_1701_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1702_; 
lean_ctor_set_uint8(v___x_1701_, sizeof(void*)*10 + 16, v___x_1202_);
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
return v___x_1702_;
}
}
}
}
else
{
lean_object* v_leanOpts_1705_; lean_object* v_forwardedArgs_1706_; uint8_t v_component_1707_; uint8_t v_printPrefix_1708_; uint8_t v_printLibDir_1709_; uint8_t v_useStdin_1710_; uint8_t v_onlyDeps_1711_; uint8_t v_onlySrcDeps_1712_; uint8_t v_depsJson_1713_; lean_object* v_opts_1714_; uint32_t v_trustLevel_1715_; uint32_t v_numThreads_1716_; lean_object* v_rootDir_x3f_1717_; lean_object* v_setupFileName_x3f_1718_; lean_object* v_oleanFileName_x3f_1719_; lean_object* v_ileanFileName_x3f_1720_; lean_object* v_cFileName_x3f_1721_; lean_object* v_bcFileName_x3f_1722_; lean_object* v_errorOnKinds_1723_; uint8_t v_printStats_1724_; uint8_t v_run_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_optArg_x3f_953_);
v_leanOpts_1705_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1706_ = lean_ctor_get(v_opts_951_, 1);
v_component_1707_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1708_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1709_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1710_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1711_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1712_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1713_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1714_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1715_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1716_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1717_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1718_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1719_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1720_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1721_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1722_ = lean_ctor_get(v_opts_951_, 8);
v_errorOnKinds_1723_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1724_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1725_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1727_ = v_opts_951_;
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_errorOnKinds_1723_);
lean_inc(v_bcFileName_x3f_1722_);
lean_inc(v_cFileName_x3f_1721_);
lean_inc(v_ileanFileName_x3f_1720_);
lean_inc(v_oleanFileName_x3f_1719_);
lean_inc(v_setupFileName_x3f_1718_);
lean_inc(v_rootDir_x3f_1717_);
lean_inc(v_opts_1714_);
lean_inc(v_forwardedArgs_1706_);
lean_inc(v_leanOpts_1705_);
lean_dec(v_opts_951_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_leanOpts_1705_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_forwardedArgs_1706_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_opts_1714_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_rootDir_x3f_1717_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v_setupFileName_x3f_1718_);
lean_ctor_set(v_reuseFailAlloc_1732_, 5, v_oleanFileName_x3f_1719_);
lean_ctor_set(v_reuseFailAlloc_1732_, 6, v_ileanFileName_x3f_1720_);
lean_ctor_set(v_reuseFailAlloc_1732_, 7, v_cFileName_x3f_1721_);
lean_ctor_set(v_reuseFailAlloc_1732_, 8, v_bcFileName_x3f_1722_);
lean_ctor_set(v_reuseFailAlloc_1732_, 9, v_errorOnKinds_1723_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*10 + 8, v_component_1707_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*10 + 9, v_printPrefix_1708_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*10 + 10, v_printLibDir_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*10 + 11, v_useStdin_1710_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*10 + 12, v_onlyDeps_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*10 + 13, v_onlySrcDeps_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*10 + 14, v_depsJson_1713_);
lean_ctor_set_uint32(v_reuseFailAlloc_1732_, sizeof(void*)*10, v_trustLevel_1715_);
lean_ctor_set_uint32(v_reuseFailAlloc_1732_, sizeof(void*)*10 + 4, v_numThreads_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*10 + 16, v_printStats_1724_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*10 + 17, v_run_1725_);
v___x_1730_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; 
lean_ctor_set_uint8(v___x_1730_, sizeof(void*)*10 + 15, v___x_1200_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
}
}
else
{
lean_object* v_leanOpts_1734_; lean_object* v_forwardedArgs_1735_; uint8_t v_component_1736_; uint8_t v_printPrefix_1737_; uint8_t v_printLibDir_1738_; uint8_t v_useStdin_1739_; uint8_t v_onlySrcDeps_1740_; lean_object* v_opts_1741_; uint32_t v_trustLevel_1742_; uint32_t v_numThreads_1743_; lean_object* v_rootDir_x3f_1744_; lean_object* v_setupFileName_x3f_1745_; lean_object* v_oleanFileName_x3f_1746_; lean_object* v_ileanFileName_x3f_1747_; lean_object* v_cFileName_x3f_1748_; lean_object* v_bcFileName_x3f_1749_; uint8_t v_jsonOutput_1750_; lean_object* v_errorOnKinds_1751_; uint8_t v_printStats_1752_; uint8_t v_run_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_optArg_x3f_953_);
v_leanOpts_1734_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1735_ = lean_ctor_get(v_opts_951_, 1);
v_component_1736_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1737_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1738_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1739_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlySrcDeps_1740_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_opts_1741_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1742_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1743_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1744_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1745_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1746_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1747_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1748_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1749_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1750_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1751_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1752_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1753_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1755_ = v_opts_951_;
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_errorOnKinds_1751_);
lean_inc(v_bcFileName_x3f_1749_);
lean_inc(v_cFileName_x3f_1748_);
lean_inc(v_ileanFileName_x3f_1747_);
lean_inc(v_oleanFileName_x3f_1746_);
lean_inc(v_setupFileName_x3f_1745_);
lean_inc(v_rootDir_x3f_1744_);
lean_inc(v_opts_1741_);
lean_inc(v_forwardedArgs_1735_);
lean_inc(v_leanOpts_1734_);
lean_dec(v_opts_951_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_leanOpts_1734_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_forwardedArgs_1735_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_opts_1741_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v_rootDir_x3f_1744_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v_setupFileName_x3f_1745_);
lean_ctor_set(v_reuseFailAlloc_1760_, 5, v_oleanFileName_x3f_1746_);
lean_ctor_set(v_reuseFailAlloc_1760_, 6, v_ileanFileName_x3f_1747_);
lean_ctor_set(v_reuseFailAlloc_1760_, 7, v_cFileName_x3f_1748_);
lean_ctor_set(v_reuseFailAlloc_1760_, 8, v_bcFileName_x3f_1749_);
lean_ctor_set(v_reuseFailAlloc_1760_, 9, v_errorOnKinds_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*10 + 8, v_component_1736_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*10 + 9, v_printPrefix_1737_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*10 + 10, v_printLibDir_1738_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*10 + 11, v_useStdin_1739_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*10 + 13, v_onlySrcDeps_1740_);
lean_ctor_set_uint32(v_reuseFailAlloc_1760_, sizeof(void*)*10, v_trustLevel_1742_);
lean_ctor_set_uint32(v_reuseFailAlloc_1760_, sizeof(void*)*10 + 4, v_numThreads_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*10 + 15, v_jsonOutput_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*10 + 16, v_printStats_1752_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*10 + 17, v_run_1753_);
v___x_1758_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; 
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*10 + 12, v___x_1198_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*10 + 14, v___x_1198_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_leanOpts_1762_; lean_object* v_forwardedArgs_1763_; uint8_t v_component_1764_; uint8_t v_printPrefix_1765_; uint8_t v_printLibDir_1766_; uint8_t v_useStdin_1767_; uint8_t v_onlyDeps_1768_; uint8_t v_depsJson_1769_; lean_object* v_opts_1770_; uint32_t v_trustLevel_1771_; uint32_t v_numThreads_1772_; lean_object* v_rootDir_x3f_1773_; lean_object* v_setupFileName_x3f_1774_; lean_object* v_oleanFileName_x3f_1775_; lean_object* v_ileanFileName_x3f_1776_; lean_object* v_cFileName_x3f_1777_; lean_object* v_bcFileName_x3f_1778_; uint8_t v_jsonOutput_1779_; lean_object* v_errorOnKinds_1780_; uint8_t v_printStats_1781_; uint8_t v_run_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1790_; 
lean_dec(v_optArg_x3f_953_);
v_leanOpts_1762_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1763_ = lean_ctor_get(v_opts_951_, 1);
v_component_1764_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1765_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1766_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1767_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1768_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_depsJson_1769_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1770_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1771_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1772_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1773_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1774_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1775_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1776_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1777_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1778_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1779_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1780_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1781_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1782_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1784_ = v_opts_951_;
v_isShared_1785_ = v_isSharedCheck_1790_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_errorOnKinds_1780_);
lean_inc(v_bcFileName_x3f_1778_);
lean_inc(v_cFileName_x3f_1777_);
lean_inc(v_ileanFileName_x3f_1776_);
lean_inc(v_oleanFileName_x3f_1775_);
lean_inc(v_setupFileName_x3f_1774_);
lean_inc(v_rootDir_x3f_1773_);
lean_inc(v_opts_1770_);
lean_inc(v_forwardedArgs_1763_);
lean_inc(v_leanOpts_1762_);
lean_dec(v_opts_951_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1790_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_leanOpts_1762_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_forwardedArgs_1763_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_opts_1770_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v_rootDir_x3f_1773_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v_setupFileName_x3f_1774_);
lean_ctor_set(v_reuseFailAlloc_1789_, 5, v_oleanFileName_x3f_1775_);
lean_ctor_set(v_reuseFailAlloc_1789_, 6, v_ileanFileName_x3f_1776_);
lean_ctor_set(v_reuseFailAlloc_1789_, 7, v_cFileName_x3f_1777_);
lean_ctor_set(v_reuseFailAlloc_1789_, 8, v_bcFileName_x3f_1778_);
lean_ctor_set(v_reuseFailAlloc_1789_, 9, v_errorOnKinds_1780_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*10 + 8, v_component_1764_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*10 + 9, v_printPrefix_1765_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*10 + 10, v_printLibDir_1766_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*10 + 11, v_useStdin_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*10 + 12, v_onlyDeps_1768_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*10 + 14, v_depsJson_1769_);
lean_ctor_set_uint32(v_reuseFailAlloc_1789_, sizeof(void*)*10, v_trustLevel_1771_);
lean_ctor_set_uint32(v_reuseFailAlloc_1789_, sizeof(void*)*10 + 4, v_numThreads_1772_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*10 + 15, v_jsonOutput_1779_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*10 + 16, v_printStats_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*10 + 17, v_run_1782_);
v___x_1787_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; 
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*10 + 13, v___x_1196_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
}
}
}
else
{
lean_object* v_leanOpts_1791_; lean_object* v_forwardedArgs_1792_; uint8_t v_component_1793_; uint8_t v_printPrefix_1794_; uint8_t v_printLibDir_1795_; uint8_t v_useStdin_1796_; uint8_t v_onlySrcDeps_1797_; uint8_t v_depsJson_1798_; lean_object* v_opts_1799_; uint32_t v_trustLevel_1800_; uint32_t v_numThreads_1801_; lean_object* v_rootDir_x3f_1802_; lean_object* v_setupFileName_x3f_1803_; lean_object* v_oleanFileName_x3f_1804_; lean_object* v_ileanFileName_x3f_1805_; lean_object* v_cFileName_x3f_1806_; lean_object* v_bcFileName_x3f_1807_; uint8_t v_jsonOutput_1808_; lean_object* v_errorOnKinds_1809_; uint8_t v_printStats_1810_; uint8_t v_run_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1819_; 
lean_dec(v_optArg_x3f_953_);
v_leanOpts_1791_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1792_ = lean_ctor_get(v_opts_951_, 1);
v_component_1793_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1794_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1795_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1796_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlySrcDeps_1797_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1798_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1799_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1800_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1801_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1802_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1803_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1804_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1805_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1806_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1807_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1808_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1809_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1810_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1811_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1813_ = v_opts_951_;
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_errorOnKinds_1809_);
lean_inc(v_bcFileName_x3f_1807_);
lean_inc(v_cFileName_x3f_1806_);
lean_inc(v_ileanFileName_x3f_1805_);
lean_inc(v_oleanFileName_x3f_1804_);
lean_inc(v_setupFileName_x3f_1803_);
lean_inc(v_rootDir_x3f_1802_);
lean_inc(v_opts_1799_);
lean_inc(v_forwardedArgs_1792_);
lean_inc(v_leanOpts_1791_);
lean_dec(v_opts_951_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_leanOpts_1791_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_forwardedArgs_1792_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_opts_1799_);
lean_ctor_set(v_reuseFailAlloc_1818_, 3, v_rootDir_x3f_1802_);
lean_ctor_set(v_reuseFailAlloc_1818_, 4, v_setupFileName_x3f_1803_);
lean_ctor_set(v_reuseFailAlloc_1818_, 5, v_oleanFileName_x3f_1804_);
lean_ctor_set(v_reuseFailAlloc_1818_, 6, v_ileanFileName_x3f_1805_);
lean_ctor_set(v_reuseFailAlloc_1818_, 7, v_cFileName_x3f_1806_);
lean_ctor_set(v_reuseFailAlloc_1818_, 8, v_bcFileName_x3f_1807_);
lean_ctor_set(v_reuseFailAlloc_1818_, 9, v_errorOnKinds_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*10 + 8, v_component_1793_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*10 + 9, v_printPrefix_1794_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*10 + 10, v_printLibDir_1795_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*10 + 11, v_useStdin_1796_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*10 + 13, v_onlySrcDeps_1797_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*10 + 14, v_depsJson_1798_);
lean_ctor_set_uint32(v_reuseFailAlloc_1818_, sizeof(void*)*10, v_trustLevel_1800_);
lean_ctor_set_uint32(v_reuseFailAlloc_1818_, sizeof(void*)*10 + 4, v_numThreads_1801_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*10 + 15, v_jsonOutput_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*10 + 16, v_printStats_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*10 + 17, v_run_1811_);
v___x_1816_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1817_; 
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*10 + 12, v___x_1194_);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
}
}
}
else
{
lean_object* v_leanOpts_1820_; lean_object* v_forwardedArgs_1821_; uint8_t v_component_1822_; uint8_t v_printPrefix_1823_; uint8_t v_printLibDir_1824_; uint8_t v_useStdin_1825_; uint8_t v_onlyDeps_1826_; uint8_t v_onlySrcDeps_1827_; uint8_t v_depsJson_1828_; lean_object* v_opts_1829_; uint32_t v_trustLevel_1830_; uint32_t v_numThreads_1831_; lean_object* v_rootDir_x3f_1832_; lean_object* v_setupFileName_x3f_1833_; lean_object* v_oleanFileName_x3f_1834_; lean_object* v_ileanFileName_x3f_1835_; lean_object* v_cFileName_x3f_1836_; lean_object* v_bcFileName_x3f_1837_; uint8_t v_jsonOutput_1838_; lean_object* v_errorOnKinds_1839_; uint8_t v_printStats_1840_; uint8_t v_run_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_optArg_x3f_953_);
v_leanOpts_1820_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1821_ = lean_ctor_get(v_opts_951_, 1);
v_component_1822_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1823_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1824_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1825_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1826_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1827_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1828_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1829_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1830_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1831_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1832_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1833_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1834_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1835_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1836_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1837_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1838_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1839_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1840_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1841_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1843_ = v_opts_951_;
v_isShared_1844_ = v_isSharedCheck_1851_;
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
lean_inc(v_opts_1829_);
lean_inc(v_forwardedArgs_1821_);
lean_inc(v_leanOpts_1820_);
lean_dec(v_opts_951_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1851_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1845_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_1846_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_1820_, v___x_1845_, v___x_1190_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1846_);
v___x_1848_ = v___x_1843_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_forwardedArgs_1821_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_opts_1829_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_rootDir_x3f_1832_);
lean_ctor_set(v_reuseFailAlloc_1850_, 4, v_setupFileName_x3f_1833_);
lean_ctor_set(v_reuseFailAlloc_1850_, 5, v_oleanFileName_x3f_1834_);
lean_ctor_set(v_reuseFailAlloc_1850_, 6, v_ileanFileName_x3f_1835_);
lean_ctor_set(v_reuseFailAlloc_1850_, 7, v_cFileName_x3f_1836_);
lean_ctor_set(v_reuseFailAlloc_1850_, 8, v_bcFileName_x3f_1837_);
lean_ctor_set(v_reuseFailAlloc_1850_, 9, v_errorOnKinds_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*10 + 8, v_component_1822_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*10 + 9, v_printPrefix_1823_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*10 + 10, v_printLibDir_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*10 + 11, v_useStdin_1825_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*10 + 12, v_onlyDeps_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*10 + 13, v_onlySrcDeps_1827_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*10 + 14, v_depsJson_1828_);
lean_ctor_set_uint32(v_reuseFailAlloc_1850_, sizeof(void*)*10, v_trustLevel_1830_);
lean_ctor_set_uint32(v_reuseFailAlloc_1850_, sizeof(void*)*10 + 4, v_numThreads_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*10 + 15, v_jsonOutput_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*10 + 16, v_printStats_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*10 + 17, v_run_1841_);
v___x_1848_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1853_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1852_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1904_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1904_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1904_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = lean_string_utf8_byte_size(v_a_1854_);
lean_inc(v_a_1854_);
v___x_1860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1860_, 0, v_a_1854_);
lean_ctor_set(v___x_1860_, 1, v___x_1858_);
lean_ctor_set(v___x_1860_, 2, v___x_1859_);
v___x_1861_ = l_String_Slice_toNat_x3f(v___x_1860_);
lean_dec_ref(v___x_1860_);
if (lean_obj_tag(v___x_1861_) == 1)
{
lean_object* v_val_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v_val_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_val_1862_);
lean_dec_ref(v___x_1861_);
v___x_1863_ = lean_cstr_to_nat("4294967296");
v___x_1864_ = lean_nat_dec_lt(v_val_1862_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
lean_dec(v_val_1862_);
lean_del_object(v___x_1856_);
lean_dec(v_a_1854_);
lean_dec_ref(v_opts_951_);
v___x_1865_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1866_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1865_);
lean_dec_ref(v___x_1866_);
goto v___jp_1021_;
}
else
{
lean_object* v_leanOpts_1867_; lean_object* v_forwardedArgs_1868_; uint8_t v_component_1869_; uint8_t v_printPrefix_1870_; uint8_t v_printLibDir_1871_; uint8_t v_useStdin_1872_; uint8_t v_onlyDeps_1873_; uint8_t v_onlySrcDeps_1874_; uint8_t v_depsJson_1875_; lean_object* v_opts_1876_; uint32_t v_numThreads_1877_; lean_object* v_rootDir_x3f_1878_; lean_object* v_setupFileName_x3f_1879_; lean_object* v_oleanFileName_x3f_1880_; lean_object* v_ileanFileName_x3f_1881_; lean_object* v_cFileName_x3f_1882_; lean_object* v_bcFileName_x3f_1883_; uint8_t v_jsonOutput_1884_; lean_object* v_errorOnKinds_1885_; uint8_t v_printStats_1886_; uint8_t v_run_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1901_; 
v_leanOpts_1867_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1868_ = lean_ctor_get(v_opts_951_, 1);
v_component_1869_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1870_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1871_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1872_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1873_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1874_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1875_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1876_ = lean_ctor_get(v_opts_951_, 2);
v_numThreads_1877_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1878_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1879_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1880_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1881_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1882_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1883_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1884_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1885_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1886_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1887_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1889_ = v_opts_951_;
v_isShared_1890_ = v_isSharedCheck_1901_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_errorOnKinds_1885_);
lean_inc(v_bcFileName_x3f_1883_);
lean_inc(v_cFileName_x3f_1882_);
lean_inc(v_ileanFileName_x3f_1881_);
lean_inc(v_oleanFileName_x3f_1880_);
lean_inc(v_setupFileName_x3f_1879_);
lean_inc(v_rootDir_x3f_1878_);
lean_inc(v_opts_1876_);
lean_inc(v_forwardedArgs_1868_);
lean_inc(v_leanOpts_1867_);
lean_dec(v_opts_951_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1901_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
uint32_t v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1891_ = lean_uint32_of_nat(v_val_1862_);
lean_dec(v_val_1862_);
v___x_1892_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1893_ = lean_string_append(v___x_1892_, v_a_1854_);
lean_dec(v_a_1854_);
v___x_1894_ = lean_array_push(v_forwardedArgs_1868_, v___x_1893_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 1, v___x_1894_);
v___x_1896_ = v___x_1889_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_leanOpts_1867_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1900_, 2, v_opts_1876_);
lean_ctor_set(v_reuseFailAlloc_1900_, 3, v_rootDir_x3f_1878_);
lean_ctor_set(v_reuseFailAlloc_1900_, 4, v_setupFileName_x3f_1879_);
lean_ctor_set(v_reuseFailAlloc_1900_, 5, v_oleanFileName_x3f_1880_);
lean_ctor_set(v_reuseFailAlloc_1900_, 6, v_ileanFileName_x3f_1881_);
lean_ctor_set(v_reuseFailAlloc_1900_, 7, v_cFileName_x3f_1882_);
lean_ctor_set(v_reuseFailAlloc_1900_, 8, v_bcFileName_x3f_1883_);
lean_ctor_set(v_reuseFailAlloc_1900_, 9, v_errorOnKinds_1885_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*10 + 8, v_component_1869_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*10 + 9, v_printPrefix_1870_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*10 + 10, v_printLibDir_1871_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*10 + 11, v_useStdin_1872_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*10 + 12, v_onlyDeps_1873_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*10 + 13, v_onlySrcDeps_1874_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*10 + 14, v_depsJson_1875_);
lean_ctor_set_uint32(v_reuseFailAlloc_1900_, sizeof(void*)*10 + 4, v_numThreads_1877_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*10 + 15, v_jsonOutput_1884_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*10 + 16, v_printStats_1886_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*10 + 17, v_run_1887_);
v___x_1896_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1898_; 
lean_ctor_set_uint32(v___x_1896_, sizeof(void*)*10, v___x_1891_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1896_);
v___x_1898_ = v___x_1856_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec(v___x_1861_);
lean_del_object(v___x_1856_);
lean_dec(v_a_1854_);
lean_dec_ref(v_opts_951_);
v___x_1902_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_1903_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1902_);
lean_dec_ref(v___x_1903_);
goto v___jp_1018_;
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
lean_dec_ref(v_opts_951_);
v_a_1905_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1905_);
lean_dec_ref(v___x_1853_);
v___x_1909_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1910_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1909_);
lean_dec_ref(v___x_1910_);
goto v___jp_1906_;
v___jp_1906_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_io_error_to_string(v_a_1905_);
v___x_1908_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1907_);
lean_dec_ref(v___x_1908_);
goto v___jp_1015_;
}
}
}
}
else
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_1912_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1911_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1961_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1961_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1961_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1917_ = lean_unsigned_to_nat(0u);
v___x_1918_ = lean_string_utf8_byte_size(v_a_1913_);
lean_inc(v_a_1913_);
v___x_1919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1919_, 0, v_a_1913_);
lean_ctor_set(v___x_1919_, 1, v___x_1917_);
lean_ctor_set(v___x_1919_, 2, v___x_1918_);
v___x_1920_ = l_String_Slice_toNat_x3f(v___x_1919_);
lean_dec_ref(v___x_1919_);
if (lean_obj_tag(v___x_1920_) == 1)
{
lean_object* v_val_1921_; lean_object* v_leanOpts_1922_; lean_object* v_forwardedArgs_1923_; uint8_t v_component_1924_; uint8_t v_printPrefix_1925_; uint8_t v_printLibDir_1926_; uint8_t v_useStdin_1927_; uint8_t v_onlyDeps_1928_; uint8_t v_onlySrcDeps_1929_; uint8_t v_depsJson_1930_; lean_object* v_opts_1931_; uint32_t v_trustLevel_1932_; uint32_t v_numThreads_1933_; lean_object* v_rootDir_x3f_1934_; lean_object* v_setupFileName_x3f_1935_; lean_object* v_oleanFileName_x3f_1936_; lean_object* v_ileanFileName_x3f_1937_; lean_object* v_cFileName_x3f_1938_; lean_object* v_bcFileName_x3f_1939_; uint8_t v_jsonOutput_1940_; lean_object* v_errorOnKinds_1941_; uint8_t v_printStats_1942_; uint8_t v_run_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1958_; 
v_val_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_val_1921_);
lean_dec_ref(v___x_1920_);
v_leanOpts_1922_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1923_ = lean_ctor_get(v_opts_951_, 1);
v_component_1924_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1925_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1926_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1927_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1928_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1929_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1930_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1931_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1932_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1933_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1934_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1935_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1936_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1937_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1938_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1939_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1940_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1941_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1942_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_1943_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1945_ = v_opts_951_;
v_isShared_1946_ = v_isSharedCheck_1958_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_errorOnKinds_1941_);
lean_inc(v_bcFileName_x3f_1939_);
lean_inc(v_cFileName_x3f_1938_);
lean_inc(v_ileanFileName_x3f_1937_);
lean_inc(v_oleanFileName_x3f_1936_);
lean_inc(v_setupFileName_x3f_1935_);
lean_inc(v_rootDir_x3f_1934_);
lean_inc(v_opts_1931_);
lean_inc(v_forwardedArgs_1923_);
lean_inc(v_leanOpts_1922_);
lean_dec(v_opts_951_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1958_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1947_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_1948_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_leanOpts_1922_, v___x_1947_, v_val_1921_);
v___x_1949_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_1950_ = lean_string_append(v___x_1949_, v_a_1913_);
lean_dec(v_a_1913_);
v___x_1951_ = lean_array_push(v_forwardedArgs_1923_, v___x_1950_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___x_1951_);
lean_ctor_set(v___x_1945_, 0, v___x_1948_);
v___x_1953_ = v___x_1945_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_opts_1931_);
lean_ctor_set(v_reuseFailAlloc_1957_, 3, v_rootDir_x3f_1934_);
lean_ctor_set(v_reuseFailAlloc_1957_, 4, v_setupFileName_x3f_1935_);
lean_ctor_set(v_reuseFailAlloc_1957_, 5, v_oleanFileName_x3f_1936_);
lean_ctor_set(v_reuseFailAlloc_1957_, 6, v_ileanFileName_x3f_1937_);
lean_ctor_set(v_reuseFailAlloc_1957_, 7, v_cFileName_x3f_1938_);
lean_ctor_set(v_reuseFailAlloc_1957_, 8, v_bcFileName_x3f_1939_);
lean_ctor_set(v_reuseFailAlloc_1957_, 9, v_errorOnKinds_1941_);
lean_ctor_set_uint8(v_reuseFailAlloc_1957_, sizeof(void*)*10 + 8, v_component_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1957_, sizeof(void*)*10 + 9, v_printPrefix_1925_);
lean_ctor_set_uint8(v_reuseFailAlloc_1957_, sizeof(void*)*10 + 10, v_printLibDir_1926_);
lean_ctor_set_uint8(v_reuseFailAlloc_1957_, sizeof(void*)*10 + 11, v_useStdin_1927_);
lean_ctor_set_uint8(v_reuseFailAlloc_1957_, sizeof(void*)*10 + 12, v_onlyDeps_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_1957_, sizeof(void*)*10 + 13, v_onlySrcDeps_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_1957_, sizeof(void*)*10 + 14, v_depsJson_1930_);
lean_ctor_set_uint32(v_reuseFailAlloc_1957_, sizeof(void*)*10, v_trustLevel_1932_);
lean_ctor_set_uint32(v_reuseFailAlloc_1957_, sizeof(void*)*10 + 4, v_numThreads_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1957_, sizeof(void*)*10 + 15, v_jsonOutput_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1957_, sizeof(void*)*10 + 16, v_printStats_1942_);
lean_ctor_set_uint8(v_reuseFailAlloc_1957_, sizeof(void*)*10 + 17, v_run_1943_);
v___x_1953_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1955_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1953_);
v___x_1955_ = v___x_1915_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
lean_dec(v___x_1920_);
lean_del_object(v___x_1915_);
lean_dec(v_a_1913_);
lean_dec_ref(v_opts_951_);
v___x_1959_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_1960_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1959_);
lean_dec_ref(v___x_1960_);
goto v___jp_1110_;
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_dec_ref(v_opts_951_);
v_a_1962_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v___x_1912_);
v___x_1966_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1967_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1966_);
lean_dec_ref(v___x_1967_);
goto v___jp_1963_;
v___jp_1963_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = lean_io_error_to_string(v_a_1962_);
v___x_1965_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1964_);
lean_dec_ref(v___x_1965_);
goto v___jp_1116_;
}
}
}
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_1969_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1968_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2018_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_2018_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2018_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_string_utf8_byte_size(v_a_1970_);
lean_inc(v_a_1970_);
v___x_1976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1976_, 0, v_a_1970_);
lean_ctor_set(v___x_1976_, 1, v___x_1974_);
lean_ctor_set(v___x_1976_, 2, v___x_1975_);
v___x_1977_ = l_String_Slice_toNat_x3f(v___x_1976_);
lean_dec_ref(v___x_1976_);
if (lean_obj_tag(v___x_1977_) == 1)
{
lean_object* v_val_1978_; lean_object* v_leanOpts_1979_; lean_object* v_forwardedArgs_1980_; uint8_t v_component_1981_; uint8_t v_printPrefix_1982_; uint8_t v_printLibDir_1983_; uint8_t v_useStdin_1984_; uint8_t v_onlyDeps_1985_; uint8_t v_onlySrcDeps_1986_; uint8_t v_depsJson_1987_; lean_object* v_opts_1988_; uint32_t v_trustLevel_1989_; uint32_t v_numThreads_1990_; lean_object* v_rootDir_x3f_1991_; lean_object* v_setupFileName_x3f_1992_; lean_object* v_oleanFileName_x3f_1993_; lean_object* v_ileanFileName_x3f_1994_; lean_object* v_cFileName_x3f_1995_; lean_object* v_bcFileName_x3f_1996_; uint8_t v_jsonOutput_1997_; lean_object* v_errorOnKinds_1998_; uint8_t v_printStats_1999_; uint8_t v_run_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2015_; 
v_val_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_val_1978_);
lean_dec_ref(v___x_1977_);
v_leanOpts_1979_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_1980_ = lean_ctor_get(v_opts_951_, 1);
v_component_1981_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_1982_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_1983_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_1984_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_1985_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1986_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_1987_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_1988_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_1989_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_1990_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1991_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_1992_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_1993_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_1994_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_1995_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_1996_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_1997_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_1998_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_1999_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_2000_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2002_ = v_opts_951_;
v_isShared_2003_ = v_isSharedCheck_2015_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_errorOnKinds_1998_);
lean_inc(v_bcFileName_x3f_1996_);
lean_inc(v_cFileName_x3f_1995_);
lean_inc(v_ileanFileName_x3f_1994_);
lean_inc(v_oleanFileName_x3f_1993_);
lean_inc(v_setupFileName_x3f_1992_);
lean_inc(v_rootDir_x3f_1991_);
lean_inc(v_opts_1988_);
lean_inc(v_forwardedArgs_1980_);
lean_inc(v_leanOpts_1979_);
lean_dec(v_opts_951_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2015_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2004_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_2005_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_leanOpts_1979_, v___x_2004_, v_val_1978_);
v___x_2006_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_2007_ = lean_string_append(v___x_2006_, v_a_1970_);
lean_dec(v_a_1970_);
v___x_2008_ = lean_array_push(v_forwardedArgs_1980_, v___x_2007_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 1, v___x_2008_);
lean_ctor_set(v___x_2002_, 0, v___x_2005_);
v___x_2010_ = v___x_2002_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_opts_1988_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_rootDir_x3f_1991_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_setupFileName_x3f_1992_);
lean_ctor_set(v_reuseFailAlloc_2014_, 5, v_oleanFileName_x3f_1993_);
lean_ctor_set(v_reuseFailAlloc_2014_, 6, v_ileanFileName_x3f_1994_);
lean_ctor_set(v_reuseFailAlloc_2014_, 7, v_cFileName_x3f_1995_);
lean_ctor_set(v_reuseFailAlloc_2014_, 8, v_bcFileName_x3f_1996_);
lean_ctor_set(v_reuseFailAlloc_2014_, 9, v_errorOnKinds_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*10 + 8, v_component_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*10 + 9, v_printPrefix_1982_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*10 + 10, v_printLibDir_1983_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*10 + 11, v_useStdin_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*10 + 12, v_onlyDeps_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*10 + 13, v_onlySrcDeps_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*10 + 14, v_depsJson_1987_);
lean_ctor_set_uint32(v_reuseFailAlloc_2014_, sizeof(void*)*10, v_trustLevel_1989_);
lean_ctor_set_uint32(v_reuseFailAlloc_2014_, sizeof(void*)*10 + 4, v_numThreads_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*10 + 15, v_jsonOutput_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*10 + 16, v_printStats_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*10 + 17, v_run_2000_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_2010_);
v___x_2012_ = v___x_1972_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_dec(v___x_1977_);
lean_del_object(v___x_1972_);
lean_dec(v_a_1970_);
lean_dec_ref(v_opts_951_);
v___x_2016_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_2017_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2016_);
lean_dec_ref(v___x_2017_);
goto v___jp_1009_;
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
lean_dec_ref(v_opts_951_);
v_a_2019_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_2019_);
lean_dec_ref(v___x_1969_);
v___x_2023_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2024_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2023_);
lean_dec_ref(v___x_2024_);
goto v___jp_2020_;
v___jp_2020_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = lean_io_error_to_string(v_a_2019_);
v___x_2022_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2021_);
lean_dec_ref(v___x_2022_);
goto v___jp_1006_;
}
}
}
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_2026_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2025_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2067_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2067_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2067_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v_leanOpts_2031_; lean_object* v_forwardedArgs_2032_; uint8_t v_component_2033_; uint8_t v_printPrefix_2034_; uint8_t v_printLibDir_2035_; uint8_t v_useStdin_2036_; uint8_t v_onlyDeps_2037_; uint8_t v_onlySrcDeps_2038_; uint8_t v_depsJson_2039_; lean_object* v_opts_2040_; uint32_t v_trustLevel_2041_; uint32_t v_numThreads_2042_; lean_object* v_setupFileName_x3f_2043_; lean_object* v_oleanFileName_x3f_2044_; lean_object* v_ileanFileName_x3f_2045_; lean_object* v_cFileName_x3f_2046_; lean_object* v_bcFileName_x3f_2047_; uint8_t v_jsonOutput_2048_; lean_object* v_errorOnKinds_2049_; uint8_t v_printStats_2050_; uint8_t v_run_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2065_; 
v_leanOpts_2031_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_2032_ = lean_ctor_get(v_opts_951_, 1);
v_component_2033_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_2034_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_2035_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_2036_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_2037_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2038_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_2039_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_2040_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_2041_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_2042_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_setupFileName_x3f_2043_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_2044_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_2045_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_2046_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_2047_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_2048_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_2049_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_2050_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_2051_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v_opts_951_, 3);
lean_dec(v_unused_2066_);
v___x_2053_ = v_opts_951_;
v_isShared_2054_ = v_isSharedCheck_2065_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_errorOnKinds_2049_);
lean_inc(v_bcFileName_x3f_2047_);
lean_inc(v_cFileName_x3f_2046_);
lean_inc(v_ileanFileName_x3f_2045_);
lean_inc(v_oleanFileName_x3f_2044_);
lean_inc(v_setupFileName_x3f_2043_);
lean_inc(v_opts_2040_);
lean_inc(v_forwardedArgs_2032_);
lean_inc(v_leanOpts_2031_);
lean_dec(v_opts_951_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2065_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2055_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2056_ = lean_string_append(v___x_2055_, v_a_2027_);
v___x_2057_ = lean_array_push(v_forwardedArgs_2032_, v___x_2056_);
v___x_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_a_2027_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 3, v___x_2058_);
lean_ctor_set(v___x_2053_, 1, v___x_2057_);
v___x_2060_ = v___x_2053_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_leanOpts_2031_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_opts_2040_);
lean_ctor_set(v_reuseFailAlloc_2064_, 3, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2064_, 4, v_setupFileName_x3f_2043_);
lean_ctor_set(v_reuseFailAlloc_2064_, 5, v_oleanFileName_x3f_2044_);
lean_ctor_set(v_reuseFailAlloc_2064_, 6, v_ileanFileName_x3f_2045_);
lean_ctor_set(v_reuseFailAlloc_2064_, 7, v_cFileName_x3f_2046_);
lean_ctor_set(v_reuseFailAlloc_2064_, 8, v_bcFileName_x3f_2047_);
lean_ctor_set(v_reuseFailAlloc_2064_, 9, v_errorOnKinds_2049_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 8, v_component_2033_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 9, v_printPrefix_2034_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 10, v_printLibDir_2035_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 11, v_useStdin_2036_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 12, v_onlyDeps_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 13, v_onlySrcDeps_2038_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 14, v_depsJson_2039_);
lean_ctor_set_uint32(v_reuseFailAlloc_2064_, sizeof(void*)*10, v_trustLevel_2041_);
lean_ctor_set_uint32(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 4, v_numThreads_2042_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 15, v_jsonOutput_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 16, v_printStats_2050_);
lean_ctor_set_uint8(v_reuseFailAlloc_2064_, sizeof(void*)*10 + 17, v_run_2051_);
v___x_2060_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2062_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2060_);
v___x_2062_ = v___x_2029_;
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
lean_dec_ref(v_opts_951_);
v_a_2068_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2068_);
lean_dec_ref(v___x_2026_);
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
goto v___jp_1122_;
}
}
}
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2075_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2074_, v_optArg_x3f_953_);
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
lean_object* v_leanOpts_2080_; lean_object* v_forwardedArgs_2081_; uint8_t v_component_2082_; uint8_t v_printPrefix_2083_; uint8_t v_printLibDir_2084_; uint8_t v_useStdin_2085_; uint8_t v_onlyDeps_2086_; uint8_t v_onlySrcDeps_2087_; uint8_t v_depsJson_2088_; lean_object* v_opts_2089_; uint32_t v_trustLevel_2090_; uint32_t v_numThreads_2091_; lean_object* v_rootDir_x3f_2092_; lean_object* v_setupFileName_x3f_2093_; lean_object* v_oleanFileName_x3f_2094_; lean_object* v_cFileName_x3f_2095_; lean_object* v_bcFileName_x3f_2096_; uint8_t v_jsonOutput_2097_; lean_object* v_errorOnKinds_2098_; uint8_t v_printStats_2099_; uint8_t v_run_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2111_; 
v_leanOpts_2080_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_2081_ = lean_ctor_get(v_opts_951_, 1);
v_component_2082_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_2083_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_2084_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_2085_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_2086_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2087_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_2088_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_2089_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_2090_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_2091_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2092_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_2093_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_2094_ = lean_ctor_get(v_opts_951_, 5);
v_cFileName_x3f_2095_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_2096_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_2097_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_2098_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_2099_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_2100_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v_opts_951_, 6);
lean_dec(v_unused_2112_);
v___x_2102_ = v_opts_951_;
v_isShared_2103_ = v_isSharedCheck_2111_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_errorOnKinds_2098_);
lean_inc(v_bcFileName_x3f_2096_);
lean_inc(v_cFileName_x3f_2095_);
lean_inc(v_oleanFileName_x3f_2094_);
lean_inc(v_setupFileName_x3f_2093_);
lean_inc(v_rootDir_x3f_2092_);
lean_inc(v_opts_2089_);
lean_inc(v_forwardedArgs_2081_);
lean_inc(v_leanOpts_2080_);
lean_dec(v_opts_951_);
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
lean_ctor_set(v___x_2102_, 6, v___x_2104_);
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
lean_ctor_set(v_reuseFailAlloc_2110_, 5, v_oleanFileName_x3f_2094_);
lean_ctor_set(v_reuseFailAlloc_2110_, 6, v___x_2104_);
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
lean_dec_ref(v_opts_951_);
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
goto v___jp_1000_;
}
}
}
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2121_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2120_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2159_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2159_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2159_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v_leanOpts_2126_; lean_object* v_forwardedArgs_2127_; uint8_t v_component_2128_; uint8_t v_printPrefix_2129_; uint8_t v_printLibDir_2130_; uint8_t v_useStdin_2131_; uint8_t v_onlyDeps_2132_; uint8_t v_onlySrcDeps_2133_; uint8_t v_depsJson_2134_; lean_object* v_opts_2135_; uint32_t v_trustLevel_2136_; uint32_t v_numThreads_2137_; lean_object* v_rootDir_x3f_2138_; lean_object* v_setupFileName_x3f_2139_; lean_object* v_ileanFileName_x3f_2140_; lean_object* v_cFileName_x3f_2141_; lean_object* v_bcFileName_x3f_2142_; uint8_t v_jsonOutput_2143_; lean_object* v_errorOnKinds_2144_; uint8_t v_printStats_2145_; uint8_t v_run_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2157_; 
v_leanOpts_2126_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_2127_ = lean_ctor_get(v_opts_951_, 1);
v_component_2128_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_2129_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_2130_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_2131_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_2132_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2133_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_2134_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_2135_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_2136_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_2137_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2138_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_2139_ = lean_ctor_get(v_opts_951_, 4);
v_ileanFileName_x3f_2140_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_2141_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_2142_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_2143_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_2144_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_2145_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_2146_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; 
v_unused_2158_ = lean_ctor_get(v_opts_951_, 5);
lean_dec(v_unused_2158_);
v___x_2148_ = v_opts_951_;
v_isShared_2149_ = v_isSharedCheck_2157_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_errorOnKinds_2144_);
lean_inc(v_bcFileName_x3f_2142_);
lean_inc(v_cFileName_x3f_2141_);
lean_inc(v_ileanFileName_x3f_2140_);
lean_inc(v_setupFileName_x3f_2139_);
lean_inc(v_rootDir_x3f_2138_);
lean_inc(v_opts_2135_);
lean_inc(v_forwardedArgs_2127_);
lean_inc(v_leanOpts_2126_);
lean_dec(v_opts_951_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2157_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2150_, 0, v_a_2122_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 5, v___x_2150_);
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_leanOpts_2126_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_forwardedArgs_2127_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_opts_2135_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v_rootDir_x3f_2138_);
lean_ctor_set(v_reuseFailAlloc_2156_, 4, v_setupFileName_x3f_2139_);
lean_ctor_set(v_reuseFailAlloc_2156_, 5, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2156_, 6, v_ileanFileName_x3f_2140_);
lean_ctor_set(v_reuseFailAlloc_2156_, 7, v_cFileName_x3f_2141_);
lean_ctor_set(v_reuseFailAlloc_2156_, 8, v_bcFileName_x3f_2142_);
lean_ctor_set(v_reuseFailAlloc_2156_, 9, v_errorOnKinds_2144_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*10 + 8, v_component_2128_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*10 + 9, v_printPrefix_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*10 + 10, v_printLibDir_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*10 + 11, v_useStdin_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*10 + 12, v_onlyDeps_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*10 + 13, v_onlySrcDeps_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*10 + 14, v_depsJson_2134_);
lean_ctor_set_uint32(v_reuseFailAlloc_2156_, sizeof(void*)*10, v_trustLevel_2136_);
lean_ctor_set_uint32(v_reuseFailAlloc_2156_, sizeof(void*)*10 + 4, v_numThreads_2137_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*10 + 15, v_jsonOutput_2143_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*10 + 16, v_printStats_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2156_, sizeof(void*)*10 + 17, v_run_2146_);
v___x_2152_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2152_);
v___x_2154_ = v___x_2124_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec_ref(v_opts_951_);
v_a_2160_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2160_);
lean_dec_ref(v___x_2121_);
v___x_2164_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2165_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2164_);
lean_dec_ref(v___x_2165_);
goto v___jp_2161_;
v___jp_2161_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_io_error_to_string(v_a_2160_);
v___x_2163_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2162_);
lean_dec_ref(v___x_2163_);
goto v___jp_1128_;
}
}
}
}
else
{
lean_object* v_leanOpts_2166_; lean_object* v_forwardedArgs_2167_; uint8_t v_component_2168_; uint8_t v_printPrefix_2169_; uint8_t v_printLibDir_2170_; uint8_t v_useStdin_2171_; uint8_t v_onlyDeps_2172_; uint8_t v_onlySrcDeps_2173_; uint8_t v_depsJson_2174_; lean_object* v_opts_2175_; uint32_t v_trustLevel_2176_; uint32_t v_numThreads_2177_; lean_object* v_rootDir_x3f_2178_; lean_object* v_setupFileName_x3f_2179_; lean_object* v_oleanFileName_x3f_2180_; lean_object* v_ileanFileName_x3f_2181_; lean_object* v_cFileName_x3f_2182_; lean_object* v_bcFileName_x3f_2183_; uint8_t v_jsonOutput_2184_; lean_object* v_errorOnKinds_2185_; uint8_t v_printStats_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_optArg_x3f_953_);
v_leanOpts_2166_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_2167_ = lean_ctor_get(v_opts_951_, 1);
v_component_2168_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_2169_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_2170_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_2171_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_2172_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2173_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_2174_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_2175_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_2176_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_2177_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2178_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_2179_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_2180_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_2181_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_2182_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_2183_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_2184_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_2185_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_2186_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2188_ = v_opts_951_;
v_isShared_2189_ = v_isSharedCheck_2196_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_errorOnKinds_2185_);
lean_inc(v_bcFileName_x3f_2183_);
lean_inc(v_cFileName_x3f_2182_);
lean_inc(v_ileanFileName_x3f_2181_);
lean_inc(v_oleanFileName_x3f_2180_);
lean_inc(v_setupFileName_x3f_2179_);
lean_inc(v_rootDir_x3f_2178_);
lean_inc(v_opts_2175_);
lean_inc(v_forwardedArgs_2167_);
lean_inc(v_leanOpts_2166_);
lean_dec(v_opts_951_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2196_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2190_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2191_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2166_, v___x_2190_, v___x_1176_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2191_);
v___x_2193_ = v___x_2188_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_forwardedArgs_2167_);
lean_ctor_set(v_reuseFailAlloc_2195_, 2, v_opts_2175_);
lean_ctor_set(v_reuseFailAlloc_2195_, 3, v_rootDir_x3f_2178_);
lean_ctor_set(v_reuseFailAlloc_2195_, 4, v_setupFileName_x3f_2179_);
lean_ctor_set(v_reuseFailAlloc_2195_, 5, v_oleanFileName_x3f_2180_);
lean_ctor_set(v_reuseFailAlloc_2195_, 6, v_ileanFileName_x3f_2181_);
lean_ctor_set(v_reuseFailAlloc_2195_, 7, v_cFileName_x3f_2182_);
lean_ctor_set(v_reuseFailAlloc_2195_, 8, v_bcFileName_x3f_2183_);
lean_ctor_set(v_reuseFailAlloc_2195_, 9, v_errorOnKinds_2185_);
lean_ctor_set_uint8(v_reuseFailAlloc_2195_, sizeof(void*)*10 + 8, v_component_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2195_, sizeof(void*)*10 + 9, v_printPrefix_2169_);
lean_ctor_set_uint8(v_reuseFailAlloc_2195_, sizeof(void*)*10 + 10, v_printLibDir_2170_);
lean_ctor_set_uint8(v_reuseFailAlloc_2195_, sizeof(void*)*10 + 11, v_useStdin_2171_);
lean_ctor_set_uint8(v_reuseFailAlloc_2195_, sizeof(void*)*10 + 12, v_onlyDeps_2172_);
lean_ctor_set_uint8(v_reuseFailAlloc_2195_, sizeof(void*)*10 + 13, v_onlySrcDeps_2173_);
lean_ctor_set_uint8(v_reuseFailAlloc_2195_, sizeof(void*)*10 + 14, v_depsJson_2174_);
lean_ctor_set_uint32(v_reuseFailAlloc_2195_, sizeof(void*)*10, v_trustLevel_2176_);
lean_ctor_set_uint32(v_reuseFailAlloc_2195_, sizeof(void*)*10 + 4, v_numThreads_2177_);
lean_ctor_set_uint8(v_reuseFailAlloc_2195_, sizeof(void*)*10 + 15, v_jsonOutput_2184_);
lean_ctor_set_uint8(v_reuseFailAlloc_2195_, sizeof(void*)*10 + 16, v_printStats_2186_);
v___x_2193_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2194_; 
lean_ctor_set_uint8(v___x_2193_, sizeof(void*)*10 + 17, v___x_1178_);
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
return v___x_2194_;
}
}
}
}
else
{
lean_object* v_leanOpts_2197_; lean_object* v_forwardedArgs_2198_; uint8_t v_component_2199_; uint8_t v_printPrefix_2200_; uint8_t v_printLibDir_2201_; uint8_t v_onlyDeps_2202_; uint8_t v_onlySrcDeps_2203_; uint8_t v_depsJson_2204_; lean_object* v_opts_2205_; uint32_t v_trustLevel_2206_; uint32_t v_numThreads_2207_; lean_object* v_rootDir_x3f_2208_; lean_object* v_setupFileName_x3f_2209_; lean_object* v_oleanFileName_x3f_2210_; lean_object* v_ileanFileName_x3f_2211_; lean_object* v_cFileName_x3f_2212_; lean_object* v_bcFileName_x3f_2213_; uint8_t v_jsonOutput_2214_; lean_object* v_errorOnKinds_2215_; uint8_t v_printStats_2216_; uint8_t v_run_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_optArg_x3f_953_);
v_leanOpts_2197_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_2198_ = lean_ctor_get(v_opts_951_, 1);
v_component_2199_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_2200_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_2201_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_onlyDeps_2202_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2203_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_2204_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_2205_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_2206_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_2207_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2208_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_2209_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_2210_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_2211_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_2212_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_2213_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_2214_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_2215_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_2216_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_2217_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2219_ = v_opts_951_;
v_isShared_2220_ = v_isSharedCheck_2225_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_errorOnKinds_2215_);
lean_inc(v_bcFileName_x3f_2213_);
lean_inc(v_cFileName_x3f_2212_);
lean_inc(v_ileanFileName_x3f_2211_);
lean_inc(v_oleanFileName_x3f_2210_);
lean_inc(v_setupFileName_x3f_2209_);
lean_inc(v_rootDir_x3f_2208_);
lean_inc(v_opts_2205_);
lean_inc(v_forwardedArgs_2198_);
lean_inc(v_leanOpts_2197_);
lean_dec(v_opts_951_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2225_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_leanOpts_2197_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_forwardedArgs_2198_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_opts_2205_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_rootDir_x3f_2208_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_setupFileName_x3f_2209_);
lean_ctor_set(v_reuseFailAlloc_2224_, 5, v_oleanFileName_x3f_2210_);
lean_ctor_set(v_reuseFailAlloc_2224_, 6, v_ileanFileName_x3f_2211_);
lean_ctor_set(v_reuseFailAlloc_2224_, 7, v_cFileName_x3f_2212_);
lean_ctor_set(v_reuseFailAlloc_2224_, 8, v_bcFileName_x3f_2213_);
lean_ctor_set(v_reuseFailAlloc_2224_, 9, v_errorOnKinds_2215_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*10 + 8, v_component_2199_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*10 + 9, v_printPrefix_2200_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*10 + 10, v_printLibDir_2201_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*10 + 12, v_onlyDeps_2202_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*10 + 13, v_onlySrcDeps_2203_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*10 + 14, v_depsJson_2204_);
lean_ctor_set_uint32(v_reuseFailAlloc_2224_, sizeof(void*)*10, v_trustLevel_2206_);
lean_ctor_set_uint32(v_reuseFailAlloc_2224_, sizeof(void*)*10 + 4, v_numThreads_2207_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*10 + 15, v_jsonOutput_2214_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*10 + 16, v_printStats_2216_);
lean_ctor_set_uint8(v_reuseFailAlloc_2224_, sizeof(void*)*10 + 17, v_run_2217_);
v___x_2222_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2223_; 
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*10 + 11, v___x_1176_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
return v___x_2223_;
}
}
}
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2227_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2226_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2286_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2230_ = v___x_2227_;
v_isShared_2231_ = v_isSharedCheck_2286_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2227_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2286_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2232_ = lean_unsigned_to_nat(0u);
v___x_2233_ = lean_string_utf8_byte_size(v_a_2228_);
lean_inc(v_a_2228_);
v___x_2234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2234_, 0, v_a_2228_);
lean_ctor_set(v___x_2234_, 1, v___x_2232_);
lean_ctor_set(v___x_2234_, 2, v___x_2233_);
v___x_2235_ = l_String_Slice_toNat_x3f(v___x_2234_);
lean_dec_ref(v___x_2234_);
if (lean_obj_tag(v___x_2235_) == 1)
{
lean_object* v_val_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; 
v_val_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_val_2236_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = lean_unsigned_to_nat(4u);
v___x_2238_ = lean_unsigned_to_nat(2u);
v___x_2239_ = lean_nat_shiftr(v_val_2236_, v___x_2238_);
lean_dec(v_val_2236_);
v___x_2240_ = lean_nat_mul(v___x_2239_, v___x_2237_);
lean_dec(v___x_2239_);
v___x_2241_ = lean_unsigned_to_nat(1024u);
v___x_2242_ = lean_nat_mul(v___x_2240_, v___x_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25);
v___x_2244_ = lean_nat_dec_lt(v___x_2242_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec(v___x_2242_);
lean_del_object(v___x_2230_);
lean_dec(v_a_2228_);
lean_dec_ref(v_opts_951_);
v___x_2245_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2246_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2245_);
lean_dec_ref(v___x_2246_);
goto v___jp_994_;
}
else
{
size_t v___x_2247_; lean_object* v___x_2248_; lean_object* v_leanOpts_2249_; lean_object* v_forwardedArgs_2250_; uint8_t v_component_2251_; uint8_t v_printPrefix_2252_; uint8_t v_printLibDir_2253_; uint8_t v_useStdin_2254_; uint8_t v_onlyDeps_2255_; uint8_t v_onlySrcDeps_2256_; uint8_t v_depsJson_2257_; lean_object* v_opts_2258_; uint32_t v_trustLevel_2259_; uint32_t v_numThreads_2260_; lean_object* v_rootDir_x3f_2261_; lean_object* v_setupFileName_x3f_2262_; lean_object* v_oleanFileName_x3f_2263_; lean_object* v_ileanFileName_x3f_2264_; lean_object* v_cFileName_x3f_2265_; lean_object* v_bcFileName_x3f_2266_; uint8_t v_jsonOutput_2267_; lean_object* v_errorOnKinds_2268_; uint8_t v_printStats_2269_; uint8_t v_run_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2283_; 
v___x_2247_ = lean_usize_of_nat(v___x_2242_);
lean_dec(v___x_2242_);
v___x_2248_ = lean_internal_set_thread_stack_size(v___x_2247_);
v_leanOpts_2249_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_2250_ = lean_ctor_get(v_opts_951_, 1);
v_component_2251_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_2252_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_2253_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_2254_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_2255_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2256_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_2257_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_2258_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_2259_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_2260_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2261_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_2262_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_2263_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_2264_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_2265_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_2266_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_2267_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_2268_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_2269_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_2270_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2272_ = v_opts_951_;
v_isShared_2273_ = v_isSharedCheck_2283_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_errorOnKinds_2268_);
lean_inc(v_bcFileName_x3f_2266_);
lean_inc(v_cFileName_x3f_2265_);
lean_inc(v_ileanFileName_x3f_2264_);
lean_inc(v_oleanFileName_x3f_2263_);
lean_inc(v_setupFileName_x3f_2262_);
lean_inc(v_rootDir_x3f_2261_);
lean_inc(v_opts_2258_);
lean_inc(v_forwardedArgs_2250_);
lean_inc(v_leanOpts_2249_);
lean_dec(v_opts_951_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2283_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2274_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2275_ = lean_string_append(v___x_2274_, v_a_2228_);
lean_dec(v_a_2228_);
v___x_2276_ = lean_array_push(v_forwardedArgs_2250_, v___x_2275_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 1, v___x_2276_);
v___x_2278_ = v___x_2272_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_leanOpts_2249_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v_opts_2258_);
lean_ctor_set(v_reuseFailAlloc_2282_, 3, v_rootDir_x3f_2261_);
lean_ctor_set(v_reuseFailAlloc_2282_, 4, v_setupFileName_x3f_2262_);
lean_ctor_set(v_reuseFailAlloc_2282_, 5, v_oleanFileName_x3f_2263_);
lean_ctor_set(v_reuseFailAlloc_2282_, 6, v_ileanFileName_x3f_2264_);
lean_ctor_set(v_reuseFailAlloc_2282_, 7, v_cFileName_x3f_2265_);
lean_ctor_set(v_reuseFailAlloc_2282_, 8, v_bcFileName_x3f_2266_);
lean_ctor_set(v_reuseFailAlloc_2282_, 9, v_errorOnKinds_2268_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*10 + 8, v_component_2251_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*10 + 9, v_printPrefix_2252_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*10 + 10, v_printLibDir_2253_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*10 + 11, v_useStdin_2254_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*10 + 12, v_onlyDeps_2255_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*10 + 13, v_onlySrcDeps_2256_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*10 + 14, v_depsJson_2257_);
lean_ctor_set_uint32(v_reuseFailAlloc_2282_, sizeof(void*)*10, v_trustLevel_2259_);
lean_ctor_set_uint32(v_reuseFailAlloc_2282_, sizeof(void*)*10 + 4, v_numThreads_2260_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*10 + 15, v_jsonOutput_2267_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*10 + 16, v_printStats_2269_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*10 + 17, v_run_2270_);
v___x_2278_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2280_; 
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v___x_2278_);
v___x_2280_ = v___x_2230_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec(v___x_2235_);
lean_del_object(v___x_2230_);
lean_dec(v_a_2228_);
lean_dec_ref(v_opts_951_);
v___x_2284_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28));
v___x_2285_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2284_);
lean_dec_ref(v___x_2285_);
goto v___jp_991_;
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec_ref(v_opts_951_);
v_a_2287_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2287_);
lean_dec_ref(v___x_2227_);
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
goto v___jp_988_;
}
}
}
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2294_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2293_, v_optArg_x3f_953_);
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
lean_object* v_leanOpts_2299_; lean_object* v_forwardedArgs_2300_; uint8_t v_component_2301_; uint8_t v_printPrefix_2302_; uint8_t v_printLibDir_2303_; uint8_t v_useStdin_2304_; uint8_t v_onlyDeps_2305_; uint8_t v_onlySrcDeps_2306_; uint8_t v_depsJson_2307_; lean_object* v_opts_2308_; uint32_t v_trustLevel_2309_; uint32_t v_numThreads_2310_; lean_object* v_rootDir_x3f_2311_; lean_object* v_setupFileName_x3f_2312_; lean_object* v_oleanFileName_x3f_2313_; lean_object* v_ileanFileName_x3f_2314_; lean_object* v_cFileName_x3f_2315_; uint8_t v_jsonOutput_2316_; lean_object* v_errorOnKinds_2317_; uint8_t v_printStats_2318_; uint8_t v_run_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2330_; 
v_leanOpts_2299_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_2300_ = lean_ctor_get(v_opts_951_, 1);
v_component_2301_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_2302_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_2303_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_2304_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_2305_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2306_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_2307_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_2308_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_2309_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_2310_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2311_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_2312_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_2313_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_2314_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_2315_ = lean_ctor_get(v_opts_951_, 7);
v_jsonOutput_2316_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_2317_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_2318_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_2319_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; 
v_unused_2331_ = lean_ctor_get(v_opts_951_, 8);
lean_dec(v_unused_2331_);
v___x_2321_ = v_opts_951_;
v_isShared_2322_ = v_isSharedCheck_2330_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_errorOnKinds_2317_);
lean_inc(v_cFileName_x3f_2315_);
lean_inc(v_ileanFileName_x3f_2314_);
lean_inc(v_oleanFileName_x3f_2313_);
lean_inc(v_setupFileName_x3f_2312_);
lean_inc(v_rootDir_x3f_2311_);
lean_inc(v_opts_2308_);
lean_inc(v_forwardedArgs_2300_);
lean_inc(v_leanOpts_2299_);
lean_dec(v_opts_951_);
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
lean_ctor_set(v___x_2321_, 8, v___x_2323_);
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
lean_ctor_set(v_reuseFailAlloc_2329_, 7, v_cFileName_x3f_2315_);
lean_ctor_set(v_reuseFailAlloc_2329_, 8, v___x_2323_);
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
lean_dec_ref(v_opts_951_);
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
goto v___jp_1134_;
}
}
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2340_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2339_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2378_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2378_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2378_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_leanOpts_2345_; lean_object* v_forwardedArgs_2346_; uint8_t v_component_2347_; uint8_t v_printPrefix_2348_; uint8_t v_printLibDir_2349_; uint8_t v_useStdin_2350_; uint8_t v_onlyDeps_2351_; uint8_t v_onlySrcDeps_2352_; uint8_t v_depsJson_2353_; lean_object* v_opts_2354_; uint32_t v_trustLevel_2355_; uint32_t v_numThreads_2356_; lean_object* v_rootDir_x3f_2357_; lean_object* v_setupFileName_x3f_2358_; lean_object* v_oleanFileName_x3f_2359_; lean_object* v_ileanFileName_x3f_2360_; lean_object* v_bcFileName_x3f_2361_; uint8_t v_jsonOutput_2362_; lean_object* v_errorOnKinds_2363_; uint8_t v_printStats_2364_; uint8_t v_run_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2376_; 
v_leanOpts_2345_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_2346_ = lean_ctor_get(v_opts_951_, 1);
v_component_2347_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_2348_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_2349_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_2350_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_2351_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2352_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_2353_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_2354_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_2355_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_numThreads_2356_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2357_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_2358_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_2359_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_2360_ = lean_ctor_get(v_opts_951_, 6);
v_bcFileName_x3f_2361_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_2362_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_2363_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_2364_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_2365_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v_opts_951_, 7);
lean_dec(v_unused_2377_);
v___x_2367_ = v_opts_951_;
v_isShared_2368_ = v_isSharedCheck_2376_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_errorOnKinds_2363_);
lean_inc(v_bcFileName_x3f_2361_);
lean_inc(v_ileanFileName_x3f_2360_);
lean_inc(v_oleanFileName_x3f_2359_);
lean_inc(v_setupFileName_x3f_2358_);
lean_inc(v_rootDir_x3f_2357_);
lean_inc(v_opts_2354_);
lean_inc(v_forwardedArgs_2346_);
lean_inc(v_leanOpts_2345_);
lean_dec(v_opts_951_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2376_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2369_, 0, v_a_2341_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 7, v___x_2369_);
v___x_2371_ = v___x_2367_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_leanOpts_2345_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_forwardedArgs_2346_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v_opts_2354_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v_rootDir_x3f_2357_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v_setupFileName_x3f_2358_);
lean_ctor_set(v_reuseFailAlloc_2375_, 5, v_oleanFileName_x3f_2359_);
lean_ctor_set(v_reuseFailAlloc_2375_, 6, v_ileanFileName_x3f_2360_);
lean_ctor_set(v_reuseFailAlloc_2375_, 7, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2375_, 8, v_bcFileName_x3f_2361_);
lean_ctor_set(v_reuseFailAlloc_2375_, 9, v_errorOnKinds_2363_);
lean_ctor_set_uint8(v_reuseFailAlloc_2375_, sizeof(void*)*10 + 8, v_component_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2375_, sizeof(void*)*10 + 9, v_printPrefix_2348_);
lean_ctor_set_uint8(v_reuseFailAlloc_2375_, sizeof(void*)*10 + 10, v_printLibDir_2349_);
lean_ctor_set_uint8(v_reuseFailAlloc_2375_, sizeof(void*)*10 + 11, v_useStdin_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2375_, sizeof(void*)*10 + 12, v_onlyDeps_2351_);
lean_ctor_set_uint8(v_reuseFailAlloc_2375_, sizeof(void*)*10 + 13, v_onlySrcDeps_2352_);
lean_ctor_set_uint8(v_reuseFailAlloc_2375_, sizeof(void*)*10 + 14, v_depsJson_2353_);
lean_ctor_set_uint32(v_reuseFailAlloc_2375_, sizeof(void*)*10, v_trustLevel_2355_);
lean_ctor_set_uint32(v_reuseFailAlloc_2375_, sizeof(void*)*10 + 4, v_numThreads_2356_);
lean_ctor_set_uint8(v_reuseFailAlloc_2375_, sizeof(void*)*10 + 15, v_jsonOutput_2362_);
lean_ctor_set_uint8(v_reuseFailAlloc_2375_, sizeof(void*)*10 + 16, v_printStats_2364_);
lean_ctor_set_uint8(v_reuseFailAlloc_2375_, sizeof(void*)*10 + 17, v_run_2365_);
v___x_2371_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2373_; 
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2371_);
v___x_2373_ = v___x_2343_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_dec_ref(v_opts_951_);
v_a_2379_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2379_);
lean_dec_ref(v___x_2340_);
v___x_2383_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2384_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2383_);
lean_dec_ref(v___x_2384_);
goto v___jp_2380_;
v___jp_2380_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = lean_io_error_to_string(v_a_2379_);
v___x_2382_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2381_);
lean_dec_ref(v___x_2382_);
goto v___jp_982_;
}
}
}
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec(v_optArg_x3f_953_);
lean_dec_ref(v_opts_951_);
v___x_2385_ = l___private_Lean_Shell_0__Lean_featuresString;
v___x_2386_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4(v___x_2385_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2394_; 
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; 
v_unused_2395_ = lean_ctor_get(v___x_2386_, 0);
lean_dec(v_unused_2395_);
v___x_2388_ = v___x_2386_;
v_isShared_2389_ = v_isSharedCheck_2394_;
goto v_resetjp_2387_;
}
else
{
lean_dec(v___x_2386_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2394_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2392_; 
v___x_2390_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2389_ == 0)
{
lean_ctor_set_tag(v___x_2388_, 1);
lean_ctor_set(v___x_2388_, 0, v___x_2390_);
v___x_2392_ = v___x_2388_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2390_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_a_2396_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2396_);
lean_dec_ref(v___x_2386_);
v___x_2400_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2401_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2400_);
lean_dec_ref(v___x_2401_);
goto v___jp_2397_;
v___jp_2397_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_io_error_to_string(v_a_2396_);
v___x_2399_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2398_);
lean_dec_ref(v___x_2399_);
goto v___jp_1140_;
}
}
}
}
else
{
lean_object* v___x_2402_; 
lean_dec(v_optArg_x3f_953_);
lean_dec_ref(v_opts_951_);
v___x_2402_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1164_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2410_; 
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; 
v_unused_2411_ = lean_ctor_get(v___x_2402_, 0);
lean_dec(v_unused_2411_);
v___x_2404_ = v___x_2402_;
v_isShared_2405_ = v_isSharedCheck_2410_;
goto v_resetjp_2403_;
}
else
{
lean_dec(v___x_2402_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2410_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2406_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2405_ == 0)
{
lean_ctor_set_tag(v___x_2404_, 1);
lean_ctor_set(v___x_2404_, 0, v___x_2406_);
v___x_2408_ = v___x_2404_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v_a_2412_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2412_);
lean_dec_ref(v___x_2402_);
v___x_2416_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2417_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2416_);
lean_dec_ref(v___x_2417_);
goto v___jp_2413_;
v___jp_2413_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_io_error_to_string(v_a_2412_);
v___x_2415_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2414_);
lean_dec_ref(v___x_2415_);
goto v___jp_976_;
}
}
}
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_dec(v_optArg_x3f_953_);
lean_dec_ref(v_opts_951_);
v___x_2418_ = l_Lean_githash;
v___x_2419_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4(v___x_2418_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2427_; 
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2427_ == 0)
{
lean_object* v_unused_2428_; 
v_unused_2428_ = lean_ctor_get(v___x_2419_, 0);
lean_dec(v_unused_2428_);
v___x_2421_ = v___x_2419_;
v_isShared_2422_ = v_isSharedCheck_2427_;
goto v_resetjp_2420_;
}
else
{
lean_dec(v___x_2419_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2427_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; lean_object* v___x_2425_; 
v___x_2423_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2422_ == 0)
{
lean_ctor_set_tag(v___x_2421_, 1);
lean_ctor_set(v___x_2421_, 0, v___x_2423_);
v___x_2425_ = v___x_2421_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v_a_2429_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2429_);
lean_dec_ref(v___x_2419_);
v___x_2433_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2434_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2433_);
lean_dec_ref(v___x_2434_);
goto v___jp_2430_;
v___jp_2430_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = lean_io_error_to_string(v_a_2429_);
v___x_2432_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2431_);
lean_dec_ref(v___x_2432_);
goto v___jp_1146_;
}
}
}
}
else
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec(v_optArg_x3f_953_);
lean_dec_ref(v_opts_951_);
v___x_2435_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2436_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4(v___x_2435_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2444_; 
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2444_ == 0)
{
lean_object* v_unused_2445_; 
v_unused_2445_ = lean_ctor_get(v___x_2436_, 0);
lean_dec(v_unused_2445_);
v___x_2438_ = v___x_2436_;
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
else
{
lean_dec(v___x_2436_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2440_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2439_ == 0)
{
lean_ctor_set_tag(v___x_2438_, 1);
lean_ctor_set(v___x_2438_, 0, v___x_2440_);
v___x_2442_ = v___x_2438_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_a_2446_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2446_);
lean_dec_ref(v___x_2436_);
v___x_2450_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2451_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2450_);
lean_dec_ref(v___x_2451_);
goto v___jp_2447_;
v___jp_2447_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = lean_io_error_to_string(v_a_2446_);
v___x_2449_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2448_);
lean_dec_ref(v___x_2449_);
goto v___jp_970_;
}
}
}
}
else
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
lean_dec(v_optArg_x3f_953_);
lean_dec_ref(v_opts_951_);
v___x_2452_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2453_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4(v___x_2452_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2461_; 
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2461_ == 0)
{
lean_object* v_unused_2462_; 
v_unused_2462_ = lean_ctor_get(v___x_2453_, 0);
lean_dec(v_unused_2462_);
v___x_2455_ = v___x_2453_;
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
else
{
lean_dec(v___x_2453_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; lean_object* v___x_2459_; 
v___x_2457_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2456_ == 0)
{
lean_ctor_set_tag(v___x_2455_, 1);
lean_ctor_set(v___x_2455_, 0, v___x_2457_);
v___x_2459_ = v___x_2455_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v_a_2463_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2463_);
lean_dec_ref(v___x_2453_);
v___x_2467_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2468_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2467_);
lean_dec_ref(v___x_2468_);
goto v___jp_2464_;
v___jp_2464_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = lean_io_error_to_string(v_a_2463_);
v___x_2466_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2465_);
lean_dec_ref(v___x_2466_);
goto v___jp_1152_;
}
}
}
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2470_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2469_, v_optArg_x3f_953_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2521_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2473_ = v___x_2470_;
v_isShared_2474_ = v_isSharedCheck_2521_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2470_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2521_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2475_ = lean_unsigned_to_nat(0u);
v___x_2476_ = lean_string_utf8_byte_size(v_a_2471_);
lean_inc(v_a_2471_);
v___x_2477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2477_, 0, v_a_2471_);
lean_ctor_set(v___x_2477_, 1, v___x_2475_);
lean_ctor_set(v___x_2477_, 2, v___x_2476_);
v___x_2478_ = l_String_Slice_toNat_x3f(v___x_2477_);
lean_dec_ref(v___x_2477_);
if (lean_obj_tag(v___x_2478_) == 1)
{
lean_object* v_val_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v_val_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_val_2479_);
lean_dec_ref(v___x_2478_);
v___x_2480_ = lean_cstr_to_nat("4294967296");
v___x_2481_ = lean_nat_dec_lt(v_val_2479_, v___x_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec(v_val_2479_);
lean_del_object(v___x_2473_);
lean_dec(v_a_2471_);
lean_dec_ref(v_opts_951_);
v___x_2482_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2483_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2482_);
lean_dec_ref(v___x_2483_);
goto v___jp_964_;
}
else
{
lean_object* v_leanOpts_2484_; lean_object* v_forwardedArgs_2485_; uint8_t v_component_2486_; uint8_t v_printPrefix_2487_; uint8_t v_printLibDir_2488_; uint8_t v_useStdin_2489_; uint8_t v_onlyDeps_2490_; uint8_t v_onlySrcDeps_2491_; uint8_t v_depsJson_2492_; lean_object* v_opts_2493_; uint32_t v_trustLevel_2494_; lean_object* v_rootDir_x3f_2495_; lean_object* v_setupFileName_x3f_2496_; lean_object* v_oleanFileName_x3f_2497_; lean_object* v_ileanFileName_x3f_2498_; lean_object* v_cFileName_x3f_2499_; lean_object* v_bcFileName_x3f_2500_; uint8_t v_jsonOutput_2501_; lean_object* v_errorOnKinds_2502_; uint8_t v_printStats_2503_; uint8_t v_run_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2518_; 
v_leanOpts_2484_ = lean_ctor_get(v_opts_951_, 0);
v_forwardedArgs_2485_ = lean_ctor_get(v_opts_951_, 1);
v_component_2486_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 8);
v_printPrefix_2487_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 9);
v_printLibDir_2488_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 10);
v_useStdin_2489_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 11);
v_onlyDeps_2490_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2491_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 13);
v_depsJson_2492_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 14);
v_opts_2493_ = lean_ctor_get(v_opts_951_, 2);
v_trustLevel_2494_ = lean_ctor_get_uint32(v_opts_951_, sizeof(void*)*10);
v_rootDir_x3f_2495_ = lean_ctor_get(v_opts_951_, 3);
v_setupFileName_x3f_2496_ = lean_ctor_get(v_opts_951_, 4);
v_oleanFileName_x3f_2497_ = lean_ctor_get(v_opts_951_, 5);
v_ileanFileName_x3f_2498_ = lean_ctor_get(v_opts_951_, 6);
v_cFileName_x3f_2499_ = lean_ctor_get(v_opts_951_, 7);
v_bcFileName_x3f_2500_ = lean_ctor_get(v_opts_951_, 8);
v_jsonOutput_2501_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 15);
v_errorOnKinds_2502_ = lean_ctor_get(v_opts_951_, 9);
v_printStats_2503_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 16);
v_run_2504_ = lean_ctor_get_uint8(v_opts_951_, sizeof(void*)*10 + 17);
v_isSharedCheck_2518_ = !lean_is_exclusive(v_opts_951_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2506_ = v_opts_951_;
v_isShared_2507_ = v_isSharedCheck_2518_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_errorOnKinds_2502_);
lean_inc(v_bcFileName_x3f_2500_);
lean_inc(v_cFileName_x3f_2499_);
lean_inc(v_ileanFileName_x3f_2498_);
lean_inc(v_oleanFileName_x3f_2497_);
lean_inc(v_setupFileName_x3f_2496_);
lean_inc(v_rootDir_x3f_2495_);
lean_inc(v_opts_2493_);
lean_inc(v_forwardedArgs_2485_);
lean_inc(v_leanOpts_2484_);
lean_dec(v_opts_951_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2518_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
uint32_t v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2513_; 
v___x_2508_ = lean_uint32_of_nat(v_val_2479_);
lean_dec(v_val_2479_);
v___x_2509_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2510_ = lean_string_append(v___x_2509_, v_a_2471_);
lean_dec(v_a_2471_);
v___x_2511_ = lean_array_push(v_forwardedArgs_2485_, v___x_2510_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 1, v___x_2511_);
v___x_2513_ = v___x_2506_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_leanOpts_2484_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2517_, 2, v_opts_2493_);
lean_ctor_set(v_reuseFailAlloc_2517_, 3, v_rootDir_x3f_2495_);
lean_ctor_set(v_reuseFailAlloc_2517_, 4, v_setupFileName_x3f_2496_);
lean_ctor_set(v_reuseFailAlloc_2517_, 5, v_oleanFileName_x3f_2497_);
lean_ctor_set(v_reuseFailAlloc_2517_, 6, v_ileanFileName_x3f_2498_);
lean_ctor_set(v_reuseFailAlloc_2517_, 7, v_cFileName_x3f_2499_);
lean_ctor_set(v_reuseFailAlloc_2517_, 8, v_bcFileName_x3f_2500_);
lean_ctor_set(v_reuseFailAlloc_2517_, 9, v_errorOnKinds_2502_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*10 + 8, v_component_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*10 + 9, v_printPrefix_2487_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*10 + 10, v_printLibDir_2488_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*10 + 11, v_useStdin_2489_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*10 + 12, v_onlyDeps_2490_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*10 + 13, v_onlySrcDeps_2491_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*10 + 14, v_depsJson_2492_);
lean_ctor_set_uint32(v_reuseFailAlloc_2517_, sizeof(void*)*10, v_trustLevel_2494_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*10 + 15, v_jsonOutput_2501_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*10 + 16, v_printStats_2503_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*10 + 17, v_run_2504_);
v___x_2513_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2515_; 
lean_ctor_set_uint32(v___x_2513_, sizeof(void*)*10 + 4, v___x_2508_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v___x_2513_);
v___x_2515_ = v___x_2473_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
lean_dec(v___x_2478_);
lean_del_object(v___x_2473_);
lean_dec(v_a_2471_);
lean_dec_ref(v_opts_951_);
v___x_2519_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2520_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2519_);
lean_dec_ref(v___x_2520_);
goto v___jp_961_;
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_dec_ref(v_opts_951_);
v_a_2522_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2522_);
lean_dec_ref(v___x_2470_);
v___x_2526_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2527_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2526_);
lean_dec_ref(v___x_2527_);
goto v___jp_2523_;
v___jp_2523_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = lean_io_error_to_string(v_a_2522_);
v___x_2525_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2524_);
lean_dec_ref(v___x_2525_);
goto v___jp_958_;
}
}
}
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_dec(v_optArg_x3f_953_);
v___x_2528_ = lean_internal_set_exit_on_panic(v___x_1156_);
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_opts_951_);
return v___x_2529_;
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
v___x_965_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
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
v___x_983_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_984_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_983_);
lean_dec_ref(v___x_984_);
goto v___jp_979_;
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
v___x_995_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
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
v___x_1001_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1002_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1001_);
lean_dec_ref(v___x_1002_);
goto v___jp_997_;
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
v___x_1022_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
return v___x_1023_;
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
lean_dec_ref(v___x_1060_);
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
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_io_error_to_string(v___y_1095_);
v___x_1097_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1096_);
lean_dec_ref(v___x_1097_);
goto v___jp_1091_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2530_, lean_object* v_opt_2531_, lean_object* v_optArg_x3f_2532_, lean_object* v_a_2533_){
_start:
{
uint32_t v_opt_boxed_2534_; lean_object* v_res_2535_; 
v_opt_boxed_2534_ = lean_unbox_uint32(v_opt_2531_);
lean_dec(v_opt_2531_);
v_res_2535_ = lean_shell_options_process(v_opts_2530_, v_opt_boxed_2534_, v_optArg_x3f_2532_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object* v___x_2536_, lean_object* v_a_2537_, lean_object* v_inst_2538_, lean_object* v_R_2539_, lean_object* v_a_2540_, lean_object* v_b_2541_, lean_object* v_c_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___redArg(v___x_2536_, v_a_2537_, v_a_2540_, v_b_2541_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object* v___x_2544_, lean_object* v_a_2545_, lean_object* v_inst_2546_, lean_object* v_R_2547_, lean_object* v_a_2548_, lean_object* v_b_2549_, lean_object* v_c_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v___x_2544_, v_a_2545_, v_inst_2546_, v_R_2547_, v_a_2548_, v_b_2549_, v_c_2550_);
lean_dec(v_b_2549_);
lean_dec_ref(v_a_2545_);
lean_dec_ref(v___x_2544_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_opts_2552_, lean_object* v_opt_2553_){
_start:
{
lean_object* v_name_2554_; lean_object* v_defValue_2555_; lean_object* v_map_2556_; lean_object* v___x_2557_; 
v_name_2554_ = lean_ctor_get(v_opt_2553_, 0);
v_defValue_2555_ = lean_ctor_get(v_opt_2553_, 1);
v_map_2556_ = lean_ctor_get(v_opts_2552_, 0);
v___x_2557_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2556_, v_name_2554_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_inc(v_defValue_2555_);
return v_defValue_2555_;
}
else
{
lean_object* v_val_2558_; 
v_val_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_val_2558_);
lean_dec_ref(v___x_2557_);
if (lean_obj_tag(v_val_2558_) == 3)
{
lean_object* v_v_2559_; 
v_v_2559_ = lean_ctor_get(v_val_2558_, 0);
lean_inc(v_v_2559_);
lean_dec_ref(v_val_2558_);
return v_v_2559_;
}
else
{
lean_dec(v_val_2558_);
lean_inc(v_defValue_2555_);
return v_defValue_2555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_opts_2560_, lean_object* v_opt_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_opts_2560_, v_opt_2561_);
lean_dec_ref(v_opt_2561_);
lean_dec_ref(v_opts_2560_);
return v_res_2562_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2565_ = lean_string_utf8_byte_size(v___x_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2566_){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2567_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2568_ = lean_string_utf8_byte_size(v_s_2566_);
v___x_2569_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1);
v___x_2570_ = lean_nat_dec_le(v___x_2569_, v___x_2568_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; 
lean_dec_ref(v_s_2566_);
v___x_2571_ = lean_box(0);
return v___x_2571_;
}
else
{
lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = lean_unsigned_to_nat(0u);
v___x_2573_ = lean_string_memcmp(v_s_2566_, v___x_2567_, v___x_2572_, v___x_2572_, v___x_2569_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; 
lean_dec_ref(v_s_2566_);
v___x_2574_ = lean_box(0);
return v___x_2574_;
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_inc_ref(v_s_2566_);
v___x_2575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2575_, 0, v_s_2566_);
lean_ctor_set(v___x_2575_, 1, v___x_2572_);
lean_ctor_set(v___x_2575_, 2, v___x_2568_);
v___x_2576_ = l_String_Slice_pos_x21(v___x_2575_, v___x_2569_);
lean_dec_ref(v___x_2575_);
v___x_2577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2577_, 0, v_s_2566_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
lean_ctor_set(v___x_2577_, 2, v___x_2568_);
v___x_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
return v___x_2578_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2579_, lean_object* v_pat_2580_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2579_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2582_, lean_object* v_pat_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2582_, v_pat_2583_);
lean_dec_ref(v_pat_2583_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v___x_2586_, lean_object* v___x_2587_, lean_object* v_mainModuleName_2588_, lean_object* v_a_2589_, lean_object* v___x_2590_, lean_object* v_fileName_2591_, lean_object* v___x_2592_, lean_object* v___x_2593_, lean_object* v___x_2594_, lean_object* v___x_2595_, lean_object* v___x_2596_, lean_object* v___x_2597_, lean_object* v___x_2598_, lean_object* v___x_2599_, uint8_t v_run_2600_){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v_env_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; lean_object* v_fileName_2611_; lean_object* v_fileMap_2612_; lean_object* v_currRecDepth_2613_; lean_object* v_ref_2614_; lean_object* v_currNamespace_2615_; lean_object* v_openDecls_2616_; lean_object* v_initHeartbeats_2617_; lean_object* v_maxHeartbeats_2618_; lean_object* v_quotContext_2619_; lean_object* v_currMacroScope_2620_; lean_object* v_cancelTk_x3f_2621_; uint8_t v_suppressElabErrors_2622_; lean_object* v_inheritedTraceOptions_2623_; lean_object* v___y_2624_; uint8_t v___y_2653_; uint8_t v___x_2674_; 
v___x_2602_ = lean_io_get_num_heartbeats();
v___x_2603_ = lean_st_mk_ref(v___x_2586_);
v___x_2604_ = l_Lean_inheritedTraceOptions;
v___x_2605_ = lean_st_ref_get(v___x_2604_);
v___x_2606_ = lean_st_ref_get(v___x_2603_);
v_env_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc_ref(v_env_2607_);
lean_dec(v___x_2606_);
v___x_2608_ = l_Lean_diagnostics;
v___x_2609_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v___x_2587_, v___x_2608_);
v___x_2674_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2607_);
lean_dec_ref(v_env_2607_);
if (v___x_2674_ == 0)
{
if (v___x_2609_ == 0)
{
lean_dec_ref(v___x_2590_);
lean_inc(v___x_2603_);
lean_inc(v___x_2595_);
v_fileName_2611_ = v_fileName_2591_;
v_fileMap_2612_ = v___x_2592_;
v_currRecDepth_2613_ = v___x_2593_;
v_ref_2614_ = v___x_2594_;
v_currNamespace_2615_ = v___x_2595_;
v_openDecls_2616_ = v___x_2596_;
v_initHeartbeats_2617_ = v___x_2602_;
v_maxHeartbeats_2618_ = v___x_2597_;
v_quotContext_2619_ = v___x_2595_;
v_currMacroScope_2620_ = v___x_2598_;
v_cancelTk_x3f_2621_ = v___x_2599_;
v_suppressElabErrors_2622_ = v_run_2600_;
v_inheritedTraceOptions_2623_ = v___x_2605_;
v___y_2624_ = v___x_2603_;
goto v___jp_2610_;
}
else
{
v___y_2653_ = v___x_2674_;
goto v___jp_2652_;
}
}
else
{
v___y_2653_ = v___x_2609_;
goto v___jp_2652_;
}
v___jp_2610_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2625_ = l_Lean_maxRecDepth;
v___x_2626_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_2587_, v___x_2625_);
v___x_2627_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2627_, 0, v_fileName_2611_);
lean_ctor_set(v___x_2627_, 1, v_fileMap_2612_);
lean_ctor_set(v___x_2627_, 2, v___x_2587_);
lean_ctor_set(v___x_2627_, 3, v_currRecDepth_2613_);
lean_ctor_set(v___x_2627_, 4, v___x_2626_);
lean_ctor_set(v___x_2627_, 5, v_ref_2614_);
lean_ctor_set(v___x_2627_, 6, v_currNamespace_2615_);
lean_ctor_set(v___x_2627_, 7, v_openDecls_2616_);
lean_ctor_set(v___x_2627_, 8, v_initHeartbeats_2617_);
lean_ctor_set(v___x_2627_, 9, v_maxHeartbeats_2618_);
lean_ctor_set(v___x_2627_, 10, v_quotContext_2619_);
lean_ctor_set(v___x_2627_, 11, v_currMacroScope_2620_);
lean_ctor_set(v___x_2627_, 12, v_cancelTk_x3f_2621_);
lean_ctor_set(v___x_2627_, 13, v_inheritedTraceOptions_2623_);
lean_ctor_set_uint8(v___x_2627_, sizeof(void*)*14, v___x_2609_);
lean_ctor_set_uint8(v___x_2627_, sizeof(void*)*14 + 1, v_suppressElabErrors_2622_);
v___x_2628_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2588_, v___x_2627_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___x_2627_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref(v___x_2628_);
v___x_2630_ = lean_st_ref_get(v___x_2603_);
lean_dec(v___x_2603_);
lean_dec(v___x_2630_);
v___x_2631_ = lean_string_to_utf8(v_a_2629_);
lean_dec(v_a_2629_);
v___x_2632_ = lean_io_prim_handle_write(v_a_2589_, v___x_2631_);
lean_dec_ref(v___x_2631_);
return v___x_2632_;
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v___x_2603_);
v_a_2633_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2635_ = v___x_2628_;
v_isShared_2636_ = v_isSharedCheck_2651_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2628_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2651_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
if (lean_obj_tag(v_a_2633_) == 0)
{
lean_object* v_msg_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2641_; 
v_msg_2637_ = lean_ctor_get(v_a_2633_, 1);
lean_inc_ref(v_msg_2637_);
lean_dec_ref(v_a_2633_);
v___x_2638_ = l_Lean_MessageData_toString(v_msg_2637_);
v___x_2639_ = lean_mk_io_user_error(v___x_2638_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2639_);
v___x_2641_ = v___x_2635_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
else
{
lean_object* v_id_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
v_id_2643_ = lean_ctor_get(v_a_2633_, 0);
lean_inc(v_id_2643_);
lean_dec_ref(v_a_2633_);
v___x_2644_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0));
v___x_2645_ = l_Nat_reprFast(v_id_2643_);
v___x_2646_ = lean_string_append(v___x_2644_, v___x_2645_);
lean_dec_ref(v___x_2645_);
v___x_2647_ = lean_mk_io_user_error(v___x_2646_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2647_);
v___x_2649_ = v___x_2635_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
v___jp_2652_:
{
if (v___y_2653_ == 0)
{
lean_object* v___x_2654_; lean_object* v_env_2655_; lean_object* v_nextMacroScope_2656_; lean_object* v_ngen_2657_; lean_object* v_auxDeclNGen_2658_; lean_object* v_traceState_2659_; lean_object* v_messages_2660_; lean_object* v_infoState_2661_; lean_object* v_snapshotTasks_2662_; lean_object* v_newDecls_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2672_; 
v___x_2654_ = lean_st_ref_take(v___x_2603_);
v_env_2655_ = lean_ctor_get(v___x_2654_, 0);
v_nextMacroScope_2656_ = lean_ctor_get(v___x_2654_, 1);
v_ngen_2657_ = lean_ctor_get(v___x_2654_, 2);
v_auxDeclNGen_2658_ = lean_ctor_get(v___x_2654_, 3);
v_traceState_2659_ = lean_ctor_get(v___x_2654_, 4);
v_messages_2660_ = lean_ctor_get(v___x_2654_, 6);
v_infoState_2661_ = lean_ctor_get(v___x_2654_, 7);
v_snapshotTasks_2662_ = lean_ctor_get(v___x_2654_, 8);
v_newDecls_2663_ = lean_ctor_get(v___x_2654_, 9);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2672_ == 0)
{
lean_object* v_unused_2673_; 
v_unused_2673_ = lean_ctor_get(v___x_2654_, 5);
lean_dec(v_unused_2673_);
v___x_2665_ = v___x_2654_;
v_isShared_2666_ = v_isSharedCheck_2672_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_newDecls_2663_);
lean_inc(v_snapshotTasks_2662_);
lean_inc(v_infoState_2661_);
lean_inc(v_messages_2660_);
lean_inc(v_traceState_2659_);
lean_inc(v_auxDeclNGen_2658_);
lean_inc(v_ngen_2657_);
lean_inc(v_nextMacroScope_2656_);
lean_inc(v_env_2655_);
lean_dec(v___x_2654_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2672_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2667_ = l_Lean_Kernel_enableDiag(v_env_2655_, v___x_2609_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 5, v___x_2590_);
lean_ctor_set(v___x_2665_, 0, v___x_2667_);
v___x_2669_ = v___x_2665_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_nextMacroScope_2656_);
lean_ctor_set(v_reuseFailAlloc_2671_, 2, v_ngen_2657_);
lean_ctor_set(v_reuseFailAlloc_2671_, 3, v_auxDeclNGen_2658_);
lean_ctor_set(v_reuseFailAlloc_2671_, 4, v_traceState_2659_);
lean_ctor_set(v_reuseFailAlloc_2671_, 5, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2671_, 6, v_messages_2660_);
lean_ctor_set(v_reuseFailAlloc_2671_, 7, v_infoState_2661_);
lean_ctor_set(v_reuseFailAlloc_2671_, 8, v_snapshotTasks_2662_);
lean_ctor_set(v_reuseFailAlloc_2671_, 9, v_newDecls_2663_);
v___x_2669_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_st_ref_set(v___x_2603_, v___x_2669_);
lean_inc(v___x_2603_);
lean_inc(v___x_2595_);
v_fileName_2611_ = v_fileName_2591_;
v_fileMap_2612_ = v___x_2592_;
v_currRecDepth_2613_ = v___x_2593_;
v_ref_2614_ = v___x_2594_;
v_currNamespace_2615_ = v___x_2595_;
v_openDecls_2616_ = v___x_2596_;
v_initHeartbeats_2617_ = v___x_2602_;
v_maxHeartbeats_2618_ = v___x_2597_;
v_quotContext_2619_ = v___x_2595_;
v_currMacroScope_2620_ = v___x_2598_;
v_cancelTk_x3f_2621_ = v___x_2599_;
v_suppressElabErrors_2622_ = v_run_2600_;
v_inheritedTraceOptions_2623_ = v___x_2605_;
v___y_2624_ = v___x_2603_;
goto v___jp_2610_;
}
}
}
else
{
lean_dec_ref(v___x_2590_);
lean_inc(v___x_2603_);
lean_inc(v___x_2595_);
v_fileName_2611_ = v_fileName_2591_;
v_fileMap_2612_ = v___x_2592_;
v_currRecDepth_2613_ = v___x_2593_;
v_ref_2614_ = v___x_2594_;
v_currNamespace_2615_ = v___x_2595_;
v_openDecls_2616_ = v___x_2596_;
v_initHeartbeats_2617_ = v___x_2602_;
v_maxHeartbeats_2618_ = v___x_2597_;
v_quotContext_2619_ = v___x_2595_;
v_currMacroScope_2620_ = v___x_2598_;
v_cancelTk_x3f_2621_ = v___x_2599_;
v_suppressElabErrors_2622_ = v_run_2600_;
v_inheritedTraceOptions_2623_ = v___x_2605_;
v___y_2624_ = v___x_2603_;
goto v___jp_2610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* v___x_2675_, lean_object* v___x_2676_, lean_object* v_mainModuleName_2677_, lean_object* v_a_2678_, lean_object* v___x_2679_, lean_object* v_fileName_2680_, lean_object* v___x_2681_, lean_object* v___x_2682_, lean_object* v___x_2683_, lean_object* v___x_2684_, lean_object* v___x_2685_, lean_object* v___x_2686_, lean_object* v___x_2687_, lean_object* v___x_2688_, lean_object* v_run_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v_run_boxed_2691_; lean_object* v_res_2692_; 
v_run_boxed_2691_ = lean_unbox(v_run_2689_);
v_res_2692_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v___x_2675_, v___x_2676_, v_mainModuleName_2677_, v_a_2678_, v___x_2679_, v_fileName_2680_, v___x_2681_, v___x_2682_, v___x_2683_, v___x_2684_, v___x_2685_, v___x_2686_, v___x_2687_, v___x_2688_, v_run_boxed_2691_);
lean_dec(v_a_2678_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_2693_, lean_object* v_a_2694_, lean_object* v_b_2695_){
_start:
{
lean_object* v_str_2696_; lean_object* v_startInclusive_2697_; lean_object* v_endExclusive_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v_str_2696_ = lean_ctor_get(v_val_2693_, 0);
v_startInclusive_2697_ = lean_ctor_get(v_val_2693_, 1);
v_endExclusive_2698_ = lean_ctor_get(v_val_2693_, 2);
v___x_2699_ = lean_nat_sub(v_endExclusive_2698_, v_startInclusive_2697_);
v___x_2700_ = lean_nat_dec_eq(v_a_2694_, v___x_2699_);
lean_dec(v___x_2699_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; uint32_t v___x_2702_; uint32_t v___x_2703_; uint8_t v___x_2704_; 
v___x_2701_ = lean_nat_add(v_startInclusive_2697_, v_a_2694_);
v___x_2702_ = lean_string_utf8_get_fast(v_str_2696_, v___x_2701_);
v___x_2703_ = 10;
v___x_2704_ = lean_uint32_dec_eq(v___x_2702_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
lean_dec(v_a_2694_);
v___x_2705_ = lean_box(0);
v___x_2706_ = lean_string_utf8_next_fast(v_str_2696_, v___x_2701_);
lean_dec(v___x_2701_);
v___x_2707_ = lean_nat_sub(v___x_2706_, v_startInclusive_2697_);
v_a_2694_ = v___x_2707_;
v_b_2695_ = v___x_2705_;
goto _start;
}
else
{
lean_object* v___x_2709_; 
lean_dec(v___x_2701_);
v___x_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2709_, 0, v_a_2694_);
return v___x_2709_;
}
}
else
{
lean_dec(v_a_2694_);
lean_inc(v_b_2695_);
return v_b_2695_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_2710_, lean_object* v_a_2711_, lean_object* v_b_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_2710_, v_a_2711_, v_b_2712_);
lean_dec(v_b_2712_);
lean_dec_ref(v_val_2710_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_2714_){
_start:
{
uint32_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = 10;
v___x_2717_ = lean_string_push(v_s_2714_, v___x_2716_);
v___x_2718_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__4_spec__6(v___x_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_2719_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_s_2722_){
_start:
{
uint32_t v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = 10;
v___x_2725_ = lean_string_push(v_s_2722_, v___x_2724_);
v___x_2726_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_s_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_s_2727_);
return v_res_2729_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0(void){
_start:
{
lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2730_ = lean_box(0);
v___x_2731_ = lean_internal_has_address_sanitizer(v___x_2730_);
return v___x_2731_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = l_Lean_Options_empty;
v___x_2737_ = l_Lean_Core_getMaxHeartbeats(v___x_2736_);
return v___x_2737_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__5(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2738_ = lean_unsigned_to_nat(1u);
v___x_2739_ = l_Lean_firstFrontendMacroScope;
v___x_2740_ = lean_nat_add(v___x_2739_, v___x_2738_);
return v___x_2740_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2751_ = lean_unsigned_to_nat(32u);
v___x_2752_ = lean_mk_empty_array_with_capacity(v___x_2751_);
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
return v___x_2753_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11(void){
_start:
{
size_t v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2754_ = ((size_t)5ULL);
v___x_2755_ = lean_unsigned_to_nat(0u);
v___x_2756_ = lean_unsigned_to_nat(32u);
v___x_2757_ = lean_mk_empty_array_with_capacity(v___x_2756_);
v___x_2758_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_2759_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v___x_2757_);
lean_ctor_set(v___x_2759_, 2, v___x_2755_);
lean_ctor_set(v___x_2759_, 3, v___x_2755_);
lean_ctor_set_usize(v___x_2759_, 4, v___x_2754_);
return v___x_2759_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12(void){
_start:
{
lean_object* v___x_2760_; uint64_t v___x_2761_; lean_object* v___x_2762_; 
v___x_2760_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__11, &l___private_Lean_Shell_0__Lean_shellMain___closed__11_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11);
v___x_2761_ = 0ULL;
v___x_2762_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set_uint64(v___x_2762_, sizeof(void*)*1, v___x_2761_);
return v___x_2762_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13(void){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2763_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14(void){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2764_);
return v___x_2765_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15(void){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__14, &l___private_Lean_Shell_0__Lean_shellMain___closed__14_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
return v___x_2767_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2768_ = l_Lean_NameSet_empty;
v___x_2769_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__11, &l___private_Lean_Shell_0__Lean_shellMain___closed__11_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11);
v___x_2770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
lean_ctor_set(v___x_2770_, 2, v___x_2768_);
return v___x_2770_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; lean_object* v___x_2774_; 
v___x_2771_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__11, &l___private_Lean_Shell_0__Lean_shellMain___closed__11_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11);
v___x_2772_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__14, &l___private_Lean_Shell_0__Lean_shellMain___closed__14_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14);
v___x_2773_ = 1;
v___x_2774_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2774_, 0, v___x_2772_);
lean_ctor_set(v___x_2774_, 1, v___x_2772_);
lean_ctor_set(v___x_2774_, 2, v___x_2771_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*3, v___x_2773_);
return v___x_2774_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__21));
v___x_2781_ = lean_string_utf8_byte_size(v___x_2780_);
return v___x_2781_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__23(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2782_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__22, &l___private_Lean_Shell_0__Lean_shellMain___closed__22_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22);
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__21));
v___x_2785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
lean_ctor_set(v___x_2785_, 1, v___x_2783_);
lean_ctor_set(v___x_2785_, 2, v___x_2782_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* v_args_2789_, lean_object* v_opts_2790_){
_start:
{
lean_object* v___y_2799_; lean_object* v_fns_2814_; lean_object* v_leanOpts_2833_; lean_object* v_forwardedArgs_2834_; uint8_t v_component_2835_; uint8_t v_printPrefix_2836_; uint8_t v_printLibDir_2837_; uint8_t v_useStdin_2838_; uint8_t v_onlyDeps_2839_; uint8_t v_onlySrcDeps_2840_; uint8_t v_depsJson_2841_; uint32_t v_trustLevel_2842_; lean_object* v_rootDir_x3f_2843_; lean_object* v_setupFileName_x3f_2844_; lean_object* v_oleanFileName_x3f_2845_; lean_object* v_ileanFileName_x3f_2846_; lean_object* v_cFileName_x3f_2847_; lean_object* v_bcFileName_x3f_2848_; uint8_t v_jsonOutput_2849_; lean_object* v_errorOnKinds_2850_; uint8_t v_printStats_2851_; uint8_t v_run_2852_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; 
v_leanOpts_2833_ = lean_ctor_get(v_opts_2790_, 0);
lean_inc_ref(v_leanOpts_2833_);
v_forwardedArgs_2834_ = lean_ctor_get(v_opts_2790_, 1);
lean_inc_ref(v_forwardedArgs_2834_);
v_component_2835_ = lean_ctor_get_uint8(v_opts_2790_, sizeof(void*)*10 + 8);
v_printPrefix_2836_ = lean_ctor_get_uint8(v_opts_2790_, sizeof(void*)*10 + 9);
v_printLibDir_2837_ = lean_ctor_get_uint8(v_opts_2790_, sizeof(void*)*10 + 10);
v_useStdin_2838_ = lean_ctor_get_uint8(v_opts_2790_, sizeof(void*)*10 + 11);
v_onlyDeps_2839_ = lean_ctor_get_uint8(v_opts_2790_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2840_ = lean_ctor_get_uint8(v_opts_2790_, sizeof(void*)*10 + 13);
v_depsJson_2841_ = lean_ctor_get_uint8(v_opts_2790_, sizeof(void*)*10 + 14);
v_trustLevel_2842_ = lean_ctor_get_uint32(v_opts_2790_, sizeof(void*)*10);
v_rootDir_x3f_2843_ = lean_ctor_get(v_opts_2790_, 3);
lean_inc(v_rootDir_x3f_2843_);
v_setupFileName_x3f_2844_ = lean_ctor_get(v_opts_2790_, 4);
lean_inc(v_setupFileName_x3f_2844_);
v_oleanFileName_x3f_2845_ = lean_ctor_get(v_opts_2790_, 5);
lean_inc(v_oleanFileName_x3f_2845_);
v_ileanFileName_x3f_2846_ = lean_ctor_get(v_opts_2790_, 6);
lean_inc(v_ileanFileName_x3f_2846_);
v_cFileName_x3f_2847_ = lean_ctor_get(v_opts_2790_, 7);
lean_inc(v_cFileName_x3f_2847_);
v_bcFileName_x3f_2848_ = lean_ctor_get(v_opts_2790_, 8);
lean_inc(v_bcFileName_x3f_2848_);
v_jsonOutput_2849_ = lean_ctor_get_uint8(v_opts_2790_, sizeof(void*)*10 + 15);
v_errorOnKinds_2850_ = lean_ctor_get(v_opts_2790_, 9);
lean_inc_ref(v_errorOnKinds_2850_);
v_printStats_2851_ = lean_ctor_get_uint8(v_opts_2790_, sizeof(void*)*10 + 16);
v_run_2852_ = lean_ctor_get_uint8(v_opts_2790_, sizeof(void*)*10 + 17);
lean_dec_ref(v_opts_2790_);
if (v_printPrefix_2836_ == 0)
{
if (v_printLibDir_2837_ == 0)
{
uint8_t v___x_2879_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v_mainModuleName_2886_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v_contents_2986_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v_str_3014_; lean_object* v_startInclusive_3015_; lean_object* v_endExclusive_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v_fileName_3118_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3156_; lean_object* v___y_3157_; uint8_t v___y_3188_; lean_object* v_fst_3189_; lean_object* v_snd_3190_; uint8_t v___y_3192_; lean_object* v___x_3222_; lean_object* v_maxMemory_3223_; lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_2879_ = 1;
v___x_3222_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3223_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_leanOpts_2833_, v___x_3222_);
v___x_3224_ = lean_unsigned_to_nat(0u);
v___x_3225_ = lean_nat_dec_eq(v_maxMemory_3223_, v___x_3224_);
if (v___x_3225_ == 0)
{
size_t v___x_3226_; size_t v___x_3227_; size_t v___x_3228_; size_t v___x_3229_; lean_object* v___x_3230_; 
v___x_3226_ = lean_usize_of_nat(v_maxMemory_3223_);
lean_dec(v_maxMemory_3223_);
v___x_3227_ = ((size_t)1024ULL);
v___x_3228_ = lean_usize_mul(v___x_3226_, v___x_3227_);
v___x_3229_ = lean_usize_mul(v___x_3228_, v___x_3227_);
v___x_3230_ = lean_internal_set_max_memory(v___x_3229_);
goto v___jp_3213_;
}
else
{
lean_dec(v_maxMemory_3223_);
goto v___jp_3213_;
}
v___jp_2880_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2887_ = lean_unsigned_to_nat(0u);
v___x_2888_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__2));
lean_inc(v_mainModuleName_2886_);
lean_inc_ref(v_leanOpts_2833_);
v___x_2889_ = l_Lean_Elab_runFrontend(v___y_2883_, v_leanOpts_2833_, v___y_2884_, v_mainModuleName_2886_, v_trustLevel_2842_, v_oleanFileName_x3f_2845_, v_ileanFileName_x3f_2846_, v_jsonOutput_2849_, v_errorOnKinds_2850_, v___x_2888_, v_printStats_2851_, v___y_2885_);
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_ileanFileName_x3f_2846_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2956_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2892_ = v___x_2889_;
v_isShared_2893_ = v_isSharedCheck_2956_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2889_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2956_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
if (lean_obj_tag(v_a_2890_) == 1)
{
if (v_run_2852_ == 0)
{
lean_del_object(v___x_2892_);
lean_dec(v___y_2882_);
if (lean_obj_tag(v_cFileName_x3f_2847_) == 1)
{
lean_object* v_val_2894_; lean_object* v_val_2895_; uint8_t v___x_2896_; lean_object* v___x_2897_; 
v_val_2894_ = lean_ctor_get(v_a_2890_, 0);
lean_inc(v_val_2894_);
v_val_2895_ = lean_ctor_get(v_cFileName_x3f_2847_, 0);
lean_inc(v_val_2895_);
lean_dec_ref(v_cFileName_x3f_2847_);
v___x_2896_ = 1;
v___x_2897_ = lean_io_prim_handle_mk(v_val_2895_, v___x_2896_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___f_2917_; lean_object* v___x_2918_; 
lean_dec(v_val_2895_);
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2897_);
v___x_2899_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__3));
v___x_2900_ = l_Lean_instInhabitedFileMap_default;
v___x_2901_ = l_Lean_Options_empty;
v___x_2902_ = lean_box(0);
v___x_2903_ = lean_box(0);
v___x_2904_ = lean_box(0);
v___x_2905_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__4, &l___private_Lean_Shell_0__Lean_shellMain___closed__4_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4);
v___x_2906_ = l_Lean_firstFrontendMacroScope;
v___x_2907_ = lean_box(0);
v___x_2908_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__5, &l___private_Lean_Shell_0__Lean_shellMain___closed__5_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__5);
v___x_2909_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__8));
v___x_2910_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__9));
v___x_2911_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__12, &l___private_Lean_Shell_0__Lean_shellMain___closed__12_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12);
v___x_2912_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__15, &l___private_Lean_Shell_0__Lean_shellMain___closed__15_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15);
v___x_2913_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__16, &l___private_Lean_Shell_0__Lean_shellMain___closed__16_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16);
v___x_2914_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__17, &l___private_Lean_Shell_0__Lean_shellMain___closed__17_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17);
lean_inc(v_val_2894_);
v___x_2915_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2915_, 0, v_val_2894_);
lean_ctor_set(v___x_2915_, 1, v___x_2908_);
lean_ctor_set(v___x_2915_, 2, v___x_2909_);
lean_ctor_set(v___x_2915_, 3, v___x_2910_);
lean_ctor_set(v___x_2915_, 4, v___x_2911_);
lean_ctor_set(v___x_2915_, 5, v___x_2912_);
lean_ctor_set(v___x_2915_, 6, v___x_2913_);
lean_ctor_set(v___x_2915_, 7, v___x_2914_);
lean_ctor_set(v___x_2915_, 8, v___x_2888_);
lean_ctor_set(v___x_2915_, 9, v___x_2888_);
v___x_2916_ = lean_box(v_run_2852_);
lean_inc(v_mainModuleName_2886_);
v___f_2917_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 16, 15);
lean_closure_set(v___f_2917_, 0, v___x_2915_);
lean_closure_set(v___f_2917_, 1, v___x_2901_);
lean_closure_set(v___f_2917_, 2, v_mainModuleName_2886_);
lean_closure_set(v___f_2917_, 3, v_a_2898_);
lean_closure_set(v___f_2917_, 4, v___x_2912_);
lean_closure_set(v___f_2917_, 5, v___y_2881_);
lean_closure_set(v___f_2917_, 6, v___x_2900_);
lean_closure_set(v___f_2917_, 7, v___x_2887_);
lean_closure_set(v___f_2917_, 8, v___x_2902_);
lean_closure_set(v___f_2917_, 9, v___x_2903_);
lean_closure_set(v___f_2917_, 10, v___x_2904_);
lean_closure_set(v___f_2917_, 11, v___x_2905_);
lean_closure_set(v___f_2917_, 12, v___x_2906_);
lean_closure_set(v___f_2917_, 13, v___x_2907_);
lean_closure_set(v___f_2917_, 14, v___x_2916_);
v___x_2918_ = l_Lean_profileitIOUnsafe___redArg(v___x_2899_, v_leanOpts_2833_, v___f_2917_, v___x_2903_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_dec_ref(v___x_2918_);
v___y_2854_ = v_a_2890_;
v___y_2855_ = v_val_2894_;
v___y_2856_ = v_mainModuleName_2886_;
goto v___jp_2853_;
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec(v_val_2894_);
lean_dec_ref(v_a_2890_);
lean_dec(v_mainModuleName_2886_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec_ref(v_leanOpts_2833_);
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2918_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2918_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
else
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_dec_ref(v___x_2897_);
lean_dec(v_val_2894_);
lean_dec_ref(v_a_2890_);
lean_dec(v_mainModuleName_2886_);
lean_dec_ref(v___y_2881_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec_ref(v_leanOpts_2833_);
v___x_2927_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__18));
v___x_2928_ = lean_string_append(v___x_2927_, v_val_2895_);
lean_dec(v_val_2895_);
v___x_2929_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_2930_ = lean_string_append(v___x_2928_, v___x_2929_);
v___x_2931_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_2930_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2939_; 
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2939_ == 0)
{
lean_object* v_unused_2940_; 
v_unused_2940_ = lean_ctor_get(v___x_2931_, 0);
lean_dec(v_unused_2940_);
v___x_2933_ = v___x_2931_;
v_isShared_2934_ = v_isSharedCheck_2939_;
goto v_resetjp_2932_;
}
else
{
lean_dec(v___x_2931_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2939_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2935_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2935_);
v___x_2937_ = v___x_2933_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
v_a_2941_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2931_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2931_);
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
else
{
lean_object* v_val_2949_; 
lean_dec_ref(v___y_2881_);
lean_dec(v_cFileName_x3f_2847_);
v_val_2949_ = lean_ctor_get(v_a_2890_, 0);
lean_inc(v_val_2949_);
v___y_2854_ = v_a_2890_;
v___y_2855_ = v_val_2949_;
v___y_2856_ = v_mainModuleName_2886_;
goto v___jp_2853_;
}
}
else
{
lean_object* v_val_2950_; uint32_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
lean_dec(v_mainModuleName_2886_);
lean_dec_ref(v___y_2881_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
v_val_2950_ = lean_ctor_get(v_a_2890_, 0);
lean_inc(v_val_2950_);
lean_dec_ref(v_a_2890_);
v___x_2951_ = lean_eval_main(v_val_2950_, v_leanOpts_2833_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v_leanOpts_2833_);
lean_dec(v_val_2950_);
v___x_2952_ = lean_box_uint32(v___x_2951_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2952_);
v___x_2954_ = v___x_2892_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
else
{
lean_del_object(v___x_2892_);
lean_dec(v_mainModuleName_2886_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec_ref(v_leanOpts_2833_);
v___y_2799_ = v_a_2890_;
goto v___jp_2798_;
}
}
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec(v_mainModuleName_2886_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec_ref(v_leanOpts_2833_);
v_a_2957_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2889_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2889_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
v___jp_2965_:
{
if (lean_obj_tag(v___y_2971_) == 0)
{
lean_object* v_a_2972_; 
v_a_2972_ = lean_ctor_get(v___y_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref(v___y_2971_);
v___y_2881_ = v___y_2966_;
v___y_2882_ = v___y_2967_;
v___y_2883_ = v___y_2968_;
v___y_2884_ = v___y_2969_;
v___y_2885_ = v___y_2970_;
v_mainModuleName_2886_ = v_a_2972_;
goto v___jp_2880_;
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec(v_ileanFileName_x3f_2846_);
lean_dec(v_oleanFileName_x3f_2845_);
lean_dec_ref(v_leanOpts_2833_);
v_a_2973_ = lean_ctor_get(v___y_2971_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___y_2971_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___y_2971_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___y_2971_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
v___jp_2981_:
{
if (lean_obj_tag(v_setupFileName_x3f_2844_) == 0)
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_box(0);
if (lean_obj_tag(v___y_2984_) == 1)
{
lean_object* v_val_2988_; lean_object* v___x_2989_; 
v_val_2988_ = lean_ctor_get(v___y_2984_, 0);
lean_inc(v_val_2988_);
lean_dec_ref(v___y_2984_);
v___x_2989_ = l_Lean_moduleNameOfFileName(v_val_2988_, v_rootDir_x3f_2843_);
if (lean_obj_tag(v___x_2989_) == 0)
{
v___y_2966_ = v___y_2982_;
v___y_2967_ = v___y_2983_;
v___y_2968_ = v_contents_2986_;
v___y_2969_ = v___y_2985_;
v___y_2970_ = v___x_2987_;
v___y_2971_ = v___x_2989_;
goto v___jp_2965_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_2845_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_2847_) == 0)
{
lean_object* v___x_2990_; 
lean_dec_ref(v___x_2989_);
v___x_2990_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___y_2881_ = v___y_2982_;
v___y_2882_ = v___y_2983_;
v___y_2883_ = v_contents_2986_;
v___y_2884_ = v___y_2985_;
v___y_2885_ = v___x_2987_;
v_mainModuleName_2886_ = v___x_2990_;
goto v___jp_2880_;
}
else
{
v___y_2966_ = v___y_2982_;
v___y_2967_ = v___y_2983_;
v___y_2968_ = v_contents_2986_;
v___y_2969_ = v___y_2985_;
v___y_2970_ = v___x_2987_;
v___y_2971_ = v___x_2989_;
goto v___jp_2965_;
}
}
else
{
v___y_2966_ = v___y_2982_;
v___y_2967_ = v___y_2983_;
v___y_2968_ = v_contents_2986_;
v___y_2969_ = v___y_2985_;
v___y_2970_ = v___x_2987_;
v___y_2971_ = v___x_2989_;
goto v___jp_2965_;
}
}
}
else
{
lean_object* v___x_2991_; 
lean_dec(v___y_2984_);
lean_dec(v_rootDir_x3f_2843_);
v___x_2991_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___y_2881_ = v___y_2982_;
v___y_2882_ = v___y_2983_;
v___y_2883_ = v_contents_2986_;
v___y_2884_ = v___y_2985_;
v___y_2885_ = v___x_2987_;
v_mainModuleName_2886_ = v___x_2991_;
goto v___jp_2880_;
}
}
else
{
lean_object* v_val_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v___y_2984_);
lean_dec(v_rootDir_x3f_2843_);
v_val_2992_ = lean_ctor_get(v_setupFileName_x3f_2844_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_setupFileName_x3f_2844_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2994_ = v_setupFileName_x3f_2844_;
v_isShared_2995_ = v_isSharedCheck_3010_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_val_2992_);
lean_dec(v_setupFileName_x3f_2844_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3010_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_ModuleSetup_load(v_val_2992_);
lean_dec(v_val_2992_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v_name_2998_; lean_object* v___x_3000_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref(v___x_2996_);
v_name_2998_ = lean_ctor_get(v_a_2997_, 0);
lean_inc(v_name_2998_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v_a_2997_);
v___x_3000_ = v___x_2994_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2997_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
v___y_2881_ = v___y_2982_;
v___y_2882_ = v___y_2983_;
v___y_2883_ = v_contents_2986_;
v___y_2884_ = v___y_2985_;
v___y_2885_ = v___x_3000_;
v_mainModuleName_2886_ = v_name_2998_;
goto v___jp_2880_;
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_del_object(v___x_2994_);
lean_dec_ref(v_contents_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec(v_ileanFileName_x3f_2846_);
lean_dec(v_oleanFileName_x3f_2845_);
lean_dec_ref(v_leanOpts_2833_);
v_a_3002_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2996_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2996_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
}
v___jp_3011_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3020_ = lean_nat_add(v_startInclusive_3015_, v___y_3019_);
lean_dec(v___y_3019_);
lean_inc(v___x_3020_);
lean_inc_ref(v_str_3014_);
v___x_3021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3021_, 0, v_str_3014_);
lean_ctor_set(v___x_3021_, 1, v_startInclusive_3015_);
lean_ctor_set(v___x_3021_, 2, v___x_3020_);
v___x_3022_ = l_String_Slice_trimAscii(v___x_3021_);
v___x_3023_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__23, &l___private_Lean_Shell_0__Lean_shellMain___closed__23_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__23);
v___x_3024_ = l_String_Slice_beq(v___x_3022_, v___x_3023_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_dec(v___x_3020_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec(v_endExclusive_3016_);
lean_dec_ref(v_str_3014_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec(v_ileanFileName_x3f_2846_);
lean_dec(v_oleanFileName_x3f_2845_);
lean_dec(v_setupFileName_x3f_2844_);
lean_dec(v_rootDir_x3f_2843_);
lean_dec_ref(v_leanOpts_2833_);
v___x_3025_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__24));
v___x_3026_ = l_String_Slice_toString(v___x_3022_);
lean_dec_ref(v___x_3022_);
v___x_3027_ = lean_string_append(v___x_3025_, v___x_3026_);
lean_dec_ref(v___x_3026_);
v___x_3028_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_3029_ = lean_string_append(v___x_3027_, v___x_3028_);
v___x_3030_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3029_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3038_; 
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3038_ == 0)
{
lean_object* v_unused_3039_; 
v_unused_3039_ = lean_ctor_get(v___x_3030_, 0);
lean_dec(v_unused_3039_);
v___x_3032_ = v___x_3030_;
v_isShared_3033_ = v_isSharedCheck_3038_;
goto v_resetjp_3031_;
}
else
{
lean_dec(v___x_3030_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3038_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3034_; lean_object* v___x_3036_; 
v___x_3034_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v___x_3034_);
v___x_3036_ = v___x_3032_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
v_a_3040_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_3030_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3030_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
else
{
lean_object* v___x_3048_; 
lean_dec_ref(v___x_3022_);
v___x_3048_ = lean_string_utf8_extract(v_str_3014_, v___x_3020_, v_endExclusive_3016_);
lean_dec(v_endExclusive_3016_);
lean_dec(v___x_3020_);
lean_dec_ref(v_str_3014_);
v___y_2982_ = v___y_3012_;
v___y_2983_ = v___y_3013_;
v___y_2984_ = v___y_3017_;
v___y_2985_ = v___y_3018_;
v_contents_2986_ = v___x_3048_;
goto v___jp_2981_;
}
}
v___jp_3049_:
{
if (lean_obj_tag(v___y_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; 
v_a_3054_ = lean_ctor_get(v___y_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref(v___y_3053_);
v___x_3055_ = lean_decode_lossy_utf8(v_a_3054_);
lean_dec(v_a_3054_);
if (v_onlyDeps_2839_ == 0)
{
if (v_onlySrcDeps_2840_ == 0)
{
lean_object* v___x_3056_; 
lean_inc_ref(v___x_3055_);
v___x_3056_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_3055_);
if (lean_obj_tag(v___x_3056_) == 1)
{
lean_object* v_val_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
lean_dec_ref(v___x_3055_);
v_val_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_val_3057_);
lean_dec_ref(v___x_3056_);
v___x_3058_ = lean_unsigned_to_nat(0u);
v___x_3059_ = lean_box(0);
v___x_3060_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3057_, v___x_3058_, v___x_3059_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_str_3061_; lean_object* v_startInclusive_3062_; lean_object* v_endExclusive_3063_; lean_object* v___x_3064_; 
v_str_3061_ = lean_ctor_get(v_val_3057_, 0);
lean_inc_ref(v_str_3061_);
v_startInclusive_3062_ = lean_ctor_get(v_val_3057_, 1);
lean_inc(v_startInclusive_3062_);
v_endExclusive_3063_ = lean_ctor_get(v_val_3057_, 2);
lean_inc(v_endExclusive_3063_);
lean_dec(v_val_3057_);
v___x_3064_ = lean_nat_sub(v_endExclusive_3063_, v_startInclusive_3062_);
lean_inc_ref(v___y_3052_);
v___y_3012_ = v___y_3052_;
v___y_3013_ = v___y_3051_;
v_str_3014_ = v_str_3061_;
v_startInclusive_3015_ = v_startInclusive_3062_;
v_endExclusive_3016_ = v_endExclusive_3063_;
v___y_3017_ = v___y_3050_;
v___y_3018_ = v___y_3052_;
v___y_3019_ = v___x_3064_;
goto v___jp_3011_;
}
else
{
lean_object* v_val_3065_; lean_object* v_str_3066_; lean_object* v_startInclusive_3067_; lean_object* v_endExclusive_3068_; 
v_val_3065_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_val_3065_);
lean_dec_ref(v___x_3060_);
v_str_3066_ = lean_ctor_get(v_val_3057_, 0);
lean_inc_ref(v_str_3066_);
v_startInclusive_3067_ = lean_ctor_get(v_val_3057_, 1);
lean_inc(v_startInclusive_3067_);
v_endExclusive_3068_ = lean_ctor_get(v_val_3057_, 2);
lean_inc(v_endExclusive_3068_);
lean_dec(v_val_3057_);
lean_inc_ref(v___y_3052_);
v___y_3012_ = v___y_3052_;
v___y_3013_ = v___y_3051_;
v_str_3014_ = v_str_3066_;
v_startInclusive_3015_ = v_startInclusive_3067_;
v_endExclusive_3016_ = v_endExclusive_3068_;
v___y_3017_ = v___y_3050_;
v___y_3018_ = v___y_3052_;
v___y_3019_ = v_val_3065_;
goto v___jp_3011_;
}
}
else
{
lean_dec(v___x_3056_);
lean_inc_ref(v___y_3052_);
v___y_2982_ = v___y_3052_;
v___y_2983_ = v___y_3051_;
v___y_2984_ = v___y_3050_;
v___y_2985_ = v___y_3052_;
v_contents_2986_ = v___x_3055_;
goto v___jp_2981_;
}
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_dec(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec(v_ileanFileName_x3f_2846_);
lean_dec(v_oleanFileName_x3f_2845_);
lean_dec(v_setupFileName_x3f_2844_);
lean_dec(v_rootDir_x3f_2843_);
lean_dec_ref(v_leanOpts_2833_);
v___x_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3069_, 0, v___y_3052_);
v___x_3070_ = l_Lean_Elab_printImportSrcs(v___x_3055_, v___x_3069_);
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
v___x_3074_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
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
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_dec(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec(v_ileanFileName_x3f_2846_);
lean_dec(v_oleanFileName_x3f_2845_);
lean_dec(v_setupFileName_x3f_2844_);
lean_dec(v_rootDir_x3f_2843_);
lean_dec_ref(v_leanOpts_2833_);
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___y_3052_);
v___x_3089_ = l_Lean_Elab_printImports(v___x_3055_, v___x_3088_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3097_; 
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3097_ == 0)
{
lean_object* v_unused_3098_; 
v_unused_3098_ = lean_ctor_get(v___x_3089_, 0);
lean_dec(v_unused_3098_);
v___x_3091_ = v___x_3089_;
v_isShared_3092_ = v_isSharedCheck_3097_;
goto v_resetjp_3090_;
}
else
{
lean_dec(v___x_3089_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3097_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v___x_3095_; 
v___x_3093_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3093_);
v___x_3095_ = v___x_3091_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
v_a_3099_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3089_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3089_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec(v_ileanFileName_x3f_2846_);
lean_dec(v_oleanFileName_x3f_2845_);
lean_dec(v_setupFileName_x3f_2844_);
lean_dec(v_rootDir_x3f_2843_);
lean_dec_ref(v_leanOpts_2833_);
v_a_3107_ = lean_ctor_get(v___y_3053_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___y_3053_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___y_3053_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___y_3053_);
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
v___jp_3115_:
{
if (v_useStdin_2838_ == 0)
{
lean_object* v___x_3119_; 
v___x_3119_ = l_IO_FS_readBinFile(v_fileName_3118_);
v___y_3050_ = v___y_3117_;
v___y_3051_ = v___y_3116_;
v___y_3052_ = v_fileName_3118_;
v___y_3053_ = v___x_3119_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = lean_get_stdin();
v___x_3121_ = l_IO_FS_Stream_readBinToEnd(v___x_3120_);
v___y_3050_ = v___y_3117_;
v___y_3051_ = v___y_3116_;
v___y_3052_ = v_fileName_3118_;
v___y_3053_ = v___x_3121_;
goto v___jp_3049_;
}
}
v___jp_3122_:
{
if (lean_obj_tag(v___y_3124_) == 1)
{
lean_object* v_val_3125_; 
v_val_3125_ = lean_ctor_get(v___y_3124_, 0);
lean_inc(v_val_3125_);
v___y_3116_ = v___y_3123_;
v___y_3117_ = v___y_3124_;
v_fileName_3118_ = v_val_3125_;
goto v___jp_3115_;
}
else
{
if (v_useStdin_2838_ == 0)
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec(v_ileanFileName_x3f_2846_);
lean_dec(v_oleanFileName_x3f_2845_);
lean_dec(v_setupFileName_x3f_2844_);
lean_dec(v_rootDir_x3f_2843_);
lean_dec_ref(v_leanOpts_2833_);
v___x_3126_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__25));
v___x_3127_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3126_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v___x_3128_; 
lean_dec_ref(v___x_3127_);
v___x_3128_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_2879_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3136_; 
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v___x_3128_, 0);
lean_dec(v_unused_3137_);
v___x_3130_ = v___x_3128_;
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
else
{
lean_dec(v___x_3128_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3132_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3132_);
v___x_3134_ = v___x_3130_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
v_a_3138_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3128_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3128_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
v_a_3146_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3127_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3127_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
else
{
lean_object* v___x_3154_; 
v___x_3154_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__26));
v___y_3116_ = v___y_3123_;
v___y_3117_ = v___y_3124_;
v_fileName_3118_ = v___x_3154_;
goto v___jp_3115_;
}
}
}
v___jp_3155_:
{
uint8_t v___x_3158_; 
v___x_3158_ = l_List_isEmpty___redArg(v___y_3156_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_dec(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec(v_ileanFileName_x3f_2846_);
lean_dec(v_oleanFileName_x3f_2845_);
lean_dec(v_setupFileName_x3f_2844_);
lean_dec(v_rootDir_x3f_2843_);
lean_dec_ref(v_leanOpts_2833_);
v___x_3159_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__25));
v___x_3160_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3159_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v___x_3161_; 
lean_dec_ref(v___x_3160_);
v___x_3161_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_2879_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3169_; 
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3169_ == 0)
{
lean_object* v_unused_3170_; 
v_unused_3170_ = lean_ctor_get(v___x_3161_, 0);
lean_dec(v_unused_3170_);
v___x_3163_ = v___x_3161_;
v_isShared_3164_ = v_isSharedCheck_3169_;
goto v_resetjp_3162_;
}
else
{
lean_dec(v___x_3161_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3169_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3165_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v___x_3165_);
v___x_3167_ = v___x_3163_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
v_a_3171_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3161_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3161_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
v_a_3179_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3160_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3160_);
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
v___y_3123_ = v___y_3156_;
v___y_3124_ = v___y_3157_;
goto v___jp_3122_;
}
}
v___jp_3187_:
{
if (v_run_2852_ == 0)
{
v___y_3156_ = v_snd_3190_;
v___y_3157_ = v_fst_3189_;
goto v___jp_3155_;
}
else
{
if (v___y_3188_ == 0)
{
v___y_3123_ = v_snd_3190_;
v___y_3124_ = v_fst_3189_;
goto v___jp_3122_;
}
else
{
v___y_3156_ = v_snd_3190_;
v___y_3157_ = v_fst_3189_;
goto v___jp_3155_;
}
}
}
v___jp_3191_:
{
if (lean_obj_tag(v_args_2789_) == 0)
{
lean_object* v___x_3193_; 
v___x_3193_ = lean_box(0);
v___y_3188_ = v___y_3192_;
v_fst_3189_ = v___x_3193_;
v_snd_3190_ = v_args_2789_;
goto v___jp_3187_;
}
else
{
lean_object* v_head_3194_; lean_object* v_tail_3195_; lean_object* v___x_3196_; 
v_head_3194_ = lean_ctor_get(v_args_2789_, 0);
lean_inc(v_head_3194_);
v_tail_3195_ = lean_ctor_get(v_args_2789_, 1);
lean_inc(v_tail_3195_);
lean_dec_ref(v_args_2789_);
v___x_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3196_, 0, v_head_3194_);
v___y_3188_ = v___y_3192_;
v_fst_3189_ = v___x_3196_;
v_snd_3190_ = v_tail_3195_;
goto v___jp_3187_;
}
}
v___jp_3197_:
{
switch(v_component_2835_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_2834_);
if (v_onlyDeps_2839_ == 0)
{
v___y_3192_ = v_onlyDeps_2839_;
goto v___jp_3191_;
}
else
{
if (v_depsJson_2841_ == 0)
{
v___y_3192_ = v_depsJson_2841_;
goto v___jp_3191_;
}
else
{
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec(v_ileanFileName_x3f_2846_);
lean_dec(v_oleanFileName_x3f_2845_);
lean_dec(v_setupFileName_x3f_2844_);
lean_dec(v_rootDir_x3f_2843_);
lean_dec_ref(v_leanOpts_2833_);
if (v_useStdin_2838_ == 0)
{
lean_object* v___x_3198_; 
v___x_3198_ = lean_array_mk(v_args_2789_);
v_fns_2814_ = v___x_3198_;
goto v___jp_2813_;
}
else
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
lean_dec(v_args_2789_);
v___x_3199_ = lean_get_stdin();
v___x_3200_ = l_IO_FS_Stream_lines(v___x_3199_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref(v___x_3200_);
v_fns_2814_ = v_a_3201_;
goto v___jp_2813_;
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
v_a_3202_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3200_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3200_);
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
}
}
}
case 1:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec(v_ileanFileName_x3f_2846_);
lean_dec(v_oleanFileName_x3f_2845_);
lean_dec(v_setupFileName_x3f_2844_);
lean_dec(v_rootDir_x3f_2843_);
lean_dec_ref(v_leanOpts_2833_);
lean_dec(v_args_2789_);
v___x_3210_ = lean_array_to_list(v_forwardedArgs_2834_);
v___x_3211_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3210_);
return v___x_3211_;
}
default: 
{
lean_object* v___x_3212_; 
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec(v_ileanFileName_x3f_2846_);
lean_dec(v_oleanFileName_x3f_2845_);
lean_dec(v_setupFileName_x3f_2844_);
lean_dec(v_rootDir_x3f_2843_);
lean_dec_ref(v_forwardedArgs_2834_);
lean_dec(v_args_2789_);
v___x_3212_ = l_Lean_Server_FileWorker_workerMain(v_leanOpts_2833_);
return v___x_3212_;
}
}
}
v___jp_3213_:
{
lean_object* v___x_3214_; lean_object* v_timeout_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; 
v___x_3214_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3215_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_leanOpts_2833_, v___x_3214_);
v___x_3216_ = lean_unsigned_to_nat(0u);
v___x_3217_ = lean_nat_dec_eq(v_timeout_3215_, v___x_3216_);
if (v___x_3217_ == 0)
{
size_t v___x_3218_; size_t v___x_3219_; size_t v___x_3220_; lean_object* v___x_3221_; 
v___x_3218_ = lean_usize_of_nat(v_timeout_3215_);
lean_dec(v_timeout_3215_);
v___x_3219_ = ((size_t)1000ULL);
v___x_3220_ = lean_usize_mul(v___x_3218_, v___x_3219_);
v___x_3221_ = lean_internal_set_max_heartbeat(v___x_3220_);
goto v___jp_3197_;
}
else
{
lean_dec(v_timeout_3215_);
goto v___jp_3197_;
}
}
}
else
{
lean_object* v___x_3231_; 
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec(v_ileanFileName_x3f_2846_);
lean_dec(v_oleanFileName_x3f_2845_);
lean_dec(v_setupFileName_x3f_2844_);
lean_dec(v_rootDir_x3f_2843_);
lean_dec_ref(v_forwardedArgs_2834_);
lean_dec_ref(v_leanOpts_2833_);
lean_dec(v_args_2789_);
v___x_3231_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3233_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref(v___x_3231_);
v___x_3233_ = l_Lean_getLibDir(v_a_3232_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3235_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_a_3234_);
lean_dec_ref(v___x_3233_);
v___x_3235_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3234_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3243_; 
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; 
v_unused_3244_ = lean_ctor_get(v___x_3235_, 0);
lean_dec(v_unused_3244_);
v___x_3237_ = v___x_3235_;
v_isShared_3238_ = v_isSharedCheck_3243_;
goto v_resetjp_3236_;
}
else
{
lean_dec(v___x_3235_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3243_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3239_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v___x_3239_);
v___x_3241_ = v___x_3237_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
v_a_3245_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3235_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3235_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
v_a_3253_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3233_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3233_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
v_a_3261_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3231_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3231_);
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
else
{
lean_object* v___x_3269_; 
lean_dec_ref(v_errorOnKinds_2850_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec(v_cFileName_x3f_2847_);
lean_dec(v_ileanFileName_x3f_2846_);
lean_dec(v_oleanFileName_x3f_2845_);
lean_dec(v_setupFileName_x3f_2844_);
lean_dec(v_rootDir_x3f_2843_);
lean_dec_ref(v_forwardedArgs_2834_);
lean_dec_ref(v_leanOpts_2833_);
lean_dec(v_args_2789_);
v___x_3269_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3271_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref(v___x_3269_);
v___x_3271_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3270_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3279_; 
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3279_ == 0)
{
lean_object* v_unused_3280_; 
v_unused_3280_ = lean_ctor_get(v___x_3271_, 0);
lean_dec(v_unused_3280_);
v___x_3273_ = v___x_3271_;
v_isShared_3274_ = v_isSharedCheck_3279_;
goto v_resetjp_3272_;
}
else
{
lean_dec(v___x_3271_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3279_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v___x_3277_; 
v___x_3275_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3275_);
v___x_3277_ = v___x_3273_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3275_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
v_a_3281_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3271_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3271_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
v_a_3289_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3269_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3269_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
v___jp_2792_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
return v___x_2794_;
}
v___jp_2795_:
{
uint8_t v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = 0;
v___x_2797_ = lean_io_exit(v___x_2796_);
return v___x_2797_;
}
v___jp_2798_:
{
lean_object* v___x_2800_; uint8_t v___x_2801_; 
v___x_2800_ = lean_display_cumulative_profiling_times();
v___x_2801_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__0, &l___private_Lean_Shell_0__Lean_shellMain___closed__0_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0);
if (v___x_2801_ == 0)
{
if (lean_obj_tag(v___y_2799_) == 0)
{
if (v___x_2801_ == 0)
{
uint8_t v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = 1;
v___x_2803_ = lean_io_exit(v___x_2802_);
return v___x_2803_;
}
else
{
goto v___jp_2795_;
}
}
else
{
lean_dec_ref(v___y_2799_);
goto v___jp_2795_;
}
}
else
{
if (lean_obj_tag(v___y_2799_) == 0)
{
goto v___jp_2792_;
}
else
{
lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2811_; 
v_isSharedCheck_2811_ = !lean_is_exclusive(v___y_2799_);
if (v_isSharedCheck_2811_ == 0)
{
lean_object* v_unused_2812_; 
v_unused_2812_ = lean_ctor_get(v___y_2799_, 0);
lean_dec(v_unused_2812_);
v___x_2805_ = v___y_2799_;
v_isShared_2806_ = v_isSharedCheck_2811_;
goto v_resetjp_2804_;
}
else
{
lean_dec(v___y_2799_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2811_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
if (v___x_2801_ == 0)
{
lean_del_object(v___x_2805_);
goto v___jp_2792_;
}
else
{
lean_object* v___x_2807_; lean_object* v___x_2809_; 
v___x_2807_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2806_ == 0)
{
lean_ctor_set_tag(v___x_2805_, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2807_);
v___x_2809_ = v___x_2805_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2807_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
}
v___jp_2813_:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_printImportsJson(v_fns_2814_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2823_; 
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v___x_2815_, 0);
lean_dec(v_unused_2824_);
v___x_2817_ = v___x_2815_;
v_isShared_2818_ = v_isSharedCheck_2823_;
goto v_resetjp_2816_;
}
else
{
lean_dec(v___x_2815_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2823_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2819_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2819_);
v___x_2821_ = v___x_2817_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_a_2825_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2815_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2815_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
v___jp_2853_:
{
if (lean_obj_tag(v_bcFileName_x3f_2848_) == 1)
{
lean_object* v_val_2857_; lean_object* v___x_2858_; 
v_val_2857_ = lean_ctor_get(v_bcFileName_x3f_2848_, 0);
lean_inc(v_val_2857_);
lean_dec_ref(v_bcFileName_x3f_2848_);
v___x_2858_ = lean_init_llvm();
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
lean_dec_ref(v___x_2858_);
v___x_2859_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__1));
v___x_2860_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(v___x_2860_, 0, v___y_2855_);
lean_closure_set(v___x_2860_, 1, v___y_2856_);
lean_closure_set(v___x_2860_, 2, v_val_2857_);
v___x_2861_ = lean_box(0);
v___x_2862_ = l_Lean_profileitIOUnsafe___redArg(v___x_2859_, v_leanOpts_2833_, v___x_2860_, v___x_2861_);
lean_dec_ref(v_leanOpts_2833_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_dec_ref(v___x_2862_);
v___y_2799_ = v___y_2854_;
goto v___jp_2798_;
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v___y_2854_);
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_val_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v_leanOpts_2833_);
v_a_2871_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2858_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2858_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
else
{
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v_bcFileName_x3f_2848_);
lean_dec_ref(v_leanOpts_2833_);
v___y_2799_ = v___y_2854_;
goto v___jp_2798_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3297_, lean_object* v_opts_3298_, lean_object* v_a_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = lean_shell_main(v_args_3297_, v_opts_3298_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3301_, lean_object* v_inst_3302_, lean_object* v_R_3303_, lean_object* v_a_3304_, lean_object* v_b_3305_, lean_object* v_c_3306_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3301_, v_a_3304_, v_b_3305_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3308_, lean_object* v_inst_3309_, lean_object* v_R_3310_, lean_object* v_a_3311_, lean_object* v_b_3312_, lean_object* v_c_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3308_, v_inst_3309_, v_R_3310_, v_a_3311_, v_b_3312_, v_c_3313_);
lean_dec(v_b_3312_);
lean_dec_ref(v_val_3308_);
return v_res_3314_;
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
