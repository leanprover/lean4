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
lean_dec_ref_known(v___x_197_, 1);
v___x_198_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__2));
lean_inc_ref(v___y_195_);
v___x_199_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_198_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec_ref_known(v___x_199_, 1);
v___x_200_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__3));
lean_inc_ref(v___y_195_);
v___x_201_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_200_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec_ref_known(v___x_201_, 1);
v___x_202_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__4));
lean_inc_ref(v___y_195_);
v___x_203_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec_ref_known(v___x_203_, 1);
v___x_204_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__5));
lean_inc_ref(v___y_195_);
v___x_205_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec_ref_known(v___x_205_, 1);
v___x_206_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__6));
lean_inc_ref(v___y_195_);
v___x_207_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec_ref_known(v___x_207_, 1);
v___x_208_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__7));
lean_inc_ref(v___y_195_);
v___x_209_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_208_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec_ref_known(v___x_209_, 1);
v___x_210_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__8));
lean_inc_ref(v___y_195_);
v___x_211_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_210_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec_ref_known(v___x_211_, 1);
v___x_212_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__9));
lean_inc_ref(v___y_195_);
v___x_213_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_212_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec_ref_known(v___x_213_, 1);
v___x_214_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__10));
lean_inc_ref(v___y_195_);
v___x_215_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_214_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec_ref_known(v___x_215_, 1);
v___x_216_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__11));
lean_inc_ref(v___y_195_);
v___x_217_ = l_IO_FS_Stream_putStrLn(v___y_195_, v___x_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
uint8_t v___x_218_; 
lean_dec_ref_known(v___x_217_, 1);
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
lean_dec_ref_known(v___x_220_, 1);
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
lean_dec_ref_known(v___x_224_, 1);
v___x_225_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__14));
lean_inc_ref(v_out_222_);
v___x_226_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_225_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec_ref_known(v___x_226_, 1);
v___x_227_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__15));
lean_inc_ref(v_out_222_);
v___x_228_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_227_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec_ref_known(v___x_228_, 1);
v___x_229_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__16));
lean_inc_ref(v_out_222_);
v___x_230_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec_ref_known(v___x_230_, 1);
v___x_231_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__17));
lean_inc_ref(v_out_222_);
v___x_232_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_231_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec_ref_known(v___x_232_, 1);
v___x_233_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__18));
lean_inc_ref(v_out_222_);
v___x_234_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_233_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec_ref_known(v___x_234_, 1);
v___x_235_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__19));
lean_inc_ref(v_out_222_);
v___x_236_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_235_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec_ref_known(v___x_236_, 1);
v___x_237_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__20));
lean_inc_ref(v_out_222_);
v___x_238_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_237_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref_known(v___x_238_, 1);
v___x_239_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__21));
lean_inc_ref(v_out_222_);
v___x_240_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_239_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec_ref_known(v___x_240_, 1);
v___x_241_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__22));
lean_inc_ref(v_out_222_);
v___x_242_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_241_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec_ref_known(v___x_242_, 1);
v___x_243_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__23));
lean_inc_ref(v_out_222_);
v___x_244_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_243_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec_ref_known(v___x_244_, 1);
v___x_245_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__24));
lean_inc_ref(v_out_222_);
v___x_246_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_245_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref_known(v___x_246_, 1);
v___x_247_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__25));
lean_inc_ref(v_out_222_);
v___x_248_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_247_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref_known(v___x_248_, 1);
v___x_249_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__26));
lean_inc_ref(v_out_222_);
v___x_250_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_249_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec_ref_known(v___x_250_, 1);
v___x_251_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__27));
lean_inc_ref(v_out_222_);
v___x_252_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec_ref_known(v___x_252_, 1);
v___x_253_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__28));
lean_inc_ref(v_out_222_);
v___x_254_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_253_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref_known(v___x_254_, 1);
v___x_255_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__29));
lean_inc_ref(v_out_222_);
v___x_256_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_255_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec_ref_known(v___x_256_, 1);
v___x_257_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__30));
lean_inc_ref(v_out_222_);
v___x_258_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_257_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref_known(v___x_258_, 1);
v___x_259_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__31));
lean_inc_ref(v_out_222_);
v___x_260_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_259_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec_ref_known(v___x_260_, 1);
v___x_261_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__32));
lean_inc_ref(v_out_222_);
v___x_262_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_261_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref_known(v___x_262_, 1);
v___x_263_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__33));
lean_inc_ref(v_out_222_);
v___x_264_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_263_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec_ref_known(v___x_264_, 1);
v___x_265_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__34));
lean_inc_ref(v_out_222_);
v___x_266_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_265_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec_ref_known(v___x_266_, 1);
v___x_267_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__35));
lean_inc_ref(v_out_222_);
v___x_268_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
uint8_t v___x_269_; 
lean_dec_ref_known(v___x_268_, 1);
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
lean_dec_ref_known(v___x_271_, 1);
v___x_272_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__38));
lean_inc_ref(v_out_222_);
v___x_273_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_272_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec_ref_known(v___x_273_, 1);
v___x_274_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__39));
lean_inc_ref(v_out_222_);
v___x_275_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_274_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec_ref_known(v___x_275_, 1);
v___x_276_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__40));
lean_inc_ref(v_out_222_);
v___x_277_ = l_IO_FS_Stream_putStrLn(v_out_222_, v___x_276_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_dec_ref_known(v___x_277_, 1);
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
lean_object* v___y_1035_; lean_object* v___y_1075_; uint32_t v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = 101;
v___x_1136_ = lean_uint32_dec_eq(v_opt_932_, v___x_1135_);
if (v___x_1136_ == 0)
{
uint32_t v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = 106;
v___x_1138_ = lean_uint32_dec_eq(v_opt_932_, v___x_1137_);
if (v___x_1138_ == 0)
{
uint32_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = 118;
v___x_1140_ = lean_uint32_dec_eq(v_opt_932_, v___x_1139_);
if (v___x_1140_ == 0)
{
uint32_t v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = 86;
v___x_1142_ = lean_uint32_dec_eq(v_opt_932_, v___x_1141_);
if (v___x_1142_ == 0)
{
uint32_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = 103;
v___x_1144_ = lean_uint32_dec_eq(v_opt_932_, v___x_1143_);
if (v___x_1144_ == 0)
{
uint32_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = 104;
v___x_1146_ = lean_uint32_dec_eq(v_opt_932_, v___x_1145_);
if (v___x_1146_ == 0)
{
uint32_t v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = 102;
v___x_1148_ = lean_uint32_dec_eq(v_opt_932_, v___x_1147_);
if (v___x_1148_ == 0)
{
uint32_t v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = 99;
v___x_1150_ = lean_uint32_dec_eq(v_opt_932_, v___x_1149_);
if (v___x_1150_ == 0)
{
uint32_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = 98;
v___x_1152_ = lean_uint32_dec_eq(v_opt_932_, v___x_1151_);
if (v___x_1152_ == 0)
{
uint32_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = 115;
v___x_1154_ = lean_uint32_dec_eq(v_opt_932_, v___x_1153_);
if (v___x_1154_ == 0)
{
uint32_t v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = 73;
v___x_1156_ = lean_uint32_dec_eq(v_opt_932_, v___x_1155_);
if (v___x_1156_ == 0)
{
uint32_t v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = 114;
v___x_1158_ = lean_uint32_dec_eq(v_opt_932_, v___x_1157_);
if (v___x_1158_ == 0)
{
uint32_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = 111;
v___x_1160_ = lean_uint32_dec_eq(v_opt_932_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint32_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = 105;
v___x_1162_ = lean_uint32_dec_eq(v_opt_932_, v___x_1161_);
if (v___x_1162_ == 0)
{
uint32_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = 82;
v___x_1164_ = lean_uint32_dec_eq(v_opt_932_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint32_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = 77;
v___x_1166_ = lean_uint32_dec_eq(v_opt_932_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint32_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = 84;
v___x_1168_ = lean_uint32_dec_eq(v_opt_932_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint32_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = 116;
v___x_1170_ = lean_uint32_dec_eq(v_opt_932_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint32_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = 113;
v___x_1172_ = lean_uint32_dec_eq(v_opt_932_, v___x_1171_);
if (v___x_1172_ == 0)
{
uint32_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 100;
v___x_1174_ = lean_uint32_dec_eq(v_opt_932_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint32_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = 79;
v___x_1176_ = lean_uint32_dec_eq(v_opt_932_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint32_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = 78;
v___x_1178_ = lean_uint32_dec_eq(v_opt_932_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint32_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = 74;
v___x_1180_ = lean_uint32_dec_eq(v_opt_932_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint32_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = 97;
v___x_1182_ = lean_uint32_dec_eq(v_opt_932_, v___x_1181_);
if (v___x_1182_ == 0)
{
uint32_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = 120;
v___x_1184_ = lean_uint32_dec_eq(v_opt_932_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint32_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = 76;
v___x_1186_ = lean_uint32_dec_eq(v_opt_932_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint32_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = 68;
v___x_1188_ = lean_uint32_dec_eq(v_opt_932_, v___x_1187_);
if (v___x_1188_ == 0)
{
uint32_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = 83;
v___x_1190_ = lean_uint32_dec_eq(v_opt_932_, v___x_1189_);
if (v___x_1190_ == 0)
{
uint32_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = 87;
v___x_1192_ = lean_uint32_dec_eq(v_opt_932_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint32_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = 80;
v___x_1194_ = lean_uint32_dec_eq(v_opt_932_, v___x_1193_);
if (v___x_1194_ == 0)
{
uint32_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = 66;
v___x_1196_ = lean_uint32_dec_eq(v_opt_932_, v___x_1195_);
if (v___x_1196_ == 0)
{
uint32_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = 112;
v___x_1198_ = lean_uint32_dec_eq(v_opt_932_, v___x_1197_);
if (v___x_1198_ == 0)
{
uint32_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 108;
v___x_1200_ = lean_uint32_dec_eq(v_opt_932_, v___x_1199_);
if (v___x_1200_ == 0)
{
uint32_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = 117;
v___x_1202_ = lean_uint32_dec_eq(v_opt_932_, v___x_1201_);
if (v___x_1202_ == 0)
{
uint32_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = 69;
v___x_1204_ = lean_uint32_dec_eq(v_opt_932_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
goto v___jp_1053_;
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1206_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1205_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1245_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1245_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1245_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v_leanOpts_1211_; lean_object* v_forwardedArgs_1212_; uint8_t v_component_1213_; uint8_t v_printPrefix_1214_; uint8_t v_printLibDir_1215_; uint8_t v_useStdin_1216_; uint8_t v_onlyDeps_1217_; uint8_t v_onlySrcDeps_1218_; uint8_t v_depsJson_1219_; lean_object* v_opts_1220_; uint32_t v_trustLevel_1221_; uint32_t v_numThreads_1222_; lean_object* v_rootDir_x3f_1223_; lean_object* v_setupFileName_x3f_1224_; lean_object* v_oleanFileName_x3f_1225_; lean_object* v_ileanFileName_x3f_1226_; lean_object* v_cFileName_x3f_1227_; lean_object* v_bcFileName_x3f_1228_; uint8_t v_jsonOutput_1229_; lean_object* v_errorOnKinds_1230_; uint8_t v_printStats_1231_; uint8_t v_run_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1244_; 
v_leanOpts_1211_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1212_ = lean_ctor_get(v_opts_931_, 1);
v_component_1213_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1214_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1215_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1216_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1217_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1218_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1219_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1220_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1221_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1222_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1223_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1224_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1225_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1226_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1227_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1228_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1229_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1230_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1231_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1232_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1234_ = v_opts_931_;
v_isShared_1235_ = v_isSharedCheck_1244_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_errorOnKinds_1230_);
lean_inc(v_bcFileName_x3f_1228_);
lean_inc(v_cFileName_x3f_1227_);
lean_inc(v_ileanFileName_x3f_1226_);
lean_inc(v_oleanFileName_x3f_1225_);
lean_inc(v_setupFileName_x3f_1224_);
lean_inc(v_rootDir_x3f_1223_);
lean_inc(v_opts_1220_);
lean_inc(v_forwardedArgs_1212_);
lean_inc(v_leanOpts_1211_);
lean_dec(v_opts_931_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1244_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1236_ = l_String_toName(v_a_1207_);
v___x_1237_ = lean_array_push(v_errorOnKinds_1230_, v___x_1236_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 9, v___x_1237_);
v___x_1239_ = v___x_1234_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_leanOpts_1211_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_forwardedArgs_1212_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_opts_1220_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_rootDir_x3f_1223_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_setupFileName_x3f_1224_);
lean_ctor_set(v_reuseFailAlloc_1243_, 5, v_oleanFileName_x3f_1225_);
lean_ctor_set(v_reuseFailAlloc_1243_, 6, v_ileanFileName_x3f_1226_);
lean_ctor_set(v_reuseFailAlloc_1243_, 7, v_cFileName_x3f_1227_);
lean_ctor_set(v_reuseFailAlloc_1243_, 8, v_bcFileName_x3f_1228_);
lean_ctor_set(v_reuseFailAlloc_1243_, 9, v___x_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1243_, sizeof(void*)*10 + 8, v_component_1213_);
lean_ctor_set_uint8(v_reuseFailAlloc_1243_, sizeof(void*)*10 + 9, v_printPrefix_1214_);
lean_ctor_set_uint8(v_reuseFailAlloc_1243_, sizeof(void*)*10 + 10, v_printLibDir_1215_);
lean_ctor_set_uint8(v_reuseFailAlloc_1243_, sizeof(void*)*10 + 11, v_useStdin_1216_);
lean_ctor_set_uint8(v_reuseFailAlloc_1243_, sizeof(void*)*10 + 12, v_onlyDeps_1217_);
lean_ctor_set_uint8(v_reuseFailAlloc_1243_, sizeof(void*)*10 + 13, v_onlySrcDeps_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1243_, sizeof(void*)*10 + 14, v_depsJson_1219_);
lean_ctor_set_uint32(v_reuseFailAlloc_1243_, sizeof(void*)*10, v_trustLevel_1221_);
lean_ctor_set_uint32(v_reuseFailAlloc_1243_, sizeof(void*)*10 + 4, v_numThreads_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1243_, sizeof(void*)*10 + 15, v_jsonOutput_1229_);
lean_ctor_set_uint8(v_reuseFailAlloc_1243_, sizeof(void*)*10 + 16, v_printStats_1231_);
lean_ctor_set_uint8(v_reuseFailAlloc_1243_, sizeof(void*)*10 + 17, v_run_1232_);
v___x_1239_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1241_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1239_);
v___x_1241_ = v___x_1209_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec_ref(v_opts_931_);
v_a_1246_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1206_, 1);
v___x_1250_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1251_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1250_);
lean_dec_ref(v___x_1251_);
goto v___jp_1247_;
v___jp_1247_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_io_error_to_string(v_a_1246_);
v___x_1249_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1248_);
lean_dec_ref(v___x_1249_);
goto v___jp_1059_;
}
}
}
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1253_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1252_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1291_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1291_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1291_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_leanOpts_1258_; lean_object* v_forwardedArgs_1259_; uint8_t v_component_1260_; uint8_t v_printPrefix_1261_; uint8_t v_printLibDir_1262_; uint8_t v_useStdin_1263_; uint8_t v_onlyDeps_1264_; uint8_t v_onlySrcDeps_1265_; uint8_t v_depsJson_1266_; lean_object* v_opts_1267_; uint32_t v_trustLevel_1268_; uint32_t v_numThreads_1269_; lean_object* v_rootDir_x3f_1270_; lean_object* v_oleanFileName_x3f_1271_; lean_object* v_ileanFileName_x3f_1272_; lean_object* v_cFileName_x3f_1273_; lean_object* v_bcFileName_x3f_1274_; uint8_t v_jsonOutput_1275_; lean_object* v_errorOnKinds_1276_; uint8_t v_printStats_1277_; uint8_t v_run_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1289_; 
v_leanOpts_1258_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1259_ = lean_ctor_get(v_opts_931_, 1);
v_component_1260_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1261_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1262_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1263_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1264_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1265_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1266_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1267_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1268_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1269_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1270_ = lean_ctor_get(v_opts_931_, 3);
v_oleanFileName_x3f_1271_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1272_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1273_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1274_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1275_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1276_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1277_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1278_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v_opts_931_, 4);
lean_dec(v_unused_1290_);
v___x_1280_ = v_opts_931_;
v_isShared_1281_ = v_isSharedCheck_1289_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_errorOnKinds_1276_);
lean_inc(v_bcFileName_x3f_1274_);
lean_inc(v_cFileName_x3f_1273_);
lean_inc(v_ileanFileName_x3f_1272_);
lean_inc(v_oleanFileName_x3f_1271_);
lean_inc(v_rootDir_x3f_1270_);
lean_inc(v_opts_1267_);
lean_inc(v_forwardedArgs_1259_);
lean_inc(v_leanOpts_1258_);
lean_dec(v_opts_931_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1289_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_a_1254_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 4, v___x_1282_);
v___x_1284_ = v___x_1280_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_leanOpts_1258_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_forwardedArgs_1259_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_opts_1267_);
lean_ctor_set(v_reuseFailAlloc_1288_, 3, v_rootDir_x3f_1270_);
lean_ctor_set(v_reuseFailAlloc_1288_, 4, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1288_, 5, v_oleanFileName_x3f_1271_);
lean_ctor_set(v_reuseFailAlloc_1288_, 6, v_ileanFileName_x3f_1272_);
lean_ctor_set(v_reuseFailAlloc_1288_, 7, v_cFileName_x3f_1273_);
lean_ctor_set(v_reuseFailAlloc_1288_, 8, v_bcFileName_x3f_1274_);
lean_ctor_set(v_reuseFailAlloc_1288_, 9, v_errorOnKinds_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1288_, sizeof(void*)*10 + 8, v_component_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1288_, sizeof(void*)*10 + 9, v_printPrefix_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1288_, sizeof(void*)*10 + 10, v_printLibDir_1262_);
lean_ctor_set_uint8(v_reuseFailAlloc_1288_, sizeof(void*)*10 + 11, v_useStdin_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1288_, sizeof(void*)*10 + 12, v_onlyDeps_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1288_, sizeof(void*)*10 + 13, v_onlySrcDeps_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1288_, sizeof(void*)*10 + 14, v_depsJson_1266_);
lean_ctor_set_uint32(v_reuseFailAlloc_1288_, sizeof(void*)*10, v_trustLevel_1268_);
lean_ctor_set_uint32(v_reuseFailAlloc_1288_, sizeof(void*)*10 + 4, v_numThreads_1269_);
lean_ctor_set_uint8(v_reuseFailAlloc_1288_, sizeof(void*)*10 + 15, v_jsonOutput_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1288_, sizeof(void*)*10 + 16, v_printStats_1277_);
lean_ctor_set_uint8(v_reuseFailAlloc_1288_, sizeof(void*)*10 + 17, v_run_1278_);
v___x_1284_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1286_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1284_);
v___x_1286_ = v___x_1256_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec_ref(v_opts_931_);
v_a_1292_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1253_, 1);
v___x_1296_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1297_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1296_);
lean_dec_ref(v___x_1297_);
goto v___jp_1293_;
v___jp_1293_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_io_error_to_string(v_a_1292_);
v___x_1295_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1294_);
lean_dec_ref(v___x_1295_);
goto v___jp_1025_;
}
}
}
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1299_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1298_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1301_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc_n(v_a_1300_, 2);
lean_dec_ref_known(v___x_1299_, 1);
v___x_1301_ = lean_load_dynlib(v_a_1300_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1340_; 
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v___x_1301_, 0);
lean_dec(v_unused_1341_);
v___x_1303_ = v___x_1301_;
v_isShared_1304_ = v_isSharedCheck_1340_;
goto v_resetjp_1302_;
}
else
{
lean_dec(v___x_1301_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1340_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v_leanOpts_1305_; lean_object* v_forwardedArgs_1306_; uint8_t v_component_1307_; uint8_t v_printPrefix_1308_; uint8_t v_printLibDir_1309_; uint8_t v_useStdin_1310_; uint8_t v_onlyDeps_1311_; uint8_t v_onlySrcDeps_1312_; uint8_t v_depsJson_1313_; lean_object* v_opts_1314_; uint32_t v_trustLevel_1315_; uint32_t v_numThreads_1316_; lean_object* v_rootDir_x3f_1317_; lean_object* v_setupFileName_x3f_1318_; lean_object* v_oleanFileName_x3f_1319_; lean_object* v_ileanFileName_x3f_1320_; lean_object* v_cFileName_x3f_1321_; lean_object* v_bcFileName_x3f_1322_; uint8_t v_jsonOutput_1323_; lean_object* v_errorOnKinds_1324_; uint8_t v_printStats_1325_; uint8_t v_run_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1339_; 
v_leanOpts_1305_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1306_ = lean_ctor_get(v_opts_931_, 1);
v_component_1307_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1308_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1309_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1310_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1311_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1312_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1313_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1314_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1315_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1316_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1317_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1318_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1319_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1320_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1321_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1322_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1323_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1324_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1325_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1326_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1328_ = v_opts_931_;
v_isShared_1329_ = v_isSharedCheck_1339_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_errorOnKinds_1324_);
lean_inc(v_bcFileName_x3f_1322_);
lean_inc(v_cFileName_x3f_1321_);
lean_inc(v_ileanFileName_x3f_1320_);
lean_inc(v_oleanFileName_x3f_1319_);
lean_inc(v_setupFileName_x3f_1318_);
lean_inc(v_rootDir_x3f_1317_);
lean_inc(v_opts_1314_);
lean_inc(v_forwardedArgs_1306_);
lean_inc(v_leanOpts_1305_);
lean_dec(v_opts_931_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1339_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1330_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1331_ = lean_string_append(v___x_1330_, v_a_1300_);
lean_dec(v_a_1300_);
v___x_1332_ = lean_array_push(v_forwardedArgs_1306_, v___x_1331_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 1, v___x_1332_);
v___x_1334_ = v___x_1328_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_leanOpts_1305_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v_opts_1314_);
lean_ctor_set(v_reuseFailAlloc_1338_, 3, v_rootDir_x3f_1317_);
lean_ctor_set(v_reuseFailAlloc_1338_, 4, v_setupFileName_x3f_1318_);
lean_ctor_set(v_reuseFailAlloc_1338_, 5, v_oleanFileName_x3f_1319_);
lean_ctor_set(v_reuseFailAlloc_1338_, 6, v_ileanFileName_x3f_1320_);
lean_ctor_set(v_reuseFailAlloc_1338_, 7, v_cFileName_x3f_1321_);
lean_ctor_set(v_reuseFailAlloc_1338_, 8, v_bcFileName_x3f_1322_);
lean_ctor_set(v_reuseFailAlloc_1338_, 9, v_errorOnKinds_1324_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*10 + 8, v_component_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*10 + 9, v_printPrefix_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*10 + 10, v_printLibDir_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*10 + 11, v_useStdin_1310_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*10 + 12, v_onlyDeps_1311_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*10 + 13, v_onlySrcDeps_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*10 + 14, v_depsJson_1313_);
lean_ctor_set_uint32(v_reuseFailAlloc_1338_, sizeof(void*)*10, v_trustLevel_1315_);
lean_ctor_set_uint32(v_reuseFailAlloc_1338_, sizeof(void*)*10 + 4, v_numThreads_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*10 + 15, v_jsonOutput_1323_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*10 + 16, v_printStats_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*10 + 17, v_run_1326_);
v___x_1334_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1336_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1334_);
v___x_1336_ = v___x_1303_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec(v_a_1300_);
lean_dec_ref(v_opts_931_);
v_a_1342_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1301_, 1);
v___x_1346_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1347_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1346_);
lean_dec_ref(v___x_1347_);
goto v___jp_1343_;
v___jp_1343_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_io_error_to_string(v_a_1342_);
v___x_1345_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1344_);
lean_dec_ref(v___x_1345_);
goto v___jp_1065_;
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec_ref(v_opts_931_);
v_a_1348_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1299_, 1);
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
goto v___jp_1019_;
}
}
}
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1355_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1354_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1425_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1425_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1425_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v_fst_1361_; lean_object* v_snd_1362_; lean_object* v___y_1408_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = lean_string_utf8_byte_size(v_a_1356_);
lean_inc(v_a_1356_);
v___x_1421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1421_, 0, v_a_1356_);
lean_ctor_set(v___x_1421_, 1, v___x_1419_);
lean_ctor_set(v___x_1421_, 2, v___x_1420_);
v___x_1422_ = lean_box(0);
v___x_1423_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_1421_, v_a_1356_, v___x_1419_, v___x_1422_);
lean_dec_ref_known(v___x_1421_, 3);
if (lean_obj_tag(v___x_1423_) == 0)
{
v___y_1408_ = v___x_1420_;
goto v___jp_1407_;
}
else
{
lean_object* v_val_1424_; 
v_val_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_val_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v___y_1408_ = v_val_1424_;
goto v___jp_1407_;
}
v___jp_1360_:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_load_plugin(v_fst_1361_, v_snd_1362_);
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
v_leanOpts_1367_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1368_ = lean_ctor_get(v_opts_931_, 1);
v_component_1369_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1370_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1371_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1372_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1373_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1374_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1375_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1376_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1377_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1378_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1379_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1380_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1381_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1382_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1383_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1384_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1385_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1386_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1387_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1388_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1390_ = v_opts_931_;
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
lean_dec(v_opts_931_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1392_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1393_ = lean_string_append(v___x_1392_, v_a_1356_);
lean_dec(v_a_1356_);
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
lean_object* v_a_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec(v_a_1356_);
lean_dec_ref(v_opts_931_);
v_a_1404_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1363_, 1);
v___x_1405_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1406_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1405_);
lean_dec_ref(v___x_1406_);
v___y_1075_ = v_a_1404_;
goto v___jp_1074_;
}
}
v___jp_1407_:
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = lean_string_utf8_byte_size(v_a_1356_);
v___x_1410_ = lean_nat_dec_eq(v___y_1408_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = lean_string_utf8_next_fast(v_a_1356_, v___y_1408_);
v___x_1413_ = lean_string_utf8_extract(v_a_1356_, v___x_1411_, v___y_1408_);
lean_dec(v___y_1408_);
v___x_1414_ = lean_string_utf8_extract(v_a_1356_, v___x_1412_, v___x_1409_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set_tag(v___x_1358_, 1);
lean_ctor_set(v___x_1358_, 0, v___x_1414_);
v___x_1416_ = v___x_1358_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
v_fst_1361_ = v___x_1413_;
v_snd_1362_ = v___x_1416_;
goto v___jp_1360_;
}
}
else
{
lean_object* v___x_1418_; 
lean_dec(v___y_1408_);
lean_del_object(v___x_1358_);
v___x_1418_ = lean_box(0);
lean_inc(v_a_1356_);
v_fst_1361_ = v_a_1356_;
v_snd_1362_ = v___x_1418_;
goto v___jp_1360_;
}
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref(v_opts_931_);
v_a_1426_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1355_, 1);
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
goto v___jp_1013_;
}
}
}
}
else
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__12, &l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12);
if (v___x_1432_ == 0)
{
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
goto v___jp_1053_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1434_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1433_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1443_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_internal_enable_debug(v_a_1435_);
lean_dec(v_a_1435_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v_opts_931_);
v___x_1441_ = v___x_1437_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_opts_931_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec_ref(v_opts_931_);
v_a_1444_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1444_);
lean_dec_ref_known(v___x_1434_, 1);
v___x_1448_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1449_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1448_);
lean_dec_ref(v___x_1449_);
goto v___jp_1445_;
v___jp_1445_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = lean_io_error_to_string(v_a_1444_);
v___x_1447_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1446_);
lean_dec_ref(v___x_1447_);
goto v___jp_1081_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1450_; lean_object* v_forwardedArgs_1451_; uint8_t v_component_1452_; uint8_t v_printPrefix_1453_; uint8_t v_printLibDir_1454_; uint8_t v_useStdin_1455_; uint8_t v_onlyDeps_1456_; uint8_t v_onlySrcDeps_1457_; uint8_t v_depsJson_1458_; lean_object* v_opts_1459_; uint32_t v_trustLevel_1460_; uint32_t v_numThreads_1461_; lean_object* v_rootDir_x3f_1462_; lean_object* v_setupFileName_x3f_1463_; lean_object* v_oleanFileName_x3f_1464_; lean_object* v_ileanFileName_x3f_1465_; lean_object* v_cFileName_x3f_1466_; lean_object* v_bcFileName_x3f_1467_; uint8_t v_jsonOutput_1468_; lean_object* v_errorOnKinds_1469_; uint8_t v_printStats_1470_; uint8_t v_run_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1481_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1450_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1451_ = lean_ctor_get(v_opts_931_, 1);
v_component_1452_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1453_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1454_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1455_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1456_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1457_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1458_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1459_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1460_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1461_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1462_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1463_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1464_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1465_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1466_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1467_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1468_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1469_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1470_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1471_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1473_ = v_opts_931_;
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_errorOnKinds_1469_);
lean_inc(v_bcFileName_x3f_1467_);
lean_inc(v_cFileName_x3f_1466_);
lean_inc(v_ileanFileName_x3f_1465_);
lean_inc(v_oleanFileName_x3f_1464_);
lean_inc(v_setupFileName_x3f_1463_);
lean_inc(v_rootDir_x3f_1462_);
lean_inc(v_opts_1459_);
lean_inc(v_forwardedArgs_1451_);
lean_inc(v_leanOpts_1450_);
lean_dec(v_opts_931_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1475_ = l_Lean_profiler;
v___x_1476_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1450_, v___x_1475_, v___x_1194_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1476_);
v___x_1478_ = v___x_1473_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_forwardedArgs_1451_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_opts_1459_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_rootDir_x3f_1462_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_setupFileName_x3f_1463_);
lean_ctor_set(v_reuseFailAlloc_1480_, 5, v_oleanFileName_x3f_1464_);
lean_ctor_set(v_reuseFailAlloc_1480_, 6, v_ileanFileName_x3f_1465_);
lean_ctor_set(v_reuseFailAlloc_1480_, 7, v_cFileName_x3f_1466_);
lean_ctor_set(v_reuseFailAlloc_1480_, 8, v_bcFileName_x3f_1467_);
lean_ctor_set(v_reuseFailAlloc_1480_, 9, v_errorOnKinds_1469_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*10 + 8, v_component_1452_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*10 + 9, v_printPrefix_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*10 + 10, v_printLibDir_1454_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*10 + 11, v_useStdin_1455_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*10 + 12, v_onlyDeps_1456_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*10 + 13, v_onlySrcDeps_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*10 + 14, v_depsJson_1458_);
lean_ctor_set_uint32(v_reuseFailAlloc_1480_, sizeof(void*)*10, v_trustLevel_1460_);
lean_ctor_set_uint32(v_reuseFailAlloc_1480_, sizeof(void*)*10 + 4, v_numThreads_1461_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*10 + 15, v_jsonOutput_1468_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*10 + 16, v_printStats_1470_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*10 + 17, v_run_1471_);
v___x_1478_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
return v___x_1479_;
}
}
}
}
else
{
lean_object* v_leanOpts_1482_; lean_object* v_forwardedArgs_1483_; uint8_t v_printPrefix_1484_; uint8_t v_printLibDir_1485_; uint8_t v_useStdin_1486_; uint8_t v_onlyDeps_1487_; uint8_t v_onlySrcDeps_1488_; uint8_t v_depsJson_1489_; lean_object* v_opts_1490_; uint32_t v_trustLevel_1491_; uint32_t v_numThreads_1492_; lean_object* v_rootDir_x3f_1493_; lean_object* v_setupFileName_x3f_1494_; lean_object* v_oleanFileName_x3f_1495_; lean_object* v_ileanFileName_x3f_1496_; lean_object* v_cFileName_x3f_1497_; lean_object* v_bcFileName_x3f_1498_; uint8_t v_jsonOutput_1499_; lean_object* v_errorOnKinds_1500_; uint8_t v_printStats_1501_; uint8_t v_run_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1511_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1482_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1483_ = lean_ctor_get(v_opts_931_, 1);
v_printPrefix_1484_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1485_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1486_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1487_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1488_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1489_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1490_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1491_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1492_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1493_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1494_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1495_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1496_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1497_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1498_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1499_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1500_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1501_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1502_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1504_ = v_opts_931_;
v_isShared_1505_ = v_isSharedCheck_1511_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_errorOnKinds_1500_);
lean_inc(v_bcFileName_x3f_1498_);
lean_inc(v_cFileName_x3f_1497_);
lean_inc(v_ileanFileName_x3f_1496_);
lean_inc(v_oleanFileName_x3f_1495_);
lean_inc(v_setupFileName_x3f_1494_);
lean_inc(v_rootDir_x3f_1493_);
lean_inc(v_opts_1490_);
lean_inc(v_forwardedArgs_1483_);
lean_inc(v_leanOpts_1482_);
lean_dec(v_opts_931_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1511_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
uint8_t v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = 2;
if (v_isShared_1505_ == 0)
{
v___x_1508_ = v___x_1504_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_leanOpts_1482_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_forwardedArgs_1483_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_opts_1490_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v_rootDir_x3f_1493_);
lean_ctor_set(v_reuseFailAlloc_1510_, 4, v_setupFileName_x3f_1494_);
lean_ctor_set(v_reuseFailAlloc_1510_, 5, v_oleanFileName_x3f_1495_);
lean_ctor_set(v_reuseFailAlloc_1510_, 6, v_ileanFileName_x3f_1496_);
lean_ctor_set(v_reuseFailAlloc_1510_, 7, v_cFileName_x3f_1497_);
lean_ctor_set(v_reuseFailAlloc_1510_, 8, v_bcFileName_x3f_1498_);
lean_ctor_set(v_reuseFailAlloc_1510_, 9, v_errorOnKinds_1500_);
lean_ctor_set_uint8(v_reuseFailAlloc_1510_, sizeof(void*)*10 + 9, v_printPrefix_1484_);
lean_ctor_set_uint8(v_reuseFailAlloc_1510_, sizeof(void*)*10 + 10, v_printLibDir_1485_);
lean_ctor_set_uint8(v_reuseFailAlloc_1510_, sizeof(void*)*10 + 11, v_useStdin_1486_);
lean_ctor_set_uint8(v_reuseFailAlloc_1510_, sizeof(void*)*10 + 12, v_onlyDeps_1487_);
lean_ctor_set_uint8(v_reuseFailAlloc_1510_, sizeof(void*)*10 + 13, v_onlySrcDeps_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1510_, sizeof(void*)*10 + 14, v_depsJson_1489_);
lean_ctor_set_uint32(v_reuseFailAlloc_1510_, sizeof(void*)*10, v_trustLevel_1491_);
lean_ctor_set_uint32(v_reuseFailAlloc_1510_, sizeof(void*)*10 + 4, v_numThreads_1492_);
lean_ctor_set_uint8(v_reuseFailAlloc_1510_, sizeof(void*)*10 + 15, v_jsonOutput_1499_);
lean_ctor_set_uint8(v_reuseFailAlloc_1510_, sizeof(void*)*10 + 16, v_printStats_1501_);
lean_ctor_set_uint8(v_reuseFailAlloc_1510_, sizeof(void*)*10 + 17, v_run_1502_);
v___x_1508_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; 
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*10 + 8, v___x_1506_);
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
return v___x_1509_;
}
}
}
}
else
{
lean_object* v_leanOpts_1512_; lean_object* v_forwardedArgs_1513_; uint8_t v_printPrefix_1514_; uint8_t v_printLibDir_1515_; uint8_t v_useStdin_1516_; uint8_t v_onlyDeps_1517_; uint8_t v_onlySrcDeps_1518_; uint8_t v_depsJson_1519_; lean_object* v_opts_1520_; uint32_t v_trustLevel_1521_; uint32_t v_numThreads_1522_; lean_object* v_rootDir_x3f_1523_; lean_object* v_setupFileName_x3f_1524_; lean_object* v_oleanFileName_x3f_1525_; lean_object* v_ileanFileName_x3f_1526_; lean_object* v_cFileName_x3f_1527_; lean_object* v_bcFileName_x3f_1528_; uint8_t v_jsonOutput_1529_; lean_object* v_errorOnKinds_1530_; uint8_t v_printStats_1531_; uint8_t v_run_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1541_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1512_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1513_ = lean_ctor_get(v_opts_931_, 1);
v_printPrefix_1514_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1515_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1516_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1517_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1518_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1519_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1520_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1521_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1522_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1523_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1524_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1525_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1526_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1527_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1528_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1529_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1530_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1531_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1532_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1534_ = v_opts_931_;
v_isShared_1535_ = v_isSharedCheck_1541_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_errorOnKinds_1530_);
lean_inc(v_bcFileName_x3f_1528_);
lean_inc(v_cFileName_x3f_1527_);
lean_inc(v_ileanFileName_x3f_1526_);
lean_inc(v_oleanFileName_x3f_1525_);
lean_inc(v_setupFileName_x3f_1524_);
lean_inc(v_rootDir_x3f_1523_);
lean_inc(v_opts_1520_);
lean_inc(v_forwardedArgs_1513_);
lean_inc(v_leanOpts_1512_);
lean_dec(v_opts_931_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1541_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
uint8_t v___x_1536_; lean_object* v___x_1538_; 
v___x_1536_ = 1;
if (v_isShared_1535_ == 0)
{
v___x_1538_ = v___x_1534_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_leanOpts_1512_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_forwardedArgs_1513_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_opts_1520_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_rootDir_x3f_1523_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v_setupFileName_x3f_1524_);
lean_ctor_set(v_reuseFailAlloc_1540_, 5, v_oleanFileName_x3f_1525_);
lean_ctor_set(v_reuseFailAlloc_1540_, 6, v_ileanFileName_x3f_1526_);
lean_ctor_set(v_reuseFailAlloc_1540_, 7, v_cFileName_x3f_1527_);
lean_ctor_set(v_reuseFailAlloc_1540_, 8, v_bcFileName_x3f_1528_);
lean_ctor_set(v_reuseFailAlloc_1540_, 9, v_errorOnKinds_1530_);
lean_ctor_set_uint8(v_reuseFailAlloc_1540_, sizeof(void*)*10 + 9, v_printPrefix_1514_);
lean_ctor_set_uint8(v_reuseFailAlloc_1540_, sizeof(void*)*10 + 10, v_printLibDir_1515_);
lean_ctor_set_uint8(v_reuseFailAlloc_1540_, sizeof(void*)*10 + 11, v_useStdin_1516_);
lean_ctor_set_uint8(v_reuseFailAlloc_1540_, sizeof(void*)*10 + 12, v_onlyDeps_1517_);
lean_ctor_set_uint8(v_reuseFailAlloc_1540_, sizeof(void*)*10 + 13, v_onlySrcDeps_1518_);
lean_ctor_set_uint8(v_reuseFailAlloc_1540_, sizeof(void*)*10 + 14, v_depsJson_1519_);
lean_ctor_set_uint32(v_reuseFailAlloc_1540_, sizeof(void*)*10, v_trustLevel_1521_);
lean_ctor_set_uint32(v_reuseFailAlloc_1540_, sizeof(void*)*10 + 4, v_numThreads_1522_);
lean_ctor_set_uint8(v_reuseFailAlloc_1540_, sizeof(void*)*10 + 15, v_jsonOutput_1529_);
lean_ctor_set_uint8(v_reuseFailAlloc_1540_, sizeof(void*)*10 + 16, v_printStats_1531_);
lean_ctor_set_uint8(v_reuseFailAlloc_1540_, sizeof(void*)*10 + 17, v_run_1532_);
v___x_1538_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; 
lean_ctor_set_uint8(v___x_1538_, sizeof(void*)*10 + 8, v___x_1536_);
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
return v___x_1539_;
}
}
}
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1543_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1542_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v_leanOpts_1545_; lean_object* v_forwardedArgs_1546_; uint8_t v_component_1547_; uint8_t v_printPrefix_1548_; uint8_t v_printLibDir_1549_; uint8_t v_useStdin_1550_; uint8_t v_onlyDeps_1551_; uint8_t v_onlySrcDeps_1552_; uint8_t v_depsJson_1553_; lean_object* v_opts_1554_; uint32_t v_trustLevel_1555_; uint32_t v_numThreads_1556_; lean_object* v_rootDir_x3f_1557_; lean_object* v_setupFileName_x3f_1558_; lean_object* v_oleanFileName_x3f_1559_; lean_object* v_ileanFileName_x3f_1560_; lean_object* v_cFileName_x3f_1561_; lean_object* v_bcFileName_x3f_1562_; uint8_t v_jsonOutput_1563_; lean_object* v_errorOnKinds_1564_; uint8_t v_printStats_1565_; uint8_t v_run_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1591_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v___x_1543_, 1);
v_leanOpts_1545_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1546_ = lean_ctor_get(v_opts_931_, 1);
v_component_1547_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1548_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1549_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1550_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1551_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1552_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1553_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1554_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1555_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1556_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1557_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1558_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1559_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1560_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1561_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1562_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1563_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1564_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1565_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1566_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1568_ = v_opts_931_;
v_isShared_1569_ = v_isSharedCheck_1591_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_errorOnKinds_1564_);
lean_inc(v_bcFileName_x3f_1562_);
lean_inc(v_cFileName_x3f_1561_);
lean_inc(v_ileanFileName_x3f_1560_);
lean_inc(v_oleanFileName_x3f_1559_);
lean_inc(v_setupFileName_x3f_1558_);
lean_inc(v_rootDir_x3f_1557_);
lean_inc(v_opts_1554_);
lean_inc(v_forwardedArgs_1546_);
lean_inc(v_leanOpts_1545_);
lean_dec(v_opts_931_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1591_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; 
lean_inc(v_a_1544_);
v___x_1570_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1545_, v_a_1544_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1584_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1584_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1584_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1575_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1576_ = lean_string_append(v___x_1575_, v_a_1544_);
lean_dec(v_a_1544_);
v___x_1577_ = lean_array_push(v_forwardedArgs_1546_, v___x_1576_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v___x_1577_);
lean_ctor_set(v___x_1568_, 0, v_a_1571_);
v___x_1579_ = v___x_1568_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1571_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_opts_1554_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v_rootDir_x3f_1557_);
lean_ctor_set(v_reuseFailAlloc_1583_, 4, v_setupFileName_x3f_1558_);
lean_ctor_set(v_reuseFailAlloc_1583_, 5, v_oleanFileName_x3f_1559_);
lean_ctor_set(v_reuseFailAlloc_1583_, 6, v_ileanFileName_x3f_1560_);
lean_ctor_set(v_reuseFailAlloc_1583_, 7, v_cFileName_x3f_1561_);
lean_ctor_set(v_reuseFailAlloc_1583_, 8, v_bcFileName_x3f_1562_);
lean_ctor_set(v_reuseFailAlloc_1583_, 9, v_errorOnKinds_1564_);
lean_ctor_set_uint8(v_reuseFailAlloc_1583_, sizeof(void*)*10 + 8, v_component_1547_);
lean_ctor_set_uint8(v_reuseFailAlloc_1583_, sizeof(void*)*10 + 9, v_printPrefix_1548_);
lean_ctor_set_uint8(v_reuseFailAlloc_1583_, sizeof(void*)*10 + 10, v_printLibDir_1549_);
lean_ctor_set_uint8(v_reuseFailAlloc_1583_, sizeof(void*)*10 + 11, v_useStdin_1550_);
lean_ctor_set_uint8(v_reuseFailAlloc_1583_, sizeof(void*)*10 + 12, v_onlyDeps_1551_);
lean_ctor_set_uint8(v_reuseFailAlloc_1583_, sizeof(void*)*10 + 13, v_onlySrcDeps_1552_);
lean_ctor_set_uint8(v_reuseFailAlloc_1583_, sizeof(void*)*10 + 14, v_depsJson_1553_);
lean_ctor_set_uint32(v_reuseFailAlloc_1583_, sizeof(void*)*10, v_trustLevel_1555_);
lean_ctor_set_uint32(v_reuseFailAlloc_1583_, sizeof(void*)*10 + 4, v_numThreads_1556_);
lean_ctor_set_uint8(v_reuseFailAlloc_1583_, sizeof(void*)*10 + 15, v_jsonOutput_1563_);
lean_ctor_set_uint8(v_reuseFailAlloc_1583_, sizeof(void*)*10 + 16, v_printStats_1565_);
lean_ctor_set_uint8(v_reuseFailAlloc_1583_, sizeof(void*)*10 + 17, v_run_1566_);
v___x_1579_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1581_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1579_);
v___x_1581_ = v___x_1573_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_del_object(v___x_1568_);
lean_dec_ref(v_errorOnKinds_1564_);
lean_dec(v_bcFileName_x3f_1562_);
lean_dec(v_cFileName_x3f_1561_);
lean_dec(v_ileanFileName_x3f_1560_);
lean_dec(v_oleanFileName_x3f_1559_);
lean_dec(v_setupFileName_x3f_1558_);
lean_dec(v_rootDir_x3f_1557_);
lean_dec_ref(v_opts_1554_);
lean_dec_ref(v_forwardedArgs_1546_);
lean_dec(v_a_1544_);
v_a_1585_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1570_, 1);
v___x_1589_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1590_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1589_);
lean_dec_ref(v___x_1590_);
goto v___jp_1586_;
v___jp_1586_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_io_error_to_string(v_a_1585_);
v___x_1588_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1587_);
lean_dec_ref(v___x_1588_);
goto v___jp_1007_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec_ref(v_opts_931_);
v_a_1592_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1596_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1597_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1596_);
lean_dec_ref(v___x_1597_);
goto v___jp_1593_;
v___jp_1593_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_io_error_to_string(v_a_1592_);
v___x_1595_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1594_);
lean_dec_ref(v___x_1595_);
goto v___jp_1087_;
}
}
}
}
else
{
lean_object* v_leanOpts_1598_; lean_object* v_forwardedArgs_1599_; uint8_t v_component_1600_; uint8_t v_printPrefix_1601_; uint8_t v_useStdin_1602_; uint8_t v_onlyDeps_1603_; uint8_t v_onlySrcDeps_1604_; uint8_t v_depsJson_1605_; lean_object* v_opts_1606_; uint32_t v_trustLevel_1607_; uint32_t v_numThreads_1608_; lean_object* v_rootDir_x3f_1609_; lean_object* v_setupFileName_x3f_1610_; lean_object* v_oleanFileName_x3f_1611_; lean_object* v_ileanFileName_x3f_1612_; lean_object* v_cFileName_x3f_1613_; lean_object* v_bcFileName_x3f_1614_; uint8_t v_jsonOutput_1615_; lean_object* v_errorOnKinds_1616_; uint8_t v_printStats_1617_; uint8_t v_run_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1626_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1598_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1599_ = lean_ctor_get(v_opts_931_, 1);
v_component_1600_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1601_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_useStdin_1602_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1603_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1604_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1605_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1606_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1607_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1608_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1609_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1610_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1611_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1612_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1613_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1614_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1615_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1616_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1617_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1618_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1620_ = v_opts_931_;
v_isShared_1621_ = v_isSharedCheck_1626_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_errorOnKinds_1616_);
lean_inc(v_bcFileName_x3f_1614_);
lean_inc(v_cFileName_x3f_1613_);
lean_inc(v_ileanFileName_x3f_1612_);
lean_inc(v_oleanFileName_x3f_1611_);
lean_inc(v_setupFileName_x3f_1610_);
lean_inc(v_rootDir_x3f_1609_);
lean_inc(v_opts_1606_);
lean_inc(v_forwardedArgs_1599_);
lean_inc(v_leanOpts_1598_);
lean_dec(v_opts_931_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1626_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_leanOpts_1598_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_forwardedArgs_1599_);
lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_opts_1606_);
lean_ctor_set(v_reuseFailAlloc_1625_, 3, v_rootDir_x3f_1609_);
lean_ctor_set(v_reuseFailAlloc_1625_, 4, v_setupFileName_x3f_1610_);
lean_ctor_set(v_reuseFailAlloc_1625_, 5, v_oleanFileName_x3f_1611_);
lean_ctor_set(v_reuseFailAlloc_1625_, 6, v_ileanFileName_x3f_1612_);
lean_ctor_set(v_reuseFailAlloc_1625_, 7, v_cFileName_x3f_1613_);
lean_ctor_set(v_reuseFailAlloc_1625_, 8, v_bcFileName_x3f_1614_);
lean_ctor_set(v_reuseFailAlloc_1625_, 9, v_errorOnKinds_1616_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*10 + 8, v_component_1600_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*10 + 9, v_printPrefix_1601_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*10 + 11, v_useStdin_1602_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*10 + 12, v_onlyDeps_1603_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*10 + 13, v_onlySrcDeps_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*10 + 14, v_depsJson_1605_);
lean_ctor_set_uint32(v_reuseFailAlloc_1625_, sizeof(void*)*10, v_trustLevel_1607_);
lean_ctor_set_uint32(v_reuseFailAlloc_1625_, sizeof(void*)*10 + 4, v_numThreads_1608_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*10 + 15, v_jsonOutput_1615_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*10 + 16, v_printStats_1617_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*10 + 17, v_run_1618_);
v___x_1623_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; 
lean_ctor_set_uint8(v___x_1623_, sizeof(void*)*10 + 10, v___x_1186_);
v___x_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
return v___x_1624_;
}
}
}
}
else
{
lean_object* v_leanOpts_1627_; lean_object* v_forwardedArgs_1628_; uint8_t v_component_1629_; uint8_t v_printLibDir_1630_; uint8_t v_useStdin_1631_; uint8_t v_onlyDeps_1632_; uint8_t v_onlySrcDeps_1633_; uint8_t v_depsJson_1634_; lean_object* v_opts_1635_; uint32_t v_trustLevel_1636_; uint32_t v_numThreads_1637_; lean_object* v_rootDir_x3f_1638_; lean_object* v_setupFileName_x3f_1639_; lean_object* v_oleanFileName_x3f_1640_; lean_object* v_ileanFileName_x3f_1641_; lean_object* v_cFileName_x3f_1642_; lean_object* v_bcFileName_x3f_1643_; uint8_t v_jsonOutput_1644_; lean_object* v_errorOnKinds_1645_; uint8_t v_printStats_1646_; uint8_t v_run_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1655_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1627_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1628_ = lean_ctor_get(v_opts_931_, 1);
v_component_1629_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printLibDir_1630_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1631_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1632_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1633_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1634_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1635_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1636_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1637_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1638_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1639_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1640_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1641_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1642_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1643_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1644_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1645_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1646_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1647_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1649_ = v_opts_931_;
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_errorOnKinds_1645_);
lean_inc(v_bcFileName_x3f_1643_);
lean_inc(v_cFileName_x3f_1642_);
lean_inc(v_ileanFileName_x3f_1641_);
lean_inc(v_oleanFileName_x3f_1640_);
lean_inc(v_setupFileName_x3f_1639_);
lean_inc(v_rootDir_x3f_1638_);
lean_inc(v_opts_1635_);
lean_inc(v_forwardedArgs_1628_);
lean_inc(v_leanOpts_1627_);
lean_dec(v_opts_931_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_leanOpts_1627_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_forwardedArgs_1628_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_opts_1635_);
lean_ctor_set(v_reuseFailAlloc_1654_, 3, v_rootDir_x3f_1638_);
lean_ctor_set(v_reuseFailAlloc_1654_, 4, v_setupFileName_x3f_1639_);
lean_ctor_set(v_reuseFailAlloc_1654_, 5, v_oleanFileName_x3f_1640_);
lean_ctor_set(v_reuseFailAlloc_1654_, 6, v_ileanFileName_x3f_1641_);
lean_ctor_set(v_reuseFailAlloc_1654_, 7, v_cFileName_x3f_1642_);
lean_ctor_set(v_reuseFailAlloc_1654_, 8, v_bcFileName_x3f_1643_);
lean_ctor_set(v_reuseFailAlloc_1654_, 9, v_errorOnKinds_1645_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, sizeof(void*)*10 + 8, v_component_1629_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, sizeof(void*)*10 + 10, v_printLibDir_1630_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, sizeof(void*)*10 + 11, v_useStdin_1631_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, sizeof(void*)*10 + 12, v_onlyDeps_1632_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, sizeof(void*)*10 + 13, v_onlySrcDeps_1633_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, sizeof(void*)*10 + 14, v_depsJson_1634_);
lean_ctor_set_uint32(v_reuseFailAlloc_1654_, sizeof(void*)*10, v_trustLevel_1636_);
lean_ctor_set_uint32(v_reuseFailAlloc_1654_, sizeof(void*)*10 + 4, v_numThreads_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, sizeof(void*)*10 + 15, v_jsonOutput_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, sizeof(void*)*10 + 16, v_printStats_1646_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, sizeof(void*)*10 + 17, v_run_1647_);
v___x_1652_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; 
lean_ctor_set_uint8(v___x_1652_, sizeof(void*)*10 + 9, v___x_1184_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
}
}
}
else
{
lean_object* v_leanOpts_1656_; lean_object* v_forwardedArgs_1657_; uint8_t v_component_1658_; uint8_t v_printPrefix_1659_; uint8_t v_printLibDir_1660_; uint8_t v_useStdin_1661_; uint8_t v_onlyDeps_1662_; uint8_t v_onlySrcDeps_1663_; uint8_t v_depsJson_1664_; lean_object* v_opts_1665_; uint32_t v_trustLevel_1666_; uint32_t v_numThreads_1667_; lean_object* v_rootDir_x3f_1668_; lean_object* v_setupFileName_x3f_1669_; lean_object* v_oleanFileName_x3f_1670_; lean_object* v_ileanFileName_x3f_1671_; lean_object* v_cFileName_x3f_1672_; lean_object* v_bcFileName_x3f_1673_; uint8_t v_jsonOutput_1674_; lean_object* v_errorOnKinds_1675_; uint8_t v_run_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1684_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1656_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1657_ = lean_ctor_get(v_opts_931_, 1);
v_component_1658_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1659_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1660_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1661_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1662_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1663_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1664_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1665_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1666_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1667_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1668_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1669_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1670_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1671_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1672_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1673_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1674_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1675_ = lean_ctor_get(v_opts_931_, 9);
v_run_1676_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1678_ = v_opts_931_;
v_isShared_1679_ = v_isSharedCheck_1684_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_errorOnKinds_1675_);
lean_inc(v_bcFileName_x3f_1673_);
lean_inc(v_cFileName_x3f_1672_);
lean_inc(v_ileanFileName_x3f_1671_);
lean_inc(v_oleanFileName_x3f_1670_);
lean_inc(v_setupFileName_x3f_1669_);
lean_inc(v_rootDir_x3f_1668_);
lean_inc(v_opts_1665_);
lean_inc(v_forwardedArgs_1657_);
lean_inc(v_leanOpts_1656_);
lean_dec(v_opts_931_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1684_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_leanOpts_1656_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_forwardedArgs_1657_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_opts_1665_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v_rootDir_x3f_1668_);
lean_ctor_set(v_reuseFailAlloc_1683_, 4, v_setupFileName_x3f_1669_);
lean_ctor_set(v_reuseFailAlloc_1683_, 5, v_oleanFileName_x3f_1670_);
lean_ctor_set(v_reuseFailAlloc_1683_, 6, v_ileanFileName_x3f_1671_);
lean_ctor_set(v_reuseFailAlloc_1683_, 7, v_cFileName_x3f_1672_);
lean_ctor_set(v_reuseFailAlloc_1683_, 8, v_bcFileName_x3f_1673_);
lean_ctor_set(v_reuseFailAlloc_1683_, 9, v_errorOnKinds_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*10 + 8, v_component_1658_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*10 + 9, v_printPrefix_1659_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*10 + 10, v_printLibDir_1660_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*10 + 11, v_useStdin_1661_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*10 + 12, v_onlyDeps_1662_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*10 + 13, v_onlySrcDeps_1663_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*10 + 14, v_depsJson_1664_);
lean_ctor_set_uint32(v_reuseFailAlloc_1683_, sizeof(void*)*10, v_trustLevel_1666_);
lean_ctor_set_uint32(v_reuseFailAlloc_1683_, sizeof(void*)*10 + 4, v_numThreads_1667_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*10 + 15, v_jsonOutput_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*10 + 17, v_run_1676_);
v___x_1681_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1682_; 
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*10 + 16, v___x_1182_);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
return v___x_1682_;
}
}
}
}
else
{
lean_object* v_leanOpts_1685_; lean_object* v_forwardedArgs_1686_; uint8_t v_component_1687_; uint8_t v_printPrefix_1688_; uint8_t v_printLibDir_1689_; uint8_t v_useStdin_1690_; uint8_t v_onlyDeps_1691_; uint8_t v_onlySrcDeps_1692_; uint8_t v_depsJson_1693_; lean_object* v_opts_1694_; uint32_t v_trustLevel_1695_; uint32_t v_numThreads_1696_; lean_object* v_rootDir_x3f_1697_; lean_object* v_setupFileName_x3f_1698_; lean_object* v_oleanFileName_x3f_1699_; lean_object* v_ileanFileName_x3f_1700_; lean_object* v_cFileName_x3f_1701_; lean_object* v_bcFileName_x3f_1702_; lean_object* v_errorOnKinds_1703_; uint8_t v_printStats_1704_; uint8_t v_run_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1713_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1685_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1686_ = lean_ctor_get(v_opts_931_, 1);
v_component_1687_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1688_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1689_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1690_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1691_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1692_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1693_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1694_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1695_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1696_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1697_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1698_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1699_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1700_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1701_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1702_ = lean_ctor_get(v_opts_931_, 8);
v_errorOnKinds_1703_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1704_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1705_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1707_ = v_opts_931_;
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_errorOnKinds_1703_);
lean_inc(v_bcFileName_x3f_1702_);
lean_inc(v_cFileName_x3f_1701_);
lean_inc(v_ileanFileName_x3f_1700_);
lean_inc(v_oleanFileName_x3f_1699_);
lean_inc(v_setupFileName_x3f_1698_);
lean_inc(v_rootDir_x3f_1697_);
lean_inc(v_opts_1694_);
lean_inc(v_forwardedArgs_1686_);
lean_inc(v_leanOpts_1685_);
lean_dec(v_opts_931_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_leanOpts_1685_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_forwardedArgs_1686_);
lean_ctor_set(v_reuseFailAlloc_1712_, 2, v_opts_1694_);
lean_ctor_set(v_reuseFailAlloc_1712_, 3, v_rootDir_x3f_1697_);
lean_ctor_set(v_reuseFailAlloc_1712_, 4, v_setupFileName_x3f_1698_);
lean_ctor_set(v_reuseFailAlloc_1712_, 5, v_oleanFileName_x3f_1699_);
lean_ctor_set(v_reuseFailAlloc_1712_, 6, v_ileanFileName_x3f_1700_);
lean_ctor_set(v_reuseFailAlloc_1712_, 7, v_cFileName_x3f_1701_);
lean_ctor_set(v_reuseFailAlloc_1712_, 8, v_bcFileName_x3f_1702_);
lean_ctor_set(v_reuseFailAlloc_1712_, 9, v_errorOnKinds_1703_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*10 + 8, v_component_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*10 + 9, v_printPrefix_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*10 + 10, v_printLibDir_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*10 + 11, v_useStdin_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*10 + 12, v_onlyDeps_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*10 + 13, v_onlySrcDeps_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*10 + 14, v_depsJson_1693_);
lean_ctor_set_uint32(v_reuseFailAlloc_1712_, sizeof(void*)*10, v_trustLevel_1695_);
lean_ctor_set_uint32(v_reuseFailAlloc_1712_, sizeof(void*)*10 + 4, v_numThreads_1696_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*10 + 16, v_printStats_1704_);
lean_ctor_set_uint8(v_reuseFailAlloc_1712_, sizeof(void*)*10 + 17, v_run_1705_);
v___x_1710_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1711_; 
lean_ctor_set_uint8(v___x_1710_, sizeof(void*)*10 + 15, v___x_1180_);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
}
}
}
else
{
lean_object* v_leanOpts_1714_; lean_object* v_forwardedArgs_1715_; uint8_t v_component_1716_; uint8_t v_printPrefix_1717_; uint8_t v_printLibDir_1718_; uint8_t v_useStdin_1719_; uint8_t v_onlySrcDeps_1720_; lean_object* v_opts_1721_; uint32_t v_trustLevel_1722_; uint32_t v_numThreads_1723_; lean_object* v_rootDir_x3f_1724_; lean_object* v_setupFileName_x3f_1725_; lean_object* v_oleanFileName_x3f_1726_; lean_object* v_ileanFileName_x3f_1727_; lean_object* v_cFileName_x3f_1728_; lean_object* v_bcFileName_x3f_1729_; uint8_t v_jsonOutput_1730_; lean_object* v_errorOnKinds_1731_; uint8_t v_printStats_1732_; uint8_t v_run_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1714_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1715_ = lean_ctor_get(v_opts_931_, 1);
v_component_1716_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1717_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1718_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1719_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlySrcDeps_1720_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_opts_1721_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1722_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1723_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1724_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1725_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1726_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1727_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1728_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1729_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1730_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1731_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1732_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1733_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1735_ = v_opts_931_;
v_isShared_1736_ = v_isSharedCheck_1741_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_errorOnKinds_1731_);
lean_inc(v_bcFileName_x3f_1729_);
lean_inc(v_cFileName_x3f_1728_);
lean_inc(v_ileanFileName_x3f_1727_);
lean_inc(v_oleanFileName_x3f_1726_);
lean_inc(v_setupFileName_x3f_1725_);
lean_inc(v_rootDir_x3f_1724_);
lean_inc(v_opts_1721_);
lean_inc(v_forwardedArgs_1715_);
lean_inc(v_leanOpts_1714_);
lean_dec(v_opts_931_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1741_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_leanOpts_1714_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_forwardedArgs_1715_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_opts_1721_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_rootDir_x3f_1724_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_setupFileName_x3f_1725_);
lean_ctor_set(v_reuseFailAlloc_1740_, 5, v_oleanFileName_x3f_1726_);
lean_ctor_set(v_reuseFailAlloc_1740_, 6, v_ileanFileName_x3f_1727_);
lean_ctor_set(v_reuseFailAlloc_1740_, 7, v_cFileName_x3f_1728_);
lean_ctor_set(v_reuseFailAlloc_1740_, 8, v_bcFileName_x3f_1729_);
lean_ctor_set(v_reuseFailAlloc_1740_, 9, v_errorOnKinds_1731_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*10 + 8, v_component_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*10 + 9, v_printPrefix_1717_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*10 + 10, v_printLibDir_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*10 + 11, v_useStdin_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*10 + 13, v_onlySrcDeps_1720_);
lean_ctor_set_uint32(v_reuseFailAlloc_1740_, sizeof(void*)*10, v_trustLevel_1722_);
lean_ctor_set_uint32(v_reuseFailAlloc_1740_, sizeof(void*)*10 + 4, v_numThreads_1723_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*10 + 15, v_jsonOutput_1730_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*10 + 16, v_printStats_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*10 + 17, v_run_1733_);
v___x_1738_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; 
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*10 + 12, v___x_1178_);
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*10 + 14, v___x_1178_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
}
}
}
else
{
lean_object* v_leanOpts_1742_; lean_object* v_forwardedArgs_1743_; uint8_t v_component_1744_; uint8_t v_printPrefix_1745_; uint8_t v_printLibDir_1746_; uint8_t v_useStdin_1747_; uint8_t v_onlyDeps_1748_; uint8_t v_depsJson_1749_; lean_object* v_opts_1750_; uint32_t v_trustLevel_1751_; uint32_t v_numThreads_1752_; lean_object* v_rootDir_x3f_1753_; lean_object* v_setupFileName_x3f_1754_; lean_object* v_oleanFileName_x3f_1755_; lean_object* v_ileanFileName_x3f_1756_; lean_object* v_cFileName_x3f_1757_; lean_object* v_bcFileName_x3f_1758_; uint8_t v_jsonOutput_1759_; lean_object* v_errorOnKinds_1760_; uint8_t v_printStats_1761_; uint8_t v_run_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1770_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1742_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1743_ = lean_ctor_get(v_opts_931_, 1);
v_component_1744_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1745_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1746_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1747_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1748_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_depsJson_1749_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1750_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1751_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1752_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1753_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1754_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1755_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1756_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1757_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1758_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1759_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1760_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1761_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1762_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1764_ = v_opts_931_;
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_errorOnKinds_1760_);
lean_inc(v_bcFileName_x3f_1758_);
lean_inc(v_cFileName_x3f_1757_);
lean_inc(v_ileanFileName_x3f_1756_);
lean_inc(v_oleanFileName_x3f_1755_);
lean_inc(v_setupFileName_x3f_1754_);
lean_inc(v_rootDir_x3f_1753_);
lean_inc(v_opts_1750_);
lean_inc(v_forwardedArgs_1743_);
lean_inc(v_leanOpts_1742_);
lean_dec(v_opts_931_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_leanOpts_1742_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_forwardedArgs_1743_);
lean_ctor_set(v_reuseFailAlloc_1769_, 2, v_opts_1750_);
lean_ctor_set(v_reuseFailAlloc_1769_, 3, v_rootDir_x3f_1753_);
lean_ctor_set(v_reuseFailAlloc_1769_, 4, v_setupFileName_x3f_1754_);
lean_ctor_set(v_reuseFailAlloc_1769_, 5, v_oleanFileName_x3f_1755_);
lean_ctor_set(v_reuseFailAlloc_1769_, 6, v_ileanFileName_x3f_1756_);
lean_ctor_set(v_reuseFailAlloc_1769_, 7, v_cFileName_x3f_1757_);
lean_ctor_set(v_reuseFailAlloc_1769_, 8, v_bcFileName_x3f_1758_);
lean_ctor_set(v_reuseFailAlloc_1769_, 9, v_errorOnKinds_1760_);
lean_ctor_set_uint8(v_reuseFailAlloc_1769_, sizeof(void*)*10 + 8, v_component_1744_);
lean_ctor_set_uint8(v_reuseFailAlloc_1769_, sizeof(void*)*10 + 9, v_printPrefix_1745_);
lean_ctor_set_uint8(v_reuseFailAlloc_1769_, sizeof(void*)*10 + 10, v_printLibDir_1746_);
lean_ctor_set_uint8(v_reuseFailAlloc_1769_, sizeof(void*)*10 + 11, v_useStdin_1747_);
lean_ctor_set_uint8(v_reuseFailAlloc_1769_, sizeof(void*)*10 + 12, v_onlyDeps_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1769_, sizeof(void*)*10 + 14, v_depsJson_1749_);
lean_ctor_set_uint32(v_reuseFailAlloc_1769_, sizeof(void*)*10, v_trustLevel_1751_);
lean_ctor_set_uint32(v_reuseFailAlloc_1769_, sizeof(void*)*10 + 4, v_numThreads_1752_);
lean_ctor_set_uint8(v_reuseFailAlloc_1769_, sizeof(void*)*10 + 15, v_jsonOutput_1759_);
lean_ctor_set_uint8(v_reuseFailAlloc_1769_, sizeof(void*)*10 + 16, v_printStats_1761_);
lean_ctor_set_uint8(v_reuseFailAlloc_1769_, sizeof(void*)*10 + 17, v_run_1762_);
v___x_1767_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1768_; 
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*10 + 13, v___x_1176_);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_leanOpts_1771_; lean_object* v_forwardedArgs_1772_; uint8_t v_component_1773_; uint8_t v_printPrefix_1774_; uint8_t v_printLibDir_1775_; uint8_t v_useStdin_1776_; uint8_t v_onlySrcDeps_1777_; uint8_t v_depsJson_1778_; lean_object* v_opts_1779_; uint32_t v_trustLevel_1780_; uint32_t v_numThreads_1781_; lean_object* v_rootDir_x3f_1782_; lean_object* v_setupFileName_x3f_1783_; lean_object* v_oleanFileName_x3f_1784_; lean_object* v_ileanFileName_x3f_1785_; lean_object* v_cFileName_x3f_1786_; lean_object* v_bcFileName_x3f_1787_; uint8_t v_jsonOutput_1788_; lean_object* v_errorOnKinds_1789_; uint8_t v_printStats_1790_; uint8_t v_run_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1771_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1772_ = lean_ctor_get(v_opts_931_, 1);
v_component_1773_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1774_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1775_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1776_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlySrcDeps_1777_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1778_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1779_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1780_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1781_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1782_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1783_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1784_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1785_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1786_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1787_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1788_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1789_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1790_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1791_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1793_ = v_opts_931_;
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_errorOnKinds_1789_);
lean_inc(v_bcFileName_x3f_1787_);
lean_inc(v_cFileName_x3f_1786_);
lean_inc(v_ileanFileName_x3f_1785_);
lean_inc(v_oleanFileName_x3f_1784_);
lean_inc(v_setupFileName_x3f_1783_);
lean_inc(v_rootDir_x3f_1782_);
lean_inc(v_opts_1779_);
lean_inc(v_forwardedArgs_1772_);
lean_inc(v_leanOpts_1771_);
lean_dec(v_opts_931_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_leanOpts_1771_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_forwardedArgs_1772_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v_opts_1779_);
lean_ctor_set(v_reuseFailAlloc_1798_, 3, v_rootDir_x3f_1782_);
lean_ctor_set(v_reuseFailAlloc_1798_, 4, v_setupFileName_x3f_1783_);
lean_ctor_set(v_reuseFailAlloc_1798_, 5, v_oleanFileName_x3f_1784_);
lean_ctor_set(v_reuseFailAlloc_1798_, 6, v_ileanFileName_x3f_1785_);
lean_ctor_set(v_reuseFailAlloc_1798_, 7, v_cFileName_x3f_1786_);
lean_ctor_set(v_reuseFailAlloc_1798_, 8, v_bcFileName_x3f_1787_);
lean_ctor_set(v_reuseFailAlloc_1798_, 9, v_errorOnKinds_1789_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*10 + 8, v_component_1773_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*10 + 9, v_printPrefix_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*10 + 10, v_printLibDir_1775_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*10 + 11, v_useStdin_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*10 + 13, v_onlySrcDeps_1777_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*10 + 14, v_depsJson_1778_);
lean_ctor_set_uint32(v_reuseFailAlloc_1798_, sizeof(void*)*10, v_trustLevel_1780_);
lean_ctor_set_uint32(v_reuseFailAlloc_1798_, sizeof(void*)*10 + 4, v_numThreads_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*10 + 15, v_jsonOutput_1788_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*10 + 16, v_printStats_1790_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*10 + 17, v_run_1791_);
v___x_1796_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; 
lean_ctor_set_uint8(v___x_1796_, sizeof(void*)*10 + 12, v___x_1174_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
}
}
}
else
{
lean_object* v_leanOpts_1800_; lean_object* v_forwardedArgs_1801_; uint8_t v_component_1802_; uint8_t v_printPrefix_1803_; uint8_t v_printLibDir_1804_; uint8_t v_useStdin_1805_; uint8_t v_onlyDeps_1806_; uint8_t v_onlySrcDeps_1807_; uint8_t v_depsJson_1808_; lean_object* v_opts_1809_; uint32_t v_trustLevel_1810_; uint32_t v_numThreads_1811_; lean_object* v_rootDir_x3f_1812_; lean_object* v_setupFileName_x3f_1813_; lean_object* v_oleanFileName_x3f_1814_; lean_object* v_ileanFileName_x3f_1815_; lean_object* v_cFileName_x3f_1816_; lean_object* v_bcFileName_x3f_1817_; uint8_t v_jsonOutput_1818_; lean_object* v_errorOnKinds_1819_; uint8_t v_printStats_1820_; uint8_t v_run_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1831_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_1800_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1801_ = lean_ctor_get(v_opts_931_, 1);
v_component_1802_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1803_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1804_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1805_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1806_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1807_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1808_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1809_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1810_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1811_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1812_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1813_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1814_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1815_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1816_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1817_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1818_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1819_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1820_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1821_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1823_ = v_opts_931_;
v_isShared_1824_ = v_isSharedCheck_1831_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_errorOnKinds_1819_);
lean_inc(v_bcFileName_x3f_1817_);
lean_inc(v_cFileName_x3f_1816_);
lean_inc(v_ileanFileName_x3f_1815_);
lean_inc(v_oleanFileName_x3f_1814_);
lean_inc(v_setupFileName_x3f_1813_);
lean_inc(v_rootDir_x3f_1812_);
lean_inc(v_opts_1809_);
lean_inc(v_forwardedArgs_1801_);
lean_inc(v_leanOpts_1800_);
lean_dec(v_opts_931_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1831_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1825_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_1826_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1800_, v___x_1825_, v___x_1170_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1826_);
v___x_1828_ = v___x_1823_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_forwardedArgs_1801_);
lean_ctor_set(v_reuseFailAlloc_1830_, 2, v_opts_1809_);
lean_ctor_set(v_reuseFailAlloc_1830_, 3, v_rootDir_x3f_1812_);
lean_ctor_set(v_reuseFailAlloc_1830_, 4, v_setupFileName_x3f_1813_);
lean_ctor_set(v_reuseFailAlloc_1830_, 5, v_oleanFileName_x3f_1814_);
lean_ctor_set(v_reuseFailAlloc_1830_, 6, v_ileanFileName_x3f_1815_);
lean_ctor_set(v_reuseFailAlloc_1830_, 7, v_cFileName_x3f_1816_);
lean_ctor_set(v_reuseFailAlloc_1830_, 8, v_bcFileName_x3f_1817_);
lean_ctor_set(v_reuseFailAlloc_1830_, 9, v_errorOnKinds_1819_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*10 + 8, v_component_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*10 + 9, v_printPrefix_1803_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*10 + 10, v_printLibDir_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*10 + 11, v_useStdin_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*10 + 12, v_onlyDeps_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*10 + 13, v_onlySrcDeps_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*10 + 14, v_depsJson_1808_);
lean_ctor_set_uint32(v_reuseFailAlloc_1830_, sizeof(void*)*10, v_trustLevel_1810_);
lean_ctor_set_uint32(v_reuseFailAlloc_1830_, sizeof(void*)*10 + 4, v_numThreads_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*10 + 15, v_jsonOutput_1818_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*10 + 16, v_printStats_1820_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*10 + 17, v_run_1821_);
v___x_1828_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; 
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
}
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1833_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1832_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1884_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1884_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1884_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = lean_string_utf8_byte_size(v_a_1834_);
lean_inc(v_a_1834_);
v___x_1840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1840_, 0, v_a_1834_);
lean_ctor_set(v___x_1840_, 1, v___x_1838_);
lean_ctor_set(v___x_1840_, 2, v___x_1839_);
v___x_1841_ = l_String_Slice_toNat_x3f(v___x_1840_);
lean_dec_ref_known(v___x_1840_, 3);
if (lean_obj_tag(v___x_1841_) == 1)
{
lean_object* v_val_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v_val_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_val_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = lean_cstr_to_nat("4294967296");
v___x_1844_ = lean_nat_dec_lt(v_val_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec(v_val_1842_);
lean_del_object(v___x_1836_);
lean_dec(v_a_1834_);
lean_dec_ref(v_opts_931_);
v___x_1845_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1846_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1845_);
lean_dec_ref(v___x_1846_);
goto v___jp_1001_;
}
else
{
lean_object* v_leanOpts_1847_; lean_object* v_forwardedArgs_1848_; uint8_t v_component_1849_; uint8_t v_printPrefix_1850_; uint8_t v_printLibDir_1851_; uint8_t v_useStdin_1852_; uint8_t v_onlyDeps_1853_; uint8_t v_onlySrcDeps_1854_; uint8_t v_depsJson_1855_; lean_object* v_opts_1856_; uint32_t v_numThreads_1857_; lean_object* v_rootDir_x3f_1858_; lean_object* v_setupFileName_x3f_1859_; lean_object* v_oleanFileName_x3f_1860_; lean_object* v_ileanFileName_x3f_1861_; lean_object* v_cFileName_x3f_1862_; lean_object* v_bcFileName_x3f_1863_; uint8_t v_jsonOutput_1864_; lean_object* v_errorOnKinds_1865_; uint8_t v_printStats_1866_; uint8_t v_run_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1881_; 
v_leanOpts_1847_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1848_ = lean_ctor_get(v_opts_931_, 1);
v_component_1849_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1850_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1851_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1852_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1853_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1854_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1855_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1856_ = lean_ctor_get(v_opts_931_, 2);
v_numThreads_1857_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1858_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1859_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1860_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1861_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1862_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1863_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1864_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1865_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1866_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1867_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1869_ = v_opts_931_;
v_isShared_1870_ = v_isSharedCheck_1881_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_errorOnKinds_1865_);
lean_inc(v_bcFileName_x3f_1863_);
lean_inc(v_cFileName_x3f_1862_);
lean_inc(v_ileanFileName_x3f_1861_);
lean_inc(v_oleanFileName_x3f_1860_);
lean_inc(v_setupFileName_x3f_1859_);
lean_inc(v_rootDir_x3f_1858_);
lean_inc(v_opts_1856_);
lean_inc(v_forwardedArgs_1848_);
lean_inc(v_leanOpts_1847_);
lean_dec(v_opts_931_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1881_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
uint32_t v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1871_ = lean_uint32_of_nat(v_val_1842_);
lean_dec(v_val_1842_);
v___x_1872_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1873_ = lean_string_append(v___x_1872_, v_a_1834_);
lean_dec(v_a_1834_);
v___x_1874_ = lean_array_push(v_forwardedArgs_1848_, v___x_1873_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 1, v___x_1874_);
v___x_1876_ = v___x_1869_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_leanOpts_1847_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1874_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_opts_1856_);
lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_rootDir_x3f_1858_);
lean_ctor_set(v_reuseFailAlloc_1880_, 4, v_setupFileName_x3f_1859_);
lean_ctor_set(v_reuseFailAlloc_1880_, 5, v_oleanFileName_x3f_1860_);
lean_ctor_set(v_reuseFailAlloc_1880_, 6, v_ileanFileName_x3f_1861_);
lean_ctor_set(v_reuseFailAlloc_1880_, 7, v_cFileName_x3f_1862_);
lean_ctor_set(v_reuseFailAlloc_1880_, 8, v_bcFileName_x3f_1863_);
lean_ctor_set(v_reuseFailAlloc_1880_, 9, v_errorOnKinds_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*10 + 8, v_component_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*10 + 9, v_printPrefix_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*10 + 10, v_printLibDir_1851_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*10 + 11, v_useStdin_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*10 + 12, v_onlyDeps_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*10 + 13, v_onlySrcDeps_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*10 + 14, v_depsJson_1855_);
lean_ctor_set_uint32(v_reuseFailAlloc_1880_, sizeof(void*)*10 + 4, v_numThreads_1857_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*10 + 15, v_jsonOutput_1864_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*10 + 16, v_printStats_1866_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*10 + 17, v_run_1867_);
v___x_1876_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1878_; 
lean_ctor_set_uint32(v___x_1876_, sizeof(void*)*10, v___x_1871_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1876_);
v___x_1878_ = v___x_1836_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec(v___x_1841_);
lean_del_object(v___x_1836_);
lean_dec(v_a_1834_);
lean_dec_ref(v_opts_931_);
v___x_1882_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_1883_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1882_);
lean_dec_ref(v___x_1883_);
goto v___jp_998_;
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec_ref(v_opts_931_);
v_a_1885_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1889_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1890_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1889_);
lean_dec_ref(v___x_1890_);
goto v___jp_1886_;
v___jp_1886_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_io_error_to_string(v_a_1885_);
v___x_1888_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1887_);
lean_dec_ref(v___x_1888_);
goto v___jp_995_;
}
}
}
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_1892_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1891_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1941_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1941_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1941_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = lean_string_utf8_byte_size(v_a_1893_);
lean_inc(v_a_1893_);
v___x_1899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1899_, 0, v_a_1893_);
lean_ctor_set(v___x_1899_, 1, v___x_1897_);
lean_ctor_set(v___x_1899_, 2, v___x_1898_);
v___x_1900_ = l_String_Slice_toNat_x3f(v___x_1899_);
lean_dec_ref_known(v___x_1899_, 3);
if (lean_obj_tag(v___x_1900_) == 1)
{
lean_object* v_val_1901_; lean_object* v_leanOpts_1902_; lean_object* v_forwardedArgs_1903_; uint8_t v_component_1904_; uint8_t v_printPrefix_1905_; uint8_t v_printLibDir_1906_; uint8_t v_useStdin_1907_; uint8_t v_onlyDeps_1908_; uint8_t v_onlySrcDeps_1909_; uint8_t v_depsJson_1910_; lean_object* v_opts_1911_; uint32_t v_trustLevel_1912_; uint32_t v_numThreads_1913_; lean_object* v_rootDir_x3f_1914_; lean_object* v_setupFileName_x3f_1915_; lean_object* v_oleanFileName_x3f_1916_; lean_object* v_ileanFileName_x3f_1917_; lean_object* v_cFileName_x3f_1918_; lean_object* v_bcFileName_x3f_1919_; uint8_t v_jsonOutput_1920_; lean_object* v_errorOnKinds_1921_; uint8_t v_printStats_1922_; uint8_t v_run_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1938_; 
v_val_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_val_1901_);
lean_dec_ref_known(v___x_1900_, 1);
v_leanOpts_1902_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1903_ = lean_ctor_get(v_opts_931_, 1);
v_component_1904_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1905_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1906_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1907_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1908_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1909_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1910_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1911_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1912_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1913_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1914_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1915_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1916_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1917_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1918_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1919_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1920_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1921_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1922_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1923_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1925_ = v_opts_931_;
v_isShared_1926_ = v_isSharedCheck_1938_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_errorOnKinds_1921_);
lean_inc(v_bcFileName_x3f_1919_);
lean_inc(v_cFileName_x3f_1918_);
lean_inc(v_ileanFileName_x3f_1917_);
lean_inc(v_oleanFileName_x3f_1916_);
lean_inc(v_setupFileName_x3f_1915_);
lean_inc(v_rootDir_x3f_1914_);
lean_inc(v_opts_1911_);
lean_inc(v_forwardedArgs_1903_);
lean_inc(v_leanOpts_1902_);
lean_dec(v_opts_931_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1938_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1927_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_1928_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_1902_, v___x_1927_, v_val_1901_);
v___x_1929_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_1930_ = lean_string_append(v___x_1929_, v_a_1893_);
lean_dec(v_a_1893_);
v___x_1931_ = lean_array_push(v_forwardedArgs_1903_, v___x_1930_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 1, v___x_1931_);
lean_ctor_set(v___x_1925_, 0, v___x_1928_);
v___x_1933_ = v___x_1925_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_opts_1911_);
lean_ctor_set(v_reuseFailAlloc_1937_, 3, v_rootDir_x3f_1914_);
lean_ctor_set(v_reuseFailAlloc_1937_, 4, v_setupFileName_x3f_1915_);
lean_ctor_set(v_reuseFailAlloc_1937_, 5, v_oleanFileName_x3f_1916_);
lean_ctor_set(v_reuseFailAlloc_1937_, 6, v_ileanFileName_x3f_1917_);
lean_ctor_set(v_reuseFailAlloc_1937_, 7, v_cFileName_x3f_1918_);
lean_ctor_set(v_reuseFailAlloc_1937_, 8, v_bcFileName_x3f_1919_);
lean_ctor_set(v_reuseFailAlloc_1937_, 9, v_errorOnKinds_1921_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*10 + 8, v_component_1904_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*10 + 9, v_printPrefix_1905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*10 + 10, v_printLibDir_1906_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*10 + 11, v_useStdin_1907_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*10 + 12, v_onlyDeps_1908_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*10 + 13, v_onlySrcDeps_1909_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*10 + 14, v_depsJson_1910_);
lean_ctor_set_uint32(v_reuseFailAlloc_1937_, sizeof(void*)*10, v_trustLevel_1912_);
lean_ctor_set_uint32(v_reuseFailAlloc_1937_, sizeof(void*)*10 + 4, v_numThreads_1913_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*10 + 15, v_jsonOutput_1920_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*10 + 16, v_printStats_1922_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*10 + 17, v_run_1923_);
v___x_1933_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1935_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1933_);
v___x_1935_ = v___x_1895_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
lean_dec(v___x_1900_);
lean_del_object(v___x_1895_);
lean_dec(v_a_1893_);
lean_dec_ref(v_opts_931_);
v___x_1939_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_1940_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1939_);
lean_dec_ref(v___x_1940_);
goto v___jp_1090_;
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
lean_dec_ref(v_opts_931_);
v_a_1942_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1892_, 1);
v___x_1946_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1947_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1946_);
lean_dec_ref(v___x_1947_);
goto v___jp_1943_;
v___jp_1943_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = lean_io_error_to_string(v_a_1942_);
v___x_1945_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1944_);
lean_dec_ref(v___x_1945_);
goto v___jp_1096_;
}
}
}
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_1949_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1948_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1998_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1998_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1998_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1954_ = lean_unsigned_to_nat(0u);
v___x_1955_ = lean_string_utf8_byte_size(v_a_1950_);
lean_inc(v_a_1950_);
v___x_1956_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1956_, 0, v_a_1950_);
lean_ctor_set(v___x_1956_, 1, v___x_1954_);
lean_ctor_set(v___x_1956_, 2, v___x_1955_);
v___x_1957_ = l_String_Slice_toNat_x3f(v___x_1956_);
lean_dec_ref_known(v___x_1956_, 3);
if (lean_obj_tag(v___x_1957_) == 1)
{
lean_object* v_val_1958_; lean_object* v_leanOpts_1959_; lean_object* v_forwardedArgs_1960_; uint8_t v_component_1961_; uint8_t v_printPrefix_1962_; uint8_t v_printLibDir_1963_; uint8_t v_useStdin_1964_; uint8_t v_onlyDeps_1965_; uint8_t v_onlySrcDeps_1966_; uint8_t v_depsJson_1967_; lean_object* v_opts_1968_; uint32_t v_trustLevel_1969_; uint32_t v_numThreads_1970_; lean_object* v_rootDir_x3f_1971_; lean_object* v_setupFileName_x3f_1972_; lean_object* v_oleanFileName_x3f_1973_; lean_object* v_ileanFileName_x3f_1974_; lean_object* v_cFileName_x3f_1975_; lean_object* v_bcFileName_x3f_1976_; uint8_t v_jsonOutput_1977_; lean_object* v_errorOnKinds_1978_; uint8_t v_printStats_1979_; uint8_t v_run_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1995_; 
v_val_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_val_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v_leanOpts_1959_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_1960_ = lean_ctor_get(v_opts_931_, 1);
v_component_1961_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_1962_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_1963_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_1964_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_1965_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_1966_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_1967_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_1968_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_1969_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_1970_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_1971_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_1972_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_1973_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_1974_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_1975_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_1976_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_1977_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_1978_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_1979_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_1980_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1982_ = v_opts_931_;
v_isShared_1983_ = v_isSharedCheck_1995_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_errorOnKinds_1978_);
lean_inc(v_bcFileName_x3f_1976_);
lean_inc(v_cFileName_x3f_1975_);
lean_inc(v_ileanFileName_x3f_1974_);
lean_inc(v_oleanFileName_x3f_1973_);
lean_inc(v_setupFileName_x3f_1972_);
lean_inc(v_rootDir_x3f_1971_);
lean_inc(v_opts_1968_);
lean_inc(v_forwardedArgs_1960_);
lean_inc(v_leanOpts_1959_);
lean_dec(v_opts_931_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1995_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1984_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_1985_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_1959_, v___x_1984_, v_val_1958_);
v___x_1986_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_1987_ = lean_string_append(v___x_1986_, v_a_1950_);
lean_dec(v_a_1950_);
v___x_1988_ = lean_array_push(v_forwardedArgs_1960_, v___x_1987_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 1, v___x_1988_);
lean_ctor_set(v___x_1982_, 0, v___x_1985_);
v___x_1990_ = v___x_1982_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_opts_1968_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_rootDir_x3f_1971_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v_setupFileName_x3f_1972_);
lean_ctor_set(v_reuseFailAlloc_1994_, 5, v_oleanFileName_x3f_1973_);
lean_ctor_set(v_reuseFailAlloc_1994_, 6, v_ileanFileName_x3f_1974_);
lean_ctor_set(v_reuseFailAlloc_1994_, 7, v_cFileName_x3f_1975_);
lean_ctor_set(v_reuseFailAlloc_1994_, 8, v_bcFileName_x3f_1976_);
lean_ctor_set(v_reuseFailAlloc_1994_, 9, v_errorOnKinds_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*10 + 8, v_component_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*10 + 9, v_printPrefix_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*10 + 10, v_printLibDir_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*10 + 11, v_useStdin_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*10 + 12, v_onlyDeps_1965_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*10 + 13, v_onlySrcDeps_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*10 + 14, v_depsJson_1967_);
lean_ctor_set_uint32(v_reuseFailAlloc_1994_, sizeof(void*)*10, v_trustLevel_1969_);
lean_ctor_set_uint32(v_reuseFailAlloc_1994_, sizeof(void*)*10 + 4, v_numThreads_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*10 + 15, v_jsonOutput_1977_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*10 + 16, v_printStats_1979_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*10 + 17, v_run_1980_);
v___x_1990_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1992_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1990_);
v___x_1992_ = v___x_1952_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_dec(v___x_1957_);
lean_del_object(v___x_1952_);
lean_dec(v_a_1950_);
lean_dec_ref(v_opts_931_);
v___x_1996_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_1997_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1996_);
lean_dec_ref(v___x_1997_);
goto v___jp_989_;
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
lean_dec_ref(v_opts_931_);
v_a_1999_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1949_, 1);
v___x_2003_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2004_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2003_);
lean_dec_ref(v___x_2004_);
goto v___jp_2000_;
v___jp_2000_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = lean_io_error_to_string(v_a_1999_);
v___x_2002_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2001_);
lean_dec_ref(v___x_2002_);
goto v___jp_986_;
}
}
}
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_2006_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2005_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2047_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2047_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2047_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_leanOpts_2011_; lean_object* v_forwardedArgs_2012_; uint8_t v_component_2013_; uint8_t v_printPrefix_2014_; uint8_t v_printLibDir_2015_; uint8_t v_useStdin_2016_; uint8_t v_onlyDeps_2017_; uint8_t v_onlySrcDeps_2018_; uint8_t v_depsJson_2019_; lean_object* v_opts_2020_; uint32_t v_trustLevel_2021_; uint32_t v_numThreads_2022_; lean_object* v_setupFileName_x3f_2023_; lean_object* v_oleanFileName_x3f_2024_; lean_object* v_ileanFileName_x3f_2025_; lean_object* v_cFileName_x3f_2026_; lean_object* v_bcFileName_x3f_2027_; uint8_t v_jsonOutput_2028_; lean_object* v_errorOnKinds_2029_; uint8_t v_printStats_2030_; uint8_t v_run_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2045_; 
v_leanOpts_2011_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2012_ = lean_ctor_get(v_opts_931_, 1);
v_component_2013_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2014_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2015_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2016_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2017_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2018_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2019_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2020_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2021_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2022_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_setupFileName_x3f_2023_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2024_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_2025_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2026_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2027_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2028_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2029_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2030_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2031_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v_opts_931_, 3);
lean_dec(v_unused_2046_);
v___x_2033_ = v_opts_931_;
v_isShared_2034_ = v_isSharedCheck_2045_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_errorOnKinds_2029_);
lean_inc(v_bcFileName_x3f_2027_);
lean_inc(v_cFileName_x3f_2026_);
lean_inc(v_ileanFileName_x3f_2025_);
lean_inc(v_oleanFileName_x3f_2024_);
lean_inc(v_setupFileName_x3f_2023_);
lean_inc(v_opts_2020_);
lean_inc(v_forwardedArgs_2012_);
lean_inc(v_leanOpts_2011_);
lean_dec(v_opts_931_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2045_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2035_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2036_ = lean_string_append(v___x_2035_, v_a_2007_);
v___x_2037_ = lean_array_push(v_forwardedArgs_2012_, v___x_2036_);
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v_a_2007_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 3, v___x_2038_);
lean_ctor_set(v___x_2033_, 1, v___x_2037_);
v___x_2040_ = v___x_2033_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_leanOpts_2011_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_opts_2020_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2044_, 4, v_setupFileName_x3f_2023_);
lean_ctor_set(v_reuseFailAlloc_2044_, 5, v_oleanFileName_x3f_2024_);
lean_ctor_set(v_reuseFailAlloc_2044_, 6, v_ileanFileName_x3f_2025_);
lean_ctor_set(v_reuseFailAlloc_2044_, 7, v_cFileName_x3f_2026_);
lean_ctor_set(v_reuseFailAlloc_2044_, 8, v_bcFileName_x3f_2027_);
lean_ctor_set(v_reuseFailAlloc_2044_, 9, v_errorOnKinds_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*10 + 8, v_component_2013_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*10 + 9, v_printPrefix_2014_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*10 + 10, v_printLibDir_2015_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*10 + 11, v_useStdin_2016_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*10 + 12, v_onlyDeps_2017_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*10 + 13, v_onlySrcDeps_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*10 + 14, v_depsJson_2019_);
lean_ctor_set_uint32(v_reuseFailAlloc_2044_, sizeof(void*)*10, v_trustLevel_2021_);
lean_ctor_set_uint32(v_reuseFailAlloc_2044_, sizeof(void*)*10 + 4, v_numThreads_2022_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*10 + 15, v_jsonOutput_2028_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*10 + 16, v_printStats_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*10 + 17, v_run_2031_);
v___x_2040_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2042_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2040_);
v___x_2042_ = v___x_2009_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec_ref(v_opts_931_);
v_a_2048_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2006_, 1);
v___x_2052_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2053_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2052_);
lean_dec_ref(v___x_2053_);
goto v___jp_2049_;
v___jp_2049_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_io_error_to_string(v_a_2048_);
v___x_2051_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2050_);
lean_dec_ref(v___x_2051_);
goto v___jp_1102_;
}
}
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2055_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2054_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2093_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2093_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2093_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v_leanOpts_2060_; lean_object* v_forwardedArgs_2061_; uint8_t v_component_2062_; uint8_t v_printPrefix_2063_; uint8_t v_printLibDir_2064_; uint8_t v_useStdin_2065_; uint8_t v_onlyDeps_2066_; uint8_t v_onlySrcDeps_2067_; uint8_t v_depsJson_2068_; lean_object* v_opts_2069_; uint32_t v_trustLevel_2070_; uint32_t v_numThreads_2071_; lean_object* v_rootDir_x3f_2072_; lean_object* v_setupFileName_x3f_2073_; lean_object* v_oleanFileName_x3f_2074_; lean_object* v_cFileName_x3f_2075_; lean_object* v_bcFileName_x3f_2076_; uint8_t v_jsonOutput_2077_; lean_object* v_errorOnKinds_2078_; uint8_t v_printStats_2079_; uint8_t v_run_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2091_; 
v_leanOpts_2060_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2061_ = lean_ctor_get(v_opts_931_, 1);
v_component_2062_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2063_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2064_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2065_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2066_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2067_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2068_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2069_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2070_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2071_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2072_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2073_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2074_ = lean_ctor_get(v_opts_931_, 5);
v_cFileName_x3f_2075_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2076_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2077_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2078_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2079_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2080_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2091_ == 0)
{
lean_object* v_unused_2092_; 
v_unused_2092_ = lean_ctor_get(v_opts_931_, 6);
lean_dec(v_unused_2092_);
v___x_2082_ = v_opts_931_;
v_isShared_2083_ = v_isSharedCheck_2091_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_errorOnKinds_2078_);
lean_inc(v_bcFileName_x3f_2076_);
lean_inc(v_cFileName_x3f_2075_);
lean_inc(v_oleanFileName_x3f_2074_);
lean_inc(v_setupFileName_x3f_2073_);
lean_inc(v_rootDir_x3f_2072_);
lean_inc(v_opts_2069_);
lean_inc(v_forwardedArgs_2061_);
lean_inc(v_leanOpts_2060_);
lean_dec(v_opts_931_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2091_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2084_, 0, v_a_2056_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 6, v___x_2084_);
v___x_2086_ = v___x_2082_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_leanOpts_2060_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_forwardedArgs_2061_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_opts_2069_);
lean_ctor_set(v_reuseFailAlloc_2090_, 3, v_rootDir_x3f_2072_);
lean_ctor_set(v_reuseFailAlloc_2090_, 4, v_setupFileName_x3f_2073_);
lean_ctor_set(v_reuseFailAlloc_2090_, 5, v_oleanFileName_x3f_2074_);
lean_ctor_set(v_reuseFailAlloc_2090_, 6, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2090_, 7, v_cFileName_x3f_2075_);
lean_ctor_set(v_reuseFailAlloc_2090_, 8, v_bcFileName_x3f_2076_);
lean_ctor_set(v_reuseFailAlloc_2090_, 9, v_errorOnKinds_2078_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*10 + 8, v_component_2062_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*10 + 9, v_printPrefix_2063_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*10 + 10, v_printLibDir_2064_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*10 + 11, v_useStdin_2065_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*10 + 12, v_onlyDeps_2066_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*10 + 13, v_onlySrcDeps_2067_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*10 + 14, v_depsJson_2068_);
lean_ctor_set_uint32(v_reuseFailAlloc_2090_, sizeof(void*)*10, v_trustLevel_2070_);
lean_ctor_set_uint32(v_reuseFailAlloc_2090_, sizeof(void*)*10 + 4, v_numThreads_2071_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*10 + 15, v_jsonOutput_2077_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*10 + 16, v_printStats_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*10 + 17, v_run_2080_);
v___x_2086_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2088_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2086_);
v___x_2088_ = v___x_2058_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_dec_ref(v_opts_931_);
v_a_2094_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2098_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2099_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2098_);
lean_dec_ref(v___x_2099_);
goto v___jp_2095_;
v___jp_2095_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = lean_io_error_to_string(v_a_2094_);
v___x_2097_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2096_);
lean_dec_ref(v___x_2097_);
goto v___jp_980_;
}
}
}
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2101_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2100_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2139_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2139_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2139_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v_leanOpts_2106_; lean_object* v_forwardedArgs_2107_; uint8_t v_component_2108_; uint8_t v_printPrefix_2109_; uint8_t v_printLibDir_2110_; uint8_t v_useStdin_2111_; uint8_t v_onlyDeps_2112_; uint8_t v_onlySrcDeps_2113_; uint8_t v_depsJson_2114_; lean_object* v_opts_2115_; uint32_t v_trustLevel_2116_; uint32_t v_numThreads_2117_; lean_object* v_rootDir_x3f_2118_; lean_object* v_setupFileName_x3f_2119_; lean_object* v_ileanFileName_x3f_2120_; lean_object* v_cFileName_x3f_2121_; lean_object* v_bcFileName_x3f_2122_; uint8_t v_jsonOutput_2123_; lean_object* v_errorOnKinds_2124_; uint8_t v_printStats_2125_; uint8_t v_run_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2137_; 
v_leanOpts_2106_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2107_ = lean_ctor_get(v_opts_931_, 1);
v_component_2108_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2109_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2110_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2111_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2112_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2113_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2114_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2115_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2116_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2117_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2118_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2119_ = lean_ctor_get(v_opts_931_, 4);
v_ileanFileName_x3f_2120_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2121_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2122_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2123_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2124_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2125_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2126_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v_opts_931_, 5);
lean_dec(v_unused_2138_);
v___x_2128_ = v_opts_931_;
v_isShared_2129_ = v_isSharedCheck_2137_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_errorOnKinds_2124_);
lean_inc(v_bcFileName_x3f_2122_);
lean_inc(v_cFileName_x3f_2121_);
lean_inc(v_ileanFileName_x3f_2120_);
lean_inc(v_setupFileName_x3f_2119_);
lean_inc(v_rootDir_x3f_2118_);
lean_inc(v_opts_2115_);
lean_inc(v_forwardedArgs_2107_);
lean_inc(v_leanOpts_2106_);
lean_dec(v_opts_931_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2137_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v_a_2102_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 5, v___x_2130_);
v___x_2132_ = v___x_2128_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_leanOpts_2106_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_forwardedArgs_2107_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_opts_2115_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_rootDir_x3f_2118_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v_setupFileName_x3f_2119_);
lean_ctor_set(v_reuseFailAlloc_2136_, 5, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2136_, 6, v_ileanFileName_x3f_2120_);
lean_ctor_set(v_reuseFailAlloc_2136_, 7, v_cFileName_x3f_2121_);
lean_ctor_set(v_reuseFailAlloc_2136_, 8, v_bcFileName_x3f_2122_);
lean_ctor_set(v_reuseFailAlloc_2136_, 9, v_errorOnKinds_2124_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*10 + 8, v_component_2108_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*10 + 9, v_printPrefix_2109_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*10 + 10, v_printLibDir_2110_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*10 + 11, v_useStdin_2111_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*10 + 12, v_onlyDeps_2112_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*10 + 13, v_onlySrcDeps_2113_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*10 + 14, v_depsJson_2114_);
lean_ctor_set_uint32(v_reuseFailAlloc_2136_, sizeof(void*)*10, v_trustLevel_2116_);
lean_ctor_set_uint32(v_reuseFailAlloc_2136_, sizeof(void*)*10 + 4, v_numThreads_2117_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*10 + 15, v_jsonOutput_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*10 + 16, v_printStats_2125_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*10 + 17, v_run_2126_);
v___x_2132_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2132_);
v___x_2134_ = v___x_2104_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec_ref(v_opts_931_);
v_a_2140_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2144_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2145_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2144_);
lean_dec_ref(v___x_2145_);
goto v___jp_2141_;
v___jp_2141_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_io_error_to_string(v_a_2140_);
v___x_2143_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2142_);
lean_dec_ref(v___x_2143_);
goto v___jp_1108_;
}
}
}
}
else
{
lean_object* v_leanOpts_2146_; lean_object* v_forwardedArgs_2147_; uint8_t v_component_2148_; uint8_t v_printPrefix_2149_; uint8_t v_printLibDir_2150_; uint8_t v_useStdin_2151_; uint8_t v_onlyDeps_2152_; uint8_t v_onlySrcDeps_2153_; uint8_t v_depsJson_2154_; lean_object* v_opts_2155_; uint32_t v_trustLevel_2156_; uint32_t v_numThreads_2157_; lean_object* v_rootDir_x3f_2158_; lean_object* v_setupFileName_x3f_2159_; lean_object* v_oleanFileName_x3f_2160_; lean_object* v_ileanFileName_x3f_2161_; lean_object* v_cFileName_x3f_2162_; lean_object* v_bcFileName_x3f_2163_; uint8_t v_jsonOutput_2164_; lean_object* v_errorOnKinds_2165_; uint8_t v_printStats_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_2146_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2147_ = lean_ctor_get(v_opts_931_, 1);
v_component_2148_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2149_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2150_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2151_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2152_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2153_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2154_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2155_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2156_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2157_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2158_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2159_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2160_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_2161_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2162_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2163_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2164_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2165_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2166_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2168_ = v_opts_931_;
v_isShared_2169_ = v_isSharedCheck_2176_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_errorOnKinds_2165_);
lean_inc(v_bcFileName_x3f_2163_);
lean_inc(v_cFileName_x3f_2162_);
lean_inc(v_ileanFileName_x3f_2161_);
lean_inc(v_oleanFileName_x3f_2160_);
lean_inc(v_setupFileName_x3f_2159_);
lean_inc(v_rootDir_x3f_2158_);
lean_inc(v_opts_2155_);
lean_inc(v_forwardedArgs_2147_);
lean_inc(v_leanOpts_2146_);
lean_dec(v_opts_931_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2176_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2170_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2171_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2146_, v___x_2170_, v___x_1156_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2171_);
v___x_2173_ = v___x_2168_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_forwardedArgs_2147_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_opts_2155_);
lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_rootDir_x3f_2158_);
lean_ctor_set(v_reuseFailAlloc_2175_, 4, v_setupFileName_x3f_2159_);
lean_ctor_set(v_reuseFailAlloc_2175_, 5, v_oleanFileName_x3f_2160_);
lean_ctor_set(v_reuseFailAlloc_2175_, 6, v_ileanFileName_x3f_2161_);
lean_ctor_set(v_reuseFailAlloc_2175_, 7, v_cFileName_x3f_2162_);
lean_ctor_set(v_reuseFailAlloc_2175_, 8, v_bcFileName_x3f_2163_);
lean_ctor_set(v_reuseFailAlloc_2175_, 9, v_errorOnKinds_2165_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*10 + 8, v_component_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*10 + 9, v_printPrefix_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*10 + 10, v_printLibDir_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*10 + 11, v_useStdin_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*10 + 12, v_onlyDeps_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*10 + 13, v_onlySrcDeps_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*10 + 14, v_depsJson_2154_);
lean_ctor_set_uint32(v_reuseFailAlloc_2175_, sizeof(void*)*10, v_trustLevel_2156_);
lean_ctor_set_uint32(v_reuseFailAlloc_2175_, sizeof(void*)*10 + 4, v_numThreads_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*10 + 15, v_jsonOutput_2164_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*10 + 16, v_printStats_2166_);
v___x_2173_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2174_; 
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*10 + 17, v___x_1158_);
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
return v___x_2174_;
}
}
}
}
else
{
lean_object* v_leanOpts_2177_; lean_object* v_forwardedArgs_2178_; uint8_t v_component_2179_; uint8_t v_printPrefix_2180_; uint8_t v_printLibDir_2181_; uint8_t v_onlyDeps_2182_; uint8_t v_onlySrcDeps_2183_; uint8_t v_depsJson_2184_; lean_object* v_opts_2185_; uint32_t v_trustLevel_2186_; uint32_t v_numThreads_2187_; lean_object* v_rootDir_x3f_2188_; lean_object* v_setupFileName_x3f_2189_; lean_object* v_oleanFileName_x3f_2190_; lean_object* v_ileanFileName_x3f_2191_; lean_object* v_cFileName_x3f_2192_; lean_object* v_bcFileName_x3f_2193_; uint8_t v_jsonOutput_2194_; lean_object* v_errorOnKinds_2195_; uint8_t v_printStats_2196_; uint8_t v_run_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_optArg_x3f_933_);
v_leanOpts_2177_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2178_ = lean_ctor_get(v_opts_931_, 1);
v_component_2179_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2180_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2181_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_onlyDeps_2182_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2183_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2184_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2185_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2186_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2187_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2188_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2189_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2190_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_2191_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2192_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2193_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2194_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2195_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2196_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2197_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2199_ = v_opts_931_;
v_isShared_2200_ = v_isSharedCheck_2205_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_errorOnKinds_2195_);
lean_inc(v_bcFileName_x3f_2193_);
lean_inc(v_cFileName_x3f_2192_);
lean_inc(v_ileanFileName_x3f_2191_);
lean_inc(v_oleanFileName_x3f_2190_);
lean_inc(v_setupFileName_x3f_2189_);
lean_inc(v_rootDir_x3f_2188_);
lean_inc(v_opts_2185_);
lean_inc(v_forwardedArgs_2178_);
lean_inc(v_leanOpts_2177_);
lean_dec(v_opts_931_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2205_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_leanOpts_2177_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_forwardedArgs_2178_);
lean_ctor_set(v_reuseFailAlloc_2204_, 2, v_opts_2185_);
lean_ctor_set(v_reuseFailAlloc_2204_, 3, v_rootDir_x3f_2188_);
lean_ctor_set(v_reuseFailAlloc_2204_, 4, v_setupFileName_x3f_2189_);
lean_ctor_set(v_reuseFailAlloc_2204_, 5, v_oleanFileName_x3f_2190_);
lean_ctor_set(v_reuseFailAlloc_2204_, 6, v_ileanFileName_x3f_2191_);
lean_ctor_set(v_reuseFailAlloc_2204_, 7, v_cFileName_x3f_2192_);
lean_ctor_set(v_reuseFailAlloc_2204_, 8, v_bcFileName_x3f_2193_);
lean_ctor_set(v_reuseFailAlloc_2204_, 9, v_errorOnKinds_2195_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*10 + 8, v_component_2179_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*10 + 9, v_printPrefix_2180_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*10 + 10, v_printLibDir_2181_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*10 + 12, v_onlyDeps_2182_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*10 + 13, v_onlySrcDeps_2183_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*10 + 14, v_depsJson_2184_);
lean_ctor_set_uint32(v_reuseFailAlloc_2204_, sizeof(void*)*10, v_trustLevel_2186_);
lean_ctor_set_uint32(v_reuseFailAlloc_2204_, sizeof(void*)*10 + 4, v_numThreads_2187_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*10 + 15, v_jsonOutput_2194_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*10 + 16, v_printStats_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*10 + 17, v_run_2197_);
v___x_2202_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2203_; 
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*10 + 11, v___x_1156_);
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
return v___x_2203_;
}
}
}
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2207_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2206_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2266_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2266_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2266_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2212_ = lean_unsigned_to_nat(0u);
v___x_2213_ = lean_string_utf8_byte_size(v_a_2208_);
lean_inc(v_a_2208_);
v___x_2214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2214_, 0, v_a_2208_);
lean_ctor_set(v___x_2214_, 1, v___x_2212_);
lean_ctor_set(v___x_2214_, 2, v___x_2213_);
v___x_2215_ = l_String_Slice_toNat_x3f(v___x_2214_);
lean_dec_ref_known(v___x_2214_, 3);
if (lean_obj_tag(v___x_2215_) == 1)
{
lean_object* v_val_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v_val_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_val_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = lean_unsigned_to_nat(4u);
v___x_2218_ = lean_unsigned_to_nat(2u);
v___x_2219_ = lean_nat_shiftr(v_val_2216_, v___x_2218_);
lean_dec(v_val_2216_);
v___x_2220_ = lean_nat_mul(v___x_2219_, v___x_2217_);
lean_dec(v___x_2219_);
v___x_2221_ = lean_unsigned_to_nat(1024u);
v___x_2222_ = lean_nat_mul(v___x_2220_, v___x_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25);
v___x_2224_ = lean_nat_dec_lt(v___x_2222_, v___x_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec(v___x_2222_);
lean_del_object(v___x_2210_);
lean_dec(v_a_2208_);
lean_dec_ref(v_opts_931_);
v___x_2225_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2226_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2225_);
lean_dec_ref(v___x_2226_);
goto v___jp_974_;
}
else
{
size_t v___x_2227_; lean_object* v___x_2228_; lean_object* v_leanOpts_2229_; lean_object* v_forwardedArgs_2230_; uint8_t v_component_2231_; uint8_t v_printPrefix_2232_; uint8_t v_printLibDir_2233_; uint8_t v_useStdin_2234_; uint8_t v_onlyDeps_2235_; uint8_t v_onlySrcDeps_2236_; uint8_t v_depsJson_2237_; lean_object* v_opts_2238_; uint32_t v_trustLevel_2239_; uint32_t v_numThreads_2240_; lean_object* v_rootDir_x3f_2241_; lean_object* v_setupFileName_x3f_2242_; lean_object* v_oleanFileName_x3f_2243_; lean_object* v_ileanFileName_x3f_2244_; lean_object* v_cFileName_x3f_2245_; lean_object* v_bcFileName_x3f_2246_; uint8_t v_jsonOutput_2247_; lean_object* v_errorOnKinds_2248_; uint8_t v_printStats_2249_; uint8_t v_run_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2263_; 
v___x_2227_ = lean_usize_of_nat(v___x_2222_);
lean_dec(v___x_2222_);
v___x_2228_ = lean_internal_set_thread_stack_size(v___x_2227_);
v_leanOpts_2229_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2230_ = lean_ctor_get(v_opts_931_, 1);
v_component_2231_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2232_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2233_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2234_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2235_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2236_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2237_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2238_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2239_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2240_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2241_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2242_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2243_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_2244_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2245_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2246_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2247_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2248_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2249_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2250_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2252_ = v_opts_931_;
v_isShared_2253_ = v_isSharedCheck_2263_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_errorOnKinds_2248_);
lean_inc(v_bcFileName_x3f_2246_);
lean_inc(v_cFileName_x3f_2245_);
lean_inc(v_ileanFileName_x3f_2244_);
lean_inc(v_oleanFileName_x3f_2243_);
lean_inc(v_setupFileName_x3f_2242_);
lean_inc(v_rootDir_x3f_2241_);
lean_inc(v_opts_2238_);
lean_inc(v_forwardedArgs_2230_);
lean_inc(v_leanOpts_2229_);
lean_dec(v_opts_931_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2263_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2254_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2255_ = lean_string_append(v___x_2254_, v_a_2208_);
lean_dec(v_a_2208_);
v___x_2256_ = lean_array_push(v_forwardedArgs_2230_, v___x_2255_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 1, v___x_2256_);
v___x_2258_ = v___x_2252_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_leanOpts_2229_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2262_, 2, v_opts_2238_);
lean_ctor_set(v_reuseFailAlloc_2262_, 3, v_rootDir_x3f_2241_);
lean_ctor_set(v_reuseFailAlloc_2262_, 4, v_setupFileName_x3f_2242_);
lean_ctor_set(v_reuseFailAlloc_2262_, 5, v_oleanFileName_x3f_2243_);
lean_ctor_set(v_reuseFailAlloc_2262_, 6, v_ileanFileName_x3f_2244_);
lean_ctor_set(v_reuseFailAlloc_2262_, 7, v_cFileName_x3f_2245_);
lean_ctor_set(v_reuseFailAlloc_2262_, 8, v_bcFileName_x3f_2246_);
lean_ctor_set(v_reuseFailAlloc_2262_, 9, v_errorOnKinds_2248_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, sizeof(void*)*10 + 8, v_component_2231_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, sizeof(void*)*10 + 9, v_printPrefix_2232_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, sizeof(void*)*10 + 10, v_printLibDir_2233_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, sizeof(void*)*10 + 11, v_useStdin_2234_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, sizeof(void*)*10 + 12, v_onlyDeps_2235_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, sizeof(void*)*10 + 13, v_onlySrcDeps_2236_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, sizeof(void*)*10 + 14, v_depsJson_2237_);
lean_ctor_set_uint32(v_reuseFailAlloc_2262_, sizeof(void*)*10, v_trustLevel_2239_);
lean_ctor_set_uint32(v_reuseFailAlloc_2262_, sizeof(void*)*10 + 4, v_numThreads_2240_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, sizeof(void*)*10 + 15, v_jsonOutput_2247_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, sizeof(void*)*10 + 16, v_printStats_2249_);
lean_ctor_set_uint8(v_reuseFailAlloc_2262_, sizeof(void*)*10 + 17, v_run_2250_);
v___x_2258_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
lean_object* v___x_2260_; 
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2258_);
v___x_2260_ = v___x_2210_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
lean_dec(v___x_2215_);
lean_del_object(v___x_2210_);
lean_dec(v_a_2208_);
lean_dec_ref(v_opts_931_);
v___x_2264_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28));
v___x_2265_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2264_);
lean_dec_ref(v___x_2265_);
goto v___jp_971_;
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec_ref(v_opts_931_);
v_a_2267_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2207_, 1);
v___x_2271_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2272_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2271_);
lean_dec_ref(v___x_2272_);
goto v___jp_2268_;
v___jp_2268_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = lean_io_error_to_string(v_a_2267_);
v___x_2270_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2269_);
lean_dec_ref(v___x_2270_);
goto v___jp_968_;
}
}
}
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2274_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2273_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2312_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2312_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2312_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v_leanOpts_2279_; lean_object* v_forwardedArgs_2280_; uint8_t v_component_2281_; uint8_t v_printPrefix_2282_; uint8_t v_printLibDir_2283_; uint8_t v_useStdin_2284_; uint8_t v_onlyDeps_2285_; uint8_t v_onlySrcDeps_2286_; uint8_t v_depsJson_2287_; lean_object* v_opts_2288_; uint32_t v_trustLevel_2289_; uint32_t v_numThreads_2290_; lean_object* v_rootDir_x3f_2291_; lean_object* v_setupFileName_x3f_2292_; lean_object* v_oleanFileName_x3f_2293_; lean_object* v_ileanFileName_x3f_2294_; lean_object* v_cFileName_x3f_2295_; uint8_t v_jsonOutput_2296_; lean_object* v_errorOnKinds_2297_; uint8_t v_printStats_2298_; uint8_t v_run_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2310_; 
v_leanOpts_2279_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2280_ = lean_ctor_get(v_opts_931_, 1);
v_component_2281_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2282_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2283_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2284_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2285_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2286_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2287_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2288_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2289_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2290_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2291_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2292_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2293_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_2294_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2295_ = lean_ctor_get(v_opts_931_, 7);
v_jsonOutput_2296_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2297_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2298_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2299_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; 
v_unused_2311_ = lean_ctor_get(v_opts_931_, 8);
lean_dec(v_unused_2311_);
v___x_2301_ = v_opts_931_;
v_isShared_2302_ = v_isSharedCheck_2310_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_errorOnKinds_2297_);
lean_inc(v_cFileName_x3f_2295_);
lean_inc(v_ileanFileName_x3f_2294_);
lean_inc(v_oleanFileName_x3f_2293_);
lean_inc(v_setupFileName_x3f_2292_);
lean_inc(v_rootDir_x3f_2291_);
lean_inc(v_opts_2288_);
lean_inc(v_forwardedArgs_2280_);
lean_inc(v_leanOpts_2279_);
lean_dec(v_opts_931_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2310_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2303_, 0, v_a_2275_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 8, v___x_2303_);
v___x_2305_ = v___x_2301_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_leanOpts_2279_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_forwardedArgs_2280_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_opts_2288_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_rootDir_x3f_2291_);
lean_ctor_set(v_reuseFailAlloc_2309_, 4, v_setupFileName_x3f_2292_);
lean_ctor_set(v_reuseFailAlloc_2309_, 5, v_oleanFileName_x3f_2293_);
lean_ctor_set(v_reuseFailAlloc_2309_, 6, v_ileanFileName_x3f_2294_);
lean_ctor_set(v_reuseFailAlloc_2309_, 7, v_cFileName_x3f_2295_);
lean_ctor_set(v_reuseFailAlloc_2309_, 8, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2309_, 9, v_errorOnKinds_2297_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*10 + 8, v_component_2281_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*10 + 9, v_printPrefix_2282_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*10 + 10, v_printLibDir_2283_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*10 + 11, v_useStdin_2284_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*10 + 12, v_onlyDeps_2285_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*10 + 13, v_onlySrcDeps_2286_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*10 + 14, v_depsJson_2287_);
lean_ctor_set_uint32(v_reuseFailAlloc_2309_, sizeof(void*)*10, v_trustLevel_2289_);
lean_ctor_set_uint32(v_reuseFailAlloc_2309_, sizeof(void*)*10 + 4, v_numThreads_2290_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*10 + 15, v_jsonOutput_2296_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*10 + 16, v_printStats_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*10 + 17, v_run_2299_);
v___x_2305_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2307_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2305_);
v___x_2307_ = v___x_2277_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_dec_ref(v_opts_931_);
v_a_2313_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2274_, 1);
v___x_2317_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2318_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2317_);
lean_dec_ref(v___x_2318_);
goto v___jp_2314_;
v___jp_2314_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_io_error_to_string(v_a_2313_);
v___x_2316_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2315_);
lean_dec_ref(v___x_2316_);
goto v___jp_1114_;
}
}
}
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2320_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2319_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2358_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2358_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2358_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v_leanOpts_2325_; lean_object* v_forwardedArgs_2326_; uint8_t v_component_2327_; uint8_t v_printPrefix_2328_; uint8_t v_printLibDir_2329_; uint8_t v_useStdin_2330_; uint8_t v_onlyDeps_2331_; uint8_t v_onlySrcDeps_2332_; uint8_t v_depsJson_2333_; lean_object* v_opts_2334_; uint32_t v_trustLevel_2335_; uint32_t v_numThreads_2336_; lean_object* v_rootDir_x3f_2337_; lean_object* v_setupFileName_x3f_2338_; lean_object* v_oleanFileName_x3f_2339_; lean_object* v_ileanFileName_x3f_2340_; lean_object* v_bcFileName_x3f_2341_; uint8_t v_jsonOutput_2342_; lean_object* v_errorOnKinds_2343_; uint8_t v_printStats_2344_; uint8_t v_run_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2356_; 
v_leanOpts_2325_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2326_ = lean_ctor_get(v_opts_931_, 1);
v_component_2327_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2328_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2329_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2330_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2331_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2332_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2333_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2334_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2335_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_numThreads_2336_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10 + 4);
v_rootDir_x3f_2337_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2338_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2339_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_2340_ = lean_ctor_get(v_opts_931_, 6);
v_bcFileName_x3f_2341_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2342_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2343_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2344_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2345_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2356_ == 0)
{
lean_object* v_unused_2357_; 
v_unused_2357_ = lean_ctor_get(v_opts_931_, 7);
lean_dec(v_unused_2357_);
v___x_2347_ = v_opts_931_;
v_isShared_2348_ = v_isSharedCheck_2356_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_errorOnKinds_2343_);
lean_inc(v_bcFileName_x3f_2341_);
lean_inc(v_ileanFileName_x3f_2340_);
lean_inc(v_oleanFileName_x3f_2339_);
lean_inc(v_setupFileName_x3f_2338_);
lean_inc(v_rootDir_x3f_2337_);
lean_inc(v_opts_2334_);
lean_inc(v_forwardedArgs_2326_);
lean_inc(v_leanOpts_2325_);
lean_dec(v_opts_931_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2356_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2349_, 0, v_a_2321_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 7, v___x_2349_);
v___x_2351_ = v___x_2347_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_leanOpts_2325_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_forwardedArgs_2326_);
lean_ctor_set(v_reuseFailAlloc_2355_, 2, v_opts_2334_);
lean_ctor_set(v_reuseFailAlloc_2355_, 3, v_rootDir_x3f_2337_);
lean_ctor_set(v_reuseFailAlloc_2355_, 4, v_setupFileName_x3f_2338_);
lean_ctor_set(v_reuseFailAlloc_2355_, 5, v_oleanFileName_x3f_2339_);
lean_ctor_set(v_reuseFailAlloc_2355_, 6, v_ileanFileName_x3f_2340_);
lean_ctor_set(v_reuseFailAlloc_2355_, 7, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2355_, 8, v_bcFileName_x3f_2341_);
lean_ctor_set(v_reuseFailAlloc_2355_, 9, v_errorOnKinds_2343_);
lean_ctor_set_uint8(v_reuseFailAlloc_2355_, sizeof(void*)*10 + 8, v_component_2327_);
lean_ctor_set_uint8(v_reuseFailAlloc_2355_, sizeof(void*)*10 + 9, v_printPrefix_2328_);
lean_ctor_set_uint8(v_reuseFailAlloc_2355_, sizeof(void*)*10 + 10, v_printLibDir_2329_);
lean_ctor_set_uint8(v_reuseFailAlloc_2355_, sizeof(void*)*10 + 11, v_useStdin_2330_);
lean_ctor_set_uint8(v_reuseFailAlloc_2355_, sizeof(void*)*10 + 12, v_onlyDeps_2331_);
lean_ctor_set_uint8(v_reuseFailAlloc_2355_, sizeof(void*)*10 + 13, v_onlySrcDeps_2332_);
lean_ctor_set_uint8(v_reuseFailAlloc_2355_, sizeof(void*)*10 + 14, v_depsJson_2333_);
lean_ctor_set_uint32(v_reuseFailAlloc_2355_, sizeof(void*)*10, v_trustLevel_2335_);
lean_ctor_set_uint32(v_reuseFailAlloc_2355_, sizeof(void*)*10 + 4, v_numThreads_2336_);
lean_ctor_set_uint8(v_reuseFailAlloc_2355_, sizeof(void*)*10 + 15, v_jsonOutput_2342_);
lean_ctor_set_uint8(v_reuseFailAlloc_2355_, sizeof(void*)*10 + 16, v_printStats_2344_);
lean_ctor_set_uint8(v_reuseFailAlloc_2355_, sizeof(void*)*10 + 17, v_run_2345_);
v___x_2351_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2353_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2351_);
v___x_2353_ = v___x_2323_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec_ref(v_opts_931_);
v_a_2359_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2363_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2364_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2363_);
lean_dec_ref(v___x_2364_);
goto v___jp_2360_;
v___jp_2360_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_io_error_to_string(v_a_2359_);
v___x_2362_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2361_);
lean_dec_ref(v___x_2362_);
goto v___jp_962_;
}
}
}
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
v___x_2365_ = l___private_Lean_Shell_0__Lean_featuresString;
v___x_2366_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2365_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2374_; 
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; 
v_unused_2375_ = lean_ctor_get(v___x_2366_, 0);
lean_dec(v_unused_2375_);
v___x_2368_ = v___x_2366_;
v_isShared_2369_ = v_isSharedCheck_2374_;
goto v_resetjp_2367_;
}
else
{
lean_dec(v___x_2366_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2374_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2372_; 
v___x_2370_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2369_ == 0)
{
lean_ctor_set_tag(v___x_2368_, 1);
lean_ctor_set(v___x_2368_, 0, v___x_2370_);
v___x_2372_ = v___x_2368_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v_a_2376_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2376_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2380_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2381_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2380_);
lean_dec_ref(v___x_2381_);
goto v___jp_2377_;
v___jp_2377_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_io_error_to_string(v_a_2376_);
v___x_2379_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2378_);
lean_dec_ref(v___x_2379_);
goto v___jp_1120_;
}
}
}
}
else
{
lean_object* v___x_2382_; 
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
v___x_2382_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1144_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2390_; 
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; 
v_unused_2391_ = lean_ctor_get(v___x_2382_, 0);
lean_dec(v_unused_2391_);
v___x_2384_ = v___x_2382_;
v_isShared_2385_ = v_isSharedCheck_2390_;
goto v_resetjp_2383_;
}
else
{
lean_dec(v___x_2382_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2390_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2386_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2385_ == 0)
{
lean_ctor_set_tag(v___x_2384_, 1);
lean_ctor_set(v___x_2384_, 0, v___x_2386_);
v___x_2388_ = v___x_2384_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_a_2392_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2382_, 1);
v___x_2396_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2397_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2396_);
lean_dec_ref(v___x_2397_);
goto v___jp_2393_;
v___jp_2393_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_io_error_to_string(v_a_2392_);
v___x_2395_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2394_);
lean_dec_ref(v___x_2395_);
goto v___jp_956_;
}
}
}
}
else
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
v___x_2398_ = l_Lean_githash;
v___x_2399_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2398_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2407_; 
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2407_ == 0)
{
lean_object* v_unused_2408_; 
v_unused_2408_ = lean_ctor_get(v___x_2399_, 0);
lean_dec(v_unused_2408_);
v___x_2401_ = v___x_2399_;
v_isShared_2402_ = v_isSharedCheck_2407_;
goto v_resetjp_2400_;
}
else
{
lean_dec(v___x_2399_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2407_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2403_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2402_ == 0)
{
lean_ctor_set_tag(v___x_2401_, 1);
lean_ctor_set(v___x_2401_, 0, v___x_2403_);
v___x_2405_ = v___x_2401_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v_a_2409_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2399_, 1);
v___x_2413_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2414_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2413_);
lean_dec_ref(v___x_2414_);
goto v___jp_2410_;
v___jp_2410_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_io_error_to_string(v_a_2409_);
v___x_2412_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2411_);
lean_dec_ref(v___x_2412_);
goto v___jp_1126_;
}
}
}
}
else
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
v___x_2415_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2416_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2415_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2424_ == 0)
{
lean_object* v_unused_2425_; 
v_unused_2425_ = lean_ctor_get(v___x_2416_, 0);
lean_dec(v_unused_2425_);
v___x_2418_ = v___x_2416_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_dec(v___x_2416_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2419_ == 0)
{
lean_ctor_set_tag(v___x_2418_, 1);
lean_ctor_set(v___x_2418_, 0, v___x_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_a_2426_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2416_, 1);
v___x_2430_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2431_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2430_);
lean_dec_ref(v___x_2431_);
goto v___jp_2427_;
v___jp_2427_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = lean_io_error_to_string(v_a_2426_);
v___x_2429_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2428_);
lean_dec_ref(v___x_2429_);
goto v___jp_950_;
}
}
}
}
else
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_dec(v_optArg_x3f_933_);
lean_dec_ref(v_opts_931_);
v___x_2432_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2433_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2432_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2441_; 
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; 
v_unused_2442_ = lean_ctor_get(v___x_2433_, 0);
lean_dec(v_unused_2442_);
v___x_2435_ = v___x_2433_;
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
else
{
lean_dec(v___x_2433_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2437_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2436_ == 0)
{
lean_ctor_set_tag(v___x_2435_, 1);
lean_ctor_set(v___x_2435_, 0, v___x_2437_);
v___x_2439_ = v___x_2435_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_a_2443_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2433_, 1);
v___x_2447_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2448_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2447_);
lean_dec_ref(v___x_2448_);
goto v___jp_2444_;
v___jp_2444_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = lean_io_error_to_string(v_a_2443_);
v___x_2446_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2445_);
lean_dec_ref(v___x_2446_);
goto v___jp_1132_;
}
}
}
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2450_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2449_, v_optArg_x3f_933_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2501_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2501_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2501_;
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
lean_object* v_val_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
v_val_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_val_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v___x_2460_ = lean_cstr_to_nat("4294967296");
v___x_2461_ = lean_nat_dec_lt(v_val_2459_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
lean_dec(v_val_2459_);
lean_del_object(v___x_2453_);
lean_dec(v_a_2451_);
lean_dec_ref(v_opts_931_);
v___x_2462_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2463_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2462_);
lean_dec_ref(v___x_2463_);
goto v___jp_944_;
}
else
{
lean_object* v_leanOpts_2464_; lean_object* v_forwardedArgs_2465_; uint8_t v_component_2466_; uint8_t v_printPrefix_2467_; uint8_t v_printLibDir_2468_; uint8_t v_useStdin_2469_; uint8_t v_onlyDeps_2470_; uint8_t v_onlySrcDeps_2471_; uint8_t v_depsJson_2472_; lean_object* v_opts_2473_; uint32_t v_trustLevel_2474_; lean_object* v_rootDir_x3f_2475_; lean_object* v_setupFileName_x3f_2476_; lean_object* v_oleanFileName_x3f_2477_; lean_object* v_ileanFileName_x3f_2478_; lean_object* v_cFileName_x3f_2479_; lean_object* v_bcFileName_x3f_2480_; uint8_t v_jsonOutput_2481_; lean_object* v_errorOnKinds_2482_; uint8_t v_printStats_2483_; uint8_t v_run_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2498_; 
v_leanOpts_2464_ = lean_ctor_get(v_opts_931_, 0);
v_forwardedArgs_2465_ = lean_ctor_get(v_opts_931_, 1);
v_component_2466_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 8);
v_printPrefix_2467_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 9);
v_printLibDir_2468_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 10);
v_useStdin_2469_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 11);
v_onlyDeps_2470_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2471_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 13);
v_depsJson_2472_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 14);
v_opts_2473_ = lean_ctor_get(v_opts_931_, 2);
v_trustLevel_2474_ = lean_ctor_get_uint32(v_opts_931_, sizeof(void*)*10);
v_rootDir_x3f_2475_ = lean_ctor_get(v_opts_931_, 3);
v_setupFileName_x3f_2476_ = lean_ctor_get(v_opts_931_, 4);
v_oleanFileName_x3f_2477_ = lean_ctor_get(v_opts_931_, 5);
v_ileanFileName_x3f_2478_ = lean_ctor_get(v_opts_931_, 6);
v_cFileName_x3f_2479_ = lean_ctor_get(v_opts_931_, 7);
v_bcFileName_x3f_2480_ = lean_ctor_get(v_opts_931_, 8);
v_jsonOutput_2481_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 15);
v_errorOnKinds_2482_ = lean_ctor_get(v_opts_931_, 9);
v_printStats_2483_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 16);
v_run_2484_ = lean_ctor_get_uint8(v_opts_931_, sizeof(void*)*10 + 17);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_opts_931_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2486_ = v_opts_931_;
v_isShared_2487_ = v_isSharedCheck_2498_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_errorOnKinds_2482_);
lean_inc(v_bcFileName_x3f_2480_);
lean_inc(v_cFileName_x3f_2479_);
lean_inc(v_ileanFileName_x3f_2478_);
lean_inc(v_oleanFileName_x3f_2477_);
lean_inc(v_setupFileName_x3f_2476_);
lean_inc(v_rootDir_x3f_2475_);
lean_inc(v_opts_2473_);
lean_inc(v_forwardedArgs_2465_);
lean_inc(v_leanOpts_2464_);
lean_dec(v_opts_931_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2498_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
uint32_t v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2488_ = lean_uint32_of_nat(v_val_2459_);
lean_dec(v_val_2459_);
v___x_2489_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2490_ = lean_string_append(v___x_2489_, v_a_2451_);
lean_dec(v_a_2451_);
v___x_2491_ = lean_array_push(v_forwardedArgs_2465_, v___x_2490_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 1, v___x_2491_);
v___x_2493_ = v___x_2486_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_leanOpts_2464_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2497_, 2, v_opts_2473_);
lean_ctor_set(v_reuseFailAlloc_2497_, 3, v_rootDir_x3f_2475_);
lean_ctor_set(v_reuseFailAlloc_2497_, 4, v_setupFileName_x3f_2476_);
lean_ctor_set(v_reuseFailAlloc_2497_, 5, v_oleanFileName_x3f_2477_);
lean_ctor_set(v_reuseFailAlloc_2497_, 6, v_ileanFileName_x3f_2478_);
lean_ctor_set(v_reuseFailAlloc_2497_, 7, v_cFileName_x3f_2479_);
lean_ctor_set(v_reuseFailAlloc_2497_, 8, v_bcFileName_x3f_2480_);
lean_ctor_set(v_reuseFailAlloc_2497_, 9, v_errorOnKinds_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2497_, sizeof(void*)*10 + 8, v_component_2466_);
lean_ctor_set_uint8(v_reuseFailAlloc_2497_, sizeof(void*)*10 + 9, v_printPrefix_2467_);
lean_ctor_set_uint8(v_reuseFailAlloc_2497_, sizeof(void*)*10 + 10, v_printLibDir_2468_);
lean_ctor_set_uint8(v_reuseFailAlloc_2497_, sizeof(void*)*10 + 11, v_useStdin_2469_);
lean_ctor_set_uint8(v_reuseFailAlloc_2497_, sizeof(void*)*10 + 12, v_onlyDeps_2470_);
lean_ctor_set_uint8(v_reuseFailAlloc_2497_, sizeof(void*)*10 + 13, v_onlySrcDeps_2471_);
lean_ctor_set_uint8(v_reuseFailAlloc_2497_, sizeof(void*)*10 + 14, v_depsJson_2472_);
lean_ctor_set_uint32(v_reuseFailAlloc_2497_, sizeof(void*)*10, v_trustLevel_2474_);
lean_ctor_set_uint8(v_reuseFailAlloc_2497_, sizeof(void*)*10 + 15, v_jsonOutput_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2497_, sizeof(void*)*10 + 16, v_printStats_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2497_, sizeof(void*)*10 + 17, v_run_2484_);
v___x_2493_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2495_; 
lean_ctor_set_uint32(v___x_2493_, sizeof(void*)*10 + 4, v___x_2488_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2493_);
v___x_2495_ = v___x_2453_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
else
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec(v___x_2458_);
lean_del_object(v___x_2453_);
lean_dec(v_a_2451_);
lean_dec_ref(v_opts_931_);
v___x_2499_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2500_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2499_);
lean_dec_ref(v___x_2500_);
goto v___jp_941_;
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec_ref(v_opts_931_);
v_a_2502_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2450_, 1);
v___x_2506_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2507_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2506_);
lean_dec_ref(v___x_2507_);
goto v___jp_2503_;
v___jp_2503_:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_io_error_to_string(v_a_2502_);
v___x_2505_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2504_);
lean_dec_ref(v___x_2505_);
goto v___jp_938_;
}
}
}
}
else
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_dec(v_optArg_x3f_933_);
v___x_2508_ = lean_internal_set_exit_on_panic(v___x_1136_);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_opts_931_);
return v___x_2509_;
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
lean_dec_ref_known(v___x_1040_, 1);
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
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_io_error_to_string(v___y_1075_);
v___x_1077_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1076_);
lean_dec_ref(v___x_1077_);
goto v___jp_1071_;
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
v___x_1094_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
v___jp_1096_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1098_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1097_);
lean_dec_ref(v___x_1098_);
goto v___jp_1093_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2510_, lean_object* v_opt_2511_, lean_object* v_optArg_x3f_2512_, lean_object* v_a_2513_){
_start:
{
uint32_t v_opt_boxed_2514_; lean_object* v_res_2515_; 
v_opt_boxed_2514_ = lean_unbox_uint32(v_opt_2511_);
lean_dec(v_opt_2511_);
v_res_2515_ = lean_shell_options_process(v_opts_2510_, v_opt_boxed_2514_, v_optArg_x3f_2512_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_opts_2516_, lean_object* v_opt_2517_){
_start:
{
lean_object* v_name_2518_; lean_object* v_defValue_2519_; lean_object* v_map_2520_; lean_object* v___x_2521_; 
v_name_2518_ = lean_ctor_get(v_opt_2517_, 0);
v_defValue_2519_ = lean_ctor_get(v_opt_2517_, 1);
v_map_2520_ = lean_ctor_get(v_opts_2516_, 0);
v___x_2521_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2520_, v_name_2518_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_inc(v_defValue_2519_);
return v_defValue_2519_;
}
else
{
lean_object* v_val_2522_; 
v_val_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_val_2522_);
lean_dec_ref_known(v___x_2521_, 1);
if (lean_obj_tag(v_val_2522_) == 3)
{
lean_object* v_v_2523_; 
v_v_2523_ = lean_ctor_get(v_val_2522_, 0);
lean_inc(v_v_2523_);
lean_dec_ref_known(v_val_2522_, 1);
return v_v_2523_;
}
else
{
lean_dec(v_val_2522_);
lean_inc(v_defValue_2519_);
return v_defValue_2519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_opts_2524_, lean_object* v_opt_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_opts_2524_, v_opt_2525_);
lean_dec_ref(v_opt_2525_);
lean_dec_ref(v_opts_2524_);
return v_res_2526_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2529_ = lean_string_utf8_byte_size(v___x_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2530_){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2531_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2532_ = lean_string_utf8_byte_size(v_s_2530_);
v___x_2533_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1);
v___x_2534_ = lean_nat_dec_le(v___x_2533_, v___x_2532_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
lean_dec_ref(v_s_2530_);
v___x_2535_ = lean_box(0);
return v___x_2535_;
}
else
{
lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = lean_unsigned_to_nat(0u);
v___x_2537_ = lean_string_memcmp(v_s_2530_, v___x_2531_, v___x_2536_, v___x_2536_, v___x_2533_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; 
lean_dec_ref(v_s_2530_);
v___x_2538_ = lean_box(0);
return v___x_2538_;
}
else
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_inc_ref(v_s_2530_);
v___x_2539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2539_, 0, v_s_2530_);
lean_ctor_set(v___x_2539_, 1, v___x_2536_);
lean_ctor_set(v___x_2539_, 2, v___x_2532_);
v___x_2540_ = l_String_Slice_pos_x21(v___x_2539_, v___x_2533_);
lean_dec_ref_known(v___x_2539_, 3);
v___x_2541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2541_, 0, v_s_2530_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
lean_ctor_set(v___x_2541_, 2, v___x_2532_);
v___x_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
return v___x_2542_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2543_, lean_object* v_pat_2544_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2543_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2546_, lean_object* v_pat_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2546_, v_pat_2547_);
lean_dec_ref(v_pat_2547_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v___x_2550_, lean_object* v___x_2551_, lean_object* v_mainModuleName_2552_, lean_object* v_a_2553_, lean_object* v___x_2554_, lean_object* v_fileName_2555_, lean_object* v___x_2556_, lean_object* v___x_2557_, lean_object* v___x_2558_, lean_object* v___x_2559_, lean_object* v___x_2560_, lean_object* v___x_2561_, lean_object* v___x_2562_, lean_object* v___x_2563_, uint8_t v_run_2564_){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v_env_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; lean_object* v_fileName_2575_; lean_object* v_fileMap_2576_; lean_object* v_currRecDepth_2577_; lean_object* v_ref_2578_; lean_object* v_currNamespace_2579_; lean_object* v_openDecls_2580_; lean_object* v_initHeartbeats_2581_; lean_object* v_maxHeartbeats_2582_; lean_object* v_quotContext_2583_; lean_object* v_currMacroScope_2584_; lean_object* v_cancelTk_x3f_2585_; uint8_t v_suppressElabErrors_2586_; lean_object* v_inheritedTraceOptions_2587_; lean_object* v___y_2588_; uint8_t v___y_2617_; uint8_t v___x_2637_; 
v___x_2566_ = lean_io_get_num_heartbeats();
v___x_2567_ = lean_st_mk_ref(v___x_2550_);
v___x_2568_ = l_Lean_inheritedTraceOptions;
v___x_2569_ = lean_st_ref_get(v___x_2568_);
v___x_2570_ = lean_st_ref_get(v___x_2567_);
v_env_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc_ref(v_env_2571_);
lean_dec(v___x_2570_);
v___x_2572_ = l_Lean_diagnostics;
v___x_2573_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v___x_2551_, v___x_2572_);
v___x_2637_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2571_);
lean_dec_ref(v_env_2571_);
if (v___x_2637_ == 0)
{
if (v___x_2573_ == 0)
{
lean_dec_ref(v___x_2554_);
lean_inc(v___x_2567_);
lean_inc(v___x_2559_);
v_fileName_2575_ = v_fileName_2555_;
v_fileMap_2576_ = v___x_2556_;
v_currRecDepth_2577_ = v___x_2557_;
v_ref_2578_ = v___x_2558_;
v_currNamespace_2579_ = v___x_2559_;
v_openDecls_2580_ = v___x_2560_;
v_initHeartbeats_2581_ = v___x_2566_;
v_maxHeartbeats_2582_ = v___x_2561_;
v_quotContext_2583_ = v___x_2559_;
v_currMacroScope_2584_ = v___x_2562_;
v_cancelTk_x3f_2585_ = v___x_2563_;
v_suppressElabErrors_2586_ = v_run_2564_;
v_inheritedTraceOptions_2587_ = v___x_2569_;
v___y_2588_ = v___x_2567_;
goto v___jp_2574_;
}
else
{
v___y_2617_ = v___x_2637_;
goto v___jp_2616_;
}
}
else
{
v___y_2617_ = v___x_2573_;
goto v___jp_2616_;
}
v___jp_2574_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2589_ = l_Lean_maxRecDepth;
v___x_2590_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_2551_, v___x_2589_);
v___x_2591_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2591_, 0, v_fileName_2575_);
lean_ctor_set(v___x_2591_, 1, v_fileMap_2576_);
lean_ctor_set(v___x_2591_, 2, v___x_2551_);
lean_ctor_set(v___x_2591_, 3, v_currRecDepth_2577_);
lean_ctor_set(v___x_2591_, 4, v___x_2590_);
lean_ctor_set(v___x_2591_, 5, v_ref_2578_);
lean_ctor_set(v___x_2591_, 6, v_currNamespace_2579_);
lean_ctor_set(v___x_2591_, 7, v_openDecls_2580_);
lean_ctor_set(v___x_2591_, 8, v_initHeartbeats_2581_);
lean_ctor_set(v___x_2591_, 9, v_maxHeartbeats_2582_);
lean_ctor_set(v___x_2591_, 10, v_quotContext_2583_);
lean_ctor_set(v___x_2591_, 11, v_currMacroScope_2584_);
lean_ctor_set(v___x_2591_, 12, v_cancelTk_x3f_2585_);
lean_ctor_set(v___x_2591_, 13, v_inheritedTraceOptions_2587_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*14, v___x_2573_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*14 + 1, v_suppressElabErrors_2586_);
v___x_2592_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2552_, v___x_2591_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref_known(v___x_2591_, 14);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2592_, 1);
v___x_2594_ = lean_st_ref_get(v___x_2567_);
lean_dec(v___x_2567_);
lean_dec(v___x_2594_);
v___x_2595_ = lean_string_to_utf8(v_a_2593_);
lean_dec(v_a_2593_);
v___x_2596_ = lean_io_prim_handle_write(v_a_2553_, v___x_2595_);
lean_dec_ref(v___x_2595_);
return v___x_2596_;
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v___x_2567_);
v_a_2597_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2599_ = v___x_2592_;
v_isShared_2600_ = v_isSharedCheck_2615_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2592_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2615_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
if (lean_obj_tag(v_a_2597_) == 0)
{
lean_object* v_msg_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2605_; 
v_msg_2601_ = lean_ctor_get(v_a_2597_, 1);
lean_inc_ref(v_msg_2601_);
lean_dec_ref_known(v_a_2597_, 2);
v___x_2602_ = l_Lean_MessageData_toString(v_msg_2601_);
v___x_2603_ = lean_mk_io_user_error(v___x_2602_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v___x_2603_);
v___x_2605_ = v___x_2599_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
else
{
lean_object* v_id_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2613_; 
v_id_2607_ = lean_ctor_get(v_a_2597_, 0);
lean_inc(v_id_2607_);
lean_dec_ref_known(v_a_2597_, 2);
v___x_2608_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0));
v___x_2609_ = l_Nat_reprFast(v_id_2607_);
v___x_2610_ = lean_string_append(v___x_2608_, v___x_2609_);
lean_dec_ref(v___x_2609_);
v___x_2611_ = lean_mk_io_user_error(v___x_2610_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v___x_2611_);
v___x_2613_ = v___x_2599_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_2616_:
{
if (v___y_2617_ == 0)
{
lean_object* v___x_2618_; lean_object* v_env_2619_; lean_object* v_nextMacroScope_2620_; lean_object* v_ngen_2621_; lean_object* v_auxDeclNGen_2622_; lean_object* v_traceState_2623_; lean_object* v_messages_2624_; lean_object* v_infoState_2625_; lean_object* v_snapshotTasks_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2635_; 
v___x_2618_ = lean_st_ref_take(v___x_2567_);
v_env_2619_ = lean_ctor_get(v___x_2618_, 0);
v_nextMacroScope_2620_ = lean_ctor_get(v___x_2618_, 1);
v_ngen_2621_ = lean_ctor_get(v___x_2618_, 2);
v_auxDeclNGen_2622_ = lean_ctor_get(v___x_2618_, 3);
v_traceState_2623_ = lean_ctor_get(v___x_2618_, 4);
v_messages_2624_ = lean_ctor_get(v___x_2618_, 6);
v_infoState_2625_ = lean_ctor_get(v___x_2618_, 7);
v_snapshotTasks_2626_ = lean_ctor_get(v___x_2618_, 8);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2635_ == 0)
{
lean_object* v_unused_2636_; 
v_unused_2636_ = lean_ctor_get(v___x_2618_, 5);
lean_dec(v_unused_2636_);
v___x_2628_ = v___x_2618_;
v_isShared_2629_ = v_isSharedCheck_2635_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_snapshotTasks_2626_);
lean_inc(v_infoState_2625_);
lean_inc(v_messages_2624_);
lean_inc(v_traceState_2623_);
lean_inc(v_auxDeclNGen_2622_);
lean_inc(v_ngen_2621_);
lean_inc(v_nextMacroScope_2620_);
lean_inc(v_env_2619_);
lean_dec(v___x_2618_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2635_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2630_; lean_object* v___x_2632_; 
v___x_2630_ = l_Lean_Kernel_enableDiag(v_env_2619_, v___x_2573_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 5, v___x_2554_);
lean_ctor_set(v___x_2628_, 0, v___x_2630_);
v___x_2632_ = v___x_2628_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_nextMacroScope_2620_);
lean_ctor_set(v_reuseFailAlloc_2634_, 2, v_ngen_2621_);
lean_ctor_set(v_reuseFailAlloc_2634_, 3, v_auxDeclNGen_2622_);
lean_ctor_set(v_reuseFailAlloc_2634_, 4, v_traceState_2623_);
lean_ctor_set(v_reuseFailAlloc_2634_, 5, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2634_, 6, v_messages_2624_);
lean_ctor_set(v_reuseFailAlloc_2634_, 7, v_infoState_2625_);
lean_ctor_set(v_reuseFailAlloc_2634_, 8, v_snapshotTasks_2626_);
v___x_2632_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_st_ref_set(v___x_2567_, v___x_2632_);
lean_inc(v___x_2567_);
lean_inc(v___x_2559_);
v_fileName_2575_ = v_fileName_2555_;
v_fileMap_2576_ = v___x_2556_;
v_currRecDepth_2577_ = v___x_2557_;
v_ref_2578_ = v___x_2558_;
v_currNamespace_2579_ = v___x_2559_;
v_openDecls_2580_ = v___x_2560_;
v_initHeartbeats_2581_ = v___x_2566_;
v_maxHeartbeats_2582_ = v___x_2561_;
v_quotContext_2583_ = v___x_2559_;
v_currMacroScope_2584_ = v___x_2562_;
v_cancelTk_x3f_2585_ = v___x_2563_;
v_suppressElabErrors_2586_ = v_run_2564_;
v_inheritedTraceOptions_2587_ = v___x_2569_;
v___y_2588_ = v___x_2567_;
goto v___jp_2574_;
}
}
}
else
{
lean_dec_ref(v___x_2554_);
lean_inc(v___x_2567_);
lean_inc(v___x_2559_);
v_fileName_2575_ = v_fileName_2555_;
v_fileMap_2576_ = v___x_2556_;
v_currRecDepth_2577_ = v___x_2557_;
v_ref_2578_ = v___x_2558_;
v_currNamespace_2579_ = v___x_2559_;
v_openDecls_2580_ = v___x_2560_;
v_initHeartbeats_2581_ = v___x_2566_;
v_maxHeartbeats_2582_ = v___x_2561_;
v_quotContext_2583_ = v___x_2559_;
v_currMacroScope_2584_ = v___x_2562_;
v_cancelTk_x3f_2585_ = v___x_2563_;
v_suppressElabErrors_2586_ = v_run_2564_;
v_inheritedTraceOptions_2587_ = v___x_2569_;
v___y_2588_ = v___x_2567_;
goto v___jp_2574_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* v___x_2638_, lean_object* v___x_2639_, lean_object* v_mainModuleName_2640_, lean_object* v_a_2641_, lean_object* v___x_2642_, lean_object* v_fileName_2643_, lean_object* v___x_2644_, lean_object* v___x_2645_, lean_object* v___x_2646_, lean_object* v___x_2647_, lean_object* v___x_2648_, lean_object* v___x_2649_, lean_object* v___x_2650_, lean_object* v___x_2651_, lean_object* v_run_2652_, lean_object* v___y_2653_){
_start:
{
uint8_t v_run_boxed_2654_; lean_object* v_res_2655_; 
v_run_boxed_2654_ = lean_unbox(v_run_2652_);
v_res_2655_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v___x_2638_, v___x_2639_, v_mainModuleName_2640_, v_a_2641_, v___x_2642_, v_fileName_2643_, v___x_2644_, v___x_2645_, v___x_2646_, v___x_2647_, v___x_2648_, v___x_2649_, v___x_2650_, v___x_2651_, v_run_boxed_2654_);
lean_dec(v_a_2641_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_2656_, lean_object* v_a_2657_, lean_object* v_b_2658_){
_start:
{
lean_object* v_str_2659_; lean_object* v_startInclusive_2660_; lean_object* v_endExclusive_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v_str_2659_ = lean_ctor_get(v_val_2656_, 0);
v_startInclusive_2660_ = lean_ctor_get(v_val_2656_, 1);
v_endExclusive_2661_ = lean_ctor_get(v_val_2656_, 2);
v___x_2662_ = lean_nat_sub(v_endExclusive_2661_, v_startInclusive_2660_);
v___x_2663_ = lean_nat_dec_eq(v_a_2657_, v___x_2662_);
lean_dec(v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; uint32_t v___x_2665_; uint32_t v___x_2666_; uint8_t v___x_2667_; 
v___x_2664_ = lean_nat_add(v_startInclusive_2660_, v_a_2657_);
v___x_2665_ = lean_string_utf8_get_fast(v_str_2659_, v___x_2664_);
v___x_2666_ = 10;
v___x_2667_ = lean_uint32_dec_eq(v___x_2665_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
lean_dec(v_a_2657_);
v___x_2668_ = lean_box(0);
v___x_2669_ = lean_string_utf8_next_fast(v_str_2659_, v___x_2664_);
lean_dec(v___x_2664_);
v___x_2670_ = lean_nat_sub(v___x_2669_, v_startInclusive_2660_);
v_a_2657_ = v___x_2670_;
v_b_2658_ = v___x_2668_;
goto _start;
}
else
{
lean_object* v___x_2672_; 
lean_dec(v___x_2664_);
v___x_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2672_, 0, v_a_2657_);
return v___x_2672_;
}
}
else
{
lean_dec(v_a_2657_);
lean_inc(v_b_2658_);
return v_b_2658_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_2673_, lean_object* v_a_2674_, lean_object* v_b_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_2673_, v_a_2674_, v_b_2675_);
lean_dec(v_b_2675_);
lean_dec_ref(v_val_2673_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_2677_){
_start:
{
uint32_t v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = 10;
v___x_2680_ = lean_string_push(v_s_2677_, v___x_2679_);
v___x_2681_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_2682_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_s_2685_){
_start:
{
uint32_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = 10;
v___x_2688_ = lean_string_push(v_s_2685_, v___x_2687_);
v___x_2689_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_s_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_s_2690_);
return v_res_2692_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0(void){
_start:
{
lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2693_ = lean_box(0);
v___x_2694_ = lean_internal_has_address_sanitizer(v___x_2693_);
return v___x_2694_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = l_Lean_Options_empty;
v___x_2700_ = l_Lean_Core_getMaxHeartbeats(v___x_2699_);
return v___x_2700_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__5(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = lean_unsigned_to_nat(1u);
v___x_2702_ = l_Lean_firstFrontendMacroScope;
v___x_2703_ = lean_nat_add(v___x_2702_, v___x_2701_);
return v___x_2703_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2714_ = lean_unsigned_to_nat(32u);
v___x_2715_ = lean_mk_empty_array_with_capacity(v___x_2714_);
v___x_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
return v___x_2716_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11(void){
_start:
{
size_t v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2717_ = ((size_t)5ULL);
v___x_2718_ = lean_unsigned_to_nat(0u);
v___x_2719_ = lean_unsigned_to_nat(32u);
v___x_2720_ = lean_mk_empty_array_with_capacity(v___x_2719_);
v___x_2721_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10);
v___x_2722_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v___x_2720_);
lean_ctor_set(v___x_2722_, 2, v___x_2718_);
lean_ctor_set(v___x_2722_, 3, v___x_2718_);
lean_ctor_set_usize(v___x_2722_, 4, v___x_2717_);
return v___x_2722_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12(void){
_start:
{
lean_object* v___x_2723_; uint64_t v___x_2724_; lean_object* v___x_2725_; 
v___x_2723_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__11, &l___private_Lean_Shell_0__Lean_shellMain___closed__11_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11);
v___x_2724_ = 0ULL;
v___x_2725_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set_uint64(v___x_2725_, sizeof(void*)*1, v___x_2724_);
return v___x_2725_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13(void){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2726_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__13, &l___private_Lean_Shell_0__Lean_shellMain___closed__13_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13);
v___x_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
return v___x_2728_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15(void){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2729_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__14, &l___private_Lean_Shell_0__Lean_shellMain___closed__14_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14);
v___x_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
return v___x_2730_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16(void){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2731_ = l_Lean_NameSet_empty;
v___x_2732_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__11, &l___private_Lean_Shell_0__Lean_shellMain___closed__11_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11);
v___x_2733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
lean_ctor_set(v___x_2733_, 2, v___x_2731_);
return v___x_2733_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17(void){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; uint8_t v___x_2736_; lean_object* v___x_2737_; 
v___x_2734_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__11, &l___private_Lean_Shell_0__Lean_shellMain___closed__11_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11);
v___x_2735_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__14, &l___private_Lean_Shell_0__Lean_shellMain___closed__14_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14);
v___x_2736_ = 1;
v___x_2737_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2737_, 0, v___x_2735_);
lean_ctor_set(v___x_2737_, 1, v___x_2735_);
lean_ctor_set(v___x_2737_, 2, v___x_2734_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*3, v___x_2736_);
return v___x_2737_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__21));
v___x_2744_ = lean_string_utf8_byte_size(v___x_2743_);
return v___x_2744_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__23(void){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2745_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__22, &l___private_Lean_Shell_0__Lean_shellMain___closed__22_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__22);
v___x_2746_ = lean_unsigned_to_nat(0u);
v___x_2747_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__21));
v___x_2748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
lean_ctor_set(v___x_2748_, 1, v___x_2746_);
lean_ctor_set(v___x_2748_, 2, v___x_2745_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* v_args_2752_, lean_object* v_opts_2753_){
_start:
{
lean_object* v___y_2762_; lean_object* v_fns_2777_; lean_object* v_leanOpts_2796_; lean_object* v_forwardedArgs_2797_; uint8_t v_component_2798_; uint8_t v_printPrefix_2799_; uint8_t v_printLibDir_2800_; uint8_t v_useStdin_2801_; uint8_t v_onlyDeps_2802_; uint8_t v_onlySrcDeps_2803_; uint8_t v_depsJson_2804_; uint32_t v_trustLevel_2805_; lean_object* v_rootDir_x3f_2806_; lean_object* v_setupFileName_x3f_2807_; lean_object* v_oleanFileName_x3f_2808_; lean_object* v_ileanFileName_x3f_2809_; lean_object* v_cFileName_x3f_2810_; lean_object* v_bcFileName_x3f_2811_; uint8_t v_jsonOutput_2812_; lean_object* v_errorOnKinds_2813_; uint8_t v_printStats_2814_; uint8_t v_run_2815_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; 
v_leanOpts_2796_ = lean_ctor_get(v_opts_2753_, 0);
lean_inc_ref(v_leanOpts_2796_);
v_forwardedArgs_2797_ = lean_ctor_get(v_opts_2753_, 1);
lean_inc_ref(v_forwardedArgs_2797_);
v_component_2798_ = lean_ctor_get_uint8(v_opts_2753_, sizeof(void*)*10 + 8);
v_printPrefix_2799_ = lean_ctor_get_uint8(v_opts_2753_, sizeof(void*)*10 + 9);
v_printLibDir_2800_ = lean_ctor_get_uint8(v_opts_2753_, sizeof(void*)*10 + 10);
v_useStdin_2801_ = lean_ctor_get_uint8(v_opts_2753_, sizeof(void*)*10 + 11);
v_onlyDeps_2802_ = lean_ctor_get_uint8(v_opts_2753_, sizeof(void*)*10 + 12);
v_onlySrcDeps_2803_ = lean_ctor_get_uint8(v_opts_2753_, sizeof(void*)*10 + 13);
v_depsJson_2804_ = lean_ctor_get_uint8(v_opts_2753_, sizeof(void*)*10 + 14);
v_trustLevel_2805_ = lean_ctor_get_uint32(v_opts_2753_, sizeof(void*)*10);
v_rootDir_x3f_2806_ = lean_ctor_get(v_opts_2753_, 3);
lean_inc(v_rootDir_x3f_2806_);
v_setupFileName_x3f_2807_ = lean_ctor_get(v_opts_2753_, 4);
lean_inc(v_setupFileName_x3f_2807_);
v_oleanFileName_x3f_2808_ = lean_ctor_get(v_opts_2753_, 5);
lean_inc(v_oleanFileName_x3f_2808_);
v_ileanFileName_x3f_2809_ = lean_ctor_get(v_opts_2753_, 6);
lean_inc(v_ileanFileName_x3f_2809_);
v_cFileName_x3f_2810_ = lean_ctor_get(v_opts_2753_, 7);
lean_inc(v_cFileName_x3f_2810_);
v_bcFileName_x3f_2811_ = lean_ctor_get(v_opts_2753_, 8);
lean_inc(v_bcFileName_x3f_2811_);
v_jsonOutput_2812_ = lean_ctor_get_uint8(v_opts_2753_, sizeof(void*)*10 + 15);
v_errorOnKinds_2813_ = lean_ctor_get(v_opts_2753_, 9);
lean_inc_ref(v_errorOnKinds_2813_);
v_printStats_2814_ = lean_ctor_get_uint8(v_opts_2753_, sizeof(void*)*10 + 16);
v_run_2815_ = lean_ctor_get_uint8(v_opts_2753_, sizeof(void*)*10 + 17);
lean_dec_ref(v_opts_2753_);
if (v_printPrefix_2799_ == 0)
{
if (v_printLibDir_2800_ == 0)
{
uint8_t v___x_2842_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v_mainModuleName_2849_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v_contents_2949_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v_str_2977_; lean_object* v_startInclusive_2978_; lean_object* v_endExclusive_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v_fileName_3081_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3119_; lean_object* v___y_3120_; uint8_t v___y_3151_; lean_object* v_fst_3152_; lean_object* v_snd_3153_; uint8_t v___y_3155_; lean_object* v___x_3185_; lean_object* v_maxMemory_3186_; lean_object* v___x_3187_; uint8_t v___x_3188_; 
v___x_2842_ = 1;
v___x_3185_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3186_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_leanOpts_2796_, v___x_3185_);
v___x_3187_ = lean_unsigned_to_nat(0u);
v___x_3188_ = lean_nat_dec_eq(v_maxMemory_3186_, v___x_3187_);
if (v___x_3188_ == 0)
{
size_t v___x_3189_; size_t v___x_3190_; size_t v___x_3191_; size_t v___x_3192_; lean_object* v___x_3193_; 
v___x_3189_ = lean_usize_of_nat(v_maxMemory_3186_);
lean_dec(v_maxMemory_3186_);
v___x_3190_ = ((size_t)1024ULL);
v___x_3191_ = lean_usize_mul(v___x_3189_, v___x_3190_);
v___x_3192_ = lean_usize_mul(v___x_3191_, v___x_3190_);
v___x_3193_ = lean_internal_set_max_memory(v___x_3192_);
goto v___jp_3176_;
}
else
{
lean_dec(v_maxMemory_3186_);
goto v___jp_3176_;
}
v___jp_2843_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = lean_unsigned_to_nat(0u);
v___x_2851_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__2));
lean_inc(v_mainModuleName_2849_);
lean_inc_ref(v_leanOpts_2796_);
v___x_2852_ = l_Lean_Elab_runFrontend(v___y_2846_, v_leanOpts_2796_, v___y_2845_, v_mainModuleName_2849_, v_trustLevel_2805_, v_oleanFileName_x3f_2808_, v_ileanFileName_x3f_2809_, v_jsonOutput_2812_, v_errorOnKinds_2813_, v___x_2851_, v_printStats_2814_, v___y_2847_);
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_ileanFileName_x3f_2809_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2919_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2919_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2919_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
if (lean_obj_tag(v_a_2853_) == 1)
{
if (v_run_2815_ == 0)
{
lean_del_object(v___x_2855_);
lean_dec(v___y_2848_);
if (lean_obj_tag(v_cFileName_x3f_2810_) == 1)
{
lean_object* v_val_2857_; lean_object* v_val_2858_; uint8_t v___x_2859_; lean_object* v___x_2860_; 
v_val_2857_ = lean_ctor_get(v_a_2853_, 0);
lean_inc(v_val_2857_);
v_val_2858_ = lean_ctor_get(v_cFileName_x3f_2810_, 0);
lean_inc(v_val_2858_);
lean_dec_ref_known(v_cFileName_x3f_2810_, 1);
v___x_2859_ = 1;
v___x_2860_ = lean_io_prim_handle_mk(v_val_2858_, v___x_2859_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___f_2880_; lean_object* v___x_2881_; 
lean_dec(v_val_2858_);
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
v___x_2862_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__3));
v___x_2863_ = l_Lean_instInhabitedFileMap_default;
v___x_2864_ = l_Lean_Options_empty;
v___x_2865_ = lean_box(0);
v___x_2866_ = lean_box(0);
v___x_2867_ = lean_box(0);
v___x_2868_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__4, &l___private_Lean_Shell_0__Lean_shellMain___closed__4_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4);
v___x_2869_ = l_Lean_firstFrontendMacroScope;
v___x_2870_ = lean_box(0);
v___x_2871_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__5, &l___private_Lean_Shell_0__Lean_shellMain___closed__5_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__5);
v___x_2872_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__8));
v___x_2873_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__9));
v___x_2874_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__12, &l___private_Lean_Shell_0__Lean_shellMain___closed__12_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12);
v___x_2875_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__15, &l___private_Lean_Shell_0__Lean_shellMain___closed__15_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__15);
v___x_2876_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__16, &l___private_Lean_Shell_0__Lean_shellMain___closed__16_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__16);
v___x_2877_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__17, &l___private_Lean_Shell_0__Lean_shellMain___closed__17_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__17);
lean_inc(v_val_2857_);
v___x_2878_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2878_, 0, v_val_2857_);
lean_ctor_set(v___x_2878_, 1, v___x_2871_);
lean_ctor_set(v___x_2878_, 2, v___x_2872_);
lean_ctor_set(v___x_2878_, 3, v___x_2873_);
lean_ctor_set(v___x_2878_, 4, v___x_2874_);
lean_ctor_set(v___x_2878_, 5, v___x_2875_);
lean_ctor_set(v___x_2878_, 6, v___x_2876_);
lean_ctor_set(v___x_2878_, 7, v___x_2877_);
lean_ctor_set(v___x_2878_, 8, v___x_2851_);
v___x_2879_ = lean_box(v_run_2815_);
lean_inc(v_mainModuleName_2849_);
v___f_2880_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 16, 15);
lean_closure_set(v___f_2880_, 0, v___x_2878_);
lean_closure_set(v___f_2880_, 1, v___x_2864_);
lean_closure_set(v___f_2880_, 2, v_mainModuleName_2849_);
lean_closure_set(v___f_2880_, 3, v_a_2861_);
lean_closure_set(v___f_2880_, 4, v___x_2875_);
lean_closure_set(v___f_2880_, 5, v___y_2844_);
lean_closure_set(v___f_2880_, 6, v___x_2863_);
lean_closure_set(v___f_2880_, 7, v___x_2850_);
lean_closure_set(v___f_2880_, 8, v___x_2865_);
lean_closure_set(v___f_2880_, 9, v___x_2866_);
lean_closure_set(v___f_2880_, 10, v___x_2867_);
lean_closure_set(v___f_2880_, 11, v___x_2868_);
lean_closure_set(v___f_2880_, 12, v___x_2869_);
lean_closure_set(v___f_2880_, 13, v___x_2870_);
lean_closure_set(v___f_2880_, 14, v___x_2879_);
v___x_2881_ = l_Lean_profileitIOUnsafe___redArg(v___x_2862_, v_leanOpts_2796_, v___f_2880_, v___x_2866_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_dec_ref_known(v___x_2881_, 1);
v___y_2817_ = v_a_2853_;
v___y_2818_ = v_mainModuleName_2849_;
v___y_2819_ = v_val_2857_;
goto v___jp_2816_;
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_val_2857_);
lean_dec_ref_known(v_a_2853_, 1);
lean_dec(v_mainModuleName_2849_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec_ref(v_leanOpts_2796_);
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2881_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec_ref_known(v___x_2860_, 1);
lean_dec(v_val_2857_);
lean_dec_ref_known(v_a_2853_, 1);
lean_dec(v_mainModuleName_2849_);
lean_dec_ref(v___y_2844_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec_ref(v_leanOpts_2796_);
v___x_2890_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__18));
v___x_2891_ = lean_string_append(v___x_2890_, v_val_2858_);
lean_dec(v_val_2858_);
v___x_2892_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_2893_ = lean_string_append(v___x_2891_, v___x_2892_);
v___x_2894_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_2893_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2902_; 
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2902_ == 0)
{
lean_object* v_unused_2903_; 
v_unused_2903_ = lean_ctor_get(v___x_2894_, 0);
lean_dec(v_unused_2903_);
v___x_2896_ = v___x_2894_;
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
else
{
lean_dec(v___x_2894_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2898_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2898_);
v___x_2900_ = v___x_2896_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
v_a_2904_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2894_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2894_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
}
else
{
lean_object* v_val_2912_; 
lean_dec_ref(v___y_2844_);
lean_dec(v_cFileName_x3f_2810_);
v_val_2912_ = lean_ctor_get(v_a_2853_, 0);
lean_inc(v_val_2912_);
v___y_2817_ = v_a_2853_;
v___y_2818_ = v_mainModuleName_2849_;
v___y_2819_ = v_val_2912_;
goto v___jp_2816_;
}
}
else
{
lean_object* v_val_2913_; uint32_t v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2917_; 
lean_dec(v_mainModuleName_2849_);
lean_dec_ref(v___y_2844_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
v_val_2913_ = lean_ctor_get(v_a_2853_, 0);
lean_inc(v_val_2913_);
lean_dec_ref_known(v_a_2853_, 1);
v___x_2914_ = lean_eval_main(v_val_2913_, v_leanOpts_2796_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v_leanOpts_2796_);
lean_dec(v_val_2913_);
v___x_2915_ = lean_box_uint32(v___x_2914_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2915_);
v___x_2917_ = v___x_2855_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
else
{
lean_del_object(v___x_2855_);
lean_dec(v_mainModuleName_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2844_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec_ref(v_leanOpts_2796_);
v___y_2762_ = v_a_2853_;
goto v___jp_2761_;
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_mainModuleName_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2844_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec_ref(v_leanOpts_2796_);
v_a_2920_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2852_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2852_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
v___jp_2928_:
{
if (lean_obj_tag(v___y_2934_) == 0)
{
lean_object* v_a_2935_; 
v_a_2935_ = lean_ctor_get(v___y_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___y_2934_, 1);
v___y_2844_ = v___y_2929_;
v___y_2845_ = v___y_2930_;
v___y_2846_ = v___y_2931_;
v___y_2847_ = v___y_2932_;
v___y_2848_ = v___y_2933_;
v_mainModuleName_2849_ = v_a_2935_;
goto v___jp_2843_;
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec(v_ileanFileName_x3f_2809_);
lean_dec(v_oleanFileName_x3f_2808_);
lean_dec_ref(v_leanOpts_2796_);
v_a_2936_ = lean_ctor_get(v___y_2934_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___y_2934_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___y_2934_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___y_2934_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
v___jp_2944_:
{
if (lean_obj_tag(v_setupFileName_x3f_2807_) == 0)
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_box(0);
if (lean_obj_tag(v___y_2947_) == 1)
{
lean_object* v_val_2951_; lean_object* v___x_2952_; 
v_val_2951_ = lean_ctor_get(v___y_2947_, 0);
lean_inc(v_val_2951_);
lean_dec_ref_known(v___y_2947_, 1);
v___x_2952_ = l_Lean_moduleNameOfFileName(v_val_2951_, v_rootDir_x3f_2806_);
if (lean_obj_tag(v___x_2952_) == 0)
{
v___y_2929_ = v___y_2945_;
v___y_2930_ = v___y_2946_;
v___y_2931_ = v_contents_2949_;
v___y_2932_ = v___x_2950_;
v___y_2933_ = v___y_2948_;
v___y_2934_ = v___x_2952_;
goto v___jp_2928_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_2808_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_2810_) == 0)
{
lean_object* v___x_2953_; 
lean_dec_ref_known(v___x_2952_, 1);
v___x_2953_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___y_2844_ = v___y_2945_;
v___y_2845_ = v___y_2946_;
v___y_2846_ = v_contents_2949_;
v___y_2847_ = v___x_2950_;
v___y_2848_ = v___y_2948_;
v_mainModuleName_2849_ = v___x_2953_;
goto v___jp_2843_;
}
else
{
v___y_2929_ = v___y_2945_;
v___y_2930_ = v___y_2946_;
v___y_2931_ = v_contents_2949_;
v___y_2932_ = v___x_2950_;
v___y_2933_ = v___y_2948_;
v___y_2934_ = v___x_2952_;
goto v___jp_2928_;
}
}
else
{
v___y_2929_ = v___y_2945_;
v___y_2930_ = v___y_2946_;
v___y_2931_ = v_contents_2949_;
v___y_2932_ = v___x_2950_;
v___y_2933_ = v___y_2948_;
v___y_2934_ = v___x_2952_;
goto v___jp_2928_;
}
}
}
else
{
lean_object* v___x_2954_; 
lean_dec(v___y_2947_);
lean_dec(v_rootDir_x3f_2806_);
v___x_2954_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__20));
v___y_2844_ = v___y_2945_;
v___y_2845_ = v___y_2946_;
v___y_2846_ = v_contents_2949_;
v___y_2847_ = v___x_2950_;
v___y_2848_ = v___y_2948_;
v_mainModuleName_2849_ = v___x_2954_;
goto v___jp_2843_;
}
}
else
{
lean_object* v_val_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2973_; 
lean_dec(v___y_2947_);
lean_dec(v_rootDir_x3f_2806_);
v_val_2955_ = lean_ctor_get(v_setupFileName_x3f_2807_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v_setupFileName_x3f_2807_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2957_ = v_setupFileName_x3f_2807_;
v_isShared_2958_ = v_isSharedCheck_2973_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_val_2955_);
lean_dec(v_setupFileName_x3f_2807_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2973_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_ModuleSetup_load(v_val_2955_);
lean_dec(v_val_2955_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v_name_2961_; lean_object* v___x_2963_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2959_, 1);
v_name_2961_ = lean_ctor_get(v_a_2960_, 0);
lean_inc(v_name_2961_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 0, v_a_2960_);
v___x_2963_ = v___x_2957_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2960_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
v___y_2844_ = v___y_2945_;
v___y_2845_ = v___y_2946_;
v___y_2846_ = v_contents_2949_;
v___y_2847_ = v___x_2963_;
v___y_2848_ = v___y_2948_;
v_mainModuleName_2849_ = v_name_2961_;
goto v___jp_2843_;
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_del_object(v___x_2957_);
lean_dec_ref(v_contents_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec(v_ileanFileName_x3f_2809_);
lean_dec(v_oleanFileName_x3f_2808_);
lean_dec_ref(v_leanOpts_2796_);
v_a_2965_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2959_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2959_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
}
}
v___jp_2974_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2983_ = lean_nat_add(v_startInclusive_2978_, v___y_2982_);
lean_dec(v___y_2982_);
lean_inc(v___x_2983_);
lean_inc_ref(v_str_2977_);
v___x_2984_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2984_, 0, v_str_2977_);
lean_ctor_set(v___x_2984_, 1, v_startInclusive_2978_);
lean_ctor_set(v___x_2984_, 2, v___x_2983_);
v___x_2985_ = l_String_Slice_trimAscii(v___x_2984_);
v___x_2986_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__23, &l___private_Lean_Shell_0__Lean_shellMain___closed__23_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__23);
v___x_2987_ = l_String_Slice_beq(v___x_2985_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
lean_dec(v___x_2983_);
lean_dec(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec(v_endExclusive_2979_);
lean_dec_ref(v_str_2977_);
lean_dec_ref(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec(v_ileanFileName_x3f_2809_);
lean_dec(v_oleanFileName_x3f_2808_);
lean_dec(v_setupFileName_x3f_2807_);
lean_dec(v_rootDir_x3f_2806_);
lean_dec_ref(v_leanOpts_2796_);
v___x_2988_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__24));
v___x_2989_ = l_String_Slice_toString(v___x_2985_);
lean_dec_ref(v___x_2985_);
v___x_2990_ = lean_string_append(v___x_2988_, v___x_2989_);
lean_dec_ref(v___x_2989_);
v___x_2991_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_2992_ = lean_string_append(v___x_2990_, v___x_2991_);
v___x_2993_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_2992_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3001_; 
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3001_ == 0)
{
lean_object* v_unused_3002_; 
v_unused_3002_ = lean_ctor_get(v___x_2993_, 0);
lean_dec(v_unused_3002_);
v___x_2995_ = v___x_2993_;
v_isShared_2996_ = v_isSharedCheck_3001_;
goto v_resetjp_2994_;
}
else
{
lean_dec(v___x_2993_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3001_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; lean_object* v___x_2999_; 
v___x_2997_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v___x_2997_);
v___x_2999_ = v___x_2995_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2997_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
v_a_3003_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2993_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2993_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
else
{
lean_object* v___x_3011_; 
lean_dec_ref(v___x_2985_);
v___x_3011_ = lean_string_utf8_extract(v_str_2977_, v___x_2983_, v_endExclusive_2979_);
lean_dec(v_endExclusive_2979_);
lean_dec(v___x_2983_);
lean_dec_ref(v_str_2977_);
v___y_2945_ = v___y_2975_;
v___y_2946_ = v___y_2976_;
v___y_2947_ = v___y_2980_;
v___y_2948_ = v___y_2981_;
v_contents_2949_ = v___x_3011_;
goto v___jp_2944_;
}
}
v___jp_3012_:
{
if (lean_obj_tag(v___y_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; 
v_a_3017_ = lean_ctor_get(v___y_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___y_3016_, 1);
v___x_3018_ = lean_decode_lossy_utf8(v_a_3017_);
lean_dec(v_a_3017_);
if (v_onlyDeps_2802_ == 0)
{
if (v_onlySrcDeps_2803_ == 0)
{
lean_object* v___x_3019_; 
lean_inc_ref(v___x_3018_);
v___x_3019_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_3018_);
if (lean_obj_tag(v___x_3019_) == 1)
{
lean_object* v_val_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_dec_ref(v___x_3018_);
v_val_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_val_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = lean_unsigned_to_nat(0u);
v___x_3022_ = lean_box(0);
v___x_3023_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3020_, v___x_3021_, v___x_3022_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_str_3024_; lean_object* v_startInclusive_3025_; lean_object* v_endExclusive_3026_; lean_object* v___x_3027_; 
v_str_3024_ = lean_ctor_get(v_val_3020_, 0);
lean_inc_ref(v_str_3024_);
v_startInclusive_3025_ = lean_ctor_get(v_val_3020_, 1);
lean_inc(v_startInclusive_3025_);
v_endExclusive_3026_ = lean_ctor_get(v_val_3020_, 2);
lean_inc(v_endExclusive_3026_);
lean_dec(v_val_3020_);
v___x_3027_ = lean_nat_sub(v_endExclusive_3026_, v_startInclusive_3025_);
lean_inc_ref(v___y_3013_);
v___y_2975_ = v___y_3013_;
v___y_2976_ = v___y_3013_;
v_str_2977_ = v_str_3024_;
v_startInclusive_2978_ = v_startInclusive_3025_;
v_endExclusive_2979_ = v_endExclusive_3026_;
v___y_2980_ = v___y_3015_;
v___y_2981_ = v___y_3014_;
v___y_2982_ = v___x_3027_;
goto v___jp_2974_;
}
else
{
lean_object* v_val_3028_; lean_object* v_str_3029_; lean_object* v_startInclusive_3030_; lean_object* v_endExclusive_3031_; 
v_val_3028_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_val_3028_);
lean_dec_ref_known(v___x_3023_, 1);
v_str_3029_ = lean_ctor_get(v_val_3020_, 0);
lean_inc_ref(v_str_3029_);
v_startInclusive_3030_ = lean_ctor_get(v_val_3020_, 1);
lean_inc(v_startInclusive_3030_);
v_endExclusive_3031_ = lean_ctor_get(v_val_3020_, 2);
lean_inc(v_endExclusive_3031_);
lean_dec(v_val_3020_);
lean_inc_ref(v___y_3013_);
v___y_2975_ = v___y_3013_;
v___y_2976_ = v___y_3013_;
v_str_2977_ = v_str_3029_;
v_startInclusive_2978_ = v_startInclusive_3030_;
v_endExclusive_2979_ = v_endExclusive_3031_;
v___y_2980_ = v___y_3015_;
v___y_2981_ = v___y_3014_;
v___y_2982_ = v_val_3028_;
goto v___jp_2974_;
}
}
else
{
lean_dec(v___x_3019_);
lean_inc_ref(v___y_3013_);
v___y_2945_ = v___y_3013_;
v___y_2946_ = v___y_3013_;
v___y_2947_ = v___y_3015_;
v___y_2948_ = v___y_3014_;
v_contents_2949_ = v___x_3018_;
goto v___jp_2944_;
}
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_dec(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec(v_ileanFileName_x3f_2809_);
lean_dec(v_oleanFileName_x3f_2808_);
lean_dec(v_setupFileName_x3f_2807_);
lean_dec(v_rootDir_x3f_2806_);
lean_dec_ref(v_leanOpts_2796_);
v___x_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3032_, 0, v___y_3013_);
v___x_3033_ = l_Lean_Elab_printImportSrcs(v___x_3018_, v___x_3032_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3041_; 
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v___x_3033_, 0);
lean_dec(v_unused_3042_);
v___x_3035_ = v___x_3033_;
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
else
{
lean_dec(v___x_3033_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3037_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 0, v___x_3037_);
v___x_3039_ = v___x_3035_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
v_a_3043_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3033_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3033_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
else
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
lean_dec(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec(v_ileanFileName_x3f_2809_);
lean_dec(v_oleanFileName_x3f_2808_);
lean_dec(v_setupFileName_x3f_2807_);
lean_dec(v_rootDir_x3f_2806_);
lean_dec_ref(v_leanOpts_2796_);
v___x_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3051_, 0, v___y_3013_);
v___x_3052_ = l_Lean_Elab_printImports(v___x_3018_, v___x_3051_);
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
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec(v_ileanFileName_x3f_2809_);
lean_dec(v_oleanFileName_x3f_2808_);
lean_dec(v_setupFileName_x3f_2807_);
lean_dec(v_rootDir_x3f_2806_);
lean_dec_ref(v_leanOpts_2796_);
v_a_3070_ = lean_ctor_get(v___y_3016_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___y_3016_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___y_3016_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___y_3016_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
v___jp_3078_:
{
if (v_useStdin_2801_ == 0)
{
lean_object* v___x_3082_; 
v___x_3082_ = l_IO_FS_readBinFile(v_fileName_3081_);
v___y_3013_ = v_fileName_3081_;
v___y_3014_ = v___y_3080_;
v___y_3015_ = v___y_3079_;
v___y_3016_ = v___x_3082_;
goto v___jp_3012_;
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = lean_get_stdin();
v___x_3084_ = l_IO_FS_Stream_readBinToEnd(v___x_3083_);
v___y_3013_ = v_fileName_3081_;
v___y_3014_ = v___y_3080_;
v___y_3015_ = v___y_3079_;
v___y_3016_ = v___x_3084_;
goto v___jp_3012_;
}
}
v___jp_3085_:
{
if (lean_obj_tag(v___y_3086_) == 1)
{
lean_object* v_val_3088_; 
v_val_3088_ = lean_ctor_get(v___y_3086_, 0);
lean_inc(v_val_3088_);
v___y_3079_ = v___y_3086_;
v___y_3080_ = v___y_3087_;
v_fileName_3081_ = v_val_3088_;
goto v___jp_3078_;
}
else
{
if (v_useStdin_2801_ == 0)
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
lean_dec(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec(v_ileanFileName_x3f_2809_);
lean_dec(v_oleanFileName_x3f_2808_);
lean_dec(v_setupFileName_x3f_2807_);
lean_dec(v_rootDir_x3f_2806_);
lean_dec_ref(v_leanOpts_2796_);
v___x_3089_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__25));
v___x_3090_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3089_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v___x_3091_; 
lean_dec_ref_known(v___x_3090_, 1);
v___x_3091_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_2842_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3099_; 
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v___x_3091_, 0);
lean_dec(v_unused_3100_);
v___x_3093_ = v___x_3091_;
v_isShared_3094_ = v_isSharedCheck_3099_;
goto v_resetjp_3092_;
}
else
{
lean_dec(v___x_3091_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3099_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3095_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3095_);
v___x_3097_ = v___x_3093_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_a_3101_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3091_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3091_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
v_a_3109_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3090_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3090_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
else
{
lean_object* v___x_3117_; 
v___x_3117_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__26));
v___y_3079_ = v___y_3086_;
v___y_3080_ = v___y_3087_;
v_fileName_3081_ = v___x_3117_;
goto v___jp_3078_;
}
}
}
v___jp_3118_:
{
uint8_t v___x_3121_; 
v___x_3121_ = l_List_isEmpty___redArg(v___y_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
lean_dec(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec(v_ileanFileName_x3f_2809_);
lean_dec(v_oleanFileName_x3f_2808_);
lean_dec(v_setupFileName_x3f_2807_);
lean_dec(v_rootDir_x3f_2806_);
lean_dec_ref(v_leanOpts_2796_);
v___x_3122_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__25));
v___x_3123_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3122_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v___x_3124_; 
lean_dec_ref_known(v___x_3123_, 1);
v___x_3124_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_2842_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3132_; 
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; 
v_unused_3133_ = lean_ctor_get(v___x_3124_, 0);
lean_dec(v_unused_3133_);
v___x_3126_ = v___x_3124_;
v_isShared_3127_ = v_isSharedCheck_3132_;
goto v_resetjp_3125_;
}
else
{
lean_dec(v___x_3124_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3132_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; lean_object* v___x_3130_; 
v___x_3128_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v___x_3128_);
v___x_3130_ = v___x_3126_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
v_a_3134_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3124_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3124_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
v_a_3142_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3123_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3123_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
v___y_3086_ = v___y_3119_;
v___y_3087_ = v___y_3120_;
goto v___jp_3085_;
}
}
v___jp_3150_:
{
if (v_run_2815_ == 0)
{
v___y_3119_ = v_fst_3152_;
v___y_3120_ = v_snd_3153_;
goto v___jp_3118_;
}
else
{
if (v___y_3151_ == 0)
{
v___y_3086_ = v_fst_3152_;
v___y_3087_ = v_snd_3153_;
goto v___jp_3085_;
}
else
{
v___y_3119_ = v_fst_3152_;
v___y_3120_ = v_snd_3153_;
goto v___jp_3118_;
}
}
}
v___jp_3154_:
{
if (lean_obj_tag(v_args_2752_) == 0)
{
lean_object* v___x_3156_; 
v___x_3156_ = lean_box(0);
v___y_3151_ = v___y_3155_;
v_fst_3152_ = v___x_3156_;
v_snd_3153_ = v_args_2752_;
goto v___jp_3150_;
}
else
{
lean_object* v_head_3157_; lean_object* v_tail_3158_; lean_object* v___x_3159_; 
v_head_3157_ = lean_ctor_get(v_args_2752_, 0);
lean_inc(v_head_3157_);
v_tail_3158_ = lean_ctor_get(v_args_2752_, 1);
lean_inc(v_tail_3158_);
lean_dec_ref_known(v_args_2752_, 2);
v___x_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3159_, 0, v_head_3157_);
v___y_3151_ = v___y_3155_;
v_fst_3152_ = v___x_3159_;
v_snd_3153_ = v_tail_3158_;
goto v___jp_3150_;
}
}
v___jp_3160_:
{
switch(v_component_2798_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_2797_);
if (v_onlyDeps_2802_ == 0)
{
v___y_3155_ = v_onlyDeps_2802_;
goto v___jp_3154_;
}
else
{
if (v_depsJson_2804_ == 0)
{
v___y_3155_ = v_depsJson_2804_;
goto v___jp_3154_;
}
else
{
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec(v_ileanFileName_x3f_2809_);
lean_dec(v_oleanFileName_x3f_2808_);
lean_dec(v_setupFileName_x3f_2807_);
lean_dec(v_rootDir_x3f_2806_);
lean_dec_ref(v_leanOpts_2796_);
if (v_useStdin_2801_ == 0)
{
lean_object* v___x_3161_; 
v___x_3161_ = lean_array_mk(v_args_2752_);
v_fns_2777_ = v___x_3161_;
goto v___jp_2776_;
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
lean_dec(v_args_2752_);
v___x_3162_ = lean_get_stdin();
v___x_3163_ = l_IO_FS_Stream_lines(v___x_3162_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v_fns_2777_ = v_a_3164_;
goto v___jp_2776_;
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
v_a_3165_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3163_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3163_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec(v_ileanFileName_x3f_2809_);
lean_dec(v_oleanFileName_x3f_2808_);
lean_dec(v_setupFileName_x3f_2807_);
lean_dec(v_rootDir_x3f_2806_);
lean_dec_ref(v_leanOpts_2796_);
lean_dec(v_args_2752_);
v___x_3173_ = lean_array_to_list(v_forwardedArgs_2797_);
v___x_3174_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3173_);
return v___x_3174_;
}
default: 
{
lean_object* v___x_3175_; 
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec(v_ileanFileName_x3f_2809_);
lean_dec(v_oleanFileName_x3f_2808_);
lean_dec(v_setupFileName_x3f_2807_);
lean_dec(v_rootDir_x3f_2806_);
lean_dec_ref(v_forwardedArgs_2797_);
lean_dec(v_args_2752_);
v___x_3175_ = l_Lean_Server_FileWorker_workerMain(v_leanOpts_2796_);
return v___x_3175_;
}
}
}
v___jp_3176_:
{
lean_object* v___x_3177_; lean_object* v_timeout_3178_; lean_object* v___x_3179_; uint8_t v___x_3180_; 
v___x_3177_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3178_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_leanOpts_2796_, v___x_3177_);
v___x_3179_ = lean_unsigned_to_nat(0u);
v___x_3180_ = lean_nat_dec_eq(v_timeout_3178_, v___x_3179_);
if (v___x_3180_ == 0)
{
size_t v___x_3181_; size_t v___x_3182_; size_t v___x_3183_; lean_object* v___x_3184_; 
v___x_3181_ = lean_usize_of_nat(v_timeout_3178_);
lean_dec(v_timeout_3178_);
v___x_3182_ = ((size_t)1000ULL);
v___x_3183_ = lean_usize_mul(v___x_3181_, v___x_3182_);
v___x_3184_ = lean_internal_set_max_heartbeat(v___x_3183_);
goto v___jp_3160_;
}
else
{
lean_dec(v_timeout_3178_);
goto v___jp_3160_;
}
}
}
else
{
lean_object* v___x_3194_; 
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec(v_ileanFileName_x3f_2809_);
lean_dec(v_oleanFileName_x3f_2808_);
lean_dec(v_setupFileName_x3f_2807_);
lean_dec(v_rootDir_x3f_2806_);
lean_dec_ref(v_forwardedArgs_2797_);
lean_dec_ref(v_leanOpts_2796_);
lean_dec(v_args_2752_);
v___x_3194_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3196_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref_known(v___x_3194_, 1);
v___x_3196_ = l_Lean_getLibDir(v_a_3195_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3198_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v___x_3198_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3197_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3206_; 
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v___x_3198_, 0);
lean_dec(v_unused_3207_);
v___x_3200_ = v___x_3198_;
v_isShared_3201_ = v_isSharedCheck_3206_;
goto v_resetjp_3199_;
}
else
{
lean_dec(v___x_3198_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3206_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3202_; lean_object* v___x_3204_; 
v___x_3202_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 0, v___x_3202_);
v___x_3204_ = v___x_3200_;
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
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
v_a_3208_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3198_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3198_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
v_a_3216_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3196_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3196_);
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
v_a_3224_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3194_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3194_);
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
}
else
{
lean_object* v___x_3232_; 
lean_dec_ref(v_errorOnKinds_2813_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec(v_cFileName_x3f_2810_);
lean_dec(v_ileanFileName_x3f_2809_);
lean_dec(v_oleanFileName_x3f_2808_);
lean_dec(v_setupFileName_x3f_2807_);
lean_dec(v_rootDir_x3f_2806_);
lean_dec_ref(v_forwardedArgs_2797_);
lean_dec_ref(v_leanOpts_2796_);
lean_dec(v_args_2752_);
v___x_3232_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3234_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3234_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3233_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3242_; 
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3242_ == 0)
{
lean_object* v_unused_3243_; 
v_unused_3243_ = lean_ctor_get(v___x_3234_, 0);
lean_dec(v_unused_3243_);
v___x_3236_ = v___x_3234_;
v_isShared_3237_ = v_isSharedCheck_3242_;
goto v_resetjp_3235_;
}
else
{
lean_dec(v___x_3234_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3242_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3238_; lean_object* v___x_3240_; 
v___x_3238_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v___x_3238_);
v___x_3240_ = v___x_3236_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
v_a_3244_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3234_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3234_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
v_a_3252_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3232_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3232_);
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
v___jp_2755_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
return v___x_2757_;
}
v___jp_2758_:
{
uint8_t v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = 0;
v___x_2760_ = lean_io_exit(v___x_2759_);
return v___x_2760_;
}
v___jp_2761_:
{
lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2763_ = lean_display_cumulative_profiling_times();
v___x_2764_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__0, &l___private_Lean_Shell_0__Lean_shellMain___closed__0_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0);
if (v___x_2764_ == 0)
{
if (lean_obj_tag(v___y_2762_) == 0)
{
if (v___x_2764_ == 0)
{
uint8_t v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = 1;
v___x_2766_ = lean_io_exit(v___x_2765_);
return v___x_2766_;
}
else
{
goto v___jp_2758_;
}
}
else
{
lean_dec_ref_known(v___y_2762_, 1);
goto v___jp_2758_;
}
}
else
{
if (lean_obj_tag(v___y_2762_) == 0)
{
goto v___jp_2755_;
}
else
{
lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2774_; 
v_isSharedCheck_2774_ = !lean_is_exclusive(v___y_2762_);
if (v_isSharedCheck_2774_ == 0)
{
lean_object* v_unused_2775_; 
v_unused_2775_ = lean_ctor_get(v___y_2762_, 0);
lean_dec(v_unused_2775_);
v___x_2768_ = v___y_2762_;
v_isShared_2769_ = v_isSharedCheck_2774_;
goto v_resetjp_2767_;
}
else
{
lean_dec(v___y_2762_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2774_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
if (v___x_2764_ == 0)
{
lean_del_object(v___x_2768_);
goto v___jp_2755_;
}
else
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2770_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2769_ == 0)
{
lean_ctor_set_tag(v___x_2768_, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2770_);
v___x_2772_ = v___x_2768_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
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
}
}
v___jp_2776_:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_printImportsJson(v_fns_2777_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2786_; 
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2786_ == 0)
{
lean_object* v_unused_2787_; 
v_unused_2787_ = lean_ctor_get(v___x_2778_, 0);
lean_dec(v_unused_2787_);
v___x_2780_ = v___x_2778_;
v_isShared_2781_ = v_isSharedCheck_2786_;
goto v_resetjp_2779_;
}
else
{
lean_dec(v___x_2778_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2786_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2782_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2782_);
v___x_2784_ = v___x_2780_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2782_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
v_a_2788_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2778_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2778_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
v___jp_2816_:
{
if (lean_obj_tag(v_bcFileName_x3f_2811_) == 1)
{
lean_object* v_val_2820_; lean_object* v___x_2821_; 
v_val_2820_ = lean_ctor_get(v_bcFileName_x3f_2811_, 0);
lean_inc(v_val_2820_);
lean_dec_ref_known(v_bcFileName_x3f_2811_, 1);
v___x_2821_ = lean_init_llvm();
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec_ref_known(v___x_2821_, 1);
v___x_2822_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__1));
v___x_2823_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(v___x_2823_, 0, v___y_2819_);
lean_closure_set(v___x_2823_, 1, v___y_2818_);
lean_closure_set(v___x_2823_, 2, v_val_2820_);
v___x_2824_ = lean_box(0);
v___x_2825_ = l_Lean_profileitIOUnsafe___redArg(v___x_2822_, v_leanOpts_2796_, v___x_2823_, v___x_2824_);
lean_dec_ref(v_leanOpts_2796_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_dec_ref_known(v___x_2825_, 1);
v___y_2762_ = v___y_2817_;
goto v___jp_2761_;
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v___y_2817_);
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_val_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v_leanOpts_2796_);
v_a_2834_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2821_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2821_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec(v_bcFileName_x3f_2811_);
lean_dec_ref(v_leanOpts_2796_);
v___y_2762_ = v___y_2817_;
goto v___jp_2761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3260_, lean_object* v_opts_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = lean_shell_main(v_args_3260_, v_opts_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3264_, lean_object* v_inst_3265_, lean_object* v_R_3266_, lean_object* v_a_3267_, lean_object* v_b_3268_, lean_object* v_c_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3264_, v_a_3267_, v_b_3268_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3271_, lean_object* v_inst_3272_, lean_object* v_R_3273_, lean_object* v_a_3274_, lean_object* v_b_3275_, lean_object* v_c_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3271_, v_inst_3272_, v_R_3273_, v_a_3274_, v_b_3275_, v_c_3276_);
lean_dec(v_b_3275_);
lean_dec_ref(v_val_3271_);
return v_res_3277_;
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
