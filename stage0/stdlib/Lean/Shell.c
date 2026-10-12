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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Compiler_LCNF_emitC(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
uint32_t lean_internal_get_hardware_concurrency(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_toName(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___impl___boxed(lean_object*);
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
static const lean_array_object l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0;
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Can't compile LLVM"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__2 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__2_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__2_value)}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__3 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__3_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__4;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Expected exactly one file name"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__5_value;
static const lean_array_object l___private_Lean_Shell_0__Lean_shellMain___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__6 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__6_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_stdin"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__7 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__7_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__7_value),LEAN_SCALAR_PTR_LITERAL(37, 142, 62, 167, 41, 238, 22, 79)}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__8 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__8_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lean4"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__9 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__9_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__10 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__10_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown language '"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__11 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__11_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<stdin>"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__12 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__12_value;
LEAN_EXPORT lean_object* lean_shell_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_decodeLossyUTF8_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_res_2_;
v_res_2_ = lean_decode_lossy_utf8(v_a_1_);
stack->m_obj
 = v_res_2_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_decodeLossyUTF8___boxed(lean_object* v_a_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lean_decode_lossy_utf8(v_a_3_);
lean_dec_ref(v_a_3_);
return v_res_4_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_runMain_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_5_ = stack[0].m_obj;
lean_object* v_opts_6_ = stack[1].m_obj;
lean_object* v_args_7_ = stack[2].m_obj;
uint32_t v_res_9_;
v_res_9_ = lean_eval_main(v_env_5_, v_opts_6_, v_args_7_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object* v_env_10_, lean_object* v_opts_11_, lean_object* v_args_12_, lean_object* v_a_00___x40___internal___hyg_13_){
_start:
{
uint32_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = lean_eval_main(v_env_10_, v_opts_11_, v_args_12_);
v_r_15_ = lean_box_uint32(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_00___x40_Lean_Shell_2339721992____hygCtx___hyg_16_ = stack[0].m_obj;
uint8_t v_res_17_;
v_res_17_ = lean_internal_has_address_sanitizer(v_x_00___x40_Lean_Shell_2339721992____hygCtx___hyg_16_);
stack->m_num = v_res_17_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(lean_object* v_x_00___x40_Lean_Shell_2339721992____hygCtx___hyg_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = lean_internal_has_address_sanitizer(v_x_00___x40_Lean_Shell_2339721992____hygCtx___hyg_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_isMultiThread_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_00___x40_Lean_Shell_3295292909____hygCtx___hyg_21_ = stack[0].m_obj;
uint8_t v_res_22_;
v_res_22_ = lean_internal_is_multi_thread(v_x_00___x40_Lean_Shell_3295292909____hygCtx___hyg_21_);
stack->m_num = v_res_22_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isMultiThread___boxed(lean_object* v_x_00___x40_Lean_Shell_3295292909____hygCtx___hyg_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = lean_internal_is_multi_thread(v_x_00___x40_Lean_Shell_3295292909____hygCtx___hyg_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_isDebug_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_00___x40_Lean_Shell_97005966____hygCtx___hyg_26_ = stack[0].m_obj;
uint8_t v_res_27_;
v_res_27_ = lean_internal_is_debug(v_x_00___x40_Lean_Shell_97005966____hygCtx___hyg_26_);
stack->m_num = v_res_27_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isDebug___boxed(lean_object* v_x_00___x40_Lean_Shell_97005966____hygCtx___hyg_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = lean_internal_is_debug(v_x_00___x40_Lean_Shell_97005966____hygCtx___hyg_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_getBuildType_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_00___x40_Lean_Shell_1721435280____hygCtx___hyg_31_ = stack[0].m_obj;
lean_object* v_res_32_;
v_res_32_ = lean_internal_get_build_type(v_x_00___x40_Lean_Shell_1721435280____hygCtx___hyg_31_);
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBuildType___boxed(lean_object* v_x_00___x40_Lean_Shell_1721435280____hygCtx___hyg_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lean_internal_get_build_type(v_x_00___x40_Lean_Shell_1721435280____hygCtx___hyg_33_);
return v_res_34_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxMemory_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_00___x40_Lean_Shell_1091001955____hygCtx___hyg_35_ = stack[0].m_obj;
lean_object* v_res_36_;
v_res_36_ = lean_internal_get_default_max_memory(v_x_00___x40_Lean_Shell_1091001955____hygCtx___hyg_35_);
stack->m_obj
 = v_res_36_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxMemory___boxed(lean_object* v_x_00___x40_Lean_Shell_1091001955____hygCtx___hyg_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lean_internal_get_default_max_memory(v_x_00___x40_Lean_Shell_1091001955____hygCtx___hyg_37_);
return v_res_38_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_setMaxMemory_0interp(lean_interpreter_value* stack)
{
size_t v_max_39_ = stack[0].m_num;
lean_object* v_res_41_;
v_res_41_ = lean_internal_set_max_memory(v_max_39_);
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxMemory___boxed(lean_object* v_max_42_, lean_object* v_a_00___x40___internal___hyg_43_){
_start:
{
size_t v_max_boxed_44_; lean_object* v_res_45_; 
v_max_boxed_44_ = lean_unbox_usize(v_max_42_);
lean_dec(v_max_42_);
v_res_45_ = lean_internal_set_max_memory(v_max_boxed_44_);
return v_res_45_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxHeartbeat_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_00___x40_Lean_Shell_2736094960____hygCtx___hyg_46_ = stack[0].m_obj;
lean_object* v_res_47_;
v_res_47_ = lean_internal_get_default_max_heartbeat(v_x_00___x40_Lean_Shell_2736094960____hygCtx___hyg_46_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxHeartbeat___boxed(lean_object* v_x_00___x40_Lean_Shell_2736094960____hygCtx___hyg_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lean_internal_get_default_max_heartbeat(v_x_00___x40_Lean_Shell_2736094960____hygCtx___hyg_48_);
return v_res_49_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_setMaxHeartbeat_0interp(lean_interpreter_value* stack)
{
size_t v_max_50_ = stack[0].m_num;
lean_object* v_res_52_;
v_res_52_ = lean_internal_set_max_heartbeat(v_max_50_);
stack->m_obj
 = v_res_52_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxHeartbeat___boxed(lean_object* v_max_53_, lean_object* v_a_00___x40___internal___hyg_54_){
_start:
{
size_t v_max_boxed_55_; lean_object* v_res_56_; 
v_max_boxed_55_ = lean_unbox_usize(v_max_53_);
lean_dec(v_max_53_);
v_res_56_ = lean_internal_set_max_heartbeat(v_max_boxed_55_);
return v_res_56_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_getDefaultVerbose_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_00___x40_Lean_Shell_28281146____hygCtx___hyg_57_ = stack[0].m_obj;
uint8_t v_res_58_;
v_res_58_ = lean_internal_get_default_verbose(v_x_00___x40_Lean_Shell_28281146____hygCtx___hyg_57_);
stack->m_num = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultVerbose___boxed(lean_object* v_x_00___x40_Lean_Shell_28281146____hygCtx___hyg_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = lean_internal_get_default_verbose(v_x_00___x40_Lean_Shell_28281146____hygCtx___hyg_59_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_setExitOnPanic_0interp(lean_interpreter_value* stack)
{
uint8_t v_exit_62_ = stack[0].m_num;
lean_object* v_res_64_;
v_res_64_ = lean_internal_set_exit_on_panic(v_exit_62_);
stack->m_obj
 = v_res_64_;
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
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_setThreadStackSize_0interp(lean_interpreter_value* stack)
{
size_t v_sz_69_ = stack[0].m_num;
lean_object* v_res_71_;
v_res_71_ = lean_internal_set_thread_stack_size(v_sz_69_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setThreadStackSize___boxed(lean_object* v_sz_72_, lean_object* v_a_00___x40___internal___hyg_73_){
_start:
{
size_t v_sz_boxed_74_; lean_object* v_res_75_; 
v_sz_boxed_74_ = lean_unbox_usize(v_sz_72_);
lean_dec(v_sz_72_);
v_res_75_ = lean_internal_set_thread_stack_size(v_sz_boxed_74_);
return v_res_75_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_enableDebug_0interp(lean_interpreter_value* stack)
{
lean_object* v_tag_76_ = stack[0].m_obj;
lean_object* v_res_78_;
v_res_78_ = lean_internal_enable_debug(v_tag_76_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_enableDebug___boxed(lean_object* v_tag_79_, lean_object* v_a_00___x40___internal___hyg_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lean_internal_enable_debug(v_tag_79_);
lean_dec_ref(v_tag_79_);
return v_res_81_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_83_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_84_ = l_Lean_version_specialDesc;
v___x_85_ = lean_string_dec_eq(v___x_84_, v___x_83_);
return v___x_85_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__2));
v___x_88_ = l_Lean_versionStringCore;
v___x_89_ = lean_string_append(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = l_Lean_version_specialDesc;
v___x_91_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__3, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__3_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3);
v___x_92_ = lean_string_append(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__5));
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
v___x_99_ = l_Lean_version_isRelease;
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__6, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__6_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6);
return v___x_100_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_versionStringCore;
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
lean_object* l___private_Lean_Shell_0__Lean_displayHelp(uint8_t v_useStderr_194_){
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
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_displayHelp_0interp(lean_interpreter_value* stack)
{
uint8_t v_useStderr_194_ = stack[0].m_num;
lean_object* v_res_294_;
v_res_294_ = l___private_Lean_Shell_0__Lean_displayHelp(v_useStderr_194_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object* v_useStderr_295_, lean_object* v_a_296_){
_start:
{
uint8_t v_useStderr_boxed_297_; lean_object* v_res_298_; 
v_useStderr_boxed_297_ = lean_unbox(v_useStderr_295_);
v_res_298_ = l___private_Lean_Shell_0__Lean_displayHelp(v_useStderr_boxed_297_);
return v_res_298_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___impl(uint8_t v_x_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_box(v_x_299_);
v___x_301_ = lean_obj_tag_nat(v___x_300_);
lean_dec(v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_299_ = stack[0].m_num;
lean_object* v_res_302_;
v_res_302_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___impl(v_x_299_);
stack->m_obj
 = v_res_302_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___impl___boxed(lean_object* v_x_303_){
_start:
{
uint8_t v_x_4__boxed_304_; lean_object* v_res_305_; 
v_x_4__boxed_304_ = lean_unbox(v_x_303_);
v_res_305_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___impl(v_x_4__boxed_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(lean_object* v_k_306_){
_start:
{
lean_inc(v_k_306_);
return v_k_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg___boxed(lean_object* v_k_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(v_k_307_);
lean_dec(v_k_307_);
return v_res_308_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(lean_object* v_motive_309_, lean_object* v_ctorIdx_310_, uint8_t v_t_311_, lean_object* v_h_312_, lean_object* v_k_313_){
_start:
{
lean_inc(v_k_313_);
return v_k_313_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_310_ = stack[1].m_obj;
uint8_t v_t_311_ = stack[2].m_num;
lean_object* v_k_313_ = stack[4].m_obj;
lean_object* v_res_314_;
v_res_314_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(lean_box(0), v_ctorIdx_310_, v_t_311_, lean_box(0), v_k_313_);
stack->m_obj
 = v_res_314_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___boxed(lean_object* v_motive_315_, lean_object* v_ctorIdx_316_, lean_object* v_t_317_, lean_object* v_h_318_, lean_object* v_k_319_){
_start:
{
uint8_t v_t_boxed_320_; lean_object* v_res_321_; 
v_t_boxed_320_ = lean_unbox(v_t_317_);
v_res_321_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(v_motive_315_, v_ctorIdx_316_, v_t_boxed_320_, v_h_318_, v_k_319_);
lean_dec(v_k_319_);
lean_dec(v_ctorIdx_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(lean_object* v_frontend_322_){
_start:
{
lean_inc(v_frontend_322_);
return v_frontend_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg___boxed(lean_object* v_frontend_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(v_frontend_323_);
lean_dec(v_frontend_323_);
return v_res_324_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(lean_object* v_motive_325_, uint8_t v_t_326_, lean_object* v_h_327_, lean_object* v_frontend_328_){
_start:
{
lean_inc(v_frontend_328_);
return v_frontend_328_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_326_ = stack[1].m_num;
lean_object* v_frontend_328_ = stack[3].m_obj;
lean_object* v_res_329_;
v_res_329_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(lean_box(0), v_t_326_, lean_box(0), v_frontend_328_);
stack->m_obj
 = v_res_329_;
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
lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(lean_object* v_motive_339_, uint8_t v_t_340_, lean_object* v_h_341_, lean_object* v_watchdog_342_){
_start:
{
lean_inc(v_watchdog_342_);
return v_watchdog_342_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_340_ = stack[1].m_num;
lean_object* v_watchdog_342_ = stack[3].m_obj;
lean_object* v_res_343_;
v_res_343_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(lean_box(0), v_t_340_, lean_box(0), v_watchdog_342_);
stack->m_obj
 = v_res_343_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___boxed(lean_object* v_motive_344_, lean_object* v_t_345_, lean_object* v_h_346_, lean_object* v_watchdog_347_){
_start:
{
uint8_t v_t_boxed_348_; lean_object* v_res_349_; 
v_t_boxed_348_ = lean_unbox(v_t_345_);
v_res_349_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(v_motive_344_, v_t_boxed_348_, v_h_346_, v_watchdog_347_);
lean_dec(v_watchdog_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(lean_object* v_worker_350_){
_start:
{
lean_inc(v_worker_350_);
return v_worker_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg___boxed(lean_object* v_worker_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(v_worker_351_);
lean_dec(v_worker_351_);
return v_res_352_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(lean_object* v_motive_353_, uint8_t v_t_354_, lean_object* v_h_355_, lean_object* v_worker_356_){
_start:
{
lean_inc(v_worker_356_);
return v_worker_356_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_354_ = stack[1].m_num;
lean_object* v_worker_356_ = stack[3].m_obj;
lean_object* v_res_357_;
v_res_357_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(lean_box(0), v_t_354_, lean_box(0), v_worker_356_);
stack->m_obj
 = v_res_357_;
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object* v_name_364_, lean_object* v_decl_365_, lean_object* v_ref_366_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_364_ = stack[0].m_obj;
lean_object* v_decl_365_ = stack[1].m_obj;
lean_object* v_ref_366_ = stack[2].m_obj;
lean_object* v_res_391_;
v_res_391_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v_name_364_, v_decl_365_, v_ref_366_);
stack->m_obj
 = v_res_391_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_392_, lean_object* v_decl_393_, lean_object* v_ref_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v_name_392_, v_decl_393_, v_ref_394_);
lean_dec_ref(v_decl_393_);
return v_res_396_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_box(0);
v___x_401_ = lean_internal_get_default_max_memory(v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_402_ = lean_box(0);
v___x_403_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_404_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
lean_ctor_set(v___x_405_, 2, v___x_402_);
return v___x_405_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_429_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_430_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_431_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_432_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_429_, v___x_430_, v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_433_;
v_res_433_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
stack->m_obj
 = v_res_433_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2____boxed(lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
return v_res_435_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_box(0);
v___x_440_ = lean_internal_get_default_max_heartbeat(v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = lean_box(0);
v___x_442_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_443_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_441_);
return v___x_444_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_449_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_450_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_451_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_452_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_449_, v___x_450_, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_453_;
v_res_453_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2____boxed(lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
return v_res_455_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(lean_object* v_name_456_, lean_object* v_decl_457_, lean_object* v_ref_458_){
_start:
{
lean_object* v_defValue_460_; lean_object* v_descr_461_; lean_object* v_deprecation_x3f_462_; lean_object* v___x_463_; uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_defValue_460_ = lean_ctor_get(v_decl_457_, 0);
v_descr_461_ = lean_ctor_get(v_decl_457_, 1);
v_deprecation_x3f_462_ = lean_ctor_get(v_decl_457_, 2);
v___x_463_ = lean_alloc_ctor(1, 0, 1);
v___x_464_ = lean_unbox(v_defValue_460_);
lean_ctor_set_uint8(v___x_463_, 0, v___x_464_);
lean_inc(v_deprecation_x3f_462_);
lean_inc_ref(v_descr_461_);
lean_inc_n(v_name_456_, 2);
v___x_465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_465_, 0, v_name_456_);
lean_ctor_set(v___x_465_, 1, v_ref_458_);
lean_ctor_set(v___x_465_, 2, v___x_463_);
lean_ctor_set(v___x_465_, 3, v_descr_461_);
lean_ctor_set(v___x_465_, 4, v_deprecation_x3f_462_);
v___x_466_ = lean_register_option(v_name_456_, v___x_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_474_; 
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v___x_466_, 0);
lean_dec(v_unused_475_);
v___x_468_ = v___x_466_;
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
else
{
lean_dec(v___x_466_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
lean_inc(v_defValue_460_);
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v_name_456_);
lean_ctor_set(v___x_470_, 1, v_defValue_460_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v_name_456_);
v_a_476_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_466_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_466_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_456_ = stack[0].m_obj;
lean_object* v_decl_457_ = stack[1].m_obj;
lean_object* v_ref_458_ = stack[2].m_obj;
lean_object* v_res_484_;
v_res_484_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v_name_456_, v_decl_457_, v_ref_458_);
stack->m_obj
 = v_res_484_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_485_, lean_object* v_decl_486_, lean_object* v_ref_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v_name_485_, v_decl_486_, v_ref_487_);
lean_dec_ref(v_decl_486_);
return v_res_489_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = lean_box(0);
v___x_494_ = lean_internal_get_default_verbose(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_495_ = lean_box(0);
v___x_496_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_497_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_498_ = lean_box(v___x_497_);
v___x_499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_496_);
lean_ctor_set(v___x_499_, 2, v___x_495_);
return v___x_499_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_504_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_505_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_506_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_507_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v___x_504_, v___x_505_, v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_508_;
v_res_508_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_();
stack->m_obj
 = v_res_508_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2____boxed(lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_();
return v_res_510_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_getOptionOverrides_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_511_ = stack[0].m_obj;
lean_object* v_res_512_;
v_res_512_ = lean_internal_get_option_overrides(v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_511_);
stack->m_obj
 = v_res_512_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getOptionOverrides___boxed(lean_object* v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = lean_internal_get_option_overrides(v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_513_);
return v_res_514_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_Internal_getBelieverTrustLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_515_ = stack[0].m_obj;
uint32_t v_res_516_;
v_res_516_ = lean_internal_get_believer_trust_level(v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_515_);
stack->m_num = v_res_516_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBelieverTrustLevel___boxed(lean_object* v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_517_){
_start:
{
uint32_t v_res_518_; lean_object* v_r_519_; 
v_res_518_ = lean_internal_get_believer_trust_level(v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_517_);
v_r_519_ = lean_box_uint32(v_res_518_);
return v_r_519_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0(void){
_start:
{
lean_object* v___x_520_; uint32_t v___x_521_; 
v___x_520_ = lean_box(0);
v___x_521_ = lean_internal_get_believer_trust_level(v___x_520_);
return v___x_521_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1(void){
_start:
{
uint32_t v___x_522_; uint32_t v___x_523_; uint32_t v___x_524_; 
v___x_522_ = 1;
v___x_523_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0);
v___x_524_ = lean_uint32_add(v___x_523_, v___x_522_);
return v___x_524_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel(void){
_start:
{
uint32_t v___x_525_; 
v___x_525_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1);
return v___x_525_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0(void){
_start:
{
lean_object* v___x_526_; uint32_t v___x_527_; 
v___x_526_ = lean_box(0);
v___x_527_ = lean_internal_get_hardware_concurrency(v___x_526_);
return v___x_527_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads(void){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__40, &l___private_Lean_Shell_0__Lean_displayHelp___closed__40_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40);
if (v___x_528_ == 0)
{
uint32_t v___x_529_; 
v___x_529_ = 0;
return v___x_529_;
}
else
{
uint32_t v___x_530_; 
v___x_530_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0, &l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0);
return v___x_530_;
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_533_; uint32_t v___x_534_; uint32_t v___x_535_; uint8_t v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_533_ = lean_box(0);
v___x_534_ = l___private_Lean_Shell_0__Lean_defaultNumThreads;
v___x_535_ = l___private_Lean_Shell_0__Lean_defaultTrustLevel;
v___x_536_ = 0;
v___x_537_ = 0;
v___x_538_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__0));
v___x_539_ = l_Lean_Options_empty;
v___x_540_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v___x_538_);
lean_ctor_set(v___x_540_, 2, v___x_539_);
lean_ctor_set(v___x_540_, 3, v___x_533_);
lean_ctor_set(v___x_540_, 4, v___x_533_);
lean_ctor_set(v___x_540_, 5, v___x_533_);
lean_ctor_set(v___x_540_, 6, v___x_533_);
lean_ctor_set(v___x_540_, 7, v___x_533_);
lean_ctor_set(v___x_540_, 8, v___x_533_);
lean_ctor_set(v___x_540_, 9, v___x_538_);
lean_ctor_set(v___x_540_, 10, v___x_533_);
lean_ctor_set(v___x_540_, 11, v___x_533_);
lean_ctor_set(v___x_540_, 12, v___x_533_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*13 + 8, v___x_537_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*13 + 9, v___x_536_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*13 + 10, v___x_536_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*13 + 11, v___x_536_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*13 + 12, v___x_536_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*13 + 13, v___x_536_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*13 + 14, v___x_536_);
lean_ctor_set_uint32(v___x_540_, sizeof(void*)*13, v___x_535_);
lean_ctor_set_uint32(v___x_540_, sizeof(void*)*13 + 4, v___x_534_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*13 + 15, v___x_536_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*13 + 16, v___x_536_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*13 + 17, v___x_536_);
return v___x_540_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg(){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1, &l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1);
return v___x_542_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_mkShellOptions___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_543_;
v_res_543_ = l___private_Lean_Shell_0__Lean_mkShellOptions___redArg();
stack->m_obj
 = v_res_543_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___boxed(lean_object* v___dummy_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Lean_Shell_0__Lean_mkShellOptions___redArg();
return v_res_545_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0(void){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Lean_Shell_0__Lean_mkShellOptions___redArg();
return v___x_546_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object* v_x_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0);
return v___x_548_;
}
}
uint8_t lean_shell_options_get_run(lean_object* v_opts_549_){
_start:
{
uint8_t v_run_550_; 
v_run_550_ = lean_ctor_get_uint8(v_opts_549_, sizeof(void*)*13 + 17);
lean_dec_ref(v_opts_549_);
return v_run_550_;
}
}
LEAN_EXPORT void lean_shell_options_get_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_549_ = stack[0].m_obj;
uint8_t v_res_551_;
v_res_551_ = lean_shell_options_get_run(v_opts_549_);
stack->m_num = v_res_551_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getRun___boxed(lean_object* v_opts_552_){
_start:
{
uint8_t v_res_553_; lean_object* v_r_554_; 
v_res_553_ = lean_shell_options_get_run(v_opts_552_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(lean_object* v_opts_555_, lean_object* v_opt_556_){
_start:
{
lean_object* v_name_557_; lean_object* v_defValue_558_; lean_object* v_map_559_; lean_object* v___x_560_; 
v_name_557_ = lean_ctor_get(v_opt_556_, 0);
v_defValue_558_ = lean_ctor_get(v_opt_556_, 1);
v_map_559_ = lean_ctor_get(v_opts_555_, 0);
v___x_560_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_559_, v_name_557_);
if (lean_obj_tag(v___x_560_) == 0)
{
uint8_t v___x_561_; 
v___x_561_ = lean_unbox(v_defValue_558_);
return v___x_561_;
}
else
{
lean_object* v_val_562_; 
v_val_562_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v___x_560_, 1);
if (lean_obj_tag(v_val_562_) == 1)
{
uint8_t v_v_563_; 
v_v_563_ = lean_ctor_get_uint8(v_val_562_, 0);
lean_dec_ref_known(v_val_562_, 0);
return v_v_563_;
}
else
{
uint8_t v___x_564_; 
lean_dec(v_val_562_);
v___x_564_ = lean_unbox(v_defValue_558_);
return v___x_564_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_555_ = stack[0].m_obj;
lean_object* v_opt_556_ = stack[1].m_obj;
uint8_t v_res_565_;
v_res_565_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_opts_555_, v_opt_556_);
stack->m_num = v_res_565_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0___boxed(lean_object* v_opts_566_, lean_object* v_opt_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_opts_566_, v_opt_567_);
lean_dec_ref(v_opt_567_);
lean_dec_ref(v_opts_566_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
uint8_t lean_shell_options_get_profiler(lean_object* v_opts_570_){
_start:
{
lean_object* v_leanOpts_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_leanOpts_571_ = lean_ctor_get(v_opts_570_, 0);
lean_inc_ref(v_leanOpts_571_);
lean_dec_ref(v_opts_570_);
v___x_572_ = l_Lean_profiler;
v___x_573_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_leanOpts_571_, v___x_572_);
lean_dec_ref(v_leanOpts_571_);
return v___x_573_;
}
}
LEAN_EXPORT void lean_shell_options_get_profiler_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_570_ = stack[0].m_obj;
uint8_t v_res_574_;
v_res_574_ = lean_shell_options_get_profiler(v_opts_570_);
stack->m_num = v_res_574_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getProfiler___boxed(lean_object* v_opts_575_){
_start:
{
uint8_t v_res_576_; lean_object* v_r_577_; 
v_res_576_ = lean_shell_options_get_profiler(v_opts_575_);
v_r_577_ = lean_box(v_res_576_);
return v_r_577_;
}
}
uint32_t lean_shell_options_get_num_threads(lean_object* v_opts_578_){
_start:
{
uint32_t v_numThreads_579_; 
v_numThreads_579_ = lean_ctor_get_uint32(v_opts_578_, sizeof(void*)*13 + 4);
lean_dec_ref(v_opts_578_);
return v_numThreads_579_;
}
}
LEAN_EXPORT void lean_shell_options_get_num_threads_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_578_ = stack[0].m_obj;
uint32_t v_res_580_;
v_res_580_ = lean_shell_options_get_num_threads(v_opts_578_);
stack->m_num = v_res_580_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getNumThreads___boxed(lean_object* v_opts_581_){
_start:
{
uint32_t v_res_582_; lean_object* v_r_583_; 
v_res_582_ = lean_shell_options_get_num_threads(v_opts_581_);
v_r_583_ = lean_box_uint32(v_res_582_);
return v_r_583_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_checkOptArg(lean_object* v_optName_586_, lean_object* v_optArg_x3f_587_){
_start:
{
if (lean_obj_tag(v_optArg_x3f_587_) == 1)
{
lean_object* v_val_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
v_val_589_ = lean_ctor_get(v_optArg_x3f_587_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v_optArg_x3f_587_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v_optArg_x3f_587_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_val_589_);
lean_dec(v_optArg_x3f_587_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set_tag(v___x_591_, 0);
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_val_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_optArg_x3f_587_);
v___x_597_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__0));
v___x_598_ = lean_string_append(v___x_597_, v_optName_586_);
v___x_599_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_600_ = lean_string_append(v___x_598_, v___x_599_);
v___x_601_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_checkOptArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_optName_586_ = stack[0].m_obj;
lean_object* v_optArg_x3f_587_ = stack[1].m_obj;
lean_object* v_res_603_;
v_res_603_ = l___private_Lean_Shell_0__Lean_checkOptArg(v_optName_586_, v_optArg_x3f_587_);
stack->m_obj
 = v_res_603_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg___boxed(lean_object* v_optName_604_, lean_object* v_optArg_x3f_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Lean_Shell_0__Lean_checkOptArg(v_optName_604_, v_optArg_x3f_605_);
lean_dec_ref(v_optName_604_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(lean_object* v_o_611_, lean_object* v_k_612_, lean_object* v_v_613_){
_start:
{
lean_object* v_map_614_; uint8_t v_hasTrace_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_629_; 
v_map_614_ = lean_ctor_get(v_o_611_, 0);
v_hasTrace_615_ = lean_ctor_get_uint8(v_o_611_, sizeof(void*)*1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_o_611_);
if (v_isSharedCheck_629_ == 0)
{
v___x_617_ = v_o_611_;
v_isShared_618_ = v_isSharedCheck_629_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_map_614_);
lean_dec(v_o_611_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_629_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v_v_613_);
lean_inc(v_k_612_);
v___x_620_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_612_, v___x_619_, v_map_614_);
if (v_hasTrace_615_ == 0)
{
lean_object* v___x_621_; uint8_t v___x_622_; lean_object* v___x_624_; 
v___x_621_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_622_ = l_Lean_Name_isPrefixOf(v___x_621_, v_k_612_);
lean_dec(v_k_612_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_620_);
v___x_624_ = v___x_617_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_620_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*1, v___x_622_);
return v___x_624_;
}
}
else
{
lean_object* v___x_627_; 
lean_dec(v_k_612_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_620_);
v___x_627_ = v___x_617_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_620_);
lean_ctor_set_uint8(v_reuseFailAlloc_628_, sizeof(void*)*1, v_hasTrace_615_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(lean_object* v___x_630_, lean_object* v_arg_631_, lean_object* v_a_632_, lean_object* v_b_633_){
_start:
{
uint8_t v_decide_634_; 
v_decide_634_ = lean_nat_dec_eq(v_a_632_, v___x_630_);
if (v_decide_634_ == 0)
{
uint32_t v___x_635_; uint32_t v___x_636_; uint8_t v___x_637_; 
v___x_635_ = lean_string_utf8_get_fast(v_arg_631_, v_a_632_);
v___x_636_ = 61;
v___x_637_ = lean_uint32_dec_eq(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_box(0);
v___x_639_ = lean_string_utf8_next_fast(v_arg_631_, v_a_632_);
lean_dec(v_a_632_);
v_a_632_ = v___x_639_;
v_b_633_ = v___x_638_;
goto _start;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v_a_632_);
return v___x_641_;
}
}
else
{
lean_dec(v_a_632_);
lean_inc(v_b_633_);
return v_b_633_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(lean_object* v___x_642_, lean_object* v_arg_643_, lean_object* v_a_644_, lean_object* v_b_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_642_, v_arg_643_, v_a_644_, v_b_645_);
lean_dec(v_b_645_);
lean_dec_ref(v_arg_643_);
lean_dec(v___x_642_);
return v_res_646_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_setConfigOption(lean_object* v_opts_650_, lean_object* v_arg_651_){
_start:
{
lean_object* v___y_654_; lean_object* v_searcher_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_searcher_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_string_utf8_byte_size(v_arg_651_);
v___x_687_ = lean_box(0);
v___x_688_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_686_, v_arg_651_, v_searcher_685_, v___x_687_);
if (lean_obj_tag(v___x_688_) == 0)
{
v___y_654_ = v___x_686_;
goto v___jp_653_;
}
else
{
lean_object* v_val_689_; 
v_val_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_val_689_);
lean_dec_ref_known(v___x_688_, 1);
v___y_654_ = v_val_689_;
goto v___jp_653_;
}
v___jp_653_:
{
lean_object* v___x_655_; uint8_t v_decide_656_; 
v___x_655_ = lean_string_utf8_byte_size(v_arg_651_);
v_decide_656_ = lean_nat_dec_eq(v___y_654_, v___x_655_);
if (v_decide_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v_name_659_; lean_object* v___x_660_; lean_object* v_val_661_; lean_object* v___x_662_; 
v___x_657_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_654_);
lean_inc_ref(v_arg_651_);
v___x_658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_658_, 0, v_arg_651_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
lean_ctor_set(v___x_658_, 2, v___y_654_);
v_name_659_ = l_String_Slice_toName(v___x_658_);
lean_dec_ref_known(v___x_658_, 3);
v___x_660_ = lean_string_utf8_next_fast(v_arg_651_, v___y_654_);
lean_dec(v___y_654_);
v_val_661_ = lean_string_utf8_extract_fast(v_arg_651_, v___x_660_, v___x_655_);
lean_dec_ref(v_arg_651_);
v___x_662_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_674_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_674_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_674_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_674_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; 
v___x_667_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_663_, v_name_659_);
lean_dec(v_a_663_);
if (lean_obj_tag(v___x_667_) == 1)
{
lean_object* v_val_668_; lean_object* v___x_669_; 
lean_del_object(v___x_665_);
v_val_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v___x_667_, 1);
v___x_669_ = l_Lean_Language_Lean_setOption(v_opts_650_, v_val_668_, v_name_659_, v_val_661_);
return v___x_669_;
}
else
{
lean_object* v___x_670_; lean_object* v___x_672_; 
lean_dec(v___x_667_);
v___x_670_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(v_opts_650_, v_name_659_, v_val_661_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_670_);
v___x_672_ = v___x_665_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v_val_661_);
lean_dec(v_name_659_);
lean_dec_ref(v_opts_650_);
v_a_675_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_662_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_662_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec(v___y_654_);
lean_dec_ref(v_arg_651_);
lean_dec_ref(v_opts_650_);
v___x_683_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_setConfigOption___closed__1));
v___x_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_setConfigOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_650_ = stack[0].m_obj;
lean_object* v_arg_651_ = stack[1].m_obj;
lean_object* v_res_690_;
v_res_690_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_opts_650_, v_arg_651_);
stack->m_obj
 = v_res_690_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___boxed(lean_object* v_opts_691_, lean_object* v_arg_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_opts_691_, v_arg_692_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object* v___x_695_, lean_object* v___x_696_, lean_object* v_arg_697_, lean_object* v_inst_698_, lean_object* v_R_699_, lean_object* v_a_700_, lean_object* v_b_701_, lean_object* v_c_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_695_, v_arg_697_, v_a_700_, v_b_701_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v_arg_706_, lean_object* v_inst_707_, lean_object* v_R_708_, lean_object* v_a_709_, lean_object* v_b_710_, lean_object* v_c_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(v___x_704_, v___x_705_, v_arg_706_, v_inst_707_, v_R_708_, v_a_709_, v_b_710_, v_c_711_);
lean_dec(v_b_710_);
lean_dec_ref(v_arg_706_);
lean_dec_ref(v___x_705_);
lean_dec(v___x_704_);
return v_res_712_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(lean_object* v_msg_714_){
_start:
{
lean_object* v___f_716_; lean_object* v___x_717_; 
v___f_716_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_717_ = l_IO_eprint___redArg(v___f_716_, v_msg_714_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_733_; 
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v___x_717_, 0);
lean_dec(v_unused_734_);
v___x_727_ = v___x_717_;
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
else
{
lean_dec(v___x_717_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_box(0);
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 0);
lean_ctor_set(v___x_727_, 0, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_714_ = stack[0].m_obj;
lean_object* v_res_735_;
v_res_735_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(v_msg_714_);
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(lean_object* v_msg_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(v_msg_736_);
return v_res_738_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_741_; lean_object* v___x_742_; 
v___x_741_ = 1;
v___x_742_ = lean_box_uint32(v___x_741_);
return v___x_742_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(lean_object* v_x_743_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_apply_1(v_x_743_, lean_box(0));
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_752_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_766_; lean_object* v___f_767_; lean_object* v___x_768_; 
v_a_761_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_752_, 1);
v___x_766_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_767_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_768_ = l_IO_eprint___redArg(v___f_767_, v___x_766_);
lean_dec_ref(v___x_768_);
goto v___jp_762_;
v___jp_762_:
{
lean_object* v___x_763_; lean_object* v___f_764_; lean_object* v___x_765_; 
v___x_763_ = lean_io_error_to_string(v_a_761_);
v___f_764_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_765_ = l_IO_eprint___redArg(v___f_764_, v___x_763_);
lean_dec_ref(v___x_765_);
goto v___jp_748_;
}
}
v___jp_745_:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
v___jp_748_:
{
lean_object* v___x_749_; lean_object* v___f_750_; lean_object* v___x_751_; 
v___x_749_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_750_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_751_ = l_IO_eprint___redArg(v___f_750_, v___x_749_);
lean_dec_ref(v___x_751_);
goto v___jp_745_;
}
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_743_ = stack[0].m_obj;
lean_object* v_res_769_;
v_res_769_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(v_x_743_);
stack->m_obj
 = v_res_769_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed(lean_object* v_x_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(v_x_770_);
return v_res_772_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(lean_object* v_00_u03b1_773_, lean_object* v_x_774_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = lean_apply_1(v_x_774_, lean_box(0));
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_797_; lean_object* v___f_798_; lean_object* v___x_799_; 
v_a_792_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_783_, 1);
v___x_797_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_798_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_799_ = l_IO_eprint___redArg(v___f_798_, v___x_797_);
lean_dec_ref(v___x_799_);
goto v___jp_793_;
v___jp_793_:
{
lean_object* v___x_794_; lean_object* v___f_795_; lean_object* v___x_796_; 
v___x_794_ = lean_io_error_to_string(v_a_792_);
v___f_795_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_796_ = l_IO_eprint___redArg(v___f_795_, v___x_794_);
lean_dec_ref(v___x_796_);
goto v___jp_779_;
}
}
v___jp_776_:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
v___jp_779_:
{
lean_object* v___x_780_; lean_object* v___f_781_; lean_object* v___x_782_; 
v___x_780_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_781_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_782_ = l_IO_eprint___redArg(v___f_781_, v___x_780_);
lean_dec_ref(v___x_782_);
goto v___jp_776_;
}
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_774_ = stack[1].m_obj;
lean_object* v_res_800_;
v_res_800_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(lean_box(0), v_x_774_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___boxed(lean_object* v_00_u03b1_801_, lean_object* v_x_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(v_00_u03b1_801_, v_x_802_);
return v_res_804_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(lean_object* v_opt_807_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___f_816_; lean_object* v___x_817_; 
v___x_812_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0));
v___x_813_ = lean_string_append(v___x_812_, v_opt_807_);
v___x_814_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_815_ = lean_string_append(v___x_813_, v___x_814_);
v___f_816_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_817_ = l_IO_eprint___redArg(v___f_816_, v___x_815_);
lean_dec_ref(v___x_817_);
goto v___jp_809_;
v___jp_809_:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_807_ = stack[0].m_obj;
lean_object* v_res_818_;
v_res_818_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(v_opt_807_);
stack->m_obj
 = v_res_818_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___boxed(lean_object* v_opt_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(v_opt_819_);
lean_dec_ref(v_opt_819_);
return v_res_821_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(lean_object* v_opt_824_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___f_833_; lean_object* v___x_834_; 
v___x_829_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0));
v___x_830_ = lean_string_append(v___x_829_, v_opt_824_);
v___x_831_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1));
v___x_832_ = lean_string_append(v___x_830_, v___x_831_);
v___f_833_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_834_ = l_IO_eprint___redArg(v___f_833_, v___x_832_);
lean_dec_ref(v___x_834_);
goto v___jp_826_;
v___jp_826_:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_824_ = stack[0].m_obj;
lean_object* v_res_835_;
v_res_835_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(v_opt_824_);
stack->m_obj
 = v_res_835_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___boxed(lean_object* v_opt_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(v_opt_836_);
lean_dec_ref(v_opt_836_);
return v_res_838_;
}
}
lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(lean_object* v_s_839_){
_start:
{
lean_object* v___x_841_; lean_object* v_putStr_842_; lean_object* v___x_843_; 
v___x_841_ = lean_get_stderr();
v_putStr_842_ = lean_ctor_get(v___x_841_, 4);
lean_inc_ref(v_putStr_842_);
lean_dec_ref(v___x_841_);
v___x_843_ = lean_apply_2(v_putStr_842_, v_s_839_, lean_box(0));
return v___x_843_;
}
}
LEAN_EXPORT void l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_839_ = stack[0].m_obj;
lean_object* v_res_844_;
v_res_844_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v_s_839_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0___boxed(lean_object* v_s_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v_s_845_);
return v_res_847_;
}
}
lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(lean_object* v_s_848_){
_start:
{
lean_object* v___x_850_; lean_object* v_putStr_851_; lean_object* v___x_852_; 
v___x_850_ = lean_get_stdout();
v_putStr_851_ = lean_ctor_get(v___x_850_, 4);
lean_inc_ref(v_putStr_851_);
lean_dec_ref(v___x_850_);
v___x_852_ = lean_apply_2(v_putStr_851_, v_s_848_, lean_box(0));
return v___x_852_;
}
}
LEAN_EXPORT void l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_848_ = stack[0].m_obj;
lean_object* v_res_853_;
v_res_853_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v_s_848_);
stack->m_obj
 = v_res_853_;
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5___boxed(lean_object* v_s_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v_s_854_);
return v_res_856_;
}
}
lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object* v_s_857_){
_start:
{
uint32_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = 10;
v___x_860_ = lean_string_push(v_s_857_, v___x_859_);
v___x_861_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT void l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_857_ = stack[0].m_obj;
lean_object* v_res_862_;
v_res_862_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_s_857_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3___boxed(lean_object* v_s_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_s_863_);
return v_res_865_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(lean_object* v_o_866_, lean_object* v_k_867_, uint8_t v_v_868_){
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
v___x_874_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_874_, 0, v_v_868_);
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
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_866_ = stack[0].m_obj;
lean_object* v_k_867_ = stack[1].m_obj;
uint8_t v_v_868_ = stack[2].m_num;
lean_object* v_res_885_;
v_res_885_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_o_866_, v_k_867_, v_v_868_);
stack->m_obj
 = v_res_885_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1___boxed(lean_object* v_o_886_, lean_object* v_k_887_, lean_object* v_v_888_){
_start:
{
uint8_t v_v_boxed_889_; lean_object* v_res_890_; 
v_v_boxed_889_ = lean_unbox(v_v_888_);
v_res_890_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_o_886_, v_k_887_, v_v_boxed_889_);
return v_res_890_;
}
}
lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object* v_opts_891_, lean_object* v_opt_892_, uint8_t v_val_893_){
_start:
{
lean_object* v_name_894_; lean_object* v___x_895_; 
v_name_894_ = lean_ctor_get(v_opt_892_, 0);
lean_inc(v_name_894_);
lean_dec_ref(v_opt_892_);
v___x_895_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_opts_891_, v_name_894_, v_val_893_);
return v___x_895_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_891_ = stack[0].m_obj;
lean_object* v_opt_892_ = stack[1].m_obj;
uint8_t v_val_893_ = stack[2].m_num;
lean_object* v_res_896_;
v_res_896_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_opts_891_, v_opt_892_, v_val_893_);
stack->m_obj
 = v_res_896_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object* v_opts_897_, lean_object* v_opt_898_, lean_object* v_val_899_){
_start:
{
uint8_t v_val_boxed_900_; lean_object* v_res_901_; 
v_val_boxed_900_ = lean_unbox(v_val_899_);
v_res_901_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_opts_897_, v_opt_898_, v_val_boxed_900_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(lean_object* v_o_902_, lean_object* v_k_903_, lean_object* v_v_904_){
_start:
{
lean_object* v_map_905_; uint8_t v_hasTrace_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_920_; 
v_map_905_ = lean_ctor_get(v_o_902_, 0);
v_hasTrace_906_ = lean_ctor_get_uint8(v_o_902_, sizeof(void*)*1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_o_902_);
if (v_isSharedCheck_920_ == 0)
{
v___x_908_ = v_o_902_;
v_isShared_909_ = v_isSharedCheck_920_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_map_905_);
lean_dec(v_o_902_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_920_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_910_, 0, v_v_904_);
lean_inc(v_k_903_);
v___x_911_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_903_, v___x_910_, v_map_905_);
if (v_hasTrace_906_ == 0)
{
lean_object* v___x_912_; uint8_t v___x_913_; lean_object* v___x_915_; 
v___x_912_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_913_ = l_Lean_Name_isPrefixOf(v___x_912_, v_k_903_);
lean_dec(v_k_903_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_911_);
v___x_915_ = v___x_908_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_911_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*1, v___x_913_);
return v___x_915_;
}
}
else
{
lean_object* v___x_918_; 
lean_dec(v_k_903_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_911_);
v___x_918_ = v___x_908_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_911_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*1, v_hasTrace_906_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object* v_opts_921_, lean_object* v_opt_922_, lean_object* v_val_923_){
_start:
{
lean_object* v_name_924_; lean_object* v___x_925_; 
v_name_924_ = lean_ctor_get(v_opt_922_, 0);
lean_inc(v_name_924_);
lean_dec_ref(v_opt_922_);
v___x_925_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(v_opts_921_, v_name_924_, v_val_923_);
return v___x_925_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = l_System_Platform_numBits;
v___x_955_ = lean_unsigned_to_nat(2u);
v___x_956_ = lean_nat_pow(v___x_955_, v___x_954_);
return v___x_956_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1(void){
_start:
{
uint32_t v___x_966_; lean_object* v___x_967_; 
v___x_966_ = 0;
v___x_967_ = lean_box_uint32(v___x_966_);
return v___x_967_;
}
}
lean_object* lean_shell_options_process(lean_object* v_opts_968_, uint32_t v_opt_969_, lean_object* v_optArg_x3f_970_){
_start:
{
lean_object* v___y_1078_; lean_object* v___y_1136_; uint32_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = 101;
v___x_1191_ = lean_uint32_dec_eq(v_opt_969_, v___x_1190_);
if (v___x_1191_ == 0)
{
uint32_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = 106;
v___x_1193_ = lean_uint32_dec_eq(v_opt_969_, v___x_1192_);
if (v___x_1193_ == 0)
{
uint32_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = 118;
v___x_1195_ = lean_uint32_dec_eq(v_opt_969_, v___x_1194_);
if (v___x_1195_ == 0)
{
uint32_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = 86;
v___x_1197_ = lean_uint32_dec_eq(v_opt_969_, v___x_1196_);
if (v___x_1197_ == 0)
{
uint32_t v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = 103;
v___x_1199_ = lean_uint32_dec_eq(v_opt_969_, v___x_1198_);
if (v___x_1199_ == 0)
{
uint32_t v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = 104;
v___x_1201_ = lean_uint32_dec_eq(v_opt_969_, v___x_1200_);
if (v___x_1201_ == 0)
{
uint32_t v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = 102;
v___x_1203_ = lean_uint32_dec_eq(v_opt_969_, v___x_1202_);
if (v___x_1203_ == 0)
{
uint32_t v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = 99;
v___x_1205_ = lean_uint32_dec_eq(v_opt_969_, v___x_1204_);
if (v___x_1205_ == 0)
{
uint32_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = 98;
v___x_1207_ = lean_uint32_dec_eq(v_opt_969_, v___x_1206_);
if (v___x_1207_ == 0)
{
uint32_t v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = 115;
v___x_1209_ = lean_uint32_dec_eq(v_opt_969_, v___x_1208_);
if (v___x_1209_ == 0)
{
uint32_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = 73;
v___x_1211_ = lean_uint32_dec_eq(v_opt_969_, v___x_1210_);
if (v___x_1211_ == 0)
{
uint32_t v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = 114;
v___x_1213_ = lean_uint32_dec_eq(v_opt_969_, v___x_1212_);
if (v___x_1213_ == 0)
{
uint32_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = 111;
v___x_1215_ = lean_uint32_dec_eq(v_opt_969_, v___x_1214_);
if (v___x_1215_ == 0)
{
uint32_t v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = 105;
v___x_1217_ = lean_uint32_dec_eq(v_opt_969_, v___x_1216_);
if (v___x_1217_ == 0)
{
uint32_t v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = 82;
v___x_1219_ = lean_uint32_dec_eq(v_opt_969_, v___x_1218_);
if (v___x_1219_ == 0)
{
uint32_t v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = 77;
v___x_1221_ = lean_uint32_dec_eq(v_opt_969_, v___x_1220_);
if (v___x_1221_ == 0)
{
uint32_t v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = 84;
v___x_1223_ = lean_uint32_dec_eq(v_opt_969_, v___x_1222_);
if (v___x_1223_ == 0)
{
uint32_t v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = 116;
v___x_1225_ = lean_uint32_dec_eq(v_opt_969_, v___x_1224_);
if (v___x_1225_ == 0)
{
uint32_t v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = 113;
v___x_1227_ = lean_uint32_dec_eq(v_opt_969_, v___x_1226_);
if (v___x_1227_ == 0)
{
uint32_t v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = 100;
v___x_1229_ = lean_uint32_dec_eq(v_opt_969_, v___x_1228_);
if (v___x_1229_ == 0)
{
uint32_t v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = 79;
v___x_1231_ = lean_uint32_dec_eq(v_opt_969_, v___x_1230_);
if (v___x_1231_ == 0)
{
uint32_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = 78;
v___x_1233_ = lean_uint32_dec_eq(v_opt_969_, v___x_1232_);
if (v___x_1233_ == 0)
{
uint32_t v___x_1234_; uint8_t v___x_1235_; 
v___x_1234_ = 74;
v___x_1235_ = lean_uint32_dec_eq(v_opt_969_, v___x_1234_);
if (v___x_1235_ == 0)
{
uint32_t v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = 97;
v___x_1237_ = lean_uint32_dec_eq(v_opt_969_, v___x_1236_);
if (v___x_1237_ == 0)
{
uint32_t v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = 120;
v___x_1239_ = lean_uint32_dec_eq(v_opt_969_, v___x_1238_);
if (v___x_1239_ == 0)
{
uint32_t v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = 76;
v___x_1241_ = lean_uint32_dec_eq(v_opt_969_, v___x_1240_);
if (v___x_1241_ == 0)
{
uint32_t v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = 68;
v___x_1243_ = lean_uint32_dec_eq(v_opt_969_, v___x_1242_);
if (v___x_1243_ == 0)
{
uint32_t v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = 83;
v___x_1245_ = lean_uint32_dec_eq(v_opt_969_, v___x_1244_);
if (v___x_1245_ == 0)
{
uint32_t v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = 87;
v___x_1247_ = lean_uint32_dec_eq(v_opt_969_, v___x_1246_);
if (v___x_1247_ == 0)
{
uint32_t v___x_1248_; uint8_t v___x_1249_; 
v___x_1248_ = 80;
v___x_1249_ = lean_uint32_dec_eq(v_opt_969_, v___x_1248_);
if (v___x_1249_ == 0)
{
uint32_t v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = 66;
v___x_1251_ = lean_uint32_dec_eq(v_opt_969_, v___x_1250_);
if (v___x_1251_ == 0)
{
uint32_t v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = 112;
v___x_1253_ = lean_uint32_dec_eq(v_opt_969_, v___x_1252_);
if (v___x_1253_ == 0)
{
uint32_t v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = 108;
v___x_1255_ = lean_uint32_dec_eq(v_opt_969_, v___x_1254_);
if (v___x_1255_ == 0)
{
uint32_t v___x_1256_; uint8_t v___x_1257_; 
v___x_1256_ = 117;
v___x_1257_ = lean_uint32_dec_eq(v_opt_969_, v___x_1256_);
if (v___x_1257_ == 0)
{
uint32_t v___x_1258_; uint8_t v___x_1259_; 
v___x_1258_ = 69;
v___x_1259_ = lean_uint32_dec_eq(v_opt_969_, v___x_1258_);
if (v___x_1259_ == 0)
{
uint32_t v___x_1260_; uint8_t v___x_1261_; 
v___x_1260_ = 89;
v___x_1261_ = lean_uint32_dec_eq(v_opt_969_, v___x_1260_);
if (v___x_1261_ == 0)
{
uint32_t v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = 90;
v___x_1263_ = lean_uint32_dec_eq(v_opt_969_, v___x_1262_);
if (v___x_1263_ == 0)
{
uint32_t v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = 72;
v___x_1265_ = lean_uint32_dec_eq(v_opt_969_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_dec(v_optArg_x3f_970_);
lean_dec_ref(v_opts_968_);
goto v___jp_1096_;
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1267_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1266_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1308_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1308_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1308_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v_leanOpts_1272_; lean_object* v_forwardedArgs_1273_; uint8_t v_component_1274_; uint8_t v_printPrefix_1275_; uint8_t v_printLibDir_1276_; uint8_t v_useStdin_1277_; uint8_t v_onlyDeps_1278_; uint8_t v_onlySrcDeps_1279_; uint8_t v_depsJson_1280_; lean_object* v_opts_1281_; uint32_t v_trustLevel_1282_; uint32_t v_numThreads_1283_; lean_object* v_rootDir_x3f_1284_; lean_object* v_setupFileName_x3f_1285_; lean_object* v_oleanFileName_x3f_1286_; lean_object* v_ileanFileName_x3f_1287_; lean_object* v_cFileName_x3f_1288_; lean_object* v_bcFileName_x3f_1289_; uint8_t v_jsonOutput_1290_; lean_object* v_errorOnKinds_1291_; uint8_t v_printStats_1292_; uint8_t v_run_1293_; lean_object* v_incrSaveFileName_x3f_1294_; lean_object* v_incrLoadFileName_x3f_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1306_; 
v_leanOpts_1272_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1273_ = lean_ctor_get(v_opts_968_, 1);
v_component_1274_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1275_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1276_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1277_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1278_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1279_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1280_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1281_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1282_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1283_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1284_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1285_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1286_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1287_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1288_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1289_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1290_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1291_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1292_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1293_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1294_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1295_ = lean_ctor_get(v_opts_968_, 11);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v_opts_968_, 12);
lean_dec(v_unused_1307_);
v___x_1297_ = v_opts_968_;
v_isShared_1298_ = v_isSharedCheck_1306_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_incrLoadFileName_x3f_1295_);
lean_inc(v_incrSaveFileName_x3f_1294_);
lean_inc(v_errorOnKinds_1291_);
lean_inc(v_bcFileName_x3f_1289_);
lean_inc(v_cFileName_x3f_1288_);
lean_inc(v_ileanFileName_x3f_1287_);
lean_inc(v_oleanFileName_x3f_1286_);
lean_inc(v_setupFileName_x3f_1285_);
lean_inc(v_rootDir_x3f_1284_);
lean_inc(v_opts_1281_);
lean_inc(v_forwardedArgs_1273_);
lean_inc(v_leanOpts_1272_);
lean_dec(v_opts_968_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1306_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_a_1268_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 12, v___x_1299_);
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_leanOpts_1272_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_forwardedArgs_1273_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_opts_1281_);
lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_rootDir_x3f_1284_);
lean_ctor_set(v_reuseFailAlloc_1305_, 4, v_setupFileName_x3f_1285_);
lean_ctor_set(v_reuseFailAlloc_1305_, 5, v_oleanFileName_x3f_1286_);
lean_ctor_set(v_reuseFailAlloc_1305_, 6, v_ileanFileName_x3f_1287_);
lean_ctor_set(v_reuseFailAlloc_1305_, 7, v_cFileName_x3f_1288_);
lean_ctor_set(v_reuseFailAlloc_1305_, 8, v_bcFileName_x3f_1289_);
lean_ctor_set(v_reuseFailAlloc_1305_, 9, v_errorOnKinds_1291_);
lean_ctor_set(v_reuseFailAlloc_1305_, 10, v_incrSaveFileName_x3f_1294_);
lean_ctor_set(v_reuseFailAlloc_1305_, 11, v_incrLoadFileName_x3f_1295_);
lean_ctor_set(v_reuseFailAlloc_1305_, 12, v___x_1299_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*13 + 8, v_component_1274_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*13 + 9, v_printPrefix_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*13 + 10, v_printLibDir_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*13 + 11, v_useStdin_1277_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*13 + 12, v_onlyDeps_1278_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*13 + 13, v_onlySrcDeps_1279_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*13 + 14, v_depsJson_1280_);
lean_ctor_set_uint32(v_reuseFailAlloc_1305_, sizeof(void*)*13, v_trustLevel_1282_);
lean_ctor_set_uint32(v_reuseFailAlloc_1305_, sizeof(void*)*13 + 4, v_numThreads_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*13 + 15, v_jsonOutput_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*13 + 16, v_printStats_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*13 + 17, v_run_1293_);
v___x_1301_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1303_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1301_);
v___x_1303_ = v___x_1270_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_dec_ref(v_opts_968_);
v_a_1309_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1313_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1314_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1313_);
lean_dec_ref(v___x_1314_);
goto v___jp_1310_;
v___jp_1310_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_io_error_to_string(v_a_1309_);
v___x_1312_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1311_);
lean_dec_ref(v___x_1312_);
goto v___jp_1068_;
}
}
}
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1316_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1315_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1357_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1357_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1357_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_leanOpts_1321_; lean_object* v_forwardedArgs_1322_; uint8_t v_component_1323_; uint8_t v_printPrefix_1324_; uint8_t v_printLibDir_1325_; uint8_t v_useStdin_1326_; uint8_t v_onlyDeps_1327_; uint8_t v_onlySrcDeps_1328_; uint8_t v_depsJson_1329_; lean_object* v_opts_1330_; uint32_t v_trustLevel_1331_; uint32_t v_numThreads_1332_; lean_object* v_rootDir_x3f_1333_; lean_object* v_setupFileName_x3f_1334_; lean_object* v_oleanFileName_x3f_1335_; lean_object* v_ileanFileName_x3f_1336_; lean_object* v_cFileName_x3f_1337_; lean_object* v_bcFileName_x3f_1338_; uint8_t v_jsonOutput_1339_; lean_object* v_errorOnKinds_1340_; uint8_t v_printStats_1341_; uint8_t v_run_1342_; lean_object* v_incrSaveFileName_x3f_1343_; lean_object* v_incrHeaderSaveFileName_x3f_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1355_; 
v_leanOpts_1321_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1322_ = lean_ctor_get(v_opts_968_, 1);
v_component_1323_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1324_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1325_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1326_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1327_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1328_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1329_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1330_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1331_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1332_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1333_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1334_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1335_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1336_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1337_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1338_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1339_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1340_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1341_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1342_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1343_ = lean_ctor_get(v_opts_968_, 10);
v_incrHeaderSaveFileName_x3f_1344_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1355_ == 0)
{
lean_object* v_unused_1356_; 
v_unused_1356_ = lean_ctor_get(v_opts_968_, 11);
lean_dec(v_unused_1356_);
v___x_1346_ = v_opts_968_;
v_isShared_1347_ = v_isSharedCheck_1355_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1344_);
lean_inc(v_incrSaveFileName_x3f_1343_);
lean_inc(v_errorOnKinds_1340_);
lean_inc(v_bcFileName_x3f_1338_);
lean_inc(v_cFileName_x3f_1337_);
lean_inc(v_ileanFileName_x3f_1336_);
lean_inc(v_oleanFileName_x3f_1335_);
lean_inc(v_setupFileName_x3f_1334_);
lean_inc(v_rootDir_x3f_1333_);
lean_inc(v_opts_1330_);
lean_inc(v_forwardedArgs_1322_);
lean_inc(v_leanOpts_1321_);
lean_dec(v_opts_968_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1355_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1348_, 0, v_a_1317_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 11, v___x_1348_);
v___x_1350_ = v___x_1346_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_leanOpts_1321_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_forwardedArgs_1322_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v_opts_1330_);
lean_ctor_set(v_reuseFailAlloc_1354_, 3, v_rootDir_x3f_1333_);
lean_ctor_set(v_reuseFailAlloc_1354_, 4, v_setupFileName_x3f_1334_);
lean_ctor_set(v_reuseFailAlloc_1354_, 5, v_oleanFileName_x3f_1335_);
lean_ctor_set(v_reuseFailAlloc_1354_, 6, v_ileanFileName_x3f_1336_);
lean_ctor_set(v_reuseFailAlloc_1354_, 7, v_cFileName_x3f_1337_);
lean_ctor_set(v_reuseFailAlloc_1354_, 8, v_bcFileName_x3f_1338_);
lean_ctor_set(v_reuseFailAlloc_1354_, 9, v_errorOnKinds_1340_);
lean_ctor_set(v_reuseFailAlloc_1354_, 10, v_incrSaveFileName_x3f_1343_);
lean_ctor_set(v_reuseFailAlloc_1354_, 11, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1354_, 12, v_incrHeaderSaveFileName_x3f_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*13 + 8, v_component_1323_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*13 + 9, v_printPrefix_1324_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*13 + 10, v_printLibDir_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*13 + 11, v_useStdin_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*13 + 12, v_onlyDeps_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*13 + 13, v_onlySrcDeps_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*13 + 14, v_depsJson_1329_);
lean_ctor_set_uint32(v_reuseFailAlloc_1354_, sizeof(void*)*13, v_trustLevel_1331_);
lean_ctor_set_uint32(v_reuseFailAlloc_1354_, sizeof(void*)*13 + 4, v_numThreads_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*13 + 15, v_jsonOutput_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*13 + 16, v_printStats_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, sizeof(void*)*13 + 17, v_run_1342_);
v___x_1350_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1350_);
v___x_1352_ = v___x_1319_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec_ref(v_opts_968_);
v_a_1358_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1362_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1363_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1362_);
lean_dec_ref(v___x_1363_);
goto v___jp_1359_;
v___jp_1359_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_io_error_to_string(v_a_1358_);
v___x_1361_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1360_);
lean_dec_ref(v___x_1361_);
goto v___jp_1102_;
}
}
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1365_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1364_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1406_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1406_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1406_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_leanOpts_1370_; lean_object* v_forwardedArgs_1371_; uint8_t v_component_1372_; uint8_t v_printPrefix_1373_; uint8_t v_printLibDir_1374_; uint8_t v_useStdin_1375_; uint8_t v_onlyDeps_1376_; uint8_t v_onlySrcDeps_1377_; uint8_t v_depsJson_1378_; lean_object* v_opts_1379_; uint32_t v_trustLevel_1380_; uint32_t v_numThreads_1381_; lean_object* v_rootDir_x3f_1382_; lean_object* v_setupFileName_x3f_1383_; lean_object* v_oleanFileName_x3f_1384_; lean_object* v_ileanFileName_x3f_1385_; lean_object* v_cFileName_x3f_1386_; lean_object* v_bcFileName_x3f_1387_; uint8_t v_jsonOutput_1388_; lean_object* v_errorOnKinds_1389_; uint8_t v_printStats_1390_; uint8_t v_run_1391_; lean_object* v_incrLoadFileName_x3f_1392_; lean_object* v_incrHeaderSaveFileName_x3f_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1404_; 
v_leanOpts_1370_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1371_ = lean_ctor_get(v_opts_968_, 1);
v_component_1372_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1373_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1374_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1375_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1376_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1377_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1378_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1379_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1380_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1381_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1382_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1383_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1384_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1385_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1386_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1387_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1388_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1389_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1390_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1391_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrLoadFileName_x3f_1392_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1393_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1404_ == 0)
{
lean_object* v_unused_1405_; 
v_unused_1405_ = lean_ctor_get(v_opts_968_, 10);
lean_dec(v_unused_1405_);
v___x_1395_ = v_opts_968_;
v_isShared_1396_ = v_isSharedCheck_1404_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1393_);
lean_inc(v_incrLoadFileName_x3f_1392_);
lean_inc(v_errorOnKinds_1389_);
lean_inc(v_bcFileName_x3f_1387_);
lean_inc(v_cFileName_x3f_1386_);
lean_inc(v_ileanFileName_x3f_1385_);
lean_inc(v_oleanFileName_x3f_1384_);
lean_inc(v_setupFileName_x3f_1383_);
lean_inc(v_rootDir_x3f_1382_);
lean_inc(v_opts_1379_);
lean_inc(v_forwardedArgs_1371_);
lean_inc(v_leanOpts_1370_);
lean_dec(v_opts_968_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1404_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_a_1366_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 10, v___x_1397_);
v___x_1399_ = v___x_1395_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_leanOpts_1370_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_forwardedArgs_1371_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_opts_1379_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v_rootDir_x3f_1382_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v_setupFileName_x3f_1383_);
lean_ctor_set(v_reuseFailAlloc_1403_, 5, v_oleanFileName_x3f_1384_);
lean_ctor_set(v_reuseFailAlloc_1403_, 6, v_ileanFileName_x3f_1385_);
lean_ctor_set(v_reuseFailAlloc_1403_, 7, v_cFileName_x3f_1386_);
lean_ctor_set(v_reuseFailAlloc_1403_, 8, v_bcFileName_x3f_1387_);
lean_ctor_set(v_reuseFailAlloc_1403_, 9, v_errorOnKinds_1389_);
lean_ctor_set(v_reuseFailAlloc_1403_, 10, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1403_, 11, v_incrLoadFileName_x3f_1392_);
lean_ctor_set(v_reuseFailAlloc_1403_, 12, v_incrHeaderSaveFileName_x3f_1393_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 8, v_component_1372_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 9, v_printPrefix_1373_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 10, v_printLibDir_1374_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 11, v_useStdin_1375_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 12, v_onlyDeps_1376_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 13, v_onlySrcDeps_1377_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 14, v_depsJson_1378_);
lean_ctor_set_uint32(v_reuseFailAlloc_1403_, sizeof(void*)*13, v_trustLevel_1380_);
lean_ctor_set_uint32(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 4, v_numThreads_1381_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 15, v_jsonOutput_1388_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 16, v_printStats_1390_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 17, v_run_1391_);
v___x_1399_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1401_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1399_);
v___x_1401_ = v___x_1368_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec_ref(v_opts_968_);
v_a_1407_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1365_, 1);
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
goto v___jp_1062_;
}
}
}
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1414_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1413_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1456_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1456_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1456_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_leanOpts_1419_; lean_object* v_forwardedArgs_1420_; uint8_t v_component_1421_; uint8_t v_printPrefix_1422_; uint8_t v_printLibDir_1423_; uint8_t v_useStdin_1424_; uint8_t v_onlyDeps_1425_; uint8_t v_onlySrcDeps_1426_; uint8_t v_depsJson_1427_; lean_object* v_opts_1428_; uint32_t v_trustLevel_1429_; uint32_t v_numThreads_1430_; lean_object* v_rootDir_x3f_1431_; lean_object* v_setupFileName_x3f_1432_; lean_object* v_oleanFileName_x3f_1433_; lean_object* v_ileanFileName_x3f_1434_; lean_object* v_cFileName_x3f_1435_; lean_object* v_bcFileName_x3f_1436_; uint8_t v_jsonOutput_1437_; lean_object* v_errorOnKinds_1438_; uint8_t v_printStats_1439_; uint8_t v_run_1440_; lean_object* v_incrSaveFileName_x3f_1441_; lean_object* v_incrLoadFileName_x3f_1442_; lean_object* v_incrHeaderSaveFileName_x3f_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1455_; 
v_leanOpts_1419_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1420_ = lean_ctor_get(v_opts_968_, 1);
v_component_1421_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1422_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1423_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1424_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1425_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1426_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1427_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1428_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1429_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1430_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1431_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1432_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1433_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1434_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1435_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1436_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1437_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1438_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1439_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1440_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1441_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1442_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1443_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1445_ = v_opts_968_;
v_isShared_1446_ = v_isSharedCheck_1455_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1443_);
lean_inc(v_incrLoadFileName_x3f_1442_);
lean_inc(v_incrSaveFileName_x3f_1441_);
lean_inc(v_errorOnKinds_1438_);
lean_inc(v_bcFileName_x3f_1436_);
lean_inc(v_cFileName_x3f_1435_);
lean_inc(v_ileanFileName_x3f_1434_);
lean_inc(v_oleanFileName_x3f_1433_);
lean_inc(v_setupFileName_x3f_1432_);
lean_inc(v_rootDir_x3f_1431_);
lean_inc(v_opts_1428_);
lean_inc(v_forwardedArgs_1420_);
lean_inc(v_leanOpts_1419_);
lean_dec(v_opts_968_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1455_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1447_ = l_String_toName(v_a_1415_);
v___x_1448_ = lean_array_push(v_errorOnKinds_1438_, v___x_1447_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 9, v___x_1448_);
v___x_1450_ = v___x_1445_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_leanOpts_1419_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_forwardedArgs_1420_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_opts_1428_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v_rootDir_x3f_1431_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v_setupFileName_x3f_1432_);
lean_ctor_set(v_reuseFailAlloc_1454_, 5, v_oleanFileName_x3f_1433_);
lean_ctor_set(v_reuseFailAlloc_1454_, 6, v_ileanFileName_x3f_1434_);
lean_ctor_set(v_reuseFailAlloc_1454_, 7, v_cFileName_x3f_1435_);
lean_ctor_set(v_reuseFailAlloc_1454_, 8, v_bcFileName_x3f_1436_);
lean_ctor_set(v_reuseFailAlloc_1454_, 9, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1454_, 10, v_incrSaveFileName_x3f_1441_);
lean_ctor_set(v_reuseFailAlloc_1454_, 11, v_incrLoadFileName_x3f_1442_);
lean_ctor_set(v_reuseFailAlloc_1454_, 12, v_incrHeaderSaveFileName_x3f_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*13 + 8, v_component_1421_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*13 + 9, v_printPrefix_1422_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*13 + 10, v_printLibDir_1423_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*13 + 11, v_useStdin_1424_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*13 + 12, v_onlyDeps_1425_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*13 + 13, v_onlySrcDeps_1426_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*13 + 14, v_depsJson_1427_);
lean_ctor_set_uint32(v_reuseFailAlloc_1454_, sizeof(void*)*13, v_trustLevel_1429_);
lean_ctor_set_uint32(v_reuseFailAlloc_1454_, sizeof(void*)*13 + 4, v_numThreads_1430_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*13 + 15, v_jsonOutput_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*13 + 16, v_printStats_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*13 + 17, v_run_1440_);
v___x_1450_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1450_);
v___x_1452_ = v___x_1417_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref(v_opts_968_);
v_a_1457_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1461_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1462_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1461_);
lean_dec_ref(v___x_1462_);
goto v___jp_1458_;
v___jp_1458_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_io_error_to_string(v_a_1457_);
v___x_1460_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1459_);
lean_dec_ref(v___x_1460_);
goto v___jp_1108_;
}
}
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1464_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1463_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1505_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1505_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1505_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v_leanOpts_1469_; lean_object* v_forwardedArgs_1470_; uint8_t v_component_1471_; uint8_t v_printPrefix_1472_; uint8_t v_printLibDir_1473_; uint8_t v_useStdin_1474_; uint8_t v_onlyDeps_1475_; uint8_t v_onlySrcDeps_1476_; uint8_t v_depsJson_1477_; lean_object* v_opts_1478_; uint32_t v_trustLevel_1479_; uint32_t v_numThreads_1480_; lean_object* v_rootDir_x3f_1481_; lean_object* v_oleanFileName_x3f_1482_; lean_object* v_ileanFileName_x3f_1483_; lean_object* v_cFileName_x3f_1484_; lean_object* v_bcFileName_x3f_1485_; uint8_t v_jsonOutput_1486_; lean_object* v_errorOnKinds_1487_; uint8_t v_printStats_1488_; uint8_t v_run_1489_; lean_object* v_incrSaveFileName_x3f_1490_; lean_object* v_incrLoadFileName_x3f_1491_; lean_object* v_incrHeaderSaveFileName_x3f_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1503_; 
v_leanOpts_1469_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1470_ = lean_ctor_get(v_opts_968_, 1);
v_component_1471_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1472_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1473_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1474_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1475_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1476_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1477_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1478_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1479_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1480_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1481_ = lean_ctor_get(v_opts_968_, 3);
v_oleanFileName_x3f_1482_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1483_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1484_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1485_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1486_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1487_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1488_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1489_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1490_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1491_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1492_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v_opts_968_, 4);
lean_dec(v_unused_1504_);
v___x_1494_ = v_opts_968_;
v_isShared_1495_ = v_isSharedCheck_1503_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1492_);
lean_inc(v_incrLoadFileName_x3f_1491_);
lean_inc(v_incrSaveFileName_x3f_1490_);
lean_inc(v_errorOnKinds_1487_);
lean_inc(v_bcFileName_x3f_1485_);
lean_inc(v_cFileName_x3f_1484_);
lean_inc(v_ileanFileName_x3f_1483_);
lean_inc(v_oleanFileName_x3f_1482_);
lean_inc(v_rootDir_x3f_1481_);
lean_inc(v_opts_1478_);
lean_inc(v_forwardedArgs_1470_);
lean_inc(v_leanOpts_1469_);
lean_dec(v_opts_968_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1503_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1496_, 0, v_a_1465_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 4, v___x_1496_);
v___x_1498_ = v___x_1494_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_leanOpts_1469_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_forwardedArgs_1470_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_opts_1478_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_rootDir_x3f_1481_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1502_, 5, v_oleanFileName_x3f_1482_);
lean_ctor_set(v_reuseFailAlloc_1502_, 6, v_ileanFileName_x3f_1483_);
lean_ctor_set(v_reuseFailAlloc_1502_, 7, v_cFileName_x3f_1484_);
lean_ctor_set(v_reuseFailAlloc_1502_, 8, v_bcFileName_x3f_1485_);
lean_ctor_set(v_reuseFailAlloc_1502_, 9, v_errorOnKinds_1487_);
lean_ctor_set(v_reuseFailAlloc_1502_, 10, v_incrSaveFileName_x3f_1490_);
lean_ctor_set(v_reuseFailAlloc_1502_, 11, v_incrLoadFileName_x3f_1491_);
lean_ctor_set(v_reuseFailAlloc_1502_, 12, v_incrHeaderSaveFileName_x3f_1492_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*13 + 8, v_component_1471_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*13 + 9, v_printPrefix_1472_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*13 + 10, v_printLibDir_1473_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*13 + 11, v_useStdin_1474_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*13 + 12, v_onlyDeps_1475_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*13 + 13, v_onlySrcDeps_1476_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*13 + 14, v_depsJson_1477_);
lean_ctor_set_uint32(v_reuseFailAlloc_1502_, sizeof(void*)*13, v_trustLevel_1479_);
lean_ctor_set_uint32(v_reuseFailAlloc_1502_, sizeof(void*)*13 + 4, v_numThreads_1480_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*13 + 15, v_jsonOutput_1486_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*13 + 16, v_printStats_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*13 + 17, v_run_1489_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1498_);
v___x_1500_ = v___x_1467_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v_opts_968_);
v_a_1506_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1464_, 1);
v___x_1510_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1511_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1510_);
lean_dec_ref(v___x_1511_);
goto v___jp_1507_;
v___jp_1507_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_io_error_to_string(v_a_1506_);
v___x_1509_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1508_);
lean_dec_ref(v___x_1509_);
goto v___jp_1056_;
}
}
}
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1513_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1512_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc_n(v_a_1514_, 2);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1515_ = lean_load_dynlib(v_a_1514_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1557_; 
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; 
v_unused_1558_ = lean_ctor_get(v___x_1515_, 0);
lean_dec(v_unused_1558_);
v___x_1517_ = v___x_1515_;
v_isShared_1518_ = v_isSharedCheck_1557_;
goto v_resetjp_1516_;
}
else
{
lean_dec(v___x_1515_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1557_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v_leanOpts_1519_; lean_object* v_forwardedArgs_1520_; uint8_t v_component_1521_; uint8_t v_printPrefix_1522_; uint8_t v_printLibDir_1523_; uint8_t v_useStdin_1524_; uint8_t v_onlyDeps_1525_; uint8_t v_onlySrcDeps_1526_; uint8_t v_depsJson_1527_; lean_object* v_opts_1528_; uint32_t v_trustLevel_1529_; uint32_t v_numThreads_1530_; lean_object* v_rootDir_x3f_1531_; lean_object* v_setupFileName_x3f_1532_; lean_object* v_oleanFileName_x3f_1533_; lean_object* v_ileanFileName_x3f_1534_; lean_object* v_cFileName_x3f_1535_; lean_object* v_bcFileName_x3f_1536_; uint8_t v_jsonOutput_1537_; lean_object* v_errorOnKinds_1538_; uint8_t v_printStats_1539_; uint8_t v_run_1540_; lean_object* v_incrSaveFileName_x3f_1541_; lean_object* v_incrLoadFileName_x3f_1542_; lean_object* v_incrHeaderSaveFileName_x3f_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1556_; 
v_leanOpts_1519_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1520_ = lean_ctor_get(v_opts_968_, 1);
v_component_1521_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1522_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1523_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1524_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1525_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1526_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1527_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1528_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1529_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1530_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1531_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1532_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1533_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1534_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1535_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1536_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1537_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1538_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1539_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1540_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1541_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1542_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1543_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1545_ = v_opts_968_;
v_isShared_1546_ = v_isSharedCheck_1556_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1543_);
lean_inc(v_incrLoadFileName_x3f_1542_);
lean_inc(v_incrSaveFileName_x3f_1541_);
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
lean_dec(v_opts_968_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1556_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1547_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1548_ = lean_string_append(v___x_1547_, v_a_1514_);
lean_dec(v_a_1514_);
v___x_1549_ = lean_array_push(v_forwardedArgs_1520_, v___x_1548_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 1, v___x_1549_);
v___x_1551_ = v___x_1545_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_leanOpts_1519_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_opts_1528_);
lean_ctor_set(v_reuseFailAlloc_1555_, 3, v_rootDir_x3f_1531_);
lean_ctor_set(v_reuseFailAlloc_1555_, 4, v_setupFileName_x3f_1532_);
lean_ctor_set(v_reuseFailAlloc_1555_, 5, v_oleanFileName_x3f_1533_);
lean_ctor_set(v_reuseFailAlloc_1555_, 6, v_ileanFileName_x3f_1534_);
lean_ctor_set(v_reuseFailAlloc_1555_, 7, v_cFileName_x3f_1535_);
lean_ctor_set(v_reuseFailAlloc_1555_, 8, v_bcFileName_x3f_1536_);
lean_ctor_set(v_reuseFailAlloc_1555_, 9, v_errorOnKinds_1538_);
lean_ctor_set(v_reuseFailAlloc_1555_, 10, v_incrSaveFileName_x3f_1541_);
lean_ctor_set(v_reuseFailAlloc_1555_, 11, v_incrLoadFileName_x3f_1542_);
lean_ctor_set(v_reuseFailAlloc_1555_, 12, v_incrHeaderSaveFileName_x3f_1543_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*13 + 8, v_component_1521_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*13 + 9, v_printPrefix_1522_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*13 + 10, v_printLibDir_1523_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*13 + 11, v_useStdin_1524_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*13 + 12, v_onlyDeps_1525_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*13 + 13, v_onlySrcDeps_1526_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*13 + 14, v_depsJson_1527_);
lean_ctor_set_uint32(v_reuseFailAlloc_1555_, sizeof(void*)*13, v_trustLevel_1529_);
lean_ctor_set_uint32(v_reuseFailAlloc_1555_, sizeof(void*)*13 + 4, v_numThreads_1530_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*13 + 15, v_jsonOutput_1537_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*13 + 16, v_printStats_1539_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*13 + 17, v_run_1540_);
v___x_1551_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1553_; 
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1551_);
v___x_1553_ = v___x_1517_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec(v_a_1514_);
lean_dec_ref(v_opts_968_);
v_a_1559_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1515_, 1);
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
goto v___jp_1114_;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_dec_ref(v_opts_968_);
v_a_1565_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1569_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1570_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1569_);
lean_dec_ref(v___x_1570_);
goto v___jp_1566_;
v___jp_1566_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = lean_io_error_to_string(v_a_1565_);
v___x_1568_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1567_);
lean_dec_ref(v___x_1568_);
goto v___jp_1120_;
}
}
}
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1572_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1571_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1644_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1644_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1644_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v_fst_1578_; lean_object* v_snd_1579_; lean_object* v___y_1628_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = lean_string_utf8_byte_size(v_a_1573_);
v___x_1641_ = lean_box(0);
v___x_1642_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_1640_, v_a_1573_, v___x_1639_, v___x_1641_);
if (lean_obj_tag(v___x_1642_) == 0)
{
v___y_1628_ = v___x_1640_;
goto v___jp_1627_;
}
else
{
lean_object* v_val_1643_; 
v_val_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_val_1643_);
lean_dec_ref_known(v___x_1642_, 1);
v___y_1628_ = v_val_1643_;
goto v___jp_1627_;
}
v___jp_1577_:
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_load_plugin(v_fst_1578_, v_snd_1579_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1622_; 
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; 
v_unused_1623_ = lean_ctor_get(v___x_1580_, 0);
lean_dec(v_unused_1623_);
v___x_1582_ = v___x_1580_;
v_isShared_1583_ = v_isSharedCheck_1622_;
goto v_resetjp_1581_;
}
else
{
lean_dec(v___x_1580_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1622_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v_leanOpts_1584_; lean_object* v_forwardedArgs_1585_; uint8_t v_component_1586_; uint8_t v_printPrefix_1587_; uint8_t v_printLibDir_1588_; uint8_t v_useStdin_1589_; uint8_t v_onlyDeps_1590_; uint8_t v_onlySrcDeps_1591_; uint8_t v_depsJson_1592_; lean_object* v_opts_1593_; uint32_t v_trustLevel_1594_; uint32_t v_numThreads_1595_; lean_object* v_rootDir_x3f_1596_; lean_object* v_setupFileName_x3f_1597_; lean_object* v_oleanFileName_x3f_1598_; lean_object* v_ileanFileName_x3f_1599_; lean_object* v_cFileName_x3f_1600_; lean_object* v_bcFileName_x3f_1601_; uint8_t v_jsonOutput_1602_; lean_object* v_errorOnKinds_1603_; uint8_t v_printStats_1604_; uint8_t v_run_1605_; lean_object* v_incrSaveFileName_x3f_1606_; lean_object* v_incrLoadFileName_x3f_1607_; lean_object* v_incrHeaderSaveFileName_x3f_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1621_; 
v_leanOpts_1584_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1585_ = lean_ctor_get(v_opts_968_, 1);
v_component_1586_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1587_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1588_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1589_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1590_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1591_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1592_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1593_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1594_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1595_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1596_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1597_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1598_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1599_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1600_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1601_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1602_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1603_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1604_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1605_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1606_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1607_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1608_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1610_ = v_opts_968_;
v_isShared_1611_ = v_isSharedCheck_1621_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1608_);
lean_inc(v_incrLoadFileName_x3f_1607_);
lean_inc(v_incrSaveFileName_x3f_1606_);
lean_inc(v_errorOnKinds_1603_);
lean_inc(v_bcFileName_x3f_1601_);
lean_inc(v_cFileName_x3f_1600_);
lean_inc(v_ileanFileName_x3f_1599_);
lean_inc(v_oleanFileName_x3f_1598_);
lean_inc(v_setupFileName_x3f_1597_);
lean_inc(v_rootDir_x3f_1596_);
lean_inc(v_opts_1593_);
lean_inc(v_forwardedArgs_1585_);
lean_inc(v_leanOpts_1584_);
lean_dec(v_opts_968_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1621_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1612_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1613_ = lean_string_append(v___x_1612_, v_a_1573_);
lean_dec(v_a_1573_);
v___x_1614_ = lean_array_push(v_forwardedArgs_1585_, v___x_1613_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 1, v___x_1614_);
v___x_1616_ = v___x_1610_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_leanOpts_1584_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_opts_1593_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v_rootDir_x3f_1596_);
lean_ctor_set(v_reuseFailAlloc_1620_, 4, v_setupFileName_x3f_1597_);
lean_ctor_set(v_reuseFailAlloc_1620_, 5, v_oleanFileName_x3f_1598_);
lean_ctor_set(v_reuseFailAlloc_1620_, 6, v_ileanFileName_x3f_1599_);
lean_ctor_set(v_reuseFailAlloc_1620_, 7, v_cFileName_x3f_1600_);
lean_ctor_set(v_reuseFailAlloc_1620_, 8, v_bcFileName_x3f_1601_);
lean_ctor_set(v_reuseFailAlloc_1620_, 9, v_errorOnKinds_1603_);
lean_ctor_set(v_reuseFailAlloc_1620_, 10, v_incrSaveFileName_x3f_1606_);
lean_ctor_set(v_reuseFailAlloc_1620_, 11, v_incrLoadFileName_x3f_1607_);
lean_ctor_set(v_reuseFailAlloc_1620_, 12, v_incrHeaderSaveFileName_x3f_1608_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*13 + 8, v_component_1586_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*13 + 9, v_printPrefix_1587_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*13 + 10, v_printLibDir_1588_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*13 + 11, v_useStdin_1589_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*13 + 12, v_onlyDeps_1590_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*13 + 13, v_onlySrcDeps_1591_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*13 + 14, v_depsJson_1592_);
lean_ctor_set_uint32(v_reuseFailAlloc_1620_, sizeof(void*)*13, v_trustLevel_1594_);
lean_ctor_set_uint32(v_reuseFailAlloc_1620_, sizeof(void*)*13 + 4, v_numThreads_1595_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*13 + 15, v_jsonOutput_1602_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*13 + 16, v_printStats_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*13 + 17, v_run_1605_);
v___x_1616_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1618_; 
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1616_);
v___x_1618_ = v___x_1582_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
lean_dec(v_a_1573_);
lean_dec_ref(v_opts_968_);
v_a_1624_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1580_, 1);
v___x_1625_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1626_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1625_);
lean_dec_ref(v___x_1626_);
v___y_1136_ = v_a_1624_;
goto v___jp_1135_;
}
}
v___jp_1627_:
{
lean_object* v___x_1629_; uint8_t v_decide_1630_; 
v___x_1629_ = lean_string_utf8_byte_size(v_a_1573_);
v_decide_1630_ = lean_nat_dec_eq(v___y_1628_, v___x_1629_);
if (v_decide_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = lean_string_utf8_next_fast(v_a_1573_, v___y_1628_);
v___x_1633_ = lean_string_utf8_extract_fast(v_a_1573_, v___x_1631_, v___y_1628_);
lean_dec(v___y_1628_);
v___x_1634_ = lean_string_utf8_extract_fast(v_a_1573_, v___x_1632_, v___x_1629_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 1);
lean_ctor_set(v___x_1575_, 0, v___x_1634_);
v___x_1636_ = v___x_1575_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
v_fst_1578_ = v___x_1633_;
v_snd_1579_ = v___x_1636_;
goto v___jp_1577_;
}
}
else
{
lean_object* v___x_1638_; 
lean_dec(v___y_1628_);
lean_del_object(v___x_1575_);
v___x_1638_ = lean_box(0);
lean_inc(v_a_1573_);
v_fst_1578_ = v_a_1573_;
v_snd_1579_ = v___x_1638_;
goto v___jp_1577_;
}
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec_ref(v_opts_968_);
v_a_1645_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1572_, 1);
v___x_1649_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1650_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1649_);
lean_dec_ref(v___x_1650_);
goto v___jp_1646_;
v___jp_1646_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_io_error_to_string(v_a_1645_);
v___x_1648_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1647_);
lean_dec_ref(v___x_1648_);
goto v___jp_1132_;
}
}
}
}
else
{
uint8_t v___x_1651_; 
v___x_1651_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__16, &l___private_Lean_Shell_0__Lean_displayHelp___closed__16_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
if (v___x_1651_ == 0)
{
lean_dec(v_optArg_x3f_970_);
lean_dec_ref(v_opts_968_);
goto v___jp_1096_;
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1653_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1652_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1662_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = lean_internal_enable_debug(v_a_1654_);
lean_dec(v_a_1654_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v_opts_968_);
v___x_1660_ = v___x_1656_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_opts_968_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec_ref(v_opts_968_);
v_a_1663_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1653_, 1);
v___x_1667_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1668_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1667_);
lean_dec_ref(v___x_1668_);
goto v___jp_1664_;
v___jp_1664_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_io_error_to_string(v_a_1663_);
v___x_1666_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1665_);
lean_dec_ref(v___x_1666_);
goto v___jp_1142_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1669_; lean_object* v_forwardedArgs_1670_; uint8_t v_component_1671_; uint8_t v_printPrefix_1672_; uint8_t v_printLibDir_1673_; uint8_t v_useStdin_1674_; uint8_t v_onlyDeps_1675_; uint8_t v_onlySrcDeps_1676_; uint8_t v_depsJson_1677_; lean_object* v_opts_1678_; uint32_t v_trustLevel_1679_; uint32_t v_numThreads_1680_; lean_object* v_rootDir_x3f_1681_; lean_object* v_setupFileName_x3f_1682_; lean_object* v_oleanFileName_x3f_1683_; lean_object* v_ileanFileName_x3f_1684_; lean_object* v_cFileName_x3f_1685_; lean_object* v_bcFileName_x3f_1686_; uint8_t v_jsonOutput_1687_; lean_object* v_errorOnKinds_1688_; uint8_t v_printStats_1689_; uint8_t v_run_1690_; lean_object* v_incrSaveFileName_x3f_1691_; lean_object* v_incrLoadFileName_x3f_1692_; lean_object* v_incrHeaderSaveFileName_x3f_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_optArg_x3f_970_);
v_leanOpts_1669_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1670_ = lean_ctor_get(v_opts_968_, 1);
v_component_1671_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1672_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1673_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1674_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1675_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1676_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1677_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1678_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1679_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1680_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1681_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1682_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1683_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1684_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1685_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1686_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1687_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1688_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1689_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1690_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1691_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1692_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1693_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1695_ = v_opts_968_;
v_isShared_1696_ = v_isSharedCheck_1703_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1693_);
lean_inc(v_incrLoadFileName_x3f_1692_);
lean_inc(v_incrSaveFileName_x3f_1691_);
lean_inc(v_errorOnKinds_1688_);
lean_inc(v_bcFileName_x3f_1686_);
lean_inc(v_cFileName_x3f_1685_);
lean_inc(v_ileanFileName_x3f_1684_);
lean_inc(v_oleanFileName_x3f_1683_);
lean_inc(v_setupFileName_x3f_1682_);
lean_inc(v_rootDir_x3f_1681_);
lean_inc(v_opts_1678_);
lean_inc(v_forwardedArgs_1670_);
lean_inc(v_leanOpts_1669_);
lean_dec(v_opts_968_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1703_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1697_ = l_Lean_profiler;
v___x_1698_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1669_, v___x_1697_, v___x_1249_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1698_);
v___x_1700_ = v___x_1695_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_forwardedArgs_1670_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v_opts_1678_);
lean_ctor_set(v_reuseFailAlloc_1702_, 3, v_rootDir_x3f_1681_);
lean_ctor_set(v_reuseFailAlloc_1702_, 4, v_setupFileName_x3f_1682_);
lean_ctor_set(v_reuseFailAlloc_1702_, 5, v_oleanFileName_x3f_1683_);
lean_ctor_set(v_reuseFailAlloc_1702_, 6, v_ileanFileName_x3f_1684_);
lean_ctor_set(v_reuseFailAlloc_1702_, 7, v_cFileName_x3f_1685_);
lean_ctor_set(v_reuseFailAlloc_1702_, 8, v_bcFileName_x3f_1686_);
lean_ctor_set(v_reuseFailAlloc_1702_, 9, v_errorOnKinds_1688_);
lean_ctor_set(v_reuseFailAlloc_1702_, 10, v_incrSaveFileName_x3f_1691_);
lean_ctor_set(v_reuseFailAlloc_1702_, 11, v_incrLoadFileName_x3f_1692_);
lean_ctor_set(v_reuseFailAlloc_1702_, 12, v_incrHeaderSaveFileName_x3f_1693_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 8, v_component_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 9, v_printPrefix_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 10, v_printLibDir_1673_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 11, v_useStdin_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 12, v_onlyDeps_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 13, v_onlySrcDeps_1676_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 14, v_depsJson_1677_);
lean_ctor_set_uint32(v_reuseFailAlloc_1702_, sizeof(void*)*13, v_trustLevel_1679_);
lean_ctor_set_uint32(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 4, v_numThreads_1680_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 15, v_jsonOutput_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 16, v_printStats_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*13 + 17, v_run_1690_);
v___x_1700_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1701_; 
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
lean_dec(v_optArg_x3f_970_);
v_leanOpts_1704_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1705_ = lean_ctor_get(v_opts_968_, 1);
v_printPrefix_1706_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1707_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1708_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1709_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1710_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1711_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1712_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1713_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1714_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1715_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1716_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1717_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1718_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1719_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1720_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1721_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1722_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1723_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1724_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1725_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1726_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1727_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1729_ = v_opts_968_;
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
lean_dec(v_opts_968_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1736_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
uint8_t v___x_1731_; lean_object* v___x_1733_; 
v___x_1731_ = 2;
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
lean_object* v_leanOpts_1737_; lean_object* v_forwardedArgs_1738_; uint8_t v_printPrefix_1739_; uint8_t v_printLibDir_1740_; uint8_t v_useStdin_1741_; uint8_t v_onlyDeps_1742_; uint8_t v_onlySrcDeps_1743_; uint8_t v_depsJson_1744_; lean_object* v_opts_1745_; uint32_t v_trustLevel_1746_; uint32_t v_numThreads_1747_; lean_object* v_rootDir_x3f_1748_; lean_object* v_setupFileName_x3f_1749_; lean_object* v_oleanFileName_x3f_1750_; lean_object* v_ileanFileName_x3f_1751_; lean_object* v_cFileName_x3f_1752_; lean_object* v_bcFileName_x3f_1753_; uint8_t v_jsonOutput_1754_; lean_object* v_errorOnKinds_1755_; uint8_t v_printStats_1756_; uint8_t v_run_1757_; lean_object* v_incrSaveFileName_x3f_1758_; lean_object* v_incrLoadFileName_x3f_1759_; lean_object* v_incrHeaderSaveFileName_x3f_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_optArg_x3f_970_);
v_leanOpts_1737_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1738_ = lean_ctor_get(v_opts_968_, 1);
v_printPrefix_1739_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1740_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1741_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1742_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1743_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1744_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1745_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1746_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1747_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1748_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1749_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1750_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1751_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1752_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1753_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1754_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1755_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1756_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1757_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1758_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1759_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1760_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1762_ = v_opts_968_;
v_isShared_1763_ = v_isSharedCheck_1769_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1760_);
lean_inc(v_incrLoadFileName_x3f_1759_);
lean_inc(v_incrSaveFileName_x3f_1758_);
lean_inc(v_errorOnKinds_1755_);
lean_inc(v_bcFileName_x3f_1753_);
lean_inc(v_cFileName_x3f_1752_);
lean_inc(v_ileanFileName_x3f_1751_);
lean_inc(v_oleanFileName_x3f_1750_);
lean_inc(v_setupFileName_x3f_1749_);
lean_inc(v_rootDir_x3f_1748_);
lean_inc(v_opts_1745_);
lean_inc(v_forwardedArgs_1738_);
lean_inc(v_leanOpts_1737_);
lean_dec(v_opts_968_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1769_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
uint8_t v___x_1764_; lean_object* v___x_1766_; 
v___x_1764_ = 1;
if (v_isShared_1763_ == 0)
{
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_leanOpts_1737_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_forwardedArgs_1738_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_opts_1745_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_rootDir_x3f_1748_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v_setupFileName_x3f_1749_);
lean_ctor_set(v_reuseFailAlloc_1768_, 5, v_oleanFileName_x3f_1750_);
lean_ctor_set(v_reuseFailAlloc_1768_, 6, v_ileanFileName_x3f_1751_);
lean_ctor_set(v_reuseFailAlloc_1768_, 7, v_cFileName_x3f_1752_);
lean_ctor_set(v_reuseFailAlloc_1768_, 8, v_bcFileName_x3f_1753_);
lean_ctor_set(v_reuseFailAlloc_1768_, 9, v_errorOnKinds_1755_);
lean_ctor_set(v_reuseFailAlloc_1768_, 10, v_incrSaveFileName_x3f_1758_);
lean_ctor_set(v_reuseFailAlloc_1768_, 11, v_incrLoadFileName_x3f_1759_);
lean_ctor_set(v_reuseFailAlloc_1768_, 12, v_incrHeaderSaveFileName_x3f_1760_);
lean_ctor_set_uint8(v_reuseFailAlloc_1768_, sizeof(void*)*13 + 9, v_printPrefix_1739_);
lean_ctor_set_uint8(v_reuseFailAlloc_1768_, sizeof(void*)*13 + 10, v_printLibDir_1740_);
lean_ctor_set_uint8(v_reuseFailAlloc_1768_, sizeof(void*)*13 + 11, v_useStdin_1741_);
lean_ctor_set_uint8(v_reuseFailAlloc_1768_, sizeof(void*)*13 + 12, v_onlyDeps_1742_);
lean_ctor_set_uint8(v_reuseFailAlloc_1768_, sizeof(void*)*13 + 13, v_onlySrcDeps_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1768_, sizeof(void*)*13 + 14, v_depsJson_1744_);
lean_ctor_set_uint32(v_reuseFailAlloc_1768_, sizeof(void*)*13, v_trustLevel_1746_);
lean_ctor_set_uint32(v_reuseFailAlloc_1768_, sizeof(void*)*13 + 4, v_numThreads_1747_);
lean_ctor_set_uint8(v_reuseFailAlloc_1768_, sizeof(void*)*13 + 15, v_jsonOutput_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1768_, sizeof(void*)*13 + 16, v_printStats_1756_);
lean_ctor_set_uint8(v_reuseFailAlloc_1768_, sizeof(void*)*13 + 17, v_run_1757_);
v___x_1766_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1767_; 
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*13 + 8, v___x_1764_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
}
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1771_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1770_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v_leanOpts_1773_; lean_object* v_forwardedArgs_1774_; uint8_t v_component_1775_; uint8_t v_printPrefix_1776_; uint8_t v_printLibDir_1777_; uint8_t v_useStdin_1778_; uint8_t v_onlyDeps_1779_; uint8_t v_onlySrcDeps_1780_; uint8_t v_depsJson_1781_; lean_object* v_opts_1782_; uint32_t v_trustLevel_1783_; uint32_t v_numThreads_1784_; lean_object* v_rootDir_x3f_1785_; lean_object* v_setupFileName_x3f_1786_; lean_object* v_oleanFileName_x3f_1787_; lean_object* v_ileanFileName_x3f_1788_; lean_object* v_cFileName_x3f_1789_; lean_object* v_bcFileName_x3f_1790_; uint8_t v_jsonOutput_1791_; lean_object* v_errorOnKinds_1792_; uint8_t v_printStats_1793_; uint8_t v_run_1794_; lean_object* v_incrSaveFileName_x3f_1795_; lean_object* v_incrLoadFileName_x3f_1796_; lean_object* v_incrHeaderSaveFileName_x3f_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1822_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v_leanOpts_1773_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1774_ = lean_ctor_get(v_opts_968_, 1);
v_component_1775_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1776_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1777_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1778_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1779_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1780_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1781_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1782_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1783_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1784_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1785_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1786_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1787_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1788_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1789_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1790_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1791_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1792_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1793_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1794_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1795_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1796_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1797_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1799_ = v_opts_968_;
v_isShared_1800_ = v_isSharedCheck_1822_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1797_);
lean_inc(v_incrLoadFileName_x3f_1796_);
lean_inc(v_incrSaveFileName_x3f_1795_);
lean_inc(v_errorOnKinds_1792_);
lean_inc(v_bcFileName_x3f_1790_);
lean_inc(v_cFileName_x3f_1789_);
lean_inc(v_ileanFileName_x3f_1788_);
lean_inc(v_oleanFileName_x3f_1787_);
lean_inc(v_setupFileName_x3f_1786_);
lean_inc(v_rootDir_x3f_1785_);
lean_inc(v_opts_1782_);
lean_inc(v_forwardedArgs_1774_);
lean_inc(v_leanOpts_1773_);
lean_dec(v_opts_968_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1822_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; 
lean_inc(v_a_1772_);
v___x_1801_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1773_, v_a_1772_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1815_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1815_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1815_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1806_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1807_ = lean_string_append(v___x_1806_, v_a_1772_);
lean_dec(v_a_1772_);
v___x_1808_ = lean_array_push(v_forwardedArgs_1774_, v___x_1807_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v___x_1808_);
lean_ctor_set(v___x_1799_, 0, v_a_1802_);
v___x_1810_ = v___x_1799_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1802_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1814_, 2, v_opts_1782_);
lean_ctor_set(v_reuseFailAlloc_1814_, 3, v_rootDir_x3f_1785_);
lean_ctor_set(v_reuseFailAlloc_1814_, 4, v_setupFileName_x3f_1786_);
lean_ctor_set(v_reuseFailAlloc_1814_, 5, v_oleanFileName_x3f_1787_);
lean_ctor_set(v_reuseFailAlloc_1814_, 6, v_ileanFileName_x3f_1788_);
lean_ctor_set(v_reuseFailAlloc_1814_, 7, v_cFileName_x3f_1789_);
lean_ctor_set(v_reuseFailAlloc_1814_, 8, v_bcFileName_x3f_1790_);
lean_ctor_set(v_reuseFailAlloc_1814_, 9, v_errorOnKinds_1792_);
lean_ctor_set(v_reuseFailAlloc_1814_, 10, v_incrSaveFileName_x3f_1795_);
lean_ctor_set(v_reuseFailAlloc_1814_, 11, v_incrLoadFileName_x3f_1796_);
lean_ctor_set(v_reuseFailAlloc_1814_, 12, v_incrHeaderSaveFileName_x3f_1797_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*13 + 8, v_component_1775_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*13 + 9, v_printPrefix_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*13 + 10, v_printLibDir_1777_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*13 + 11, v_useStdin_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*13 + 12, v_onlyDeps_1779_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*13 + 13, v_onlySrcDeps_1780_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*13 + 14, v_depsJson_1781_);
lean_ctor_set_uint32(v_reuseFailAlloc_1814_, sizeof(void*)*13, v_trustLevel_1783_);
lean_ctor_set_uint32(v_reuseFailAlloc_1814_, sizeof(void*)*13 + 4, v_numThreads_1784_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*13 + 15, v_jsonOutput_1791_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*13 + 16, v_printStats_1793_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*13 + 17, v_run_1794_);
v___x_1810_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1812_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1810_);
v___x_1812_ = v___x_1804_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_del_object(v___x_1799_);
lean_dec(v_incrHeaderSaveFileName_x3f_1797_);
lean_dec(v_incrLoadFileName_x3f_1796_);
lean_dec(v_incrSaveFileName_x3f_1795_);
lean_dec_ref(v_errorOnKinds_1792_);
lean_dec(v_bcFileName_x3f_1790_);
lean_dec(v_cFileName_x3f_1789_);
lean_dec(v_ileanFileName_x3f_1788_);
lean_dec(v_oleanFileName_x3f_1787_);
lean_dec(v_setupFileName_x3f_1786_);
lean_dec(v_rootDir_x3f_1785_);
lean_dec_ref(v_opts_1782_);
lean_dec_ref(v_forwardedArgs_1774_);
lean_dec(v_a_1772_);
v_a_1816_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1816_);
lean_dec_ref_known(v___x_1801_, 1);
v___x_1820_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1821_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1820_);
lean_dec_ref(v___x_1821_);
goto v___jp_1817_;
v___jp_1817_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = lean_io_error_to_string(v_a_1816_);
v___x_1819_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1818_);
lean_dec_ref(v___x_1819_);
goto v___jp_1044_;
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec_ref(v_opts_968_);
v_a_1823_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1771_, 1);
v___x_1827_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1828_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1827_);
lean_dec_ref(v___x_1828_);
goto v___jp_1824_;
v___jp_1824_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_io_error_to_string(v_a_1823_);
v___x_1826_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1825_);
lean_dec_ref(v___x_1826_);
goto v___jp_1050_;
}
}
}
}
else
{
lean_object* v_leanOpts_1829_; lean_object* v_forwardedArgs_1830_; uint8_t v_component_1831_; uint8_t v_printPrefix_1832_; uint8_t v_useStdin_1833_; uint8_t v_onlyDeps_1834_; uint8_t v_onlySrcDeps_1835_; uint8_t v_depsJson_1836_; lean_object* v_opts_1837_; uint32_t v_trustLevel_1838_; uint32_t v_numThreads_1839_; lean_object* v_rootDir_x3f_1840_; lean_object* v_setupFileName_x3f_1841_; lean_object* v_oleanFileName_x3f_1842_; lean_object* v_ileanFileName_x3f_1843_; lean_object* v_cFileName_x3f_1844_; lean_object* v_bcFileName_x3f_1845_; uint8_t v_jsonOutput_1846_; lean_object* v_errorOnKinds_1847_; uint8_t v_printStats_1848_; uint8_t v_run_1849_; lean_object* v_incrSaveFileName_x3f_1850_; lean_object* v_incrLoadFileName_x3f_1851_; lean_object* v_incrHeaderSaveFileName_x3f_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v_optArg_x3f_970_);
v_leanOpts_1829_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1830_ = lean_ctor_get(v_opts_968_, 1);
v_component_1831_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1832_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_useStdin_1833_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1834_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1835_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1836_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1837_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1838_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1839_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1840_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1841_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1842_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1843_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1844_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1845_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1846_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1847_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1848_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1849_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1850_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1851_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1852_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1854_ = v_opts_968_;
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1852_);
lean_inc(v_incrLoadFileName_x3f_1851_);
lean_inc(v_incrSaveFileName_x3f_1850_);
lean_inc(v_errorOnKinds_1847_);
lean_inc(v_bcFileName_x3f_1845_);
lean_inc(v_cFileName_x3f_1844_);
lean_inc(v_ileanFileName_x3f_1843_);
lean_inc(v_oleanFileName_x3f_1842_);
lean_inc(v_setupFileName_x3f_1841_);
lean_inc(v_rootDir_x3f_1840_);
lean_inc(v_opts_1837_);
lean_inc(v_forwardedArgs_1830_);
lean_inc(v_leanOpts_1829_);
lean_dec(v_opts_968_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_leanOpts_1829_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_forwardedArgs_1830_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_opts_1837_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_rootDir_x3f_1840_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_setupFileName_x3f_1841_);
lean_ctor_set(v_reuseFailAlloc_1859_, 5, v_oleanFileName_x3f_1842_);
lean_ctor_set(v_reuseFailAlloc_1859_, 6, v_ileanFileName_x3f_1843_);
lean_ctor_set(v_reuseFailAlloc_1859_, 7, v_cFileName_x3f_1844_);
lean_ctor_set(v_reuseFailAlloc_1859_, 8, v_bcFileName_x3f_1845_);
lean_ctor_set(v_reuseFailAlloc_1859_, 9, v_errorOnKinds_1847_);
lean_ctor_set(v_reuseFailAlloc_1859_, 10, v_incrSaveFileName_x3f_1850_);
lean_ctor_set(v_reuseFailAlloc_1859_, 11, v_incrLoadFileName_x3f_1851_);
lean_ctor_set(v_reuseFailAlloc_1859_, 12, v_incrHeaderSaveFileName_x3f_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*13 + 8, v_component_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*13 + 9, v_printPrefix_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*13 + 11, v_useStdin_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*13 + 12, v_onlyDeps_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*13 + 13, v_onlySrcDeps_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*13 + 14, v_depsJson_1836_);
lean_ctor_set_uint32(v_reuseFailAlloc_1859_, sizeof(void*)*13, v_trustLevel_1838_);
lean_ctor_set_uint32(v_reuseFailAlloc_1859_, sizeof(void*)*13 + 4, v_numThreads_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*13 + 15, v_jsonOutput_1846_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*13 + 16, v_printStats_1848_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*13 + 17, v_run_1849_);
v___x_1857_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; 
lean_ctor_set_uint8(v___x_1857_, sizeof(void*)*13 + 10, v___x_1241_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
}
}
else
{
lean_object* v_leanOpts_1861_; lean_object* v_forwardedArgs_1862_; uint8_t v_component_1863_; uint8_t v_printLibDir_1864_; uint8_t v_useStdin_1865_; uint8_t v_onlyDeps_1866_; uint8_t v_onlySrcDeps_1867_; uint8_t v_depsJson_1868_; lean_object* v_opts_1869_; uint32_t v_trustLevel_1870_; uint32_t v_numThreads_1871_; lean_object* v_rootDir_x3f_1872_; lean_object* v_setupFileName_x3f_1873_; lean_object* v_oleanFileName_x3f_1874_; lean_object* v_ileanFileName_x3f_1875_; lean_object* v_cFileName_x3f_1876_; lean_object* v_bcFileName_x3f_1877_; uint8_t v_jsonOutput_1878_; lean_object* v_errorOnKinds_1879_; uint8_t v_printStats_1880_; uint8_t v_run_1881_; lean_object* v_incrSaveFileName_x3f_1882_; lean_object* v_incrLoadFileName_x3f_1883_; lean_object* v_incrHeaderSaveFileName_x3f_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_optArg_x3f_970_);
v_leanOpts_1861_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1862_ = lean_ctor_get(v_opts_968_, 1);
v_component_1863_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printLibDir_1864_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1865_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1866_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1867_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1868_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1869_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1870_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1871_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1872_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1873_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1874_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1875_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1876_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1877_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1878_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1879_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1880_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1881_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1882_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1883_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1884_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1886_ = v_opts_968_;
v_isShared_1887_ = v_isSharedCheck_1892_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1884_);
lean_inc(v_incrLoadFileName_x3f_1883_);
lean_inc(v_incrSaveFileName_x3f_1882_);
lean_inc(v_errorOnKinds_1879_);
lean_inc(v_bcFileName_x3f_1877_);
lean_inc(v_cFileName_x3f_1876_);
lean_inc(v_ileanFileName_x3f_1875_);
lean_inc(v_oleanFileName_x3f_1874_);
lean_inc(v_setupFileName_x3f_1873_);
lean_inc(v_rootDir_x3f_1872_);
lean_inc(v_opts_1869_);
lean_inc(v_forwardedArgs_1862_);
lean_inc(v_leanOpts_1861_);
lean_dec(v_opts_968_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1892_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_leanOpts_1861_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_forwardedArgs_1862_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_opts_1869_);
lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_rootDir_x3f_1872_);
lean_ctor_set(v_reuseFailAlloc_1891_, 4, v_setupFileName_x3f_1873_);
lean_ctor_set(v_reuseFailAlloc_1891_, 5, v_oleanFileName_x3f_1874_);
lean_ctor_set(v_reuseFailAlloc_1891_, 6, v_ileanFileName_x3f_1875_);
lean_ctor_set(v_reuseFailAlloc_1891_, 7, v_cFileName_x3f_1876_);
lean_ctor_set(v_reuseFailAlloc_1891_, 8, v_bcFileName_x3f_1877_);
lean_ctor_set(v_reuseFailAlloc_1891_, 9, v_errorOnKinds_1879_);
lean_ctor_set(v_reuseFailAlloc_1891_, 10, v_incrSaveFileName_x3f_1882_);
lean_ctor_set(v_reuseFailAlloc_1891_, 11, v_incrLoadFileName_x3f_1883_);
lean_ctor_set(v_reuseFailAlloc_1891_, 12, v_incrHeaderSaveFileName_x3f_1884_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 8, v_component_1863_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 10, v_printLibDir_1864_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 11, v_useStdin_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 12, v_onlyDeps_1866_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 13, v_onlySrcDeps_1867_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 14, v_depsJson_1868_);
lean_ctor_set_uint32(v_reuseFailAlloc_1891_, sizeof(void*)*13, v_trustLevel_1870_);
lean_ctor_set_uint32(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 4, v_numThreads_1871_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 15, v_jsonOutput_1878_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 16, v_printStats_1880_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 17, v_run_1881_);
v___x_1889_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; 
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*13 + 9, v___x_1239_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
}
}
}
else
{
lean_object* v_leanOpts_1893_; lean_object* v_forwardedArgs_1894_; uint8_t v_component_1895_; uint8_t v_printPrefix_1896_; uint8_t v_printLibDir_1897_; uint8_t v_useStdin_1898_; uint8_t v_onlyDeps_1899_; uint8_t v_onlySrcDeps_1900_; uint8_t v_depsJson_1901_; lean_object* v_opts_1902_; uint32_t v_trustLevel_1903_; uint32_t v_numThreads_1904_; lean_object* v_rootDir_x3f_1905_; lean_object* v_setupFileName_x3f_1906_; lean_object* v_oleanFileName_x3f_1907_; lean_object* v_ileanFileName_x3f_1908_; lean_object* v_cFileName_x3f_1909_; lean_object* v_bcFileName_x3f_1910_; uint8_t v_jsonOutput_1911_; lean_object* v_errorOnKinds_1912_; uint8_t v_run_1913_; lean_object* v_incrSaveFileName_x3f_1914_; lean_object* v_incrLoadFileName_x3f_1915_; lean_object* v_incrHeaderSaveFileName_x3f_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_optArg_x3f_970_);
v_leanOpts_1893_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1894_ = lean_ctor_get(v_opts_968_, 1);
v_component_1895_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1896_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1897_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1898_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1899_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1900_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1901_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1902_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1903_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1904_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1905_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1906_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1907_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1908_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1909_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1910_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1911_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1912_ = lean_ctor_get(v_opts_968_, 9);
v_run_1913_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1914_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1915_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1916_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1918_ = v_opts_968_;
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1916_);
lean_inc(v_incrLoadFileName_x3f_1915_);
lean_inc(v_incrSaveFileName_x3f_1914_);
lean_inc(v_errorOnKinds_1912_);
lean_inc(v_bcFileName_x3f_1910_);
lean_inc(v_cFileName_x3f_1909_);
lean_inc(v_ileanFileName_x3f_1908_);
lean_inc(v_oleanFileName_x3f_1907_);
lean_inc(v_setupFileName_x3f_1906_);
lean_inc(v_rootDir_x3f_1905_);
lean_inc(v_opts_1902_);
lean_inc(v_forwardedArgs_1894_);
lean_inc(v_leanOpts_1893_);
lean_dec(v_opts_968_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_leanOpts_1893_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_forwardedArgs_1894_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_opts_1902_);
lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_rootDir_x3f_1905_);
lean_ctor_set(v_reuseFailAlloc_1923_, 4, v_setupFileName_x3f_1906_);
lean_ctor_set(v_reuseFailAlloc_1923_, 5, v_oleanFileName_x3f_1907_);
lean_ctor_set(v_reuseFailAlloc_1923_, 6, v_ileanFileName_x3f_1908_);
lean_ctor_set(v_reuseFailAlloc_1923_, 7, v_cFileName_x3f_1909_);
lean_ctor_set(v_reuseFailAlloc_1923_, 8, v_bcFileName_x3f_1910_);
lean_ctor_set(v_reuseFailAlloc_1923_, 9, v_errorOnKinds_1912_);
lean_ctor_set(v_reuseFailAlloc_1923_, 10, v_incrSaveFileName_x3f_1914_);
lean_ctor_set(v_reuseFailAlloc_1923_, 11, v_incrLoadFileName_x3f_1915_);
lean_ctor_set(v_reuseFailAlloc_1923_, 12, v_incrHeaderSaveFileName_x3f_1916_);
lean_ctor_set_uint8(v_reuseFailAlloc_1923_, sizeof(void*)*13 + 8, v_component_1895_);
lean_ctor_set_uint8(v_reuseFailAlloc_1923_, sizeof(void*)*13 + 9, v_printPrefix_1896_);
lean_ctor_set_uint8(v_reuseFailAlloc_1923_, sizeof(void*)*13 + 10, v_printLibDir_1897_);
lean_ctor_set_uint8(v_reuseFailAlloc_1923_, sizeof(void*)*13 + 11, v_useStdin_1898_);
lean_ctor_set_uint8(v_reuseFailAlloc_1923_, sizeof(void*)*13 + 12, v_onlyDeps_1899_);
lean_ctor_set_uint8(v_reuseFailAlloc_1923_, sizeof(void*)*13 + 13, v_onlySrcDeps_1900_);
lean_ctor_set_uint8(v_reuseFailAlloc_1923_, sizeof(void*)*13 + 14, v_depsJson_1901_);
lean_ctor_set_uint32(v_reuseFailAlloc_1923_, sizeof(void*)*13, v_trustLevel_1903_);
lean_ctor_set_uint32(v_reuseFailAlloc_1923_, sizeof(void*)*13 + 4, v_numThreads_1904_);
lean_ctor_set_uint8(v_reuseFailAlloc_1923_, sizeof(void*)*13 + 15, v_jsonOutput_1911_);
lean_ctor_set_uint8(v_reuseFailAlloc_1923_, sizeof(void*)*13 + 17, v_run_1913_);
v___x_1921_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; 
lean_ctor_set_uint8(v___x_1921_, sizeof(void*)*13 + 16, v___x_1237_);
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
return v___x_1922_;
}
}
}
}
else
{
lean_object* v_leanOpts_1925_; lean_object* v_forwardedArgs_1926_; uint8_t v_component_1927_; uint8_t v_printPrefix_1928_; uint8_t v_printLibDir_1929_; uint8_t v_useStdin_1930_; uint8_t v_onlyDeps_1931_; uint8_t v_onlySrcDeps_1932_; uint8_t v_depsJson_1933_; lean_object* v_opts_1934_; uint32_t v_trustLevel_1935_; uint32_t v_numThreads_1936_; lean_object* v_rootDir_x3f_1937_; lean_object* v_setupFileName_x3f_1938_; lean_object* v_oleanFileName_x3f_1939_; lean_object* v_ileanFileName_x3f_1940_; lean_object* v_cFileName_x3f_1941_; lean_object* v_bcFileName_x3f_1942_; lean_object* v_errorOnKinds_1943_; uint8_t v_printStats_1944_; uint8_t v_run_1945_; lean_object* v_incrSaveFileName_x3f_1946_; lean_object* v_incrLoadFileName_x3f_1947_; lean_object* v_incrHeaderSaveFileName_x3f_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v_optArg_x3f_970_);
v_leanOpts_1925_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1926_ = lean_ctor_get(v_opts_968_, 1);
v_component_1927_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1928_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1929_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1930_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1931_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1932_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_1933_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1934_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1935_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1936_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1937_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1938_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1939_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1940_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1941_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1942_ = lean_ctor_get(v_opts_968_, 8);
v_errorOnKinds_1943_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1944_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1945_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1946_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1947_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1948_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1950_ = v_opts_968_;
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1948_);
lean_inc(v_incrLoadFileName_x3f_1947_);
lean_inc(v_incrSaveFileName_x3f_1946_);
lean_inc(v_errorOnKinds_1943_);
lean_inc(v_bcFileName_x3f_1942_);
lean_inc(v_cFileName_x3f_1941_);
lean_inc(v_ileanFileName_x3f_1940_);
lean_inc(v_oleanFileName_x3f_1939_);
lean_inc(v_setupFileName_x3f_1938_);
lean_inc(v_rootDir_x3f_1937_);
lean_inc(v_opts_1934_);
lean_inc(v_forwardedArgs_1926_);
lean_inc(v_leanOpts_1925_);
lean_dec(v_opts_968_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_leanOpts_1925_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_forwardedArgs_1926_);
lean_ctor_set(v_reuseFailAlloc_1955_, 2, v_opts_1934_);
lean_ctor_set(v_reuseFailAlloc_1955_, 3, v_rootDir_x3f_1937_);
lean_ctor_set(v_reuseFailAlloc_1955_, 4, v_setupFileName_x3f_1938_);
lean_ctor_set(v_reuseFailAlloc_1955_, 5, v_oleanFileName_x3f_1939_);
lean_ctor_set(v_reuseFailAlloc_1955_, 6, v_ileanFileName_x3f_1940_);
lean_ctor_set(v_reuseFailAlloc_1955_, 7, v_cFileName_x3f_1941_);
lean_ctor_set(v_reuseFailAlloc_1955_, 8, v_bcFileName_x3f_1942_);
lean_ctor_set(v_reuseFailAlloc_1955_, 9, v_errorOnKinds_1943_);
lean_ctor_set(v_reuseFailAlloc_1955_, 10, v_incrSaveFileName_x3f_1946_);
lean_ctor_set(v_reuseFailAlloc_1955_, 11, v_incrLoadFileName_x3f_1947_);
lean_ctor_set(v_reuseFailAlloc_1955_, 12, v_incrHeaderSaveFileName_x3f_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 8, v_component_1927_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 9, v_printPrefix_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 10, v_printLibDir_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 11, v_useStdin_1930_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 12, v_onlyDeps_1931_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 13, v_onlySrcDeps_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 14, v_depsJson_1933_);
lean_ctor_set_uint32(v_reuseFailAlloc_1955_, sizeof(void*)*13, v_trustLevel_1935_);
lean_ctor_set_uint32(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 4, v_numThreads_1936_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 16, v_printStats_1944_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*13 + 17, v_run_1945_);
v___x_1953_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; 
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*13 + 15, v___x_1235_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
}
}
}
else
{
lean_object* v_leanOpts_1957_; lean_object* v_forwardedArgs_1958_; uint8_t v_component_1959_; uint8_t v_printPrefix_1960_; uint8_t v_printLibDir_1961_; uint8_t v_useStdin_1962_; uint8_t v_onlySrcDeps_1963_; lean_object* v_opts_1964_; uint32_t v_trustLevel_1965_; uint32_t v_numThreads_1966_; lean_object* v_rootDir_x3f_1967_; lean_object* v_setupFileName_x3f_1968_; lean_object* v_oleanFileName_x3f_1969_; lean_object* v_ileanFileName_x3f_1970_; lean_object* v_cFileName_x3f_1971_; lean_object* v_bcFileName_x3f_1972_; uint8_t v_jsonOutput_1973_; lean_object* v_errorOnKinds_1974_; uint8_t v_printStats_1975_; uint8_t v_run_1976_; lean_object* v_incrSaveFileName_x3f_1977_; lean_object* v_incrLoadFileName_x3f_1978_; lean_object* v_incrHeaderSaveFileName_x3f_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_optArg_x3f_970_);
v_leanOpts_1957_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1958_ = lean_ctor_get(v_opts_968_, 1);
v_component_1959_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1960_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1961_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1962_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1963_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_opts_1964_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1965_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1966_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1967_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_1968_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_1969_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_1970_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_1971_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_1972_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_1973_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_1974_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_1975_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_1976_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1977_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_1978_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_1979_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1981_ = v_opts_968_;
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1979_);
lean_inc(v_incrLoadFileName_x3f_1978_);
lean_inc(v_incrSaveFileName_x3f_1977_);
lean_inc(v_errorOnKinds_1974_);
lean_inc(v_bcFileName_x3f_1972_);
lean_inc(v_cFileName_x3f_1971_);
lean_inc(v_ileanFileName_x3f_1970_);
lean_inc(v_oleanFileName_x3f_1969_);
lean_inc(v_setupFileName_x3f_1968_);
lean_inc(v_rootDir_x3f_1967_);
lean_inc(v_opts_1964_);
lean_inc(v_forwardedArgs_1958_);
lean_inc(v_leanOpts_1957_);
lean_dec(v_opts_968_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_leanOpts_1957_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_forwardedArgs_1958_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_opts_1964_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_rootDir_x3f_1967_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v_setupFileName_x3f_1968_);
lean_ctor_set(v_reuseFailAlloc_1986_, 5, v_oleanFileName_x3f_1969_);
lean_ctor_set(v_reuseFailAlloc_1986_, 6, v_ileanFileName_x3f_1970_);
lean_ctor_set(v_reuseFailAlloc_1986_, 7, v_cFileName_x3f_1971_);
lean_ctor_set(v_reuseFailAlloc_1986_, 8, v_bcFileName_x3f_1972_);
lean_ctor_set(v_reuseFailAlloc_1986_, 9, v_errorOnKinds_1974_);
lean_ctor_set(v_reuseFailAlloc_1986_, 10, v_incrSaveFileName_x3f_1977_);
lean_ctor_set(v_reuseFailAlloc_1986_, 11, v_incrLoadFileName_x3f_1978_);
lean_ctor_set(v_reuseFailAlloc_1986_, 12, v_incrHeaderSaveFileName_x3f_1979_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 8, v_component_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 9, v_printPrefix_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 10, v_printLibDir_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 11, v_useStdin_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 13, v_onlySrcDeps_1963_);
lean_ctor_set_uint32(v_reuseFailAlloc_1986_, sizeof(void*)*13, v_trustLevel_1965_);
lean_ctor_set_uint32(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 4, v_numThreads_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 15, v_jsonOutput_1973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 16, v_printStats_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 17, v_run_1976_);
v___x_1984_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; 
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*13 + 12, v___x_1233_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*13 + 14, v___x_1233_);
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
return v___x_1985_;
}
}
}
}
else
{
lean_object* v_leanOpts_1988_; lean_object* v_forwardedArgs_1989_; uint8_t v_component_1990_; uint8_t v_printPrefix_1991_; uint8_t v_printLibDir_1992_; uint8_t v_useStdin_1993_; uint8_t v_onlyDeps_1994_; uint8_t v_depsJson_1995_; lean_object* v_opts_1996_; uint32_t v_trustLevel_1997_; uint32_t v_numThreads_1998_; lean_object* v_rootDir_x3f_1999_; lean_object* v_setupFileName_x3f_2000_; lean_object* v_oleanFileName_x3f_2001_; lean_object* v_ileanFileName_x3f_2002_; lean_object* v_cFileName_x3f_2003_; lean_object* v_bcFileName_x3f_2004_; uint8_t v_jsonOutput_2005_; lean_object* v_errorOnKinds_2006_; uint8_t v_printStats_2007_; uint8_t v_run_2008_; lean_object* v_incrSaveFileName_x3f_2009_; lean_object* v_incrLoadFileName_x3f_2010_; lean_object* v_incrHeaderSaveFileName_x3f_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2019_; 
lean_dec(v_optArg_x3f_970_);
v_leanOpts_1988_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_1989_ = lean_ctor_get(v_opts_968_, 1);
v_component_1990_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_1991_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_1992_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_1993_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_1994_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_depsJson_1995_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_1996_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_1997_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_1998_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1999_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2000_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2001_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_2002_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_2003_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_2004_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2005_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2006_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2007_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2008_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2009_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2010_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2011_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2013_ = v_opts_968_;
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2011_);
lean_inc(v_incrLoadFileName_x3f_2010_);
lean_inc(v_incrSaveFileName_x3f_2009_);
lean_inc(v_errorOnKinds_2006_);
lean_inc(v_bcFileName_x3f_2004_);
lean_inc(v_cFileName_x3f_2003_);
lean_inc(v_ileanFileName_x3f_2002_);
lean_inc(v_oleanFileName_x3f_2001_);
lean_inc(v_setupFileName_x3f_2000_);
lean_inc(v_rootDir_x3f_1999_);
lean_inc(v_opts_1996_);
lean_inc(v_forwardedArgs_1989_);
lean_inc(v_leanOpts_1988_);
lean_dec(v_opts_968_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_leanOpts_1988_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_forwardedArgs_1989_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_opts_1996_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v_rootDir_x3f_1999_);
lean_ctor_set(v_reuseFailAlloc_2018_, 4, v_setupFileName_x3f_2000_);
lean_ctor_set(v_reuseFailAlloc_2018_, 5, v_oleanFileName_x3f_2001_);
lean_ctor_set(v_reuseFailAlloc_2018_, 6, v_ileanFileName_x3f_2002_);
lean_ctor_set(v_reuseFailAlloc_2018_, 7, v_cFileName_x3f_2003_);
lean_ctor_set(v_reuseFailAlloc_2018_, 8, v_bcFileName_x3f_2004_);
lean_ctor_set(v_reuseFailAlloc_2018_, 9, v_errorOnKinds_2006_);
lean_ctor_set(v_reuseFailAlloc_2018_, 10, v_incrSaveFileName_x3f_2009_);
lean_ctor_set(v_reuseFailAlloc_2018_, 11, v_incrLoadFileName_x3f_2010_);
lean_ctor_set(v_reuseFailAlloc_2018_, 12, v_incrHeaderSaveFileName_x3f_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*13 + 8, v_component_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*13 + 9, v_printPrefix_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*13 + 10, v_printLibDir_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*13 + 11, v_useStdin_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*13 + 12, v_onlyDeps_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*13 + 14, v_depsJson_1995_);
lean_ctor_set_uint32(v_reuseFailAlloc_2018_, sizeof(void*)*13, v_trustLevel_1997_);
lean_ctor_set_uint32(v_reuseFailAlloc_2018_, sizeof(void*)*13 + 4, v_numThreads_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*13 + 15, v_jsonOutput_2005_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*13 + 16, v_printStats_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*13 + 17, v_run_2008_);
v___x_2016_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; 
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*13 + 13, v___x_1231_);
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_leanOpts_2020_; lean_object* v_forwardedArgs_2021_; uint8_t v_component_2022_; uint8_t v_printPrefix_2023_; uint8_t v_printLibDir_2024_; uint8_t v_useStdin_2025_; uint8_t v_onlySrcDeps_2026_; uint8_t v_depsJson_2027_; lean_object* v_opts_2028_; uint32_t v_trustLevel_2029_; uint32_t v_numThreads_2030_; lean_object* v_rootDir_x3f_2031_; lean_object* v_setupFileName_x3f_2032_; lean_object* v_oleanFileName_x3f_2033_; lean_object* v_ileanFileName_x3f_2034_; lean_object* v_cFileName_x3f_2035_; lean_object* v_bcFileName_x3f_2036_; uint8_t v_jsonOutput_2037_; lean_object* v_errorOnKinds_2038_; uint8_t v_printStats_2039_; uint8_t v_run_2040_; lean_object* v_incrSaveFileName_x3f_2041_; lean_object* v_incrLoadFileName_x3f_2042_; lean_object* v_incrHeaderSaveFileName_x3f_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v_optArg_x3f_970_);
v_leanOpts_2020_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2021_ = lean_ctor_get(v_opts_968_, 1);
v_component_2022_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2023_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2024_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_2025_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlySrcDeps_2026_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2027_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2028_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_2029_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_2030_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2031_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2032_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2033_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_2034_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_2035_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_2036_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2037_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2038_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2039_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2040_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2041_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2042_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2043_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2045_ = v_opts_968_;
v_isShared_2046_ = v_isSharedCheck_2051_;
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
lean_inc(v_forwardedArgs_2021_);
lean_inc(v_leanOpts_2020_);
lean_dec(v_opts_968_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_leanOpts_2020_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_forwardedArgs_2021_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_opts_2028_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_rootDir_x3f_2031_);
lean_ctor_set(v_reuseFailAlloc_2050_, 4, v_setupFileName_x3f_2032_);
lean_ctor_set(v_reuseFailAlloc_2050_, 5, v_oleanFileName_x3f_2033_);
lean_ctor_set(v_reuseFailAlloc_2050_, 6, v_ileanFileName_x3f_2034_);
lean_ctor_set(v_reuseFailAlloc_2050_, 7, v_cFileName_x3f_2035_);
lean_ctor_set(v_reuseFailAlloc_2050_, 8, v_bcFileName_x3f_2036_);
lean_ctor_set(v_reuseFailAlloc_2050_, 9, v_errorOnKinds_2038_);
lean_ctor_set(v_reuseFailAlloc_2050_, 10, v_incrSaveFileName_x3f_2041_);
lean_ctor_set(v_reuseFailAlloc_2050_, 11, v_incrLoadFileName_x3f_2042_);
lean_ctor_set(v_reuseFailAlloc_2050_, 12, v_incrHeaderSaveFileName_x3f_2043_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 8, v_component_2022_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 9, v_printPrefix_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 10, v_printLibDir_2024_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 11, v_useStdin_2025_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 13, v_onlySrcDeps_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 14, v_depsJson_2027_);
lean_ctor_set_uint32(v_reuseFailAlloc_2050_, sizeof(void*)*13, v_trustLevel_2029_);
lean_ctor_set_uint32(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 4, v_numThreads_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 15, v_jsonOutput_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 16, v_printStats_2039_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 17, v_run_2040_);
v___x_2048_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; 
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*13 + 12, v___x_1229_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
return v___x_2049_;
}
}
}
}
else
{
lean_object* v_leanOpts_2052_; lean_object* v_forwardedArgs_2053_; uint8_t v_component_2054_; uint8_t v_printPrefix_2055_; uint8_t v_printLibDir_2056_; uint8_t v_useStdin_2057_; uint8_t v_onlyDeps_2058_; uint8_t v_onlySrcDeps_2059_; uint8_t v_depsJson_2060_; lean_object* v_opts_2061_; uint32_t v_trustLevel_2062_; uint32_t v_numThreads_2063_; lean_object* v_rootDir_x3f_2064_; lean_object* v_setupFileName_x3f_2065_; lean_object* v_oleanFileName_x3f_2066_; lean_object* v_ileanFileName_x3f_2067_; lean_object* v_cFileName_x3f_2068_; lean_object* v_bcFileName_x3f_2069_; uint8_t v_jsonOutput_2070_; lean_object* v_errorOnKinds_2071_; uint8_t v_printStats_2072_; uint8_t v_run_2073_; lean_object* v_incrSaveFileName_x3f_2074_; lean_object* v_incrLoadFileName_x3f_2075_; lean_object* v_incrHeaderSaveFileName_x3f_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2086_; 
lean_dec(v_optArg_x3f_970_);
v_leanOpts_2052_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2053_ = lean_ctor_get(v_opts_968_, 1);
v_component_2054_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2055_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2056_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_2057_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_2058_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2059_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2060_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2061_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_2062_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_2063_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2064_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2065_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2066_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_2067_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_2068_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_2069_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2070_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2071_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2072_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2073_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2074_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2075_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2076_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2078_ = v_opts_968_;
v_isShared_2079_ = v_isSharedCheck_2086_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2076_);
lean_inc(v_incrLoadFileName_x3f_2075_);
lean_inc(v_incrSaveFileName_x3f_2074_);
lean_inc(v_errorOnKinds_2071_);
lean_inc(v_bcFileName_x3f_2069_);
lean_inc(v_cFileName_x3f_2068_);
lean_inc(v_ileanFileName_x3f_2067_);
lean_inc(v_oleanFileName_x3f_2066_);
lean_inc(v_setupFileName_x3f_2065_);
lean_inc(v_rootDir_x3f_2064_);
lean_inc(v_opts_2061_);
lean_inc(v_forwardedArgs_2053_);
lean_inc(v_leanOpts_2052_);
lean_dec(v_opts_968_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2086_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2080_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_2081_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2052_, v___x_2080_, v___x_1225_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2081_);
v___x_2083_ = v___x_2078_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_forwardedArgs_2053_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_opts_2061_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_rootDir_x3f_2064_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_setupFileName_x3f_2065_);
lean_ctor_set(v_reuseFailAlloc_2085_, 5, v_oleanFileName_x3f_2066_);
lean_ctor_set(v_reuseFailAlloc_2085_, 6, v_ileanFileName_x3f_2067_);
lean_ctor_set(v_reuseFailAlloc_2085_, 7, v_cFileName_x3f_2068_);
lean_ctor_set(v_reuseFailAlloc_2085_, 8, v_bcFileName_x3f_2069_);
lean_ctor_set(v_reuseFailAlloc_2085_, 9, v_errorOnKinds_2071_);
lean_ctor_set(v_reuseFailAlloc_2085_, 10, v_incrSaveFileName_x3f_2074_);
lean_ctor_set(v_reuseFailAlloc_2085_, 11, v_incrLoadFileName_x3f_2075_);
lean_ctor_set(v_reuseFailAlloc_2085_, 12, v_incrHeaderSaveFileName_x3f_2076_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*13 + 8, v_component_2054_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*13 + 9, v_printPrefix_2055_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*13 + 10, v_printLibDir_2056_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*13 + 11, v_useStdin_2057_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*13 + 12, v_onlyDeps_2058_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*13 + 13, v_onlySrcDeps_2059_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*13 + 14, v_depsJson_2060_);
lean_ctor_set_uint32(v_reuseFailAlloc_2085_, sizeof(void*)*13, v_trustLevel_2062_);
lean_ctor_set_uint32(v_reuseFailAlloc_2085_, sizeof(void*)*13 + 4, v_numThreads_2063_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*13 + 15, v_jsonOutput_2070_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*13 + 16, v_printStats_2072_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*13 + 17, v_run_2073_);
v___x_2083_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
}
}
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_2088_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2087_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2142_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2142_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2142_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2093_ = lean_unsigned_to_nat(0u);
v___x_2094_ = lean_string_utf8_byte_size(v_a_2089_);
lean_inc(v_a_2089_);
v___x_2095_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2095_, 0, v_a_2089_);
lean_ctor_set(v___x_2095_, 1, v___x_2093_);
lean_ctor_set(v___x_2095_, 2, v___x_2094_);
v___x_2096_ = l_String_Slice_toNat_x3f(v___x_2095_);
lean_dec_ref_known(v___x_2095_, 3);
if (lean_obj_tag(v___x_2096_) == 1)
{
lean_object* v_val_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_val_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_val_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = lean_cstr_to_nat("4294967296");
v___x_2099_ = lean_nat_dec_lt(v_val_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_dec(v_val_2097_);
lean_del_object(v___x_2091_);
lean_dec(v_a_2089_);
lean_dec_ref(v_opts_968_);
v___x_2100_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_2101_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2100_);
lean_dec_ref(v___x_2101_);
goto v___jp_1032_;
}
else
{
lean_object* v_leanOpts_2102_; lean_object* v_forwardedArgs_2103_; uint8_t v_component_2104_; uint8_t v_printPrefix_2105_; uint8_t v_printLibDir_2106_; uint8_t v_useStdin_2107_; uint8_t v_onlyDeps_2108_; uint8_t v_onlySrcDeps_2109_; uint8_t v_depsJson_2110_; lean_object* v_opts_2111_; uint32_t v_numThreads_2112_; lean_object* v_rootDir_x3f_2113_; lean_object* v_setupFileName_x3f_2114_; lean_object* v_oleanFileName_x3f_2115_; lean_object* v_ileanFileName_x3f_2116_; lean_object* v_cFileName_x3f_2117_; lean_object* v_bcFileName_x3f_2118_; uint8_t v_jsonOutput_2119_; lean_object* v_errorOnKinds_2120_; uint8_t v_printStats_2121_; uint8_t v_run_2122_; lean_object* v_incrSaveFileName_x3f_2123_; lean_object* v_incrLoadFileName_x3f_2124_; lean_object* v_incrHeaderSaveFileName_x3f_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2139_; 
v_leanOpts_2102_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2103_ = lean_ctor_get(v_opts_968_, 1);
v_component_2104_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2105_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2106_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_2107_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_2108_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2109_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2110_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2111_ = lean_ctor_get(v_opts_968_, 2);
v_numThreads_2112_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2113_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2114_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2115_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_2116_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_2117_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_2118_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2119_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2120_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2121_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2122_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2123_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2124_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2125_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2127_ = v_opts_968_;
v_isShared_2128_ = v_isSharedCheck_2139_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2125_);
lean_inc(v_incrLoadFileName_x3f_2124_);
lean_inc(v_incrSaveFileName_x3f_2123_);
lean_inc(v_errorOnKinds_2120_);
lean_inc(v_bcFileName_x3f_2118_);
lean_inc(v_cFileName_x3f_2117_);
lean_inc(v_ileanFileName_x3f_2116_);
lean_inc(v_oleanFileName_x3f_2115_);
lean_inc(v_setupFileName_x3f_2114_);
lean_inc(v_rootDir_x3f_2113_);
lean_inc(v_opts_2111_);
lean_inc(v_forwardedArgs_2103_);
lean_inc(v_leanOpts_2102_);
lean_dec(v_opts_968_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2139_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
uint32_t v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2129_ = lean_uint32_of_nat(v_val_2097_);
lean_dec(v_val_2097_);
v___x_2130_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_2131_ = lean_string_append(v___x_2130_, v_a_2089_);
lean_dec(v_a_2089_);
v___x_2132_ = lean_array_push(v_forwardedArgs_2103_, v___x_2131_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 1, v___x_2132_);
v___x_2134_ = v___x_2127_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_leanOpts_2102_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_opts_2111_);
lean_ctor_set(v_reuseFailAlloc_2138_, 3, v_rootDir_x3f_2113_);
lean_ctor_set(v_reuseFailAlloc_2138_, 4, v_setupFileName_x3f_2114_);
lean_ctor_set(v_reuseFailAlloc_2138_, 5, v_oleanFileName_x3f_2115_);
lean_ctor_set(v_reuseFailAlloc_2138_, 6, v_ileanFileName_x3f_2116_);
lean_ctor_set(v_reuseFailAlloc_2138_, 7, v_cFileName_x3f_2117_);
lean_ctor_set(v_reuseFailAlloc_2138_, 8, v_bcFileName_x3f_2118_);
lean_ctor_set(v_reuseFailAlloc_2138_, 9, v_errorOnKinds_2120_);
lean_ctor_set(v_reuseFailAlloc_2138_, 10, v_incrSaveFileName_x3f_2123_);
lean_ctor_set(v_reuseFailAlloc_2138_, 11, v_incrLoadFileName_x3f_2124_);
lean_ctor_set(v_reuseFailAlloc_2138_, 12, v_incrHeaderSaveFileName_x3f_2125_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*13 + 8, v_component_2104_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*13 + 9, v_printPrefix_2105_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*13 + 10, v_printLibDir_2106_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*13 + 11, v_useStdin_2107_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*13 + 12, v_onlyDeps_2108_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*13 + 13, v_onlySrcDeps_2109_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*13 + 14, v_depsJson_2110_);
lean_ctor_set_uint32(v_reuseFailAlloc_2138_, sizeof(void*)*13 + 4, v_numThreads_2112_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*13 + 15, v_jsonOutput_2119_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*13 + 16, v_printStats_2121_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*13 + 17, v_run_2122_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
lean_ctor_set_uint32(v___x_2134_, sizeof(void*)*13, v___x_2129_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2134_);
v___x_2136_ = v___x_2091_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_dec(v___x_2096_);
lean_del_object(v___x_2091_);
lean_dec(v_a_2089_);
lean_dec_ref(v_opts_968_);
v___x_2140_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_2141_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2140_);
lean_dec_ref(v___x_2141_);
goto v___jp_1029_;
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec_ref(v_opts_968_);
v_a_2143_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2147_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2148_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2147_);
lean_dec_ref(v___x_2148_);
goto v___jp_2144_;
v___jp_2144_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_io_error_to_string(v_a_2143_);
v___x_2146_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2145_);
lean_dec_ref(v___x_2146_);
goto v___jp_1038_;
}
}
}
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_2150_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2149_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2202_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2202_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2202_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = lean_string_utf8_byte_size(v_a_2151_);
lean_inc(v_a_2151_);
v___x_2157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2157_, 0, v_a_2151_);
lean_ctor_set(v___x_2157_, 1, v___x_2155_);
lean_ctor_set(v___x_2157_, 2, v___x_2156_);
v___x_2158_ = l_String_Slice_toNat_x3f(v___x_2157_);
lean_dec_ref_known(v___x_2157_, 3);
if (lean_obj_tag(v___x_2158_) == 1)
{
lean_object* v_val_2159_; lean_object* v_leanOpts_2160_; lean_object* v_forwardedArgs_2161_; uint8_t v_component_2162_; uint8_t v_printPrefix_2163_; uint8_t v_printLibDir_2164_; uint8_t v_useStdin_2165_; uint8_t v_onlyDeps_2166_; uint8_t v_onlySrcDeps_2167_; uint8_t v_depsJson_2168_; lean_object* v_opts_2169_; uint32_t v_trustLevel_2170_; uint32_t v_numThreads_2171_; lean_object* v_rootDir_x3f_2172_; lean_object* v_setupFileName_x3f_2173_; lean_object* v_oleanFileName_x3f_2174_; lean_object* v_ileanFileName_x3f_2175_; lean_object* v_cFileName_x3f_2176_; lean_object* v_bcFileName_x3f_2177_; uint8_t v_jsonOutput_2178_; lean_object* v_errorOnKinds_2179_; uint8_t v_printStats_2180_; uint8_t v_run_2181_; lean_object* v_incrSaveFileName_x3f_2182_; lean_object* v_incrLoadFileName_x3f_2183_; lean_object* v_incrHeaderSaveFileName_x3f_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2199_; 
v_val_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_val_2159_);
lean_dec_ref_known(v___x_2158_, 1);
v_leanOpts_2160_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2161_ = lean_ctor_get(v_opts_968_, 1);
v_component_2162_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2163_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2164_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_2165_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_2166_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2167_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2168_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2169_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_2170_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_2171_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2172_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2173_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2174_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_2175_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_2176_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_2177_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2178_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2179_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2180_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2181_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2182_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2183_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2184_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2186_ = v_opts_968_;
v_isShared_2187_ = v_isSharedCheck_2199_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2184_);
lean_inc(v_incrLoadFileName_x3f_2183_);
lean_inc(v_incrSaveFileName_x3f_2182_);
lean_inc(v_errorOnKinds_2179_);
lean_inc(v_bcFileName_x3f_2177_);
lean_inc(v_cFileName_x3f_2176_);
lean_inc(v_ileanFileName_x3f_2175_);
lean_inc(v_oleanFileName_x3f_2174_);
lean_inc(v_setupFileName_x3f_2173_);
lean_inc(v_rootDir_x3f_2172_);
lean_inc(v_opts_2169_);
lean_inc(v_forwardedArgs_2161_);
lean_inc(v_leanOpts_2160_);
lean_dec(v_opts_968_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2199_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2188_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_2189_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2160_, v___x_2188_, v_val_2159_);
v___x_2190_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_2191_ = lean_string_append(v___x_2190_, v_a_2151_);
lean_dec(v_a_2151_);
v___x_2192_ = lean_array_push(v_forwardedArgs_2161_, v___x_2191_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v___x_2192_);
lean_ctor_set(v___x_2186_, 0, v___x_2189_);
v___x_2194_ = v___x_2186_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_opts_2169_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_rootDir_x3f_2172_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_setupFileName_x3f_2173_);
lean_ctor_set(v_reuseFailAlloc_2198_, 5, v_oleanFileName_x3f_2174_);
lean_ctor_set(v_reuseFailAlloc_2198_, 6, v_ileanFileName_x3f_2175_);
lean_ctor_set(v_reuseFailAlloc_2198_, 7, v_cFileName_x3f_2176_);
lean_ctor_set(v_reuseFailAlloc_2198_, 8, v_bcFileName_x3f_2177_);
lean_ctor_set(v_reuseFailAlloc_2198_, 9, v_errorOnKinds_2179_);
lean_ctor_set(v_reuseFailAlloc_2198_, 10, v_incrSaveFileName_x3f_2182_);
lean_ctor_set(v_reuseFailAlloc_2198_, 11, v_incrLoadFileName_x3f_2183_);
lean_ctor_set(v_reuseFailAlloc_2198_, 12, v_incrHeaderSaveFileName_x3f_2184_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 8, v_component_2162_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 9, v_printPrefix_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 10, v_printLibDir_2164_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 11, v_useStdin_2165_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 12, v_onlyDeps_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 13, v_onlySrcDeps_2167_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 14, v_depsJson_2168_);
lean_ctor_set_uint32(v_reuseFailAlloc_2198_, sizeof(void*)*13, v_trustLevel_2170_);
lean_ctor_set_uint32(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 4, v_numThreads_2171_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 15, v_jsonOutput_2178_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 16, v_printStats_2180_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 17, v_run_2181_);
v___x_2194_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2196_; 
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2194_);
v___x_2196_ = v___x_2153_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_dec(v___x_2158_);
lean_del_object(v___x_2153_);
lean_dec(v_a_2151_);
lean_dec_ref(v_opts_968_);
v___x_2200_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_2201_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2200_);
lean_dec_ref(v___x_2201_);
goto v___jp_1145_;
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec_ref(v_opts_968_);
v_a_2203_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2150_, 1);
v___x_2207_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2208_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2207_);
lean_dec_ref(v___x_2208_);
goto v___jp_2204_;
v___jp_2204_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_io_error_to_string(v_a_2203_);
v___x_2206_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2205_);
lean_dec_ref(v___x_2206_);
goto v___jp_1151_;
}
}
}
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_2210_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2209_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2262_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2262_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2262_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2215_ = lean_unsigned_to_nat(0u);
v___x_2216_ = lean_string_utf8_byte_size(v_a_2211_);
lean_inc(v_a_2211_);
v___x_2217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2217_, 0, v_a_2211_);
lean_ctor_set(v___x_2217_, 1, v___x_2215_);
lean_ctor_set(v___x_2217_, 2, v___x_2216_);
v___x_2218_ = l_String_Slice_toNat_x3f(v___x_2217_);
lean_dec_ref_known(v___x_2217_, 3);
if (lean_obj_tag(v___x_2218_) == 1)
{
lean_object* v_val_2219_; lean_object* v_leanOpts_2220_; lean_object* v_forwardedArgs_2221_; uint8_t v_component_2222_; uint8_t v_printPrefix_2223_; uint8_t v_printLibDir_2224_; uint8_t v_useStdin_2225_; uint8_t v_onlyDeps_2226_; uint8_t v_onlySrcDeps_2227_; uint8_t v_depsJson_2228_; lean_object* v_opts_2229_; uint32_t v_trustLevel_2230_; uint32_t v_numThreads_2231_; lean_object* v_rootDir_x3f_2232_; lean_object* v_setupFileName_x3f_2233_; lean_object* v_oleanFileName_x3f_2234_; lean_object* v_ileanFileName_x3f_2235_; lean_object* v_cFileName_x3f_2236_; lean_object* v_bcFileName_x3f_2237_; uint8_t v_jsonOutput_2238_; lean_object* v_errorOnKinds_2239_; uint8_t v_printStats_2240_; uint8_t v_run_2241_; lean_object* v_incrSaveFileName_x3f_2242_; lean_object* v_incrLoadFileName_x3f_2243_; lean_object* v_incrHeaderSaveFileName_x3f_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2259_; 
v_val_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_val_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v_leanOpts_2220_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2221_ = lean_ctor_get(v_opts_968_, 1);
v_component_2222_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2223_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2224_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_2225_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_2226_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2227_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2228_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2229_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_2230_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_2231_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2232_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2233_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2234_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_2235_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_2236_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_2237_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2238_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2239_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2240_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2241_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2242_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2243_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2244_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2246_ = v_opts_968_;
v_isShared_2247_ = v_isSharedCheck_2259_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2244_);
lean_inc(v_incrLoadFileName_x3f_2243_);
lean_inc(v_incrSaveFileName_x3f_2242_);
lean_inc(v_errorOnKinds_2239_);
lean_inc(v_bcFileName_x3f_2237_);
lean_inc(v_cFileName_x3f_2236_);
lean_inc(v_ileanFileName_x3f_2235_);
lean_inc(v_oleanFileName_x3f_2234_);
lean_inc(v_setupFileName_x3f_2233_);
lean_inc(v_rootDir_x3f_2232_);
lean_inc(v_opts_2229_);
lean_inc(v_forwardedArgs_2221_);
lean_inc(v_leanOpts_2220_);
lean_dec(v_opts_968_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2259_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2248_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_2249_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2220_, v___x_2248_, v_val_2219_);
v___x_2250_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2251_ = lean_string_append(v___x_2250_, v_a_2211_);
lean_dec(v_a_2211_);
v___x_2252_ = lean_array_push(v_forwardedArgs_2221_, v___x_2251_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 1, v___x_2252_);
lean_ctor_set(v___x_2246_, 0, v___x_2249_);
v___x_2254_ = v___x_2246_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_opts_2229_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_rootDir_x3f_2232_);
lean_ctor_set(v_reuseFailAlloc_2258_, 4, v_setupFileName_x3f_2233_);
lean_ctor_set(v_reuseFailAlloc_2258_, 5, v_oleanFileName_x3f_2234_);
lean_ctor_set(v_reuseFailAlloc_2258_, 6, v_ileanFileName_x3f_2235_);
lean_ctor_set(v_reuseFailAlloc_2258_, 7, v_cFileName_x3f_2236_);
lean_ctor_set(v_reuseFailAlloc_2258_, 8, v_bcFileName_x3f_2237_);
lean_ctor_set(v_reuseFailAlloc_2258_, 9, v_errorOnKinds_2239_);
lean_ctor_set(v_reuseFailAlloc_2258_, 10, v_incrSaveFileName_x3f_2242_);
lean_ctor_set(v_reuseFailAlloc_2258_, 11, v_incrLoadFileName_x3f_2243_);
lean_ctor_set(v_reuseFailAlloc_2258_, 12, v_incrHeaderSaveFileName_x3f_2244_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*13 + 8, v_component_2222_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*13 + 9, v_printPrefix_2223_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*13 + 10, v_printLibDir_2224_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*13 + 11, v_useStdin_2225_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*13 + 12, v_onlyDeps_2226_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*13 + 13, v_onlySrcDeps_2227_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*13 + 14, v_depsJson_2228_);
lean_ctor_set_uint32(v_reuseFailAlloc_2258_, sizeof(void*)*13, v_trustLevel_2230_);
lean_ctor_set_uint32(v_reuseFailAlloc_2258_, sizeof(void*)*13 + 4, v_numThreads_2231_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*13 + 15, v_jsonOutput_2238_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*13 + 16, v_printStats_2240_);
lean_ctor_set_uint8(v_reuseFailAlloc_2258_, sizeof(void*)*13 + 17, v_run_2241_);
v___x_2254_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2256_; 
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v___x_2254_);
v___x_2256_ = v___x_2213_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec(v___x_2218_);
lean_del_object(v___x_2213_);
lean_dec(v_a_2211_);
lean_dec_ref(v_opts_968_);
v___x_2260_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2261_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2260_);
lean_dec_ref(v___x_2261_);
goto v___jp_1020_;
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
lean_dec_ref(v_opts_968_);
v_a_2263_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2210_, 1);
v___x_2267_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2268_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2267_);
lean_dec_ref(v___x_2268_);
goto v___jp_2264_;
v___jp_2264_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_io_error_to_string(v_a_2263_);
v___x_2266_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2265_);
lean_dec_ref(v___x_2266_);
goto v___jp_1026_;
}
}
}
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2270_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2269_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2314_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2314_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2314_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v_leanOpts_2275_; lean_object* v_forwardedArgs_2276_; uint8_t v_component_2277_; uint8_t v_printPrefix_2278_; uint8_t v_printLibDir_2279_; uint8_t v_useStdin_2280_; uint8_t v_onlyDeps_2281_; uint8_t v_onlySrcDeps_2282_; uint8_t v_depsJson_2283_; lean_object* v_opts_2284_; uint32_t v_trustLevel_2285_; uint32_t v_numThreads_2286_; lean_object* v_setupFileName_x3f_2287_; lean_object* v_oleanFileName_x3f_2288_; lean_object* v_ileanFileName_x3f_2289_; lean_object* v_cFileName_x3f_2290_; lean_object* v_bcFileName_x3f_2291_; uint8_t v_jsonOutput_2292_; lean_object* v_errorOnKinds_2293_; uint8_t v_printStats_2294_; uint8_t v_run_2295_; lean_object* v_incrSaveFileName_x3f_2296_; lean_object* v_incrLoadFileName_x3f_2297_; lean_object* v_incrHeaderSaveFileName_x3f_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2312_; 
v_leanOpts_2275_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2276_ = lean_ctor_get(v_opts_968_, 1);
v_component_2277_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2278_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2279_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_2280_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_2281_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2282_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2283_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2284_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_2285_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_2286_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_setupFileName_x3f_2287_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2288_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_2289_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_2290_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_2291_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2292_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2293_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2294_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2295_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2296_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2297_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2298_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; 
v_unused_2313_ = lean_ctor_get(v_opts_968_, 3);
lean_dec(v_unused_2313_);
v___x_2300_ = v_opts_968_;
v_isShared_2301_ = v_isSharedCheck_2312_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2298_);
lean_inc(v_incrLoadFileName_x3f_2297_);
lean_inc(v_incrSaveFileName_x3f_2296_);
lean_inc(v_errorOnKinds_2293_);
lean_inc(v_bcFileName_x3f_2291_);
lean_inc(v_cFileName_x3f_2290_);
lean_inc(v_ileanFileName_x3f_2289_);
lean_inc(v_oleanFileName_x3f_2288_);
lean_inc(v_setupFileName_x3f_2287_);
lean_inc(v_opts_2284_);
lean_inc(v_forwardedArgs_2276_);
lean_inc(v_leanOpts_2275_);
lean_dec(v_opts_968_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2312_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2307_; 
v___x_2302_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2303_ = lean_string_append(v___x_2302_, v_a_2271_);
v___x_2304_ = lean_array_push(v_forwardedArgs_2276_, v___x_2303_);
v___x_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2305_, 0, v_a_2271_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 3, v___x_2305_);
lean_ctor_set(v___x_2300_, 1, v___x_2304_);
v___x_2307_ = v___x_2300_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_leanOpts_2275_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_opts_2284_);
lean_ctor_set(v_reuseFailAlloc_2311_, 3, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2311_, 4, v_setupFileName_x3f_2287_);
lean_ctor_set(v_reuseFailAlloc_2311_, 5, v_oleanFileName_x3f_2288_);
lean_ctor_set(v_reuseFailAlloc_2311_, 6, v_ileanFileName_x3f_2289_);
lean_ctor_set(v_reuseFailAlloc_2311_, 7, v_cFileName_x3f_2290_);
lean_ctor_set(v_reuseFailAlloc_2311_, 8, v_bcFileName_x3f_2291_);
lean_ctor_set(v_reuseFailAlloc_2311_, 9, v_errorOnKinds_2293_);
lean_ctor_set(v_reuseFailAlloc_2311_, 10, v_incrSaveFileName_x3f_2296_);
lean_ctor_set(v_reuseFailAlloc_2311_, 11, v_incrLoadFileName_x3f_2297_);
lean_ctor_set(v_reuseFailAlloc_2311_, 12, v_incrHeaderSaveFileName_x3f_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2311_, sizeof(void*)*13 + 8, v_component_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2311_, sizeof(void*)*13 + 9, v_printPrefix_2278_);
lean_ctor_set_uint8(v_reuseFailAlloc_2311_, sizeof(void*)*13 + 10, v_printLibDir_2279_);
lean_ctor_set_uint8(v_reuseFailAlloc_2311_, sizeof(void*)*13 + 11, v_useStdin_2280_);
lean_ctor_set_uint8(v_reuseFailAlloc_2311_, sizeof(void*)*13 + 12, v_onlyDeps_2281_);
lean_ctor_set_uint8(v_reuseFailAlloc_2311_, sizeof(void*)*13 + 13, v_onlySrcDeps_2282_);
lean_ctor_set_uint8(v_reuseFailAlloc_2311_, sizeof(void*)*13 + 14, v_depsJson_2283_);
lean_ctor_set_uint32(v_reuseFailAlloc_2311_, sizeof(void*)*13, v_trustLevel_2285_);
lean_ctor_set_uint32(v_reuseFailAlloc_2311_, sizeof(void*)*13 + 4, v_numThreads_2286_);
lean_ctor_set_uint8(v_reuseFailAlloc_2311_, sizeof(void*)*13 + 15, v_jsonOutput_2292_);
lean_ctor_set_uint8(v_reuseFailAlloc_2311_, sizeof(void*)*13 + 16, v_printStats_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2311_, sizeof(void*)*13 + 17, v_run_2295_);
v___x_2307_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2309_; 
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2307_);
v___x_2309_ = v___x_2273_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
lean_dec_ref(v_opts_968_);
v_a_2315_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2319_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2320_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2319_);
lean_dec_ref(v___x_2320_);
goto v___jp_2316_;
v___jp_2316_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_io_error_to_string(v_a_2315_);
v___x_2318_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2317_);
lean_dec_ref(v___x_2318_);
goto v___jp_1157_;
}
}
}
}
else
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25));
v___x_2322_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2321_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2363_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2363_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2363_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v_leanOpts_2327_; lean_object* v_forwardedArgs_2328_; uint8_t v_component_2329_; uint8_t v_printPrefix_2330_; uint8_t v_printLibDir_2331_; uint8_t v_useStdin_2332_; uint8_t v_onlyDeps_2333_; uint8_t v_onlySrcDeps_2334_; uint8_t v_depsJson_2335_; lean_object* v_opts_2336_; uint32_t v_trustLevel_2337_; uint32_t v_numThreads_2338_; lean_object* v_rootDir_x3f_2339_; lean_object* v_setupFileName_x3f_2340_; lean_object* v_oleanFileName_x3f_2341_; lean_object* v_cFileName_x3f_2342_; lean_object* v_bcFileName_x3f_2343_; uint8_t v_jsonOutput_2344_; lean_object* v_errorOnKinds_2345_; uint8_t v_printStats_2346_; uint8_t v_run_2347_; lean_object* v_incrSaveFileName_x3f_2348_; lean_object* v_incrLoadFileName_x3f_2349_; lean_object* v_incrHeaderSaveFileName_x3f_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2361_; 
v_leanOpts_2327_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2328_ = lean_ctor_get(v_opts_968_, 1);
v_component_2329_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2330_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2331_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_2332_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_2333_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2334_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2335_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2336_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_2337_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_2338_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2339_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2340_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2341_ = lean_ctor_get(v_opts_968_, 5);
v_cFileName_x3f_2342_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_2343_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2344_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2345_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2346_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2347_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2348_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2349_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2350_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2361_ == 0)
{
lean_object* v_unused_2362_; 
v_unused_2362_ = lean_ctor_get(v_opts_968_, 6);
lean_dec(v_unused_2362_);
v___x_2352_ = v_opts_968_;
v_isShared_2353_ = v_isSharedCheck_2361_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2350_);
lean_inc(v_incrLoadFileName_x3f_2349_);
lean_inc(v_incrSaveFileName_x3f_2348_);
lean_inc(v_errorOnKinds_2345_);
lean_inc(v_bcFileName_x3f_2343_);
lean_inc(v_cFileName_x3f_2342_);
lean_inc(v_oleanFileName_x3f_2341_);
lean_inc(v_setupFileName_x3f_2340_);
lean_inc(v_rootDir_x3f_2339_);
lean_inc(v_opts_2336_);
lean_inc(v_forwardedArgs_2328_);
lean_inc(v_leanOpts_2327_);
lean_dec(v_opts_968_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2361_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2354_, 0, v_a_2323_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 6, v___x_2354_);
v___x_2356_ = v___x_2352_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_leanOpts_2327_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_forwardedArgs_2328_);
lean_ctor_set(v_reuseFailAlloc_2360_, 2, v_opts_2336_);
lean_ctor_set(v_reuseFailAlloc_2360_, 3, v_rootDir_x3f_2339_);
lean_ctor_set(v_reuseFailAlloc_2360_, 4, v_setupFileName_x3f_2340_);
lean_ctor_set(v_reuseFailAlloc_2360_, 5, v_oleanFileName_x3f_2341_);
lean_ctor_set(v_reuseFailAlloc_2360_, 6, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2360_, 7, v_cFileName_x3f_2342_);
lean_ctor_set(v_reuseFailAlloc_2360_, 8, v_bcFileName_x3f_2343_);
lean_ctor_set(v_reuseFailAlloc_2360_, 9, v_errorOnKinds_2345_);
lean_ctor_set(v_reuseFailAlloc_2360_, 10, v_incrSaveFileName_x3f_2348_);
lean_ctor_set(v_reuseFailAlloc_2360_, 11, v_incrLoadFileName_x3f_2349_);
lean_ctor_set(v_reuseFailAlloc_2360_, 12, v_incrHeaderSaveFileName_x3f_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2360_, sizeof(void*)*13 + 8, v_component_2329_);
lean_ctor_set_uint8(v_reuseFailAlloc_2360_, sizeof(void*)*13 + 9, v_printPrefix_2330_);
lean_ctor_set_uint8(v_reuseFailAlloc_2360_, sizeof(void*)*13 + 10, v_printLibDir_2331_);
lean_ctor_set_uint8(v_reuseFailAlloc_2360_, sizeof(void*)*13 + 11, v_useStdin_2332_);
lean_ctor_set_uint8(v_reuseFailAlloc_2360_, sizeof(void*)*13 + 12, v_onlyDeps_2333_);
lean_ctor_set_uint8(v_reuseFailAlloc_2360_, sizeof(void*)*13 + 13, v_onlySrcDeps_2334_);
lean_ctor_set_uint8(v_reuseFailAlloc_2360_, sizeof(void*)*13 + 14, v_depsJson_2335_);
lean_ctor_set_uint32(v_reuseFailAlloc_2360_, sizeof(void*)*13, v_trustLevel_2337_);
lean_ctor_set_uint32(v_reuseFailAlloc_2360_, sizeof(void*)*13 + 4, v_numThreads_2338_);
lean_ctor_set_uint8(v_reuseFailAlloc_2360_, sizeof(void*)*13 + 15, v_jsonOutput_2344_);
lean_ctor_set_uint8(v_reuseFailAlloc_2360_, sizeof(void*)*13 + 16, v_printStats_2346_);
lean_ctor_set_uint8(v_reuseFailAlloc_2360_, sizeof(void*)*13 + 17, v_run_2347_);
v___x_2356_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2358_; 
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2356_);
v___x_2358_ = v___x_2325_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
lean_dec_ref(v_opts_968_);
v_a_2364_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2322_, 1);
v___x_2368_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2369_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2368_);
lean_dec_ref(v___x_2369_);
goto v___jp_2365_;
v___jp_2365_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_io_error_to_string(v_a_2364_);
v___x_2367_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2366_);
lean_dec_ref(v___x_2367_);
goto v___jp_1017_;
}
}
}
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2371_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2370_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2412_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2412_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2412_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v_leanOpts_2376_; lean_object* v_forwardedArgs_2377_; uint8_t v_component_2378_; uint8_t v_printPrefix_2379_; uint8_t v_printLibDir_2380_; uint8_t v_useStdin_2381_; uint8_t v_onlyDeps_2382_; uint8_t v_onlySrcDeps_2383_; uint8_t v_depsJson_2384_; lean_object* v_opts_2385_; uint32_t v_trustLevel_2386_; uint32_t v_numThreads_2387_; lean_object* v_rootDir_x3f_2388_; lean_object* v_setupFileName_x3f_2389_; lean_object* v_ileanFileName_x3f_2390_; lean_object* v_cFileName_x3f_2391_; lean_object* v_bcFileName_x3f_2392_; uint8_t v_jsonOutput_2393_; lean_object* v_errorOnKinds_2394_; uint8_t v_printStats_2395_; uint8_t v_run_2396_; lean_object* v_incrSaveFileName_x3f_2397_; lean_object* v_incrLoadFileName_x3f_2398_; lean_object* v_incrHeaderSaveFileName_x3f_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2410_; 
v_leanOpts_2376_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2377_ = lean_ctor_get(v_opts_968_, 1);
v_component_2378_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2379_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2380_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_2381_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_2382_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2383_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2384_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2385_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_2386_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_2387_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2388_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2389_ = lean_ctor_get(v_opts_968_, 4);
v_ileanFileName_x3f_2390_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_2391_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_2392_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2393_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2394_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2395_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2396_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2397_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2398_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2399_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; 
v_unused_2411_ = lean_ctor_get(v_opts_968_, 5);
lean_dec(v_unused_2411_);
v___x_2401_ = v_opts_968_;
v_isShared_2402_ = v_isSharedCheck_2410_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2399_);
lean_inc(v_incrLoadFileName_x3f_2398_);
lean_inc(v_incrSaveFileName_x3f_2397_);
lean_inc(v_errorOnKinds_2394_);
lean_inc(v_bcFileName_x3f_2392_);
lean_inc(v_cFileName_x3f_2391_);
lean_inc(v_ileanFileName_x3f_2390_);
lean_inc(v_setupFileName_x3f_2389_);
lean_inc(v_rootDir_x3f_2388_);
lean_inc(v_opts_2385_);
lean_inc(v_forwardedArgs_2377_);
lean_inc(v_leanOpts_2376_);
lean_dec(v_opts_968_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2410_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2403_, 0, v_a_2372_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 5, v___x_2403_);
v___x_2405_ = v___x_2401_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_leanOpts_2376_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_forwardedArgs_2377_);
lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_opts_2385_);
lean_ctor_set(v_reuseFailAlloc_2409_, 3, v_rootDir_x3f_2388_);
lean_ctor_set(v_reuseFailAlloc_2409_, 4, v_setupFileName_x3f_2389_);
lean_ctor_set(v_reuseFailAlloc_2409_, 5, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2409_, 6, v_ileanFileName_x3f_2390_);
lean_ctor_set(v_reuseFailAlloc_2409_, 7, v_cFileName_x3f_2391_);
lean_ctor_set(v_reuseFailAlloc_2409_, 8, v_bcFileName_x3f_2392_);
lean_ctor_set(v_reuseFailAlloc_2409_, 9, v_errorOnKinds_2394_);
lean_ctor_set(v_reuseFailAlloc_2409_, 10, v_incrSaveFileName_x3f_2397_);
lean_ctor_set(v_reuseFailAlloc_2409_, 11, v_incrLoadFileName_x3f_2398_);
lean_ctor_set(v_reuseFailAlloc_2409_, 12, v_incrHeaderSaveFileName_x3f_2399_);
lean_ctor_set_uint8(v_reuseFailAlloc_2409_, sizeof(void*)*13 + 8, v_component_2378_);
lean_ctor_set_uint8(v_reuseFailAlloc_2409_, sizeof(void*)*13 + 9, v_printPrefix_2379_);
lean_ctor_set_uint8(v_reuseFailAlloc_2409_, sizeof(void*)*13 + 10, v_printLibDir_2380_);
lean_ctor_set_uint8(v_reuseFailAlloc_2409_, sizeof(void*)*13 + 11, v_useStdin_2381_);
lean_ctor_set_uint8(v_reuseFailAlloc_2409_, sizeof(void*)*13 + 12, v_onlyDeps_2382_);
lean_ctor_set_uint8(v_reuseFailAlloc_2409_, sizeof(void*)*13 + 13, v_onlySrcDeps_2383_);
lean_ctor_set_uint8(v_reuseFailAlloc_2409_, sizeof(void*)*13 + 14, v_depsJson_2384_);
lean_ctor_set_uint32(v_reuseFailAlloc_2409_, sizeof(void*)*13, v_trustLevel_2386_);
lean_ctor_set_uint32(v_reuseFailAlloc_2409_, sizeof(void*)*13 + 4, v_numThreads_2387_);
lean_ctor_set_uint8(v_reuseFailAlloc_2409_, sizeof(void*)*13 + 15, v_jsonOutput_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2409_, sizeof(void*)*13 + 16, v_printStats_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2409_, sizeof(void*)*13 + 17, v_run_2396_);
v___x_2405_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2407_; 
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2405_);
v___x_2407_ = v___x_2374_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_dec_ref(v_opts_968_);
v_a_2413_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2371_, 1);
v___x_2417_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2418_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2417_);
lean_dec_ref(v___x_2418_);
goto v___jp_2414_;
v___jp_2414_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = lean_io_error_to_string(v_a_2413_);
v___x_2416_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2415_);
lean_dec_ref(v___x_2416_);
goto v___jp_1163_;
}
}
}
}
else
{
lean_object* v_leanOpts_2419_; lean_object* v_forwardedArgs_2420_; uint8_t v_component_2421_; uint8_t v_printPrefix_2422_; uint8_t v_printLibDir_2423_; uint8_t v_useStdin_2424_; uint8_t v_onlyDeps_2425_; uint8_t v_onlySrcDeps_2426_; uint8_t v_depsJson_2427_; lean_object* v_opts_2428_; uint32_t v_trustLevel_2429_; uint32_t v_numThreads_2430_; lean_object* v_rootDir_x3f_2431_; lean_object* v_setupFileName_x3f_2432_; lean_object* v_oleanFileName_x3f_2433_; lean_object* v_ileanFileName_x3f_2434_; lean_object* v_cFileName_x3f_2435_; lean_object* v_bcFileName_x3f_2436_; uint8_t v_jsonOutput_2437_; lean_object* v_errorOnKinds_2438_; uint8_t v_printStats_2439_; lean_object* v_incrSaveFileName_x3f_2440_; lean_object* v_incrLoadFileName_x3f_2441_; lean_object* v_incrHeaderSaveFileName_x3f_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2452_; 
lean_dec(v_optArg_x3f_970_);
v_leanOpts_2419_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2420_ = lean_ctor_get(v_opts_968_, 1);
v_component_2421_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2422_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2423_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_2424_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_2425_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2426_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2427_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2428_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_2429_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_2430_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2431_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2432_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2433_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_2434_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_2435_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_2436_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2437_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2438_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2439_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_incrSaveFileName_x3f_2440_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2441_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2442_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2444_ = v_opts_968_;
v_isShared_2445_ = v_isSharedCheck_2452_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2442_);
lean_inc(v_incrLoadFileName_x3f_2441_);
lean_inc(v_incrSaveFileName_x3f_2440_);
lean_inc(v_errorOnKinds_2438_);
lean_inc(v_bcFileName_x3f_2436_);
lean_inc(v_cFileName_x3f_2435_);
lean_inc(v_ileanFileName_x3f_2434_);
lean_inc(v_oleanFileName_x3f_2433_);
lean_inc(v_setupFileName_x3f_2432_);
lean_inc(v_rootDir_x3f_2431_);
lean_inc(v_opts_2428_);
lean_inc(v_forwardedArgs_2420_);
lean_inc(v_leanOpts_2419_);
lean_dec(v_opts_968_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2452_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2446_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2447_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2419_, v___x_2446_, v___x_1211_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2447_);
v___x_2449_ = v___x_2444_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_forwardedArgs_2420_);
lean_ctor_set(v_reuseFailAlloc_2451_, 2, v_opts_2428_);
lean_ctor_set(v_reuseFailAlloc_2451_, 3, v_rootDir_x3f_2431_);
lean_ctor_set(v_reuseFailAlloc_2451_, 4, v_setupFileName_x3f_2432_);
lean_ctor_set(v_reuseFailAlloc_2451_, 5, v_oleanFileName_x3f_2433_);
lean_ctor_set(v_reuseFailAlloc_2451_, 6, v_ileanFileName_x3f_2434_);
lean_ctor_set(v_reuseFailAlloc_2451_, 7, v_cFileName_x3f_2435_);
lean_ctor_set(v_reuseFailAlloc_2451_, 8, v_bcFileName_x3f_2436_);
lean_ctor_set(v_reuseFailAlloc_2451_, 9, v_errorOnKinds_2438_);
lean_ctor_set(v_reuseFailAlloc_2451_, 10, v_incrSaveFileName_x3f_2440_);
lean_ctor_set(v_reuseFailAlloc_2451_, 11, v_incrLoadFileName_x3f_2441_);
lean_ctor_set(v_reuseFailAlloc_2451_, 12, v_incrHeaderSaveFileName_x3f_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 8, v_component_2421_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 9, v_printPrefix_2422_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 10, v_printLibDir_2423_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 11, v_useStdin_2424_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 12, v_onlyDeps_2425_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 13, v_onlySrcDeps_2426_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 14, v_depsJson_2427_);
lean_ctor_set_uint32(v_reuseFailAlloc_2451_, sizeof(void*)*13, v_trustLevel_2429_);
lean_ctor_set_uint32(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 4, v_numThreads_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 15, v_jsonOutput_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 16, v_printStats_2439_);
v___x_2449_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; 
lean_ctor_set_uint8(v___x_2449_, sizeof(void*)*13 + 17, v___x_1213_);
v___x_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
return v___x_2450_;
}
}
}
}
else
{
lean_object* v_leanOpts_2453_; lean_object* v_forwardedArgs_2454_; uint8_t v_component_2455_; uint8_t v_printPrefix_2456_; uint8_t v_printLibDir_2457_; uint8_t v_onlyDeps_2458_; uint8_t v_onlySrcDeps_2459_; uint8_t v_depsJson_2460_; lean_object* v_opts_2461_; uint32_t v_trustLevel_2462_; uint32_t v_numThreads_2463_; lean_object* v_rootDir_x3f_2464_; lean_object* v_setupFileName_x3f_2465_; lean_object* v_oleanFileName_x3f_2466_; lean_object* v_ileanFileName_x3f_2467_; lean_object* v_cFileName_x3f_2468_; lean_object* v_bcFileName_x3f_2469_; uint8_t v_jsonOutput_2470_; lean_object* v_errorOnKinds_2471_; uint8_t v_printStats_2472_; uint8_t v_run_2473_; lean_object* v_incrSaveFileName_x3f_2474_; lean_object* v_incrLoadFileName_x3f_2475_; lean_object* v_incrHeaderSaveFileName_x3f_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v_optArg_x3f_970_);
v_leanOpts_2453_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2454_ = lean_ctor_get(v_opts_968_, 1);
v_component_2455_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2456_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2457_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_onlyDeps_2458_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2459_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2460_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2461_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_2462_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_2463_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2464_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2465_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2466_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_2467_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_2468_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_2469_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2470_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2471_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2472_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2473_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2474_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2475_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2476_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2478_ = v_opts_968_;
v_isShared_2479_ = v_isSharedCheck_2484_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2476_);
lean_inc(v_incrLoadFileName_x3f_2475_);
lean_inc(v_incrSaveFileName_x3f_2474_);
lean_inc(v_errorOnKinds_2471_);
lean_inc(v_bcFileName_x3f_2469_);
lean_inc(v_cFileName_x3f_2468_);
lean_inc(v_ileanFileName_x3f_2467_);
lean_inc(v_oleanFileName_x3f_2466_);
lean_inc(v_setupFileName_x3f_2465_);
lean_inc(v_rootDir_x3f_2464_);
lean_inc(v_opts_2461_);
lean_inc(v_forwardedArgs_2454_);
lean_inc(v_leanOpts_2453_);
lean_dec(v_opts_968_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2484_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_leanOpts_2453_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_forwardedArgs_2454_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_opts_2461_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_rootDir_x3f_2464_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v_setupFileName_x3f_2465_);
lean_ctor_set(v_reuseFailAlloc_2483_, 5, v_oleanFileName_x3f_2466_);
lean_ctor_set(v_reuseFailAlloc_2483_, 6, v_ileanFileName_x3f_2467_);
lean_ctor_set(v_reuseFailAlloc_2483_, 7, v_cFileName_x3f_2468_);
lean_ctor_set(v_reuseFailAlloc_2483_, 8, v_bcFileName_x3f_2469_);
lean_ctor_set(v_reuseFailAlloc_2483_, 9, v_errorOnKinds_2471_);
lean_ctor_set(v_reuseFailAlloc_2483_, 10, v_incrSaveFileName_x3f_2474_);
lean_ctor_set(v_reuseFailAlloc_2483_, 11, v_incrLoadFileName_x3f_2475_);
lean_ctor_set(v_reuseFailAlloc_2483_, 12, v_incrHeaderSaveFileName_x3f_2476_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*13 + 8, v_component_2455_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*13 + 9, v_printPrefix_2456_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*13 + 10, v_printLibDir_2457_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*13 + 12, v_onlyDeps_2458_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*13 + 13, v_onlySrcDeps_2459_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*13 + 14, v_depsJson_2460_);
lean_ctor_set_uint32(v_reuseFailAlloc_2483_, sizeof(void*)*13, v_trustLevel_2462_);
lean_ctor_set_uint32(v_reuseFailAlloc_2483_, sizeof(void*)*13 + 4, v_numThreads_2463_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*13 + 15, v_jsonOutput_2470_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*13 + 16, v_printStats_2472_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*13 + 17, v_run_2473_);
v___x_2481_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
lean_object* v___x_2482_; 
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*13 + 11, v___x_1211_);
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
return v___x_2482_;
}
}
}
}
else
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2486_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2485_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2548_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2548_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2548_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2491_ = lean_unsigned_to_nat(0u);
v___x_2492_ = lean_string_utf8_byte_size(v_a_2487_);
lean_inc(v_a_2487_);
v___x_2493_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2493_, 0, v_a_2487_);
lean_ctor_set(v___x_2493_, 1, v___x_2491_);
lean_ctor_set(v___x_2493_, 2, v___x_2492_);
v___x_2494_ = l_String_Slice_toNat_x3f(v___x_2493_);
lean_dec_ref_known(v___x_2493_, 3);
if (lean_obj_tag(v___x_2494_) == 1)
{
lean_object* v_val_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v_val_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_val_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v___x_2496_ = lean_unsigned_to_nat(4u);
v___x_2497_ = lean_unsigned_to_nat(2u);
v___x_2498_ = lean_nat_shiftr(v_val_2495_, v___x_2497_);
lean_dec(v_val_2495_);
v___x_2499_ = lean_nat_mul(v___x_2498_, v___x_2496_);
lean_dec(v___x_2498_);
v___x_2500_ = lean_unsigned_to_nat(1024u);
v___x_2501_ = lean_nat_mul(v___x_2499_, v___x_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28);
v___x_2503_ = lean_nat_dec_lt(v___x_2501_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_dec(v___x_2501_);
lean_del_object(v___x_2489_);
lean_dec(v_a_2487_);
lean_dec_ref(v_opts_968_);
v___x_2504_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2505_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2504_);
lean_dec_ref(v___x_2505_);
goto v___jp_1005_;
}
else
{
size_t v___x_2506_; lean_object* v___x_2507_; lean_object* v_leanOpts_2508_; lean_object* v_forwardedArgs_2509_; uint8_t v_component_2510_; uint8_t v_printPrefix_2511_; uint8_t v_printLibDir_2512_; uint8_t v_useStdin_2513_; uint8_t v_onlyDeps_2514_; uint8_t v_onlySrcDeps_2515_; uint8_t v_depsJson_2516_; lean_object* v_opts_2517_; uint32_t v_trustLevel_2518_; uint32_t v_numThreads_2519_; lean_object* v_rootDir_x3f_2520_; lean_object* v_setupFileName_x3f_2521_; lean_object* v_oleanFileName_x3f_2522_; lean_object* v_ileanFileName_x3f_2523_; lean_object* v_cFileName_x3f_2524_; lean_object* v_bcFileName_x3f_2525_; uint8_t v_jsonOutput_2526_; lean_object* v_errorOnKinds_2527_; uint8_t v_printStats_2528_; uint8_t v_run_2529_; lean_object* v_incrSaveFileName_x3f_2530_; lean_object* v_incrLoadFileName_x3f_2531_; lean_object* v_incrHeaderSaveFileName_x3f_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2545_; 
v___x_2506_ = lean_usize_of_nat(v___x_2501_);
lean_dec(v___x_2501_);
v___x_2507_ = lean_internal_set_thread_stack_size(v___x_2506_);
v_leanOpts_2508_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2509_ = lean_ctor_get(v_opts_968_, 1);
v_component_2510_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2511_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2512_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_2513_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_2514_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2515_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2516_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2517_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_2518_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_2519_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2520_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2521_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2522_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_2523_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_2524_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_2525_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2526_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2527_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2528_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2529_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2530_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2531_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2532_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2534_ = v_opts_968_;
v_isShared_2535_ = v_isSharedCheck_2545_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2532_);
lean_inc(v_incrLoadFileName_x3f_2531_);
lean_inc(v_incrSaveFileName_x3f_2530_);
lean_inc(v_errorOnKinds_2527_);
lean_inc(v_bcFileName_x3f_2525_);
lean_inc(v_cFileName_x3f_2524_);
lean_inc(v_ileanFileName_x3f_2523_);
lean_inc(v_oleanFileName_x3f_2522_);
lean_inc(v_setupFileName_x3f_2521_);
lean_inc(v_rootDir_x3f_2520_);
lean_inc(v_opts_2517_);
lean_inc(v_forwardedArgs_2509_);
lean_inc(v_leanOpts_2508_);
lean_dec(v_opts_968_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2545_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2536_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2537_ = lean_string_append(v___x_2536_, v_a_2487_);
lean_dec(v_a_2487_);
v___x_2538_ = lean_array_push(v_forwardedArgs_2509_, v___x_2537_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 1, v___x_2538_);
v___x_2540_ = v___x_2534_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_leanOpts_2508_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2544_, 2, v_opts_2517_);
lean_ctor_set(v_reuseFailAlloc_2544_, 3, v_rootDir_x3f_2520_);
lean_ctor_set(v_reuseFailAlloc_2544_, 4, v_setupFileName_x3f_2521_);
lean_ctor_set(v_reuseFailAlloc_2544_, 5, v_oleanFileName_x3f_2522_);
lean_ctor_set(v_reuseFailAlloc_2544_, 6, v_ileanFileName_x3f_2523_);
lean_ctor_set(v_reuseFailAlloc_2544_, 7, v_cFileName_x3f_2524_);
lean_ctor_set(v_reuseFailAlloc_2544_, 8, v_bcFileName_x3f_2525_);
lean_ctor_set(v_reuseFailAlloc_2544_, 9, v_errorOnKinds_2527_);
lean_ctor_set(v_reuseFailAlloc_2544_, 10, v_incrSaveFileName_x3f_2530_);
lean_ctor_set(v_reuseFailAlloc_2544_, 11, v_incrLoadFileName_x3f_2531_);
lean_ctor_set(v_reuseFailAlloc_2544_, 12, v_incrHeaderSaveFileName_x3f_2532_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*13 + 8, v_component_2510_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*13 + 9, v_printPrefix_2511_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*13 + 10, v_printLibDir_2512_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*13 + 11, v_useStdin_2513_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*13 + 12, v_onlyDeps_2514_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*13 + 13, v_onlySrcDeps_2515_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*13 + 14, v_depsJson_2516_);
lean_ctor_set_uint32(v_reuseFailAlloc_2544_, sizeof(void*)*13, v_trustLevel_2518_);
lean_ctor_set_uint32(v_reuseFailAlloc_2544_, sizeof(void*)*13 + 4, v_numThreads_2519_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*13 + 15, v_jsonOutput_2526_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*13 + 16, v_printStats_2528_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*13 + 17, v_run_2529_);
v___x_2540_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2542_; 
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2540_);
v___x_2542_ = v___x_2489_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
lean_dec(v___x_2494_);
lean_del_object(v___x_2489_);
lean_dec(v_a_2487_);
lean_dec_ref(v_opts_968_);
v___x_2546_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2547_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2546_);
lean_dec_ref(v___x_2547_);
goto v___jp_1002_;
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
lean_dec_ref(v_opts_968_);
v_a_2549_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2486_, 1);
v___x_2553_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2554_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2553_);
lean_dec_ref(v___x_2554_);
goto v___jp_2550_;
v___jp_2550_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_io_error_to_string(v_a_2549_);
v___x_2552_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2551_);
lean_dec_ref(v___x_2552_);
goto v___jp_1011_;
}
}
}
}
else
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2556_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2555_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2597_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2597_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2597_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v_leanOpts_2561_; lean_object* v_forwardedArgs_2562_; uint8_t v_component_2563_; uint8_t v_printPrefix_2564_; uint8_t v_printLibDir_2565_; uint8_t v_useStdin_2566_; uint8_t v_onlyDeps_2567_; uint8_t v_onlySrcDeps_2568_; uint8_t v_depsJson_2569_; lean_object* v_opts_2570_; uint32_t v_trustLevel_2571_; uint32_t v_numThreads_2572_; lean_object* v_rootDir_x3f_2573_; lean_object* v_setupFileName_x3f_2574_; lean_object* v_oleanFileName_x3f_2575_; lean_object* v_ileanFileName_x3f_2576_; lean_object* v_cFileName_x3f_2577_; uint8_t v_jsonOutput_2578_; lean_object* v_errorOnKinds_2579_; uint8_t v_printStats_2580_; uint8_t v_run_2581_; lean_object* v_incrSaveFileName_x3f_2582_; lean_object* v_incrLoadFileName_x3f_2583_; lean_object* v_incrHeaderSaveFileName_x3f_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2595_; 
v_leanOpts_2561_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2562_ = lean_ctor_get(v_opts_968_, 1);
v_component_2563_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2564_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2565_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_2566_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_2567_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2568_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2569_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2570_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_2571_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_2572_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2573_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2574_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2575_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_2576_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_2577_ = lean_ctor_get(v_opts_968_, 7);
v_jsonOutput_2578_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2579_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2580_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2581_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2582_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2583_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2584_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2595_ == 0)
{
lean_object* v_unused_2596_; 
v_unused_2596_ = lean_ctor_get(v_opts_968_, 8);
lean_dec(v_unused_2596_);
v___x_2586_ = v_opts_968_;
v_isShared_2587_ = v_isSharedCheck_2595_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2584_);
lean_inc(v_incrLoadFileName_x3f_2583_);
lean_inc(v_incrSaveFileName_x3f_2582_);
lean_inc(v_errorOnKinds_2579_);
lean_inc(v_cFileName_x3f_2577_);
lean_inc(v_ileanFileName_x3f_2576_);
lean_inc(v_oleanFileName_x3f_2575_);
lean_inc(v_setupFileName_x3f_2574_);
lean_inc(v_rootDir_x3f_2573_);
lean_inc(v_opts_2570_);
lean_inc(v_forwardedArgs_2562_);
lean_inc(v_leanOpts_2561_);
lean_dec(v_opts_968_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2595_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2588_, 0, v_a_2557_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 8, v___x_2588_);
v___x_2590_ = v___x_2586_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_leanOpts_2561_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_forwardedArgs_2562_);
lean_ctor_set(v_reuseFailAlloc_2594_, 2, v_opts_2570_);
lean_ctor_set(v_reuseFailAlloc_2594_, 3, v_rootDir_x3f_2573_);
lean_ctor_set(v_reuseFailAlloc_2594_, 4, v_setupFileName_x3f_2574_);
lean_ctor_set(v_reuseFailAlloc_2594_, 5, v_oleanFileName_x3f_2575_);
lean_ctor_set(v_reuseFailAlloc_2594_, 6, v_ileanFileName_x3f_2576_);
lean_ctor_set(v_reuseFailAlloc_2594_, 7, v_cFileName_x3f_2577_);
lean_ctor_set(v_reuseFailAlloc_2594_, 8, v___x_2588_);
lean_ctor_set(v_reuseFailAlloc_2594_, 9, v_errorOnKinds_2579_);
lean_ctor_set(v_reuseFailAlloc_2594_, 10, v_incrSaveFileName_x3f_2582_);
lean_ctor_set(v_reuseFailAlloc_2594_, 11, v_incrLoadFileName_x3f_2583_);
lean_ctor_set(v_reuseFailAlloc_2594_, 12, v_incrHeaderSaveFileName_x3f_2584_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*13 + 8, v_component_2563_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*13 + 9, v_printPrefix_2564_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*13 + 10, v_printLibDir_2565_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*13 + 11, v_useStdin_2566_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*13 + 12, v_onlyDeps_2567_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*13 + 13, v_onlySrcDeps_2568_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*13 + 14, v_depsJson_2569_);
lean_ctor_set_uint32(v_reuseFailAlloc_2594_, sizeof(void*)*13, v_trustLevel_2571_);
lean_ctor_set_uint32(v_reuseFailAlloc_2594_, sizeof(void*)*13 + 4, v_numThreads_2572_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*13 + 15, v_jsonOutput_2578_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*13 + 16, v_printStats_2580_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*13 + 17, v_run_2581_);
v___x_2590_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_object* v___x_2592_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2590_);
v___x_2592_ = v___x_2559_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2598_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_dec_ref(v_opts_968_);
v_a_2598_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2556_, 1);
v___x_2602_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2603_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2602_);
lean_dec_ref(v___x_2603_);
goto v___jp_2599_;
v___jp_2599_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_io_error_to_string(v_a_2598_);
v___x_2601_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2600_);
lean_dec_ref(v___x_2601_);
goto v___jp_1169_;
}
}
}
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2605_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2604_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2646_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2646_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2646_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v_leanOpts_2610_; lean_object* v_forwardedArgs_2611_; uint8_t v_component_2612_; uint8_t v_printPrefix_2613_; uint8_t v_printLibDir_2614_; uint8_t v_useStdin_2615_; uint8_t v_onlyDeps_2616_; uint8_t v_onlySrcDeps_2617_; uint8_t v_depsJson_2618_; lean_object* v_opts_2619_; uint32_t v_trustLevel_2620_; uint32_t v_numThreads_2621_; lean_object* v_rootDir_x3f_2622_; lean_object* v_setupFileName_x3f_2623_; lean_object* v_oleanFileName_x3f_2624_; lean_object* v_ileanFileName_x3f_2625_; lean_object* v_bcFileName_x3f_2626_; uint8_t v_jsonOutput_2627_; lean_object* v_errorOnKinds_2628_; uint8_t v_printStats_2629_; uint8_t v_run_2630_; lean_object* v_incrSaveFileName_x3f_2631_; lean_object* v_incrLoadFileName_x3f_2632_; lean_object* v_incrHeaderSaveFileName_x3f_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2644_; 
v_leanOpts_2610_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2611_ = lean_ctor_get(v_opts_968_, 1);
v_component_2612_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2613_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2614_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_2615_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_2616_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2617_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2618_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2619_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_2620_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_numThreads_2621_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2622_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2623_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2624_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_2625_ = lean_ctor_get(v_opts_968_, 6);
v_bcFileName_x3f_2626_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2627_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2628_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2629_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2630_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2631_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2632_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2633_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2644_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2644_ == 0)
{
lean_object* v_unused_2645_; 
v_unused_2645_ = lean_ctor_get(v_opts_968_, 7);
lean_dec(v_unused_2645_);
v___x_2635_ = v_opts_968_;
v_isShared_2636_ = v_isSharedCheck_2644_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2633_);
lean_inc(v_incrLoadFileName_x3f_2632_);
lean_inc(v_incrSaveFileName_x3f_2631_);
lean_inc(v_errorOnKinds_2628_);
lean_inc(v_bcFileName_x3f_2626_);
lean_inc(v_ileanFileName_x3f_2625_);
lean_inc(v_oleanFileName_x3f_2624_);
lean_inc(v_setupFileName_x3f_2623_);
lean_inc(v_rootDir_x3f_2622_);
lean_inc(v_opts_2619_);
lean_inc(v_forwardedArgs_2611_);
lean_inc(v_leanOpts_2610_);
lean_dec(v_opts_968_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2644_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2637_, 0, v_a_2606_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 7, v___x_2637_);
v___x_2639_ = v___x_2635_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_leanOpts_2610_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_forwardedArgs_2611_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_opts_2619_);
lean_ctor_set(v_reuseFailAlloc_2643_, 3, v_rootDir_x3f_2622_);
lean_ctor_set(v_reuseFailAlloc_2643_, 4, v_setupFileName_x3f_2623_);
lean_ctor_set(v_reuseFailAlloc_2643_, 5, v_oleanFileName_x3f_2624_);
lean_ctor_set(v_reuseFailAlloc_2643_, 6, v_ileanFileName_x3f_2625_);
lean_ctor_set(v_reuseFailAlloc_2643_, 7, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2643_, 8, v_bcFileName_x3f_2626_);
lean_ctor_set(v_reuseFailAlloc_2643_, 9, v_errorOnKinds_2628_);
lean_ctor_set(v_reuseFailAlloc_2643_, 10, v_incrSaveFileName_x3f_2631_);
lean_ctor_set(v_reuseFailAlloc_2643_, 11, v_incrLoadFileName_x3f_2632_);
lean_ctor_set(v_reuseFailAlloc_2643_, 12, v_incrHeaderSaveFileName_x3f_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*13 + 8, v_component_2612_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*13 + 9, v_printPrefix_2613_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*13 + 10, v_printLibDir_2614_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*13 + 11, v_useStdin_2615_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*13 + 12, v_onlyDeps_2616_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*13 + 13, v_onlySrcDeps_2617_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*13 + 14, v_depsJson_2618_);
lean_ctor_set_uint32(v_reuseFailAlloc_2643_, sizeof(void*)*13, v_trustLevel_2620_);
lean_ctor_set_uint32(v_reuseFailAlloc_2643_, sizeof(void*)*13 + 4, v_numThreads_2621_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*13 + 15, v_jsonOutput_2627_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*13 + 16, v_printStats_2629_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*13 + 17, v_run_2630_);
v___x_2639_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2641_; 
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2639_);
v___x_2641_ = v___x_2608_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_dec_ref(v_opts_968_);
v_a_2647_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2605_, 1);
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
goto v___jp_999_;
}
}
}
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec(v_optArg_x3f_970_);
lean_dec_ref(v_opts_968_);
v___x_2653_ = l___private_Lean_Shell_0__Lean_featuresString;
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
goto v___jp_1175_;
}
}
}
}
else
{
lean_object* v___x_2670_; 
lean_dec(v_optArg_x3f_970_);
lean_dec_ref(v_opts_968_);
v___x_2670_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1199_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2678_; 
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; 
v_unused_2679_ = lean_ctor_get(v___x_2670_, 0);
lean_dec(v_unused_2679_);
v___x_2672_ = v___x_2670_;
v_isShared_2673_ = v_isSharedCheck_2678_;
goto v_resetjp_2671_;
}
else
{
lean_dec(v___x_2670_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2678_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2674_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2673_ == 0)
{
lean_ctor_set_tag(v___x_2672_, 1);
lean_ctor_set(v___x_2672_, 0, v___x_2674_);
v___x_2676_ = v___x_2672_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v_a_2680_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2684_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2685_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2684_);
lean_dec_ref(v___x_2685_);
goto v___jp_2681_;
v___jp_2681_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = lean_io_error_to_string(v_a_2680_);
v___x_2683_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2682_);
lean_dec_ref(v___x_2683_);
goto v___jp_993_;
}
}
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_dec(v_optArg_x3f_970_);
lean_dec_ref(v_opts_968_);
v___x_2686_ = l_Lean_githash;
v___x_2687_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2686_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2695_; 
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; 
v_unused_2696_ = lean_ctor_get(v___x_2687_, 0);
lean_dec(v_unused_2696_);
v___x_2689_ = v___x_2687_;
v_isShared_2690_ = v_isSharedCheck_2695_;
goto v_resetjp_2688_;
}
else
{
lean_dec(v___x_2687_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2695_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; lean_object* v___x_2693_; 
v___x_2691_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2690_ == 0)
{
lean_ctor_set_tag(v___x_2689_, 1);
lean_ctor_set(v___x_2689_, 0, v___x_2691_);
v___x_2693_ = v___x_2689_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v_a_2697_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2697_);
lean_dec_ref_known(v___x_2687_, 1);
v___x_2701_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2702_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2701_);
lean_dec_ref(v___x_2702_);
goto v___jp_2698_;
v___jp_2698_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_io_error_to_string(v_a_2697_);
v___x_2700_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2699_);
lean_dec_ref(v___x_2700_);
goto v___jp_1181_;
}
}
}
}
else
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
lean_dec(v_optArg_x3f_970_);
lean_dec_ref(v_opts_968_);
v___x_2703_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2704_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2703_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2712_; 
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; 
v_unused_2713_ = lean_ctor_get(v___x_2704_, 0);
lean_dec(v_unused_2713_);
v___x_2706_ = v___x_2704_;
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
else
{
lean_dec(v___x_2704_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2708_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2707_ == 0)
{
lean_ctor_set_tag(v___x_2706_, 1);
lean_ctor_set(v___x_2706_, 0, v___x_2708_);
v___x_2710_ = v___x_2706_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v_a_2714_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2704_, 1);
v___x_2718_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2719_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2718_);
lean_dec_ref(v___x_2719_);
goto v___jp_2715_;
v___jp_2715_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = lean_io_error_to_string(v_a_2714_);
v___x_2717_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2716_);
lean_dec_ref(v___x_2717_);
goto v___jp_987_;
}
}
}
}
else
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
lean_dec(v_optArg_x3f_970_);
lean_dec_ref(v_opts_968_);
v___x_2720_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2721_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2720_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2729_; 
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; 
v_unused_2730_ = lean_ctor_get(v___x_2721_, 0);
lean_dec(v_unused_2730_);
v___x_2723_ = v___x_2721_;
v_isShared_2724_ = v_isSharedCheck_2729_;
goto v_resetjp_2722_;
}
else
{
lean_dec(v___x_2721_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2729_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
v___x_2725_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2724_ == 0)
{
lean_ctor_set_tag(v___x_2723_, 1);
lean_ctor_set(v___x_2723_, 0, v___x_2725_);
v___x_2727_ = v___x_2723_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_a_2731_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2721_, 1);
v___x_2735_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2736_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2735_);
lean_dec_ref(v___x_2736_);
goto v___jp_2732_;
v___jp_2732_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = lean_io_error_to_string(v_a_2731_);
v___x_2734_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2733_);
lean_dec_ref(v___x_2734_);
goto v___jp_1187_;
}
}
}
}
else
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2738_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2737_, v_optArg_x3f_970_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2792_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2792_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2792_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2743_ = lean_unsigned_to_nat(0u);
v___x_2744_ = lean_string_utf8_byte_size(v_a_2739_);
lean_inc(v_a_2739_);
v___x_2745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2745_, 0, v_a_2739_);
lean_ctor_set(v___x_2745_, 1, v___x_2743_);
lean_ctor_set(v___x_2745_, 2, v___x_2744_);
v___x_2746_ = l_String_Slice_toNat_x3f(v___x_2745_);
lean_dec_ref_known(v___x_2745_, 3);
if (lean_obj_tag(v___x_2746_) == 1)
{
lean_object* v_val_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; 
v_val_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_val_2747_);
lean_dec_ref_known(v___x_2746_, 1);
v___x_2748_ = lean_cstr_to_nat("4294967296");
v___x_2749_ = lean_nat_dec_lt(v_val_2747_, v___x_2748_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
lean_dec(v_val_2747_);
lean_del_object(v___x_2741_);
lean_dec(v_a_2739_);
lean_dec_ref(v_opts_968_);
v___x_2750_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__35));
v___x_2751_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2750_);
lean_dec_ref(v___x_2751_);
goto v___jp_975_;
}
else
{
lean_object* v_leanOpts_2752_; lean_object* v_forwardedArgs_2753_; uint8_t v_component_2754_; uint8_t v_printPrefix_2755_; uint8_t v_printLibDir_2756_; uint8_t v_useStdin_2757_; uint8_t v_onlyDeps_2758_; uint8_t v_onlySrcDeps_2759_; uint8_t v_depsJson_2760_; lean_object* v_opts_2761_; uint32_t v_trustLevel_2762_; lean_object* v_rootDir_x3f_2763_; lean_object* v_setupFileName_x3f_2764_; lean_object* v_oleanFileName_x3f_2765_; lean_object* v_ileanFileName_x3f_2766_; lean_object* v_cFileName_x3f_2767_; lean_object* v_bcFileName_x3f_2768_; uint8_t v_jsonOutput_2769_; lean_object* v_errorOnKinds_2770_; uint8_t v_printStats_2771_; uint8_t v_run_2772_; lean_object* v_incrSaveFileName_x3f_2773_; lean_object* v_incrLoadFileName_x3f_2774_; lean_object* v_incrHeaderSaveFileName_x3f_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2789_; 
v_leanOpts_2752_ = lean_ctor_get(v_opts_968_, 0);
v_forwardedArgs_2753_ = lean_ctor_get(v_opts_968_, 1);
v_component_2754_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 8);
v_printPrefix_2755_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 9);
v_printLibDir_2756_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 10);
v_useStdin_2757_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 11);
v_onlyDeps_2758_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2759_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 13);
v_depsJson_2760_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 14);
v_opts_2761_ = lean_ctor_get(v_opts_968_, 2);
v_trustLevel_2762_ = lean_ctor_get_uint32(v_opts_968_, sizeof(void*)*13);
v_rootDir_x3f_2763_ = lean_ctor_get(v_opts_968_, 3);
v_setupFileName_x3f_2764_ = lean_ctor_get(v_opts_968_, 4);
v_oleanFileName_x3f_2765_ = lean_ctor_get(v_opts_968_, 5);
v_ileanFileName_x3f_2766_ = lean_ctor_get(v_opts_968_, 6);
v_cFileName_x3f_2767_ = lean_ctor_get(v_opts_968_, 7);
v_bcFileName_x3f_2768_ = lean_ctor_get(v_opts_968_, 8);
v_jsonOutput_2769_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 15);
v_errorOnKinds_2770_ = lean_ctor_get(v_opts_968_, 9);
v_printStats_2771_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 16);
v_run_2772_ = lean_ctor_get_uint8(v_opts_968_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2773_ = lean_ctor_get(v_opts_968_, 10);
v_incrLoadFileName_x3f_2774_ = lean_ctor_get(v_opts_968_, 11);
v_incrHeaderSaveFileName_x3f_2775_ = lean_ctor_get(v_opts_968_, 12);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_opts_968_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2777_ = v_opts_968_;
v_isShared_2778_ = v_isSharedCheck_2789_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2775_);
lean_inc(v_incrLoadFileName_x3f_2774_);
lean_inc(v_incrSaveFileName_x3f_2773_);
lean_inc(v_errorOnKinds_2770_);
lean_inc(v_bcFileName_x3f_2768_);
lean_inc(v_cFileName_x3f_2767_);
lean_inc(v_ileanFileName_x3f_2766_);
lean_inc(v_oleanFileName_x3f_2765_);
lean_inc(v_setupFileName_x3f_2764_);
lean_inc(v_rootDir_x3f_2763_);
lean_inc(v_opts_2761_);
lean_inc(v_forwardedArgs_2753_);
lean_inc(v_leanOpts_2752_);
lean_dec(v_opts_968_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2789_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
uint32_t v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2779_ = lean_uint32_of_nat(v_val_2747_);
lean_dec(v_val_2747_);
v___x_2780_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__36));
v___x_2781_ = lean_string_append(v___x_2780_, v_a_2739_);
lean_dec(v_a_2739_);
v___x_2782_ = lean_array_push(v_forwardedArgs_2753_, v___x_2781_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 1, v___x_2782_);
v___x_2784_ = v___x_2777_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_leanOpts_2752_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2782_);
lean_ctor_set(v_reuseFailAlloc_2788_, 2, v_opts_2761_);
lean_ctor_set(v_reuseFailAlloc_2788_, 3, v_rootDir_x3f_2763_);
lean_ctor_set(v_reuseFailAlloc_2788_, 4, v_setupFileName_x3f_2764_);
lean_ctor_set(v_reuseFailAlloc_2788_, 5, v_oleanFileName_x3f_2765_);
lean_ctor_set(v_reuseFailAlloc_2788_, 6, v_ileanFileName_x3f_2766_);
lean_ctor_set(v_reuseFailAlloc_2788_, 7, v_cFileName_x3f_2767_);
lean_ctor_set(v_reuseFailAlloc_2788_, 8, v_bcFileName_x3f_2768_);
lean_ctor_set(v_reuseFailAlloc_2788_, 9, v_errorOnKinds_2770_);
lean_ctor_set(v_reuseFailAlloc_2788_, 10, v_incrSaveFileName_x3f_2773_);
lean_ctor_set(v_reuseFailAlloc_2788_, 11, v_incrLoadFileName_x3f_2774_);
lean_ctor_set(v_reuseFailAlloc_2788_, 12, v_incrHeaderSaveFileName_x3f_2775_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, sizeof(void*)*13 + 8, v_component_2754_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, sizeof(void*)*13 + 9, v_printPrefix_2755_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, sizeof(void*)*13 + 10, v_printLibDir_2756_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, sizeof(void*)*13 + 11, v_useStdin_2757_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, sizeof(void*)*13 + 12, v_onlyDeps_2758_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, sizeof(void*)*13 + 13, v_onlySrcDeps_2759_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, sizeof(void*)*13 + 14, v_depsJson_2760_);
lean_ctor_set_uint32(v_reuseFailAlloc_2788_, sizeof(void*)*13, v_trustLevel_2762_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, sizeof(void*)*13 + 15, v_jsonOutput_2769_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, sizeof(void*)*13 + 16, v_printStats_2771_);
lean_ctor_set_uint8(v_reuseFailAlloc_2788_, sizeof(void*)*13 + 17, v_run_2772_);
v___x_2784_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2786_; 
lean_ctor_set_uint32(v___x_2784_, sizeof(void*)*13 + 4, v___x_2779_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2784_);
v___x_2786_ = v___x_2741_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
lean_dec(v___x_2746_);
lean_del_object(v___x_2741_);
lean_dec(v_a_2739_);
lean_dec_ref(v_opts_968_);
v___x_2790_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__37));
v___x_2791_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2790_);
lean_dec_ref(v___x_2791_);
goto v___jp_972_;
}
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
lean_dec_ref(v_opts_968_);
v_a_2793_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2738_, 1);
v___x_2797_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2798_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2797_);
lean_dec_ref(v___x_2798_);
goto v___jp_2794_;
v___jp_2794_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_io_error_to_string(v_a_2793_);
v___x_2796_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2795_);
lean_dec_ref(v___x_2796_);
goto v___jp_981_;
}
}
}
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
lean_dec(v_optArg_x3f_970_);
v___x_2799_ = lean_internal_set_exit_on_panic(v___x_1191_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v_opts_968_);
return v___x_2800_;
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
v___x_1000_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1001_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1000_);
lean_dec_ref(v___x_1001_);
goto v___jp_996_;
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
v___x_1009_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
v___jp_1011_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1013_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1012_);
lean_dec_ref(v___x_1013_);
goto v___jp_1008_;
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
v___x_1033_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
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
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
v___jp_1050_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1052_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1051_);
lean_dec_ref(v___x_1052_);
goto v___jp_1047_;
}
v___jp_1053_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
v___jp_1056_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1058_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1057_);
lean_dec_ref(v___x_1058_);
goto v___jp_1053_;
}
v___jp_1059_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
v___jp_1062_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1064_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1063_);
lean_dec_ref(v___x_1064_);
goto v___jp_1059_;
}
v___jp_1065_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
v___jp_1068_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1070_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1069_);
lean_dec_ref(v___x_1070_);
goto v___jp_1065_;
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
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_io_error_to_string(v___y_1078_);
v___x_1080_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1079_);
lean_dec_ref(v___x_1080_);
goto v___jp_1074_;
}
v___jp_1081_:
{
uint8_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = 1;
v___x_1083_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1082_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1091_; 
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v___x_1083_, 0);
lean_dec(v_unused_1092_);
v___x_1085_ = v___x_1083_;
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
else
{
lean_dec(v___x_1083_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 1);
lean_ctor_set(v___x_1085_, 0, v___x_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_a_1093_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1083_, 1);
v___x_1094_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1095_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1094_);
lean_dec_ref(v___x_1095_);
v___y_1078_ = v_a_1093_;
goto v___jp_1077_;
}
}
v___jp_1096_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
v___x_1098_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1097_);
lean_dec_ref(v___x_1098_);
goto v___jp_1081_;
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
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_io_error_to_string(v___y_1136_);
v___x_1138_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1137_);
lean_dec_ref(v___x_1138_);
goto v___jp_1126_;
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
v___jp_1154_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
v___jp_1157_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1159_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1158_);
lean_dec_ref(v___x_1159_);
goto v___jp_1154_;
}
v___jp_1160_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
v___jp_1163_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1165_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1164_);
lean_dec_ref(v___x_1165_);
goto v___jp_1160_;
}
v___jp_1166_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
v___jp_1169_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1171_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1170_);
lean_dec_ref(v___x_1171_);
goto v___jp_1166_;
}
v___jp_1172_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
v___jp_1175_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1177_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1176_);
lean_dec_ref(v___x_1177_);
goto v___jp_1172_;
}
v___jp_1178_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
v___jp_1181_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1183_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1182_);
lean_dec_ref(v___x_1183_);
goto v___jp_1178_;
}
v___jp_1184_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
v___jp_1187_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1189_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1188_);
lean_dec_ref(v___x_1189_);
goto v___jp_1184_;
}
}
}
LEAN_EXPORT void lean_shell_options_process_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_968_ = stack[0].m_obj;
uint32_t v_opt_969_ = stack[1].m_num;
lean_object* v_optArg_x3f_970_ = stack[2].m_obj;
lean_object* v_res_2801_;
v_res_2801_ = lean_shell_options_process(v_opts_968_, v_opt_969_, v_optArg_x3f_970_);
stack->m_obj
 = v_res_2801_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2802_, lean_object* v_opt_2803_, lean_object* v_optArg_x3f_2804_, lean_object* v_a_2805_){
_start:
{
uint32_t v_opt_boxed_2806_; lean_object* v_res_2807_; 
v_opt_boxed_2806_ = lean_unbox_uint32(v_opt_2803_);
lean_dec(v_opt_2803_);
v_res_2807_ = lean_shell_options_process(v_opts_2802_, v_opt_boxed_2806_, v_optArg_x3f_2804_);
return v_res_2807_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(lean_object* v_name_2809_, lean_object* v_f_2810_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_uv_os_getpid();
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2848_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2848_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2848_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; uint64_t v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v_a_2824_; uint8_t v___x_2838_; lean_object* v___x_2839_; 
v___x_2817_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___closed__0));
v___x_2818_ = lean_unbox_uint64(v_a_2813_);
lean_dec(v_a_2813_);
v___x_2819_ = lean_uint64_to_nat(v___x_2818_);
v___x_2820_ = l_Nat_reprFast(v___x_2819_);
v___x_2821_ = lean_string_append(v___x_2817_, v___x_2820_);
lean_dec_ref(v___x_2820_);
lean_inc_ref(v_name_2809_);
v___x_2822_ = l_System_FilePath_addExtension(v_name_2809_, v___x_2821_);
lean_dec_ref(v___x_2821_);
v___x_2838_ = 1;
v___x_2839_ = lean_io_prim_handle_mk(v___x_2822_, v___x_2838_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc_n(v_a_2840_, 2);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2841_ = lean_apply_2(v_f_2810_, v_a_2840_, lean_box(0));
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v___x_2842_; 
lean_dec_ref_known(v___x_2841_, 1);
v___x_2842_ = lean_io_prim_handle_flush(v_a_2840_);
lean_dec(v_a_2840_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v___x_2843_; 
lean_dec_ref_known(v___x_2842_, 1);
v___x_2843_ = lean_io_rename(v___x_2822_, v_name_2809_);
lean_dec_ref(v_name_2809_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_dec_ref(v___x_2822_);
lean_del_object(v___x_2815_);
return v___x_2843_;
}
else
{
lean_object* v_a_2844_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v_a_2824_ = v_a_2844_;
goto v___jp_2823_;
}
}
else
{
lean_object* v_a_2845_; 
lean_dec_ref(v_name_2809_);
v_a_2845_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2842_, 1);
v_a_2824_ = v_a_2845_;
goto v___jp_2823_;
}
}
else
{
lean_object* v_a_2846_; 
lean_dec(v_a_2840_);
lean_dec_ref(v_name_2809_);
v_a_2846_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v___x_2841_, 1);
v_a_2824_ = v_a_2846_;
goto v___jp_2823_;
}
}
else
{
lean_object* v_a_2847_; 
lean_dec_ref(v_f_2810_);
lean_dec_ref(v_name_2809_);
v_a_2847_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2839_, 1);
v_a_2824_ = v_a_2847_;
goto v___jp_2823_;
}
v___jp_2823_:
{
uint8_t v___x_2825_; 
v___x_2825_ = l_System_FilePath_pathExists(v___x_2822_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2827_; 
lean_dec_ref(v___x_2822_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set_tag(v___x_2815_, 1);
lean_ctor_set(v___x_2815_, 0, v_a_2824_);
v___x_2827_ = v___x_2815_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2824_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
else
{
lean_object* v___x_2829_; 
lean_del_object(v___x_2815_);
v___x_2829_ = lean_io_remove_file(v___x_2822_);
lean_dec_ref(v___x_2822_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v___x_2829_, 0);
lean_dec(v_unused_2837_);
v___x_2831_ = v___x_2829_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_dec(v___x_2829_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
lean_ctor_set_tag(v___x_2831_, 1);
lean_ctor_set(v___x_2831_, 0, v_a_2824_);
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2824_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
else
{
lean_dec(v_a_2824_);
return v___x_2829_;
}
}
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec_ref(v_f_2810_);
lean_dec_ref(v_name_2809_);
v_a_2849_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2812_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2812_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2809_ = stack[0].m_obj;
lean_object* v_f_2810_ = stack[1].m_obj;
lean_object* v_res_2857_;
v_res_2857_ = l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(v_name_2809_, v_f_2810_);
stack->m_obj
 = v_res_2857_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___boxed(lean_object* v_name_2858_, lean_object* v_f_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(v_name_2858_, v_f_2859_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_opts_2862_, lean_object* v_opt_2863_){
_start:
{
lean_object* v_name_2864_; lean_object* v_defValue_2865_; lean_object* v_map_2866_; lean_object* v___x_2867_; 
v_name_2864_ = lean_ctor_get(v_opt_2863_, 0);
v_defValue_2865_ = lean_ctor_get(v_opt_2863_, 1);
v_map_2866_ = lean_ctor_get(v_opts_2862_, 0);
v___x_2867_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2866_, v_name_2864_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_inc(v_defValue_2865_);
return v_defValue_2865_;
}
else
{
lean_object* v_val_2868_; 
v_val_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_val_2868_);
lean_dec_ref_known(v___x_2867_, 1);
if (lean_obj_tag(v_val_2868_) == 3)
{
lean_object* v_v_2869_; 
v_v_2869_ = lean_ctor_get(v_val_2868_, 0);
lean_inc(v_v_2869_);
lean_dec_ref_known(v_val_2868_, 1);
return v_v_2869_;
}
else
{
lean_dec(v_val_2868_);
lean_inc(v_defValue_2865_);
return v_defValue_2865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_opts_2870_, lean_object* v_opt_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_opts_2870_, v_opt_2871_);
lean_dec_ref(v_opt_2871_);
lean_dec_ref(v_opts_2870_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2874_){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2875_ = lean_string_utf8_byte_size(v_s_2874_);
v___x_2876_ = lean_unsigned_to_nat(5u);
v___x_2877_ = lean_nat_dec_le(v___x_2876_, v___x_2875_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
lean_dec_ref(v_s_2874_);
v___x_2878_ = lean_box(0);
return v___x_2878_;
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2879_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2880_ = lean_unsigned_to_nat(0u);
v___x_2881_ = lean_string_memcmp(v_s_2874_, v___x_2879_, v___x_2880_, v___x_2880_, v___x_2876_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; 
lean_dec_ref(v_s_2874_);
v___x_2882_ = lean_box(0);
return v___x_2882_;
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_inc_ref(v_s_2874_);
v___x_2883_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2883_, 0, v_s_2874_);
lean_ctor_set(v___x_2883_, 1, v___x_2880_);
lean_ctor_set(v___x_2883_, 2, v___x_2875_);
v___x_2884_ = l_String_Slice_pos_x21(v___x_2883_, v___x_2876_);
lean_dec_ref_known(v___x_2883_, 3);
v___x_2885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2885_, 0, v_s_2874_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
lean_ctor_set(v___x_2885_, 2, v___x_2875_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
return v___x_2886_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2887_, lean_object* v_pat_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2887_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2890_, lean_object* v_pat_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2890_, v_pat_2891_);
lean_dec_ref(v_pat_2891_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v_x_2893_, lean_object* v_x_2894_, lean_object* v_v_2895_){
_start:
{
lean_inc_ref(v_v_2895_);
return v_v_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* v_x_2896_, lean_object* v_x_2897_, lean_object* v_v_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v_x_2896_, v_x_2897_, v_v_2898_);
lean_dec_ref(v_v_2898_);
lean_dec_ref(v_x_2897_);
lean_dec(v_x_2896_);
return v_res_2899_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object* v___x_2903_, lean_object* v_mainModuleName_2904_, lean_object* v_out_2905_, uint8_t v___x_2906_, lean_object* v___x_2907_, lean_object* v_fileName_2908_, lean_object* v___x_2909_, lean_object* v___x_2910_, lean_object* v___x_2911_, lean_object* v___x_2912_, lean_object* v___x_2913_, lean_object* v___x_2914_, lean_object* v___x_2915_, lean_object* v___x_2916_, uint8_t v_run_2917_, lean_object* v___x_2918_, uint8_t v_printLibDir_2919_){
_start:
{
lean_object* v_a_2922_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___y_2928_; uint16_t v___y_2929_; lean_object* v_fileName_2930_; lean_object* v_fileMap_2931_; lean_object* v_currNamespace_2932_; lean_object* v_openDecls_2933_; lean_object* v_initHeartbeats_2934_; lean_object* v_maxHeartbeats_2935_; lean_object* v_quotContext_2936_; lean_object* v_currMacroScope_2937_; lean_object* v_cancelTk_x3f_2938_; lean_object* v_inheritedTraceOptions_2939_; lean_object* v_currRecDepth_2940_; lean_object* v_ref_2941_; uint8_t v_suppressElabErrors_2942_; uint8_t v_isRecordingDeps_2943_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___y_2978_; uint8_t v___y_2979_; uint16_t v___y_2980_; uint16_t v___x_3001_; lean_object* v___x_3002_; lean_object* v_env_3003_; uint8_t v___x_3004_; uint16_t v___x_3005_; uint16_t v___x_3006_; uint16_t v___x_3007_; uint8_t v___x_3008_; 
v___x_2925_ = lean_io_get_num_heartbeats();
v___x_2926_ = lean_st_mk_ref(v___x_2903_);
v___x_2975_ = l_Lean_inheritedTraceOptions;
v___x_2976_ = lean_st_ref_get(v___x_2975_);
v___x_3001_ = l_Lean_OptionFlags_ofOptions(v___x_2918_);
v___x_3002_ = lean_st_ref_get(v___x_2926_);
v_env_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc_ref(v_env_3003_);
lean_dec(v___x_3002_);
v___x_3004_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3003_);
lean_dec_ref(v_env_3003_);
v___x_3005_ = 512;
v___x_3006_ = lean_uint16_land(v___x_3001_, v___x_3005_);
v___x_3007_ = 0;
v___x_3008_ = lean_uint16_dec_eq(v___x_3006_, v___x_3007_);
if (v___x_3008_ == 0)
{
if (v___x_3004_ == 0)
{
v___y_2978_ = v___x_2918_;
v___y_2979_ = v___x_2906_;
v___y_2980_ = v___x_3001_;
goto v___jp_2977_;
}
else
{
lean_dec_ref(v___x_2907_);
lean_inc(v___x_2910_);
v___y_2928_ = v___x_2918_;
v___y_2929_ = v___x_3001_;
v_fileName_2930_ = v_fileName_2908_;
v_fileMap_2931_ = v___x_2909_;
v_currNamespace_2932_ = v___x_2910_;
v_openDecls_2933_ = v___x_2911_;
v_initHeartbeats_2934_ = v___x_2925_;
v_maxHeartbeats_2935_ = v___x_2912_;
v_quotContext_2936_ = v___x_2910_;
v_currMacroScope_2937_ = v___x_2913_;
v_cancelTk_x3f_2938_ = v___x_2914_;
v_inheritedTraceOptions_2939_ = v___x_2976_;
v_currRecDepth_2940_ = v___x_2915_;
v_ref_2941_ = v___x_2916_;
v_suppressElabErrors_2942_ = v_run_2917_;
v_isRecordingDeps_2943_ = v_run_2917_;
goto v___jp_2927_;
}
}
else
{
if (v___x_3004_ == 0)
{
lean_dec_ref(v___x_2907_);
lean_inc(v___x_2910_);
v___y_2928_ = v___x_2918_;
v___y_2929_ = v___x_3001_;
v_fileName_2930_ = v_fileName_2908_;
v_fileMap_2931_ = v___x_2909_;
v_currNamespace_2932_ = v___x_2910_;
v_openDecls_2933_ = v___x_2911_;
v_initHeartbeats_2934_ = v___x_2925_;
v_maxHeartbeats_2935_ = v___x_2912_;
v_quotContext_2936_ = v___x_2910_;
v_currMacroScope_2937_ = v___x_2913_;
v_cancelTk_x3f_2938_ = v___x_2914_;
v_inheritedTraceOptions_2939_ = v___x_2976_;
v_currRecDepth_2940_ = v___x_2915_;
v_ref_2941_ = v___x_2916_;
v_suppressElabErrors_2942_ = v_run_2917_;
v_isRecordingDeps_2943_ = v_run_2917_;
goto v___jp_2927_;
}
else
{
v___y_2978_ = v___x_2918_;
v___y_2979_ = v_printLibDir_2919_;
v___y_2980_ = v___x_3001_;
goto v___jp_2977_;
}
}
v___jp_2921_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = lean_mk_io_user_error(v_a_2922_);
v___x_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
return v___x_2924_;
}
v___jp_2927_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2944_ = l_Lean_maxRecDepth;
v___x_2945_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___y_2928_, v___x_2944_);
v___x_2946_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2946_, 0, v_fileName_2930_);
lean_ctor_set(v___x_2946_, 1, v_fileMap_2931_);
lean_ctor_set(v___x_2946_, 2, v___y_2928_);
lean_ctor_set(v___x_2946_, 3, v___x_2945_);
lean_ctor_set(v___x_2946_, 4, v_currNamespace_2932_);
lean_ctor_set(v___x_2946_, 5, v_openDecls_2933_);
lean_ctor_set(v___x_2946_, 6, v_initHeartbeats_2934_);
lean_ctor_set(v___x_2946_, 7, v_maxHeartbeats_2935_);
lean_ctor_set(v___x_2946_, 8, v_quotContext_2936_);
lean_ctor_set(v___x_2946_, 9, v_currMacroScope_2937_);
lean_ctor_set(v___x_2946_, 10, v_cancelTk_x3f_2938_);
lean_ctor_set(v___x_2946_, 11, v_inheritedTraceOptions_2939_);
v___x_2947_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
lean_ctor_set(v___x_2947_, 1, v_currRecDepth_2940_);
lean_ctor_set(v___x_2947_, 2, v_ref_2941_);
lean_ctor_set_uint16(v___x_2947_, sizeof(void*)*3, v___y_2929_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 2, v_suppressElabErrors_2942_);
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*3 + 3, v_isRecordingDeps_2943_);
v___x_2948_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2904_, v___x_2947_, v___x_2926_);
lean_dec_ref_known(v___x_2947_, 3);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2950_ = lean_st_ref_get(v___x_2926_);
lean_dec(v___x_2926_);
lean_dec(v___x_2950_);
v___x_2951_ = lean_string_to_utf8(v_a_2949_);
lean_dec(v_a_2949_);
v___x_2952_ = lean_io_prim_handle_write(v_out_2905_, v___x_2951_);
lean_dec_ref(v___x_2951_);
return v___x_2952_;
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v___x_2926_);
v_a_2953_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2955_ = v___x_2948_;
v_isShared_2956_ = v_isSharedCheck_2974_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2948_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2974_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
if (lean_obj_tag(v_a_2953_) == 0)
{
lean_object* v_msg_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2961_; 
v_msg_2957_ = lean_ctor_get(v_a_2953_, 1);
lean_inc_ref(v_msg_2957_);
lean_dec_ref_known(v_a_2953_, 2);
v___x_2958_ = l_Lean_MessageData_toString(v_msg_2957_);
v___x_2959_ = lean_mk_io_user_error(v___x_2958_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2959_);
v___x_2961_ = v___x_2955_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
else
{
lean_object* v_id_2963_; lean_object* v___x_2964_; 
lean_del_object(v___x_2955_);
v_id_2963_ = lean_ctor_get(v_a_2953_, 0);
lean_inc(v_id_2963_);
lean_dec_ref_known(v_a_2953_, 2);
v___x_2964_ = l_Lean_InternalExceptionId_getName(v_id_2963_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
lean_dec(v_id_2963_);
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
v___x_2966_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0));
v___x_2967_ = l_Lean_Name_toString(v_a_2965_, v___x_2906_);
v___x_2968_ = lean_string_append(v___x_2966_, v___x_2967_);
lean_dec_ref(v___x_2967_);
v_a_2922_ = v___x_2968_;
goto v___jp_2921_;
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_dec_ref_known(v___x_2964_, 1);
v___x_2969_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1));
v___x_2970_ = l_Nat_reprFast(v_id_2963_);
v___x_2971_ = lean_string_append(v___x_2969_, v___x_2970_);
lean_dec_ref(v___x_2970_);
v___x_2972_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2));
v___x_2973_ = lean_string_append(v___x_2971_, v___x_2972_);
v_a_2922_ = v___x_2973_;
goto v___jp_2921_;
}
}
}
}
}
v___jp_2977_:
{
lean_object* v___x_2981_; lean_object* v_env_2982_; lean_object* v_nextMacroScope_2983_; lean_object* v_ngen_2984_; lean_object* v_auxDeclNGen_2985_; lean_object* v_traceState_2986_; lean_object* v_recordedDeps_2987_; lean_object* v_messages_2988_; lean_object* v_infoState_2989_; lean_object* v_snapshotTasks_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2999_; 
v___x_2981_ = lean_st_ref_take(v___x_2926_);
v_env_2982_ = lean_ctor_get(v___x_2981_, 0);
v_nextMacroScope_2983_ = lean_ctor_get(v___x_2981_, 1);
v_ngen_2984_ = lean_ctor_get(v___x_2981_, 2);
v_auxDeclNGen_2985_ = lean_ctor_get(v___x_2981_, 3);
v_traceState_2986_ = lean_ctor_get(v___x_2981_, 4);
v_recordedDeps_2987_ = lean_ctor_get(v___x_2981_, 6);
v_messages_2988_ = lean_ctor_get(v___x_2981_, 7);
v_infoState_2989_ = lean_ctor_get(v___x_2981_, 8);
v_snapshotTasks_2990_ = lean_ctor_get(v___x_2981_, 9);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; 
v_unused_3000_ = lean_ctor_get(v___x_2981_, 5);
lean_dec(v_unused_3000_);
v___x_2992_ = v___x_2981_;
v_isShared_2993_ = v_isSharedCheck_2999_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_snapshotTasks_2990_);
lean_inc(v_infoState_2989_);
lean_inc(v_messages_2988_);
lean_inc(v_recordedDeps_2987_);
lean_inc(v_traceState_2986_);
lean_inc(v_auxDeclNGen_2985_);
lean_inc(v_ngen_2984_);
lean_inc(v_nextMacroScope_2983_);
lean_inc(v_env_2982_);
lean_dec(v___x_2981_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2999_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; lean_object* v___x_2996_; 
v___x_2994_ = l_Lean_Kernel_enableDiag(v_env_2982_, v___y_2979_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 5, v___x_2907_);
lean_ctor_set(v___x_2992_, 0, v___x_2994_);
v___x_2996_ = v___x_2992_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_nextMacroScope_2983_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v_ngen_2984_);
lean_ctor_set(v_reuseFailAlloc_2998_, 3, v_auxDeclNGen_2985_);
lean_ctor_set(v_reuseFailAlloc_2998_, 4, v_traceState_2986_);
lean_ctor_set(v_reuseFailAlloc_2998_, 5, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_2998_, 6, v_recordedDeps_2987_);
lean_ctor_set(v_reuseFailAlloc_2998_, 7, v_messages_2988_);
lean_ctor_set(v_reuseFailAlloc_2998_, 8, v_infoState_2989_);
lean_ctor_set(v_reuseFailAlloc_2998_, 9, v_snapshotTasks_2990_);
v___x_2996_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_st_ref_put(v___x_2926_, v___x_2996_);
lean_inc(v___x_2910_);
v___y_2928_ = v___y_2978_;
v___y_2929_ = v___y_2980_;
v_fileName_2930_ = v_fileName_2908_;
v_fileMap_2931_ = v___x_2909_;
v_currNamespace_2932_ = v___x_2910_;
v_openDecls_2933_ = v___x_2911_;
v_initHeartbeats_2934_ = v___x_2925_;
v_maxHeartbeats_2935_ = v___x_2912_;
v_quotContext_2936_ = v___x_2910_;
v_currMacroScope_2937_ = v___x_2913_;
v_cancelTk_x3f_2938_ = v___x_2914_;
v_inheritedTraceOptions_2939_ = v___x_2976_;
v_currRecDepth_2940_ = v___x_2915_;
v_ref_2941_ = v___x_2916_;
v_suppressElabErrors_2942_ = v_run_2917_;
v_isRecordingDeps_2943_ = v_run_2917_;
goto v___jp_2927_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_shellMain___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2903_ = stack[0].m_obj;
lean_object* v_mainModuleName_2904_ = stack[1].m_obj;
lean_object* v_out_2905_ = stack[2].m_obj;
uint8_t v___x_2906_ = stack[3].m_num;
lean_object* v___x_2907_ = stack[4].m_obj;
lean_object* v_fileName_2908_ = stack[5].m_obj;
lean_object* v___x_2909_ = stack[6].m_obj;
lean_object* v___x_2910_ = stack[7].m_obj;
lean_object* v___x_2911_ = stack[8].m_obj;
lean_object* v___x_2912_ = stack[9].m_obj;
lean_object* v___x_2913_ = stack[10].m_obj;
lean_object* v___x_2914_ = stack[11].m_obj;
lean_object* v___x_2915_ = stack[12].m_obj;
lean_object* v___x_2916_ = stack[13].m_obj;
uint8_t v_run_2917_ = stack[14].m_num;
lean_object* v___x_2918_ = stack[15].m_obj;
uint8_t v_printLibDir_2919_ = stack[16].m_num;
lean_object* v_res_3009_;
v_res_3009_ = l___private_Lean_Shell_0__Lean_shellMain___lam__1(v___x_2903_, v_mainModuleName_2904_, v_out_2905_, v___x_2906_, v___x_2907_, v_fileName_2908_, v___x_2909_, v___x_2910_, v___x_2911_, v___x_2912_, v___x_2913_, v___x_2914_, v___x_2915_, v___x_2916_, v_run_2917_, v___x_2918_, v_printLibDir_2919_);
stack->m_obj
 = v_res_3009_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object** _args){
lean_object* v___x_3010_ = _args[0];
lean_object* v_mainModuleName_3011_ = _args[1];
lean_object* v_out_3012_ = _args[2];
lean_object* v___x_3013_ = _args[3];
lean_object* v___x_3014_ = _args[4];
lean_object* v_fileName_3015_ = _args[5];
lean_object* v___x_3016_ = _args[6];
lean_object* v___x_3017_ = _args[7];
lean_object* v___x_3018_ = _args[8];
lean_object* v___x_3019_ = _args[9];
lean_object* v___x_3020_ = _args[10];
lean_object* v___x_3021_ = _args[11];
lean_object* v___x_3022_ = _args[12];
lean_object* v___x_3023_ = _args[13];
lean_object* v_run_3024_ = _args[14];
lean_object* v___x_3025_ = _args[15];
lean_object* v_printLibDir_3026_ = _args[16];
lean_object* v___y_3027_ = _args[17];
_start:
{
uint8_t v___x_12558__boxed_3028_; uint8_t v_run_boxed_3029_; uint8_t v_printLibDir_boxed_3030_; lean_object* v_res_3031_; 
v___x_12558__boxed_3028_ = lean_unbox(v___x_3013_);
v_run_boxed_3029_ = lean_unbox(v_run_3024_);
v_printLibDir_boxed_3030_ = lean_unbox(v_printLibDir_3026_);
v_res_3031_ = l___private_Lean_Shell_0__Lean_shellMain___lam__1(v___x_3010_, v_mainModuleName_3011_, v_out_3012_, v___x_12558__boxed_3028_, v___x_3014_, v_fileName_3015_, v___x_3016_, v___x_3017_, v___x_3018_, v___x_3019_, v___x_3020_, v___x_3021_, v___x_3022_, v___x_3023_, v_run_boxed_3029_, v___x_3025_, v_printLibDir_boxed_3030_);
lean_dec(v_out_3012_);
return v_res_3031_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = l_Lean_Options_empty;
v___x_3034_ = l_Lean_Core_getMaxHeartbeats(v___x_3033_);
return v___x_3034_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = lean_unsigned_to_nat(1u);
v___x_3036_ = l_Lean_firstFrontendMacroScope;
v___x_3037_ = lean_nat_add(v___x_3036_, v___x_3035_);
return v___x_3037_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = lean_unsigned_to_nat(32u);
v___x_3049_ = lean_mk_empty_array_with_capacity(v___x_3048_);
v___x_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
return v___x_3050_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8(void){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_3051_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8);
v___x_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
return v___x_3053_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9);
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
return v___x_3055_;
}
}
lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2(lean_object* v___x_3056_, uint8_t v___x_3057_, lean_object* v_val_3058_, lean_object* v_mainModuleName_3059_, lean_object* v_fileName_3060_, uint8_t v_run_3061_, uint8_t v_printLibDir_3062_, lean_object* v___x_3063_, lean_object* v_out_3064_){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; uint64_t v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; size_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___f_3096_; lean_object* v___x_3097_; 
v___x_3066_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__0));
v___x_3067_ = l_Lean_instInhabitedFileMap_default;
v___x_3068_ = l_Lean_Options_empty;
v___x_3069_ = lean_box(0);
v___x_3070_ = lean_box(0);
v___x_3071_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1);
v___x_3072_ = l_Lean_firstFrontendMacroScope;
v___x_3073_ = lean_box(0);
v___x_3074_ = lean_box(0);
v___x_3075_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2);
v___x_3076_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__5));
v___x_3077_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__6));
v___x_3078_ = 0ULL;
v___x_3079_ = lean_unsigned_to_nat(32u);
v___x_3080_ = lean_mk_empty_array_with_capacity(v___x_3079_);
v___x_3081_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7);
v___x_3082_ = ((size_t)5ULL);
lean_inc_n(v___x_3056_, 5);
v___x_3083_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3083_, 0, v___x_3081_);
lean_ctor_set(v___x_3083_, 1, v___x_3080_);
lean_ctor_set(v___x_3083_, 2, v___x_3056_);
lean_ctor_set(v___x_3083_, 3, v___x_3056_);
lean_ctor_set_usize(v___x_3083_, 4, v___x_3082_);
lean_inc_ref_n(v___x_3083_, 3);
v___x_3084_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
lean_ctor_set_uint64(v___x_3084_, sizeof(void*)*1, v___x_3078_);
v___x_3085_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9);
v___x_3086_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10);
v___x_3087_ = lean_mk_empty_array_with_capacity(v___x_3056_);
lean_inc_ref_n(v___x_3087_, 2);
v___x_3088_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
lean_ctor_set(v___x_3088_, 1, v___x_3068_);
lean_ctor_set(v___x_3088_, 2, v___x_3087_);
lean_ctor_set(v___x_3088_, 3, v___x_3056_);
lean_ctor_set(v___x_3088_, 4, v___x_3056_);
lean_ctor_set(v___x_3088_, 5, v___x_3056_);
v___x_3089_ = l_Lean_NameSet_empty;
v___x_3090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3083_);
lean_ctor_set(v___x_3090_, 1, v___x_3083_);
lean_ctor_set(v___x_3090_, 2, v___x_3089_);
v___x_3091_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3091_, 0, v___x_3085_);
lean_ctor_set(v___x_3091_, 1, v___x_3085_);
lean_ctor_set(v___x_3091_, 2, v___x_3083_);
lean_ctor_set_uint8(v___x_3091_, sizeof(void*)*3, v___x_3057_);
v___x_3092_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3092_, 0, v_val_3058_);
lean_ctor_set(v___x_3092_, 1, v___x_3075_);
lean_ctor_set(v___x_3092_, 2, v___x_3076_);
lean_ctor_set(v___x_3092_, 3, v___x_3077_);
lean_ctor_set(v___x_3092_, 4, v___x_3084_);
lean_ctor_set(v___x_3092_, 5, v___x_3086_);
lean_ctor_set(v___x_3092_, 6, v___x_3088_);
lean_ctor_set(v___x_3092_, 7, v___x_3090_);
lean_ctor_set(v___x_3092_, 8, v___x_3091_);
lean_ctor_set(v___x_3092_, 9, v___x_3087_);
v___x_3093_ = lean_box(v___x_3057_);
v___x_3094_ = lean_box(v_run_3061_);
v___x_3095_ = lean_box(v_printLibDir_3062_);
v___f_3096_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 18, 17);
lean_closure_set(v___f_3096_, 0, v___x_3092_);
lean_closure_set(v___f_3096_, 1, v_mainModuleName_3059_);
lean_closure_set(v___f_3096_, 2, v_out_3064_);
lean_closure_set(v___f_3096_, 3, v___x_3093_);
lean_closure_set(v___f_3096_, 4, v___x_3086_);
lean_closure_set(v___f_3096_, 5, v_fileName_3060_);
lean_closure_set(v___f_3096_, 6, v___x_3067_);
lean_closure_set(v___f_3096_, 7, v___x_3069_);
lean_closure_set(v___f_3096_, 8, v___x_3070_);
lean_closure_set(v___f_3096_, 9, v___x_3071_);
lean_closure_set(v___f_3096_, 10, v___x_3072_);
lean_closure_set(v___f_3096_, 11, v___x_3073_);
lean_closure_set(v___f_3096_, 12, v___x_3056_);
lean_closure_set(v___f_3096_, 13, v___x_3074_);
lean_closure_set(v___f_3096_, 14, v___x_3094_);
lean_closure_set(v___f_3096_, 15, v___x_3068_);
lean_closure_set(v___f_3096_, 16, v___x_3095_);
v___x_3097_ = l_Lean_profileitIOUnsafe___redArg(v___x_3066_, v___x_3063_, v___f_3096_, v___x_3069_);
return v___x_3097_;
}
}
LEAN_EXPORT void l___private_Lean_Shell_0__Lean_shellMain___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3056_ = stack[0].m_obj;
uint8_t v___x_3057_ = stack[1].m_num;
lean_object* v_val_3058_ = stack[2].m_obj;
lean_object* v_mainModuleName_3059_ = stack[3].m_obj;
lean_object* v_fileName_3060_ = stack[4].m_obj;
uint8_t v_run_3061_ = stack[5].m_num;
uint8_t v_printLibDir_3062_ = stack[6].m_num;
lean_object* v___x_3063_ = stack[7].m_obj;
lean_object* v_out_3064_ = stack[8].m_obj;
lean_object* v_res_3098_;
v_res_3098_ = l___private_Lean_Shell_0__Lean_shellMain___lam__2(v___x_3056_, v___x_3057_, v_val_3058_, v_mainModuleName_3059_, v_fileName_3060_, v_run_3061_, v_printLibDir_3062_, v___x_3063_, v_out_3064_);
stack->m_obj
 = v_res_3098_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___boxed(lean_object* v___x_3099_, lean_object* v___x_3100_, lean_object* v_val_3101_, lean_object* v_mainModuleName_3102_, lean_object* v_fileName_3103_, lean_object* v_run_3104_, lean_object* v_printLibDir_3105_, lean_object* v___x_3106_, lean_object* v_out_3107_, lean_object* v___y_3108_){
_start:
{
uint8_t v___x_12874__boxed_3109_; uint8_t v_run_boxed_3110_; uint8_t v_printLibDir_boxed_3111_; lean_object* v_res_3112_; 
v___x_12874__boxed_3109_ = lean_unbox(v___x_3100_);
v_run_boxed_3110_ = lean_unbox(v_run_3104_);
v_printLibDir_boxed_3111_ = lean_unbox(v_printLibDir_3105_);
v_res_3112_ = l___private_Lean_Shell_0__Lean_shellMain___lam__2(v___x_3099_, v___x_12874__boxed_3109_, v_val_3101_, v_mainModuleName_3102_, v_fileName_3103_, v_run_boxed_3110_, v_printLibDir_boxed_3111_, v___x_3106_, v_out_3107_);
lean_dec_ref(v___x_3106_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_3113_, lean_object* v_a_3114_, lean_object* v_b_3115_){
_start:
{
lean_object* v_str_3116_; lean_object* v_startInclusive_3117_; lean_object* v_endExclusive_3118_; lean_object* v___x_3119_; uint8_t v_decide_3120_; 
v_str_3116_ = lean_ctor_get(v_val_3113_, 0);
v_startInclusive_3117_ = lean_ctor_get(v_val_3113_, 1);
v_endExclusive_3118_ = lean_ctor_get(v_val_3113_, 2);
v___x_3119_ = lean_nat_sub(v_endExclusive_3118_, v_startInclusive_3117_);
v_decide_3120_ = lean_nat_dec_eq(v_a_3114_, v___x_3119_);
lean_dec(v___x_3119_);
if (v_decide_3120_ == 0)
{
lean_object* v___x_3121_; uint32_t v___x_3122_; uint32_t v___x_3123_; uint8_t v___x_3124_; 
v___x_3121_ = lean_nat_add(v_startInclusive_3117_, v_a_3114_);
v___x_3122_ = lean_string_utf8_get_fast(v_str_3116_, v___x_3121_);
v___x_3123_ = 10;
v___x_3124_ = lean_uint32_dec_eq(v___x_3122_, v___x_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec(v_a_3114_);
v___x_3125_ = lean_box(0);
v___x_3126_ = lean_string_utf8_next_fast(v_str_3116_, v___x_3121_);
lean_dec(v___x_3121_);
v___x_3127_ = lean_nat_sub(v___x_3126_, v_startInclusive_3117_);
v_a_3114_ = v___x_3127_;
v_b_3115_ = v___x_3125_;
goto _start;
}
else
{
lean_object* v___x_3129_; 
lean_dec(v___x_3121_);
v___x_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3129_, 0, v_a_3114_);
return v___x_3129_;
}
}
else
{
lean_dec(v_a_3114_);
lean_inc(v_b_3115_);
return v_b_3115_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_3130_, lean_object* v_a_3131_, lean_object* v_b_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3130_, v_a_3131_, v_b_3132_);
lean_dec(v_b_3132_);
lean_dec_ref(v_val_3130_);
return v_res_3133_;
}
}
lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_s_3134_){
_start:
{
uint32_t v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = 10;
v___x_3137_ = lean_string_push(v_s_3134_, v___x_3136_);
v___x_3138_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT void l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3134_ = stack[0].m_obj;
lean_object* v_res_3139_;
v_res_3139_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_s_3134_);
stack->m_obj
 = v_res_3139_;
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_s_3140_, lean_object* v_a_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_s_3140_);
return v_res_3142_;
}
}
lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_3143_){
_start:
{
uint32_t v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3145_ = 10;
v___x_3146_ = lean_string_push(v_s_3143_, v___x_3145_);
v___x_3147_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_3146_);
return v___x_3147_;
}
}
LEAN_EXPORT void l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3143_ = stack[0].m_obj;
lean_object* v_res_3148_;
v_res_3148_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_3143_);
stack->m_obj
 = v_res_3148_;
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_3149_);
return v_res_3151_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1(void){
_start:
{
lean_object* v___x_3153_; uint8_t v___x_3154_; 
v___x_3153_ = lean_box(0);
v___x_3154_ = lean_internal_has_address_sanitizer(v___x_3153_);
return v___x_3154_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4(void){
_start:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = lean_box(0);
v___x_3159_ = lean_internal_get_option_overrides(v___x_3158_);
return v___x_3159_;
}
}
lean_object* lean_shell_main(lean_object* v_args_3173_, lean_object* v_opts_3174_){
_start:
{
lean_object* v_fns_3177_; uint8_t v_printPrefix_3202_; 
v_printPrefix_3202_ = lean_ctor_get_uint8(v_opts_3174_, sizeof(void*)*13 + 9);
if (v_printPrefix_3202_ == 0)
{
uint8_t v_printLibDir_3203_; 
v_printLibDir_3203_ = lean_ctor_get_uint8(v_opts_3174_, sizeof(void*)*13 + 10);
if (v_printLibDir_3203_ == 0)
{
lean_object* v_leanOpts_3204_; lean_object* v_forwardedArgs_3205_; uint8_t v_component_3206_; uint8_t v_useStdin_3207_; uint8_t v_onlyDeps_3208_; uint8_t v_onlySrcDeps_3209_; uint8_t v_depsJson_3210_; uint32_t v_trustLevel_3211_; lean_object* v_rootDir_x3f_3212_; lean_object* v_setupFileName_x3f_3213_; lean_object* v_oleanFileName_x3f_3214_; lean_object* v_ileanFileName_x3f_3215_; lean_object* v_cFileName_x3f_3216_; lean_object* v_bcFileName_x3f_3217_; uint8_t v_jsonOutput_3218_; lean_object* v_errorOnKinds_3219_; uint8_t v_printStats_3220_; uint8_t v_run_3221_; lean_object* v_incrSaveFileName_x3f_3222_; lean_object* v_incrLoadFileName_x3f_3223_; lean_object* v_incrHeaderSaveFileName_x3f_3224_; lean_object* v___f_3225_; lean_object* v___y_3227_; lean_object* v___y_3242_; lean_object* v___x_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v_mainModuleName_3290_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v_contents_3349_; lean_object* v___y_3375_; lean_object* v_str_3376_; lean_object* v_startInclusive_3377_; lean_object* v_endExclusive_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v_fileName_3481_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3519_; lean_object* v___y_3520_; uint8_t v___y_3521_; uint8_t v___y_3524_; lean_object* v_fst_3525_; lean_object* v_snd_3526_; uint8_t v___y_3528_; lean_object* v___x_3558_; lean_object* v_maxMemory_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; 
v_leanOpts_3204_ = lean_ctor_get(v_opts_3174_, 0);
lean_inc_ref(v_leanOpts_3204_);
v_forwardedArgs_3205_ = lean_ctor_get(v_opts_3174_, 1);
lean_inc_ref(v_forwardedArgs_3205_);
v_component_3206_ = lean_ctor_get_uint8(v_opts_3174_, sizeof(void*)*13 + 8);
v_useStdin_3207_ = lean_ctor_get_uint8(v_opts_3174_, sizeof(void*)*13 + 11);
v_onlyDeps_3208_ = lean_ctor_get_uint8(v_opts_3174_, sizeof(void*)*13 + 12);
v_onlySrcDeps_3209_ = lean_ctor_get_uint8(v_opts_3174_, sizeof(void*)*13 + 13);
v_depsJson_3210_ = lean_ctor_get_uint8(v_opts_3174_, sizeof(void*)*13 + 14);
v_trustLevel_3211_ = lean_ctor_get_uint32(v_opts_3174_, sizeof(void*)*13);
v_rootDir_x3f_3212_ = lean_ctor_get(v_opts_3174_, 3);
lean_inc(v_rootDir_x3f_3212_);
v_setupFileName_x3f_3213_ = lean_ctor_get(v_opts_3174_, 4);
lean_inc(v_setupFileName_x3f_3213_);
v_oleanFileName_x3f_3214_ = lean_ctor_get(v_opts_3174_, 5);
lean_inc(v_oleanFileName_x3f_3214_);
v_ileanFileName_x3f_3215_ = lean_ctor_get(v_opts_3174_, 6);
lean_inc(v_ileanFileName_x3f_3215_);
v_cFileName_x3f_3216_ = lean_ctor_get(v_opts_3174_, 7);
lean_inc(v_cFileName_x3f_3216_);
v_bcFileName_x3f_3217_ = lean_ctor_get(v_opts_3174_, 8);
lean_inc(v_bcFileName_x3f_3217_);
v_jsonOutput_3218_ = lean_ctor_get_uint8(v_opts_3174_, sizeof(void*)*13 + 15);
v_errorOnKinds_3219_ = lean_ctor_get(v_opts_3174_, 9);
lean_inc_ref(v_errorOnKinds_3219_);
v_printStats_3220_ = lean_ctor_get_uint8(v_opts_3174_, sizeof(void*)*13 + 16);
v_run_3221_ = lean_ctor_get_uint8(v_opts_3174_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_3222_ = lean_ctor_get(v_opts_3174_, 10);
lean_inc(v_incrSaveFileName_x3f_3222_);
v_incrLoadFileName_x3f_3223_ = lean_ctor_get(v_opts_3174_, 11);
lean_inc(v_incrLoadFileName_x3f_3223_);
v_incrHeaderSaveFileName_x3f_3224_ = lean_ctor_get(v_opts_3174_, 12);
lean_inc(v_incrHeaderSaveFileName_x3f_3224_);
lean_dec_ref(v_opts_3174_);
v___f_3225_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__0));
v___x_3252_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__4, &l___private_Lean_Shell_0__Lean_shellMain___closed__4_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4);
v___x_3253_ = l_Lean_Options_mergeBy(v___f_3225_, v_leanOpts_3204_, v___x_3252_);
v___x_3254_ = 1;
v___x_3558_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3559_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3253_, v___x_3558_);
v___x_3560_ = lean_unsigned_to_nat(0u);
v___x_3561_ = lean_nat_dec_eq(v_maxMemory_3559_, v___x_3560_);
if (v___x_3561_ == 0)
{
size_t v___x_3562_; size_t v___x_3563_; size_t v___x_3564_; size_t v___x_3565_; lean_object* v___x_3566_; 
v___x_3562_ = lean_usize_of_nat(v_maxMemory_3559_);
lean_dec(v_maxMemory_3559_);
v___x_3563_ = ((size_t)10ULL);
v___x_3564_ = lean_usize_shift_left(v___x_3562_, v___x_3563_);
v___x_3565_ = lean_usize_shift_left(v___x_3564_, v___x_3563_);
v___x_3566_ = lean_internal_set_max_memory(v___x_3565_);
goto v___jp_3549_;
}
else
{
lean_dec(v_maxMemory_3559_);
goto v___jp_3549_;
}
v___jp_3226_:
{
lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3228_ = lean_display_cumulative_profiling_times();
v___x_3229_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__1, &l___private_Lean_Shell_0__Lean_shellMain___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1);
if (v___x_3229_ == 0)
{
if (lean_obj_tag(v___y_3227_) == 0)
{
if (v___x_3229_ == 0)
{
uint8_t v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = 1;
v___x_3231_ = lean_io_exit(v___x_3230_);
return v___x_3231_;
}
else
{
goto v___jp_3196_;
}
}
else
{
lean_dec_ref_known(v___y_3227_, 1);
goto v___jp_3196_;
}
}
else
{
if (lean_obj_tag(v___y_3227_) == 0)
{
goto v___jp_3199_;
}
else
{
lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3239_; 
v_isSharedCheck_3239_ = !lean_is_exclusive(v___y_3227_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v___y_3227_, 0);
lean_dec(v_unused_3240_);
v___x_3233_ = v___y_3227_;
v_isShared_3234_ = v_isSharedCheck_3239_;
goto v_resetjp_3232_;
}
else
{
lean_dec(v___y_3227_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3239_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
if (v___x_3229_ == 0)
{
lean_del_object(v___x_3233_);
goto v___jp_3199_;
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3237_; 
v___x_3235_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3234_ == 0)
{
lean_ctor_set_tag(v___x_3233_, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3235_);
v___x_3237_ = v___x_3233_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
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
}
}
v___jp_3241_:
{
if (lean_obj_tag(v_bcFileName_x3f_3217_) == 1)
{
lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3250_; 
lean_dec(v___y_3242_);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_bcFileName_x3f_3217_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v_bcFileName_x3f_3217_, 0);
lean_dec(v_unused_3251_);
v___x_3244_ = v_bcFileName_x3f_3217_;
v_isShared_3245_ = v_isSharedCheck_3250_;
goto v_resetjp_3243_;
}
else
{
lean_dec(v_bcFileName_x3f_3217_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3250_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3248_; 
v___x_3246_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__3));
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v___x_3246_);
v___x_3248_ = v___x_3244_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
else
{
lean_dec(v_bcFileName_x3f_3217_);
v___y_3227_ = v___y_3242_;
goto v___jp_3226_;
}
}
v___jp_3255_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__5));
v___x_3257_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3256_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v___x_3258_; 
lean_dec_ref_known(v___x_3257_, 1);
v___x_3258_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3254_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3266_; 
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3266_ == 0)
{
lean_object* v_unused_3267_; 
v_unused_3267_ = lean_ctor_get(v___x_3258_, 0);
lean_dec(v_unused_3267_);
v___x_3260_ = v___x_3258_;
v_isShared_3261_ = v_isSharedCheck_3266_;
goto v_resetjp_3259_;
}
else
{
lean_dec(v___x_3258_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3266_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3262_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3262_);
v___x_3264_ = v___x_3260_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
v_a_3268_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3258_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3258_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
v_a_3276_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3257_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3257_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
v___jp_3284_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = lean_unsigned_to_nat(0u);
v___x_3292_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__6));
lean_inc(v_mainModuleName_3290_);
lean_inc_ref(v___x_3253_);
v___x_3293_ = l_Lean_Elab_runFrontend(v___y_3286_, v___x_3253_, v___y_3289_, v_mainModuleName_3290_, v_trustLevel_3211_, v_oleanFileName_x3f_3214_, v_ileanFileName_x3f_3215_, v_jsonOutput_3218_, v_errorOnKinds_3219_, v___x_3292_, v_printStats_3220_, v___y_3288_, v_incrSaveFileName_x3f_3222_, v_incrLoadFileName_x3f_3223_, v_incrHeaderSaveFileName_x3f_3224_);
lean_dec_ref(v_errorOnKinds_3219_);
lean_dec(v_ileanFileName_x3f_3215_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3319_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3296_ = v___x_3293_;
v_isShared_3297_ = v_isSharedCheck_3319_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3293_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3319_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
if (lean_obj_tag(v_a_3294_) == 1)
{
if (v_run_3221_ == 0)
{
lean_del_object(v___x_3296_);
lean_dec(v___y_3287_);
if (lean_obj_tag(v_cFileName_x3f_3216_) == 1)
{
lean_object* v_val_3298_; lean_object* v_val_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___f_3303_; lean_object* v___x_3304_; 
v_val_3298_ = lean_ctor_get(v_a_3294_, 0);
v_val_3299_ = lean_ctor_get(v_cFileName_x3f_3216_, 0);
lean_inc(v_val_3299_);
lean_dec_ref_known(v_cFileName_x3f_3216_, 1);
v___x_3300_ = lean_box(v___x_3254_);
v___x_3301_ = lean_box(v_run_3221_);
v___x_3302_ = lean_box(v_printLibDir_3203_);
lean_inc(v_val_3298_);
v___f_3303_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___boxed), 10, 8);
lean_closure_set(v___f_3303_, 0, v___x_3291_);
lean_closure_set(v___f_3303_, 1, v___x_3300_);
lean_closure_set(v___f_3303_, 2, v_val_3298_);
lean_closure_set(v___f_3303_, 3, v_mainModuleName_3290_);
lean_closure_set(v___f_3303_, 4, v___y_3285_);
lean_closure_set(v___f_3303_, 5, v___x_3301_);
lean_closure_set(v___f_3303_, 6, v___x_3302_);
lean_closure_set(v___f_3303_, 7, v___x_3253_);
v___x_3304_ = l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(v_val_3299_, v___f_3303_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_dec_ref_known(v___x_3304_, 1);
v___y_3242_ = v_a_3294_;
goto v___jp_3241_;
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_dec_ref_known(v_a_3294_, 1);
lean_dec(v_bcFileName_x3f_3217_);
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3304_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3304_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
else
{
lean_dec(v_mainModuleName_3290_);
lean_dec_ref(v___y_3285_);
lean_dec_ref(v___x_3253_);
lean_dec(v_cFileName_x3f_3216_);
v___y_3242_ = v_a_3294_;
goto v___jp_3241_;
}
}
else
{
lean_object* v_val_3313_; uint32_t v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3317_; 
lean_dec(v_mainModuleName_3290_);
lean_dec_ref(v___y_3285_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
v_val_3313_ = lean_ctor_get(v_a_3294_, 0);
lean_inc(v_val_3313_);
lean_dec_ref_known(v_a_3294_, 1);
v___x_3314_ = lean_eval_main(v_val_3313_, v___x_3253_, v___y_3287_);
v___x_3315_ = lean_box_uint32(v___x_3314_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 0, v___x_3315_);
v___x_3317_ = v___x_3296_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
else
{
lean_del_object(v___x_3296_);
lean_dec(v_mainModuleName_3290_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3285_);
lean_dec_ref(v___x_3253_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
v___y_3227_ = v_a_3294_;
goto v___jp_3226_;
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec(v_mainModuleName_3290_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3285_);
lean_dec_ref(v___x_3253_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
v_a_3320_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3293_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3293_);
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
v___jp_3328_:
{
if (lean_obj_tag(v___y_3334_) == 0)
{
lean_object* v_a_3335_; 
v_a_3335_ = lean_ctor_get(v___y_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___y_3334_, 1);
v___y_3285_ = v___y_3329_;
v___y_3286_ = v___y_3330_;
v___y_3287_ = v___y_3332_;
v___y_3288_ = v___y_3331_;
v___y_3289_ = v___y_3333_;
v_mainModuleName_3290_ = v_a_3335_;
goto v___jp_3284_;
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec_ref(v___x_3253_);
lean_dec(v_incrHeaderSaveFileName_x3f_3224_);
lean_dec(v_incrLoadFileName_x3f_3223_);
lean_dec(v_incrSaveFileName_x3f_3222_);
lean_dec_ref(v_errorOnKinds_3219_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
lean_dec(v_ileanFileName_x3f_3215_);
lean_dec(v_oleanFileName_x3f_3214_);
v_a_3336_ = lean_ctor_get(v___y_3334_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___y_3334_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___y_3334_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___y_3334_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3336_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
v___jp_3344_:
{
if (lean_obj_tag(v_setupFileName_x3f_3213_) == 0)
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_box(0);
if (lean_obj_tag(v___y_3346_) == 1)
{
lean_object* v_val_3351_; lean_object* v___x_3352_; 
v_val_3351_ = lean_ctor_get(v___y_3346_, 0);
lean_inc(v_val_3351_);
lean_dec_ref_known(v___y_3346_, 1);
v___x_3352_ = l_Lean_moduleNameOfFileName(v_val_3351_, v_rootDir_x3f_3212_);
if (lean_obj_tag(v___x_3352_) == 0)
{
v___y_3329_ = v___y_3345_;
v___y_3330_ = v_contents_3349_;
v___y_3331_ = v___x_3350_;
v___y_3332_ = v___y_3347_;
v___y_3333_ = v___y_3348_;
v___y_3334_ = v___x_3352_;
goto v___jp_3328_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_3214_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_3216_) == 0)
{
lean_object* v___x_3353_; 
lean_dec_ref_known(v___x_3352_, 1);
v___x_3353_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__8));
v___y_3285_ = v___y_3345_;
v___y_3286_ = v_contents_3349_;
v___y_3287_ = v___y_3347_;
v___y_3288_ = v___x_3350_;
v___y_3289_ = v___y_3348_;
v_mainModuleName_3290_ = v___x_3353_;
goto v___jp_3284_;
}
else
{
v___y_3329_ = v___y_3345_;
v___y_3330_ = v_contents_3349_;
v___y_3331_ = v___x_3350_;
v___y_3332_ = v___y_3347_;
v___y_3333_ = v___y_3348_;
v___y_3334_ = v___x_3352_;
goto v___jp_3328_;
}
}
else
{
v___y_3329_ = v___y_3345_;
v___y_3330_ = v_contents_3349_;
v___y_3331_ = v___x_3350_;
v___y_3332_ = v___y_3347_;
v___y_3333_ = v___y_3348_;
v___y_3334_ = v___x_3352_;
goto v___jp_3328_;
}
}
}
else
{
lean_object* v___x_3354_; 
lean_dec(v___y_3346_);
lean_dec(v_rootDir_x3f_3212_);
v___x_3354_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__8));
v___y_3285_ = v___y_3345_;
v___y_3286_ = v_contents_3349_;
v___y_3287_ = v___y_3347_;
v___y_3288_ = v___x_3350_;
v___y_3289_ = v___y_3348_;
v_mainModuleName_3290_ = v___x_3354_;
goto v___jp_3284_;
}
}
else
{
lean_object* v_val_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3373_; 
lean_dec(v___y_3346_);
lean_dec(v_rootDir_x3f_3212_);
v_val_3355_ = lean_ctor_get(v_setupFileName_x3f_3213_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v_setupFileName_x3f_3213_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3357_ = v_setupFileName_x3f_3213_;
v_isShared_3358_ = v_isSharedCheck_3373_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_val_3355_);
lean_dec(v_setupFileName_x3f_3213_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3373_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Lean_ModuleSetup_load(v_val_3355_);
lean_dec(v_val_3355_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v_name_3361_; lean_object* v___x_3363_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3359_, 1);
v_name_3361_ = lean_ctor_get(v_a_3360_, 0);
lean_inc(v_name_3361_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v_a_3360_);
v___x_3363_ = v___x_3357_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3360_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
v___y_3285_ = v___y_3345_;
v___y_3286_ = v_contents_3349_;
v___y_3287_ = v___y_3347_;
v___y_3288_ = v___x_3363_;
v___y_3289_ = v___y_3348_;
v_mainModuleName_3290_ = v_name_3361_;
goto v___jp_3284_;
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_del_object(v___x_3357_);
lean_dec_ref(v_contents_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3345_);
lean_dec_ref(v___x_3253_);
lean_dec(v_incrHeaderSaveFileName_x3f_3224_);
lean_dec(v_incrLoadFileName_x3f_3223_);
lean_dec(v_incrSaveFileName_x3f_3222_);
lean_dec_ref(v_errorOnKinds_3219_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
lean_dec(v_ileanFileName_x3f_3215_);
lean_dec(v_oleanFileName_x3f_3214_);
v_a_3365_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3359_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3359_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
}
}
v___jp_3374_:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; uint8_t v___x_3387_; 
v___x_3383_ = lean_nat_add(v_startInclusive_3377_, v___y_3382_);
lean_dec(v___y_3382_);
lean_inc(v___x_3383_);
lean_inc_ref(v_str_3376_);
v___x_3384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3384_, 0, v_str_3376_);
lean_ctor_set(v___x_3384_, 1, v_startInclusive_3377_);
lean_ctor_set(v___x_3384_, 2, v___x_3383_);
v___x_3385_ = l_String_Slice_trimAscii(v___x_3384_);
v___x_3386_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__10));
v___x_3387_ = l_String_Slice_beq(v___x_3385_, v___x_3386_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
lean_dec(v___x_3383_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec(v_endExclusive_3378_);
lean_dec_ref(v_str_3376_);
lean_dec_ref(v___y_3375_);
lean_dec_ref(v___x_3253_);
lean_dec(v_incrHeaderSaveFileName_x3f_3224_);
lean_dec(v_incrLoadFileName_x3f_3223_);
lean_dec(v_incrSaveFileName_x3f_3222_);
lean_dec_ref(v_errorOnKinds_3219_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
lean_dec(v_ileanFileName_x3f_3215_);
lean_dec(v_oleanFileName_x3f_3214_);
lean_dec(v_setupFileName_x3f_3213_);
lean_dec(v_rootDir_x3f_3212_);
v___x_3388_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__11));
v___x_3389_ = l_String_Slice_toString(v___x_3385_);
lean_dec_ref(v___x_3385_);
v___x_3390_ = lean_string_append(v___x_3388_, v___x_3389_);
lean_dec_ref(v___x_3389_);
v___x_3391_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_3392_ = lean_string_append(v___x_3390_, v___x_3391_);
v___x_3393_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3392_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3401_; 
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3401_ == 0)
{
lean_object* v_unused_3402_; 
v_unused_3402_ = lean_ctor_get(v___x_3393_, 0);
lean_dec(v_unused_3402_);
v___x_3395_ = v___x_3393_;
v_isShared_3396_ = v_isSharedCheck_3401_;
goto v_resetjp_3394_;
}
else
{
lean_dec(v___x_3393_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3401_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; lean_object* v___x_3399_; 
v___x_3397_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 0, v___x_3397_);
v___x_3399_ = v___x_3395_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3397_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
v_a_3403_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3393_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3393_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v___x_3411_; 
lean_dec_ref(v___x_3385_);
v___x_3411_ = lean_string_utf8_extract_fast(v_str_3376_, v___x_3383_, v_endExclusive_3378_);
lean_dec(v_endExclusive_3378_);
lean_dec(v___x_3383_);
lean_dec_ref(v_str_3376_);
v___y_3345_ = v___y_3375_;
v___y_3346_ = v___y_3379_;
v___y_3347_ = v___y_3380_;
v___y_3348_ = v___y_3381_;
v_contents_3349_ = v___x_3411_;
goto v___jp_3344_;
}
}
v___jp_3412_:
{
if (lean_obj_tag(v___y_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3418_; 
v_a_3417_ = lean_ctor_get(v___y_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref_known(v___y_3416_, 1);
v___x_3418_ = lean_decode_lossy_utf8(v_a_3417_);
lean_dec(v_a_3417_);
if (v_onlyDeps_3208_ == 0)
{
if (v_onlySrcDeps_3209_ == 0)
{
lean_object* v___x_3419_; 
lean_inc_ref(v___x_3418_);
v___x_3419_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_3418_);
if (lean_obj_tag(v___x_3419_) == 1)
{
lean_object* v_val_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec_ref(v___x_3418_);
v_val_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_val_3420_);
lean_dec_ref_known(v___x_3419_, 1);
v___x_3421_ = lean_unsigned_to_nat(0u);
v___x_3422_ = lean_box(0);
v___x_3423_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3420_, v___x_3421_, v___x_3422_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_str_3424_; lean_object* v_startInclusive_3425_; lean_object* v_endExclusive_3426_; lean_object* v___x_3427_; 
v_str_3424_ = lean_ctor_get(v_val_3420_, 0);
lean_inc_ref(v_str_3424_);
v_startInclusive_3425_ = lean_ctor_get(v_val_3420_, 1);
lean_inc(v_startInclusive_3425_);
v_endExclusive_3426_ = lean_ctor_get(v_val_3420_, 2);
lean_inc(v_endExclusive_3426_);
lean_dec(v_val_3420_);
v___x_3427_ = lean_nat_sub(v_endExclusive_3426_, v_startInclusive_3425_);
lean_inc_ref(v___y_3414_);
v___y_3375_ = v___y_3414_;
v_str_3376_ = v_str_3424_;
v_startInclusive_3377_ = v_startInclusive_3425_;
v_endExclusive_3378_ = v_endExclusive_3426_;
v___y_3379_ = v___y_3415_;
v___y_3380_ = v___y_3413_;
v___y_3381_ = v___y_3414_;
v___y_3382_ = v___x_3427_;
goto v___jp_3374_;
}
else
{
lean_object* v_val_3428_; lean_object* v_str_3429_; lean_object* v_startInclusive_3430_; lean_object* v_endExclusive_3431_; 
v_val_3428_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_val_3428_);
lean_dec_ref_known(v___x_3423_, 1);
v_str_3429_ = lean_ctor_get(v_val_3420_, 0);
lean_inc_ref(v_str_3429_);
v_startInclusive_3430_ = lean_ctor_get(v_val_3420_, 1);
lean_inc(v_startInclusive_3430_);
v_endExclusive_3431_ = lean_ctor_get(v_val_3420_, 2);
lean_inc(v_endExclusive_3431_);
lean_dec(v_val_3420_);
lean_inc_ref(v___y_3414_);
v___y_3375_ = v___y_3414_;
v_str_3376_ = v_str_3429_;
v_startInclusive_3377_ = v_startInclusive_3430_;
v_endExclusive_3378_ = v_endExclusive_3431_;
v___y_3379_ = v___y_3415_;
v___y_3380_ = v___y_3413_;
v___y_3381_ = v___y_3414_;
v___y_3382_ = v_val_3428_;
goto v___jp_3374_;
}
}
else
{
lean_dec(v___x_3419_);
lean_inc_ref(v___y_3414_);
v___y_3345_ = v___y_3414_;
v___y_3346_ = v___y_3415_;
v___y_3347_ = v___y_3413_;
v___y_3348_ = v___y_3414_;
v_contents_3349_ = v___x_3418_;
goto v___jp_3344_;
}
}
else
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
lean_dec(v___y_3415_);
lean_dec(v___y_3413_);
lean_dec_ref(v___x_3253_);
lean_dec(v_incrHeaderSaveFileName_x3f_3224_);
lean_dec(v_incrLoadFileName_x3f_3223_);
lean_dec(v_incrSaveFileName_x3f_3222_);
lean_dec_ref(v_errorOnKinds_3219_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
lean_dec(v_ileanFileName_x3f_3215_);
lean_dec(v_oleanFileName_x3f_3214_);
lean_dec(v_setupFileName_x3f_3213_);
lean_dec(v_rootDir_x3f_3212_);
v___x_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3432_, 0, v___y_3414_);
v___x_3433_ = l_Lean_Elab_printImportSrcs(v___x_3418_, v___x_3432_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3441_; 
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3441_ == 0)
{
lean_object* v_unused_3442_; 
v_unused_3442_ = lean_ctor_get(v___x_3433_, 0);
lean_dec(v_unused_3442_);
v___x_3435_ = v___x_3433_;
v_isShared_3436_ = v_isSharedCheck_3441_;
goto v_resetjp_3434_;
}
else
{
lean_dec(v___x_3433_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3441_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3437_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3437_);
v___x_3439_ = v___x_3435_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
v_a_3443_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3433_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3433_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3452_; 
lean_dec(v___y_3415_);
lean_dec(v___y_3413_);
lean_dec_ref(v___x_3253_);
lean_dec(v_incrHeaderSaveFileName_x3f_3224_);
lean_dec(v_incrLoadFileName_x3f_3223_);
lean_dec(v_incrSaveFileName_x3f_3222_);
lean_dec_ref(v_errorOnKinds_3219_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
lean_dec(v_ileanFileName_x3f_3215_);
lean_dec(v_oleanFileName_x3f_3214_);
lean_dec(v_setupFileName_x3f_3213_);
lean_dec(v_rootDir_x3f_3212_);
v___x_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___y_3414_);
v___x_3452_ = l_Lean_Elab_printImports(v___x_3418_, v___x_3451_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3460_; 
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v___x_3452_, 0);
lean_dec(v_unused_3461_);
v___x_3454_ = v___x_3452_;
v_isShared_3455_ = v_isSharedCheck_3460_;
goto v_resetjp_3453_;
}
else
{
lean_dec(v___x_3452_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3460_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3458_; 
v___x_3456_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 0, v___x_3456_);
v___x_3458_ = v___x_3454_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3456_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
v_a_3462_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3452_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3452_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___x_3253_);
lean_dec(v_incrHeaderSaveFileName_x3f_3224_);
lean_dec(v_incrLoadFileName_x3f_3223_);
lean_dec(v_incrSaveFileName_x3f_3222_);
lean_dec_ref(v_errorOnKinds_3219_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
lean_dec(v_ileanFileName_x3f_3215_);
lean_dec(v_oleanFileName_x3f_3214_);
lean_dec(v_setupFileName_x3f_3213_);
lean_dec(v_rootDir_x3f_3212_);
v_a_3470_ = lean_ctor_get(v___y_3416_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___y_3416_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___y_3416_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___y_3416_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
v___jp_3478_:
{
if (v_useStdin_3207_ == 0)
{
lean_object* v___x_3482_; 
v___x_3482_ = l_IO_FS_readBinFile(v_fileName_3481_);
v___y_3413_ = v___y_3480_;
v___y_3414_ = v_fileName_3481_;
v___y_3415_ = v___y_3479_;
v___y_3416_ = v___x_3482_;
goto v___jp_3412_;
}
else
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = lean_get_stdin();
v___x_3484_ = l_IO_FS_Stream_readBinToEnd(v___x_3483_);
v___y_3413_ = v___y_3480_;
v___y_3414_ = v_fileName_3481_;
v___y_3415_ = v___y_3479_;
v___y_3416_ = v___x_3484_;
goto v___jp_3412_;
}
}
v___jp_3485_:
{
if (lean_obj_tag(v___y_3486_) == 1)
{
lean_object* v_val_3488_; 
v_val_3488_ = lean_ctor_get(v___y_3486_, 0);
lean_inc(v_val_3488_);
v___y_3479_ = v___y_3486_;
v___y_3480_ = v___y_3487_;
v_fileName_3481_ = v_val_3488_;
goto v___jp_3478_;
}
else
{
if (v_useStdin_3207_ == 0)
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
lean_dec(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___x_3253_);
lean_dec(v_incrHeaderSaveFileName_x3f_3224_);
lean_dec(v_incrLoadFileName_x3f_3223_);
lean_dec(v_incrSaveFileName_x3f_3222_);
lean_dec_ref(v_errorOnKinds_3219_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
lean_dec(v_ileanFileName_x3f_3215_);
lean_dec(v_oleanFileName_x3f_3214_);
lean_dec(v_setupFileName_x3f_3213_);
lean_dec(v_rootDir_x3f_3212_);
v___x_3489_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__5));
v___x_3490_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3489_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v___x_3491_; 
lean_dec_ref_known(v___x_3490_, 1);
v___x_3491_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3254_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3499_; 
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3499_ == 0)
{
lean_object* v_unused_3500_; 
v_unused_3500_ = lean_ctor_get(v___x_3491_, 0);
lean_dec(v_unused_3500_);
v___x_3493_ = v___x_3491_;
v_isShared_3494_ = v_isSharedCheck_3499_;
goto v_resetjp_3492_;
}
else
{
lean_dec(v___x_3491_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3499_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3495_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v___x_3495_);
v___x_3497_ = v___x_3493_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
v_a_3501_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3491_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3491_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
v_a_3509_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3490_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3490_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
else
{
lean_object* v___x_3517_; 
v___x_3517_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__12));
v___y_3479_ = v___y_3486_;
v___y_3480_ = v___y_3487_;
v_fileName_3481_ = v___x_3517_;
goto v___jp_3478_;
}
}
}
v___jp_3518_:
{
uint8_t v___x_3522_; 
v___x_3522_ = l_List_isEmpty___redArg(v___y_3520_);
if (v___x_3522_ == 0)
{
lean_dec(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___x_3253_);
lean_dec(v_incrHeaderSaveFileName_x3f_3224_);
lean_dec(v_incrLoadFileName_x3f_3223_);
lean_dec(v_incrSaveFileName_x3f_3222_);
lean_dec_ref(v_errorOnKinds_3219_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
lean_dec(v_ileanFileName_x3f_3215_);
lean_dec(v_oleanFileName_x3f_3214_);
lean_dec(v_setupFileName_x3f_3213_);
lean_dec(v_rootDir_x3f_3212_);
goto v___jp_3255_;
}
else
{
if (v___y_3521_ == 0)
{
v___y_3486_ = v___y_3519_;
v___y_3487_ = v___y_3520_;
goto v___jp_3485_;
}
else
{
lean_dec(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___x_3253_);
lean_dec(v_incrHeaderSaveFileName_x3f_3224_);
lean_dec(v_incrLoadFileName_x3f_3223_);
lean_dec(v_incrSaveFileName_x3f_3222_);
lean_dec_ref(v_errorOnKinds_3219_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
lean_dec(v_ileanFileName_x3f_3215_);
lean_dec(v_oleanFileName_x3f_3214_);
lean_dec(v_setupFileName_x3f_3213_);
lean_dec(v_rootDir_x3f_3212_);
goto v___jp_3255_;
}
}
}
v___jp_3523_:
{
if (v_run_3221_ == 0)
{
v___y_3519_ = v_fst_3525_;
v___y_3520_ = v_snd_3526_;
v___y_3521_ = v___y_3524_;
goto v___jp_3518_;
}
else
{
if (v___y_3524_ == 0)
{
v___y_3486_ = v_fst_3525_;
v___y_3487_ = v_snd_3526_;
goto v___jp_3485_;
}
else
{
v___y_3519_ = v_fst_3525_;
v___y_3520_ = v_snd_3526_;
v___y_3521_ = v___y_3524_;
goto v___jp_3518_;
}
}
}
v___jp_3527_:
{
if (lean_obj_tag(v_args_3173_) == 0)
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_box(0);
v___y_3524_ = v___y_3528_;
v_fst_3525_ = v___x_3529_;
v_snd_3526_ = v_args_3173_;
goto v___jp_3523_;
}
else
{
lean_object* v_head_3530_; lean_object* v_tail_3531_; lean_object* v___x_3532_; 
v_head_3530_ = lean_ctor_get(v_args_3173_, 0);
lean_inc(v_head_3530_);
v_tail_3531_ = lean_ctor_get(v_args_3173_, 1);
lean_inc(v_tail_3531_);
lean_dec_ref_known(v_args_3173_, 2);
v___x_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3532_, 0, v_head_3530_);
v___y_3524_ = v___y_3528_;
v_fst_3525_ = v___x_3532_;
v_snd_3526_ = v_tail_3531_;
goto v___jp_3523_;
}
}
v___jp_3533_:
{
switch(v_component_3206_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_3205_);
if (v_onlyDeps_3208_ == 0)
{
v___y_3528_ = v_printLibDir_3203_;
goto v___jp_3527_;
}
else
{
if (v_depsJson_3210_ == 0)
{
v___y_3528_ = v_depsJson_3210_;
goto v___jp_3527_;
}
else
{
lean_dec_ref(v___x_3253_);
lean_dec(v_incrHeaderSaveFileName_x3f_3224_);
lean_dec(v_incrLoadFileName_x3f_3223_);
lean_dec(v_incrSaveFileName_x3f_3222_);
lean_dec_ref(v_errorOnKinds_3219_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
lean_dec(v_ileanFileName_x3f_3215_);
lean_dec(v_oleanFileName_x3f_3214_);
lean_dec(v_setupFileName_x3f_3213_);
lean_dec(v_rootDir_x3f_3212_);
if (v_useStdin_3207_ == 0)
{
lean_object* v___x_3534_; 
v___x_3534_ = lean_array_mk(v_args_3173_);
v_fns_3177_ = v___x_3534_;
goto v___jp_3176_;
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
lean_dec(v_args_3173_);
v___x_3535_ = lean_get_stdin();
v___x_3536_ = l_IO_FS_Stream_lines(v___x_3535_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
v_fns_3177_ = v_a_3537_;
goto v___jp_3176_;
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
v_a_3538_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3536_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3536_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
lean_dec_ref(v___x_3253_);
lean_dec(v_incrHeaderSaveFileName_x3f_3224_);
lean_dec(v_incrLoadFileName_x3f_3223_);
lean_dec(v_incrSaveFileName_x3f_3222_);
lean_dec_ref(v_errorOnKinds_3219_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
lean_dec(v_ileanFileName_x3f_3215_);
lean_dec(v_oleanFileName_x3f_3214_);
lean_dec(v_setupFileName_x3f_3213_);
lean_dec(v_rootDir_x3f_3212_);
lean_dec(v_args_3173_);
v___x_3546_ = lean_array_to_list(v_forwardedArgs_3205_);
v___x_3547_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3546_);
return v___x_3547_;
}
default: 
{
lean_object* v___x_3548_; 
lean_dec(v_incrHeaderSaveFileName_x3f_3224_);
lean_dec(v_incrLoadFileName_x3f_3223_);
lean_dec(v_incrSaveFileName_x3f_3222_);
lean_dec_ref(v_errorOnKinds_3219_);
lean_dec(v_bcFileName_x3f_3217_);
lean_dec(v_cFileName_x3f_3216_);
lean_dec(v_ileanFileName_x3f_3215_);
lean_dec(v_oleanFileName_x3f_3214_);
lean_dec(v_setupFileName_x3f_3213_);
lean_dec(v_rootDir_x3f_3212_);
lean_dec_ref(v_forwardedArgs_3205_);
lean_dec(v_args_3173_);
v___x_3548_ = l_Lean_Server_FileWorker_workerMain(v___x_3253_);
return v___x_3548_;
}
}
}
v___jp_3549_:
{
lean_object* v___x_3550_; lean_object* v_timeout_3551_; lean_object* v___x_3552_; uint8_t v___x_3553_; 
v___x_3550_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3551_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3253_, v___x_3550_);
v___x_3552_ = lean_unsigned_to_nat(0u);
v___x_3553_ = lean_nat_dec_eq(v_timeout_3551_, v___x_3552_);
if (v___x_3553_ == 0)
{
size_t v___x_3554_; size_t v___x_3555_; size_t v___x_3556_; lean_object* v___x_3557_; 
v___x_3554_ = lean_usize_of_nat(v_timeout_3551_);
lean_dec(v_timeout_3551_);
v___x_3555_ = ((size_t)1000ULL);
v___x_3556_ = lean_usize_mul(v___x_3554_, v___x_3555_);
v___x_3557_ = lean_internal_set_max_heartbeat(v___x_3556_);
goto v___jp_3533_;
}
else
{
lean_dec(v_timeout_3551_);
goto v___jp_3533_;
}
}
}
else
{
lean_object* v___x_3567_; 
lean_dec_ref(v_opts_3174_);
lean_dec(v_args_3173_);
v___x_3567_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3569_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
v___x_3569_ = l_Lean_getLibDir(v_a_3568_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v___x_3571_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3570_);
lean_dec_ref_known(v___x_3569_, 1);
v___x_3571_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3570_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3579_; 
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3579_ == 0)
{
lean_object* v_unused_3580_; 
v_unused_3580_ = lean_ctor_get(v___x_3571_, 0);
lean_dec(v_unused_3580_);
v___x_3573_ = v___x_3571_;
v_isShared_3574_ = v_isSharedCheck_3579_;
goto v_resetjp_3572_;
}
else
{
lean_dec(v___x_3571_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3579_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; lean_object* v___x_3577_; 
v___x_3575_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3575_);
v___x_3577_ = v___x_3573_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
v_a_3581_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3571_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3571_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
v_a_3589_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3569_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3569_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
v_a_3597_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3567_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3567_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
}
else
{
lean_object* v___x_3605_; 
lean_dec_ref(v_opts_3174_);
lean_dec(v_args_3173_);
v___x_3605_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3607_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref_known(v___x_3605_, 1);
v___x_3607_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3606_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3615_; 
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3615_ == 0)
{
lean_object* v_unused_3616_; 
v_unused_3616_ = lean_ctor_get(v___x_3607_, 0);
lean_dec(v_unused_3616_);
v___x_3609_ = v___x_3607_;
v_isShared_3610_ = v_isSharedCheck_3615_;
goto v_resetjp_3608_;
}
else
{
lean_dec(v___x_3607_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3615_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3611_);
v___x_3613_ = v___x_3609_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
v_a_3617_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3607_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3607_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
v_a_3625_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3605_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3605_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
v___jp_3176_:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_printImportsJson(v_fns_3177_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3186_; 
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3186_ == 0)
{
lean_object* v_unused_3187_; 
v_unused_3187_ = lean_ctor_get(v___x_3178_, 0);
lean_dec(v_unused_3187_);
v___x_3180_ = v___x_3178_;
v_isShared_3181_ = v_isSharedCheck_3186_;
goto v_resetjp_3179_;
}
else
{
lean_dec(v___x_3178_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3186_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3182_; lean_object* v___x_3184_; 
v___x_3182_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3182_);
v___x_3184_ = v___x_3180_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
v_a_3188_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3178_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3178_);
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
v___jp_3196_:
{
uint8_t v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = 0;
v___x_3198_ = lean_io_exit(v___x_3197_);
return v___x_3198_;
}
v___jp_3199_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
return v___x_3201_;
}
}
}
LEAN_EXPORT void lean_shell_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_3173_ = stack[0].m_obj;
lean_object* v_opts_3174_ = stack[1].m_obj;
lean_object* v_res_3633_;
v_res_3633_ = lean_shell_main(v_args_3173_, v_opts_3174_);
stack->m_obj
 = v_res_3633_;
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3634_, lean_object* v_opts_3635_, lean_object* v_a_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = lean_shell_main(v_args_3634_, v_opts_3635_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3638_, lean_object* v_inst_3639_, lean_object* v_R_3640_, lean_object* v_a_3641_, lean_object* v_b_3642_, lean_object* v_c_3643_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3638_, v_a_3641_, v_b_3642_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3645_, lean_object* v_inst_3646_, lean_object* v_R_3647_, lean_object* v_a_3648_, lean_object* v_b_3649_, lean_object* v_c_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3645_, v_inst_3646_, v_R_3647_, v_a_3648_, v_b_3649_, v_c_3650_);
lean_dec(v_b_3649_);
lean_dec_ref(v_val_3645_);
return v_res_3651_;
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
