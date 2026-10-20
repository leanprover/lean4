// Lean compiler output
// Module: Lean.Shell
// Imports: import Lean.Elab.Frontend import Lean.Elab.ParseImportsFast import Lean.Server.Watchdog import Lean.Server.FileWorker import Lean.Compiler.LCNF.EmitC import Init.System.Platform import Init.Data.String.Lossy import Lean.Compiler.Options import Std.Async.Process
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
lean_object* lean_display_cumulative_profiling_times();
lean_object* lean_io_exit(uint8_t);
lean_object* l_Lean_Options_mergeBy(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_moduleNameOfFileName(lean_object*, lean_object*);
lean_object* l_Lean_ModuleSetup_load(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
uint8_t l_String_Slice_beq(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "max_memory"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 81, 94, 214, 186, 212, 139, 105)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__5_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__5_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__5_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__7_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__5_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__7_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__7_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__8_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Shell"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__8_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__8_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__9_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__7_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__8_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 69, 169, 154, 100, 37, 235, 16)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__9_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__9_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__10_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__9_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(89, 66, 50, 199, 34, 209, 110, 139)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__10_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__10_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__10_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__6_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 66, 221, 81, 125, 65, 65, 89)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__12_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "maxMemory"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__12_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__12_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__12_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(28, 55, 113, 152, 101, 101, 83, 88)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_maxMemory;
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "timeout"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(108, 201, 121, 146, 245, 42, 97, 81)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 41, 251, 70, 36, 12, 36, 182)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_timeout;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "verbose"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 17, 151, 162, 143, 207, 214, 14)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__11_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 79, 210, 200, 161, 113, 65, 201)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2____boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__2;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "LLVM code generation"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__3 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__3_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Expected exactly one file name"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__4 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__4_value;
static const lean_array_object l___private_Lean_Shell_0__Lean_shellMain___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__5_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_stdin"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__6 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__6_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__6_value),LEAN_SCALAR_PTR_LITERAL(37, 142, 62, 167, 41, 238, 22, 79)}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__7 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__7_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lean4"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__8 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__8_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown language '"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__9 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__9_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<stdin>"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__10 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__10_value;
LEAN_EXPORT lean_object* lean_shell_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object* v_env_5_, lean_object* v_opts_6_, lean_object* v_args_7_, lean_object* v_a_00___x40___internal___hyg_8_){
_start:
{
uint32_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = lean_eval_main(v_env_5_, v_opts_6_, v_args_7_);
lean_dec(v_args_7_);
lean_dec_ref(v_opts_6_);
lean_dec_ref(v_env_5_);
v_r_10_ = lean_box_uint32(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object* v_a_00___x40___internal___hyg_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lean_init_llvm();
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object* v_env_18_, lean_object* v_modName_19_, lean_object* v_filepath_20_, lean_object* v_a_00___x40___internal___hyg_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lean_emit_llvm(v_env_18_, v_modName_19_, v_filepath_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(lean_object* v_x_00___x40_Lean_Shell_2339721992____hygCtx___hyg_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = lean_internal_has_address_sanitizer(v_x_00___x40_Lean_Shell_2339721992____hygCtx___hyg_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isMultiThread___boxed(lean_object* v_x_00___x40_Lean_Shell_3295292909____hygCtx___hyg_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = lean_internal_is_multi_thread(v_x_00___x40_Lean_Shell_3295292909____hygCtx___hyg_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isDebug___boxed(lean_object* v_x_00___x40_Lean_Shell_97005966____hygCtx___hyg_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = lean_internal_is_debug(v_x_00___x40_Lean_Shell_97005966____hygCtx___hyg_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBuildType___boxed(lean_object* v_x_00___x40_Lean_Shell_1721435280____hygCtx___hyg_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lean_internal_get_build_type(v_x_00___x40_Lean_Shell_1721435280____hygCtx___hyg_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxMemory___boxed(lean_object* v_x_00___x40_Lean_Shell_1091001955____hygCtx___hyg_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lean_internal_get_default_max_memory(v_x_00___x40_Lean_Shell_1091001955____hygCtx___hyg_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxMemory___boxed(lean_object* v_max_43_, lean_object* v_a_00___x40___internal___hyg_44_){
_start:
{
size_t v_max_boxed_45_; lean_object* v_res_46_; 
v_max_boxed_45_ = lean_unbox_usize(v_max_43_);
lean_dec(v_max_43_);
v_res_46_ = lean_internal_set_max_memory(v_max_boxed_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxHeartbeat___boxed(lean_object* v_x_00___x40_Lean_Shell_2736094960____hygCtx___hyg_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lean_internal_get_default_max_heartbeat(v_x_00___x40_Lean_Shell_2736094960____hygCtx___hyg_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxHeartbeat___boxed(lean_object* v_max_52_, lean_object* v_a_00___x40___internal___hyg_53_){
_start:
{
size_t v_max_boxed_54_; lean_object* v_res_55_; 
v_max_boxed_54_ = lean_unbox_usize(v_max_52_);
lean_dec(v_max_52_);
v_res_55_ = lean_internal_set_max_heartbeat(v_max_boxed_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultVerbose___boxed(lean_object* v_x_00___x40_Lean_Shell_28281146____hygCtx___hyg_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = lean_internal_get_default_verbose(v_x_00___x40_Lean_Shell_28281146____hygCtx___hyg_57_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setExitOnPanic___boxed(lean_object* v_exit_62_, lean_object* v_a_00___x40___internal___hyg_63_){
_start:
{
uint8_t v_exit_boxed_64_; lean_object* v_res_65_; 
v_exit_boxed_64_ = lean_unbox(v_exit_62_);
v_res_65_ = lean_internal_set_exit_on_panic(v_exit_boxed_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setThreadStackSize___boxed(lean_object* v_sz_68_, lean_object* v_a_00___x40___internal___hyg_69_){
_start:
{
size_t v_sz_boxed_70_; lean_object* v_res_71_; 
v_sz_boxed_70_ = lean_unbox_usize(v_sz_68_);
lean_dec(v_sz_68_);
v_res_71_ = lean_internal_set_thread_stack_size(v_sz_boxed_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_enableDebug___boxed(lean_object* v_tag_74_, lean_object* v_a_00___x40___internal___hyg_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lean_internal_enable_debug(v_tag_74_);
lean_dec_ref(v_tag_74_);
return v_res_76_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_78_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_79_ = l_Lean_version_specialDesc;
v___x_80_ = lean_string_dec_eq(v___x_79_, v___x_78_);
return v___x_80_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__2));
v___x_83_ = l_Lean_versionStringCore;
v___x_84_ = lean_string_append(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = l_Lean_version_specialDesc;
v___x_86_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__3, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__3_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3);
v___x_87_ = lean_string_append(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__5));
v___x_90_ = l_Lean_versionStringCore;
v___x_91_ = lean_string_append(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString(void){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__1, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
v___x_93_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__4, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__4_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4);
return v___x_93_;
}
else
{
uint8_t v___x_94_; 
v___x_94_ = l_Lean_version_isRelease;
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__6, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__6_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6);
return v___x_95_;
}
else
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_versionStringCore;
return v___x_96_;
}
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_box(0);
v___x_100_ = lean_internal_get_build_type(v___x_99_);
return v___x_100_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_102_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_103_ = l_Lean_githash;
v___x_104_ = lean_string_dec_eq(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_106_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_107_ = l_System_Platform_target;
v___x_108_ = lean_string_dec_eq(v___x_107_, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7(void){
_start:
{
lean_object* v___x_109_; lean_object* v_ver_110_; lean_object* v___x_111_; 
v___x_109_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__1));
v_ver_110_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_111_ = lean_string_append(v_ver_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_ver_114_; 
v___x_112_ = l_System_Platform_target;
v___x_113_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__7, &l___private_Lean_Shell_0__Lean_versionHeader___closed__7_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7);
v_ver_114_ = lean_string_append(v___x_113_, v___x_112_);
return v_ver_114_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader(void){
_start:
{
lean_object* v_ver_116_; lean_object* v_ver_126_; lean_object* v_ver_132_; uint8_t v___x_133_; 
v_ver_132_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_133_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__6, &l___private_Lean_Shell_0__Lean_versionHeader___closed__6_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6);
if (v___x_133_ == 0)
{
lean_object* v_ver_134_; 
v_ver_134_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__8, &l___private_Lean_Shell_0__Lean_versionHeader___closed__8_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8);
v_ver_126_ = v_ver_134_;
goto v___jp_125_;
}
else
{
v_ver_126_ = v_ver_132_;
goto v___jp_125_;
}
v___jp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_117_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__0));
v___x_118_ = lean_string_append(v___x_117_, v_ver_116_);
lean_dec_ref(v_ver_116_);
v___x_119_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__1));
v___x_120_ = lean_string_append(v___x_118_, v___x_119_);
v___x_121_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__2, &l___private_Lean_Shell_0__Lean_versionHeader___closed__2_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2);
v___x_122_ = lean_string_append(v___x_120_, v___x_121_);
v___x_123_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__3));
v___x_124_ = lean_string_append(v___x_122_, v___x_123_);
return v___x_124_;
}
v___jp_125_:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = l_Lean_githash;
v___x_128_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__4, &l___private_Lean_Shell_0__Lean_versionHeader___closed__4_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_ver_131_; 
v___x_129_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__5));
lean_inc_ref(v_ver_126_);
v___x_130_ = lean_string_append(v_ver_126_, v___x_129_);
v_ver_131_ = lean_string_append(v___x_130_, v___x_127_);
v_ver_116_ = v_ver_131_;
goto v___jp_115_;
}
else
{
lean_inc_ref(v_ver_126_);
v_ver_116_ = v_ver_126_;
goto v___jp_115_;
}
}
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_featuresString___closed__0(void){
_start:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_box(0);
v___x_136_ = lean_internal_has_llvm_backend(v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_featuresString(void){
_start:
{
uint8_t v___x_139_; 
v___x_139_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_featuresString___closed__0, &l___private_Lean_Shell_0__Lean_featuresString___closed__0_once, _init_l___private_Lean_Shell_0__Lean_featuresString___closed__0);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_featuresString___closed__1));
return v___x_140_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_featuresString___closed__2));
return v___x_141_;
}
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16(void){
_start:
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = lean_box(0);
v___x_159_ = lean_internal_is_debug(v___x_158_);
return v___x_159_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40(void){
_start:
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = lean_box(0);
v___x_184_ = lean_internal_is_multi_thread(v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp(uint8_t v_useStderr_189_){
_start:
{
lean_object* v___y_192_; lean_object* v___y_196_; lean_object* v_out_231_; 
if (v_useStderr_189_ == 0)
{
lean_object* v___x_287_; 
v___x_287_ = lean_get_stdout();
v_out_231_ = v___x_287_;
goto v___jp_230_;
}
else
{
lean_object* v___x_288_; 
v___x_288_ = lean_get_stderr();
v_out_231_ = v___x_288_;
goto v___jp_230_;
}
v___jp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__0));
v___x_194_ = l_IO_FS_Stream_putStrLn(v___y_192_, v___x_193_);
return v___x_194_;
}
v___jp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__1));
lean_inc_ref(v___y_196_);
v___x_198_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_197_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec_ref_known(v___x_198_, 1);
v___x_199_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__2));
lean_inc_ref(v___y_196_);
v___x_200_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec_ref_known(v___x_200_, 1);
v___x_201_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__3));
lean_inc_ref(v___y_196_);
v___x_202_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec_ref_known(v___x_202_, 1);
v___x_203_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__4));
lean_inc_ref(v___y_196_);
v___x_204_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_203_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec_ref_known(v___x_204_, 1);
v___x_205_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__5));
lean_inc_ref(v___y_196_);
v___x_206_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_205_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec_ref_known(v___x_206_, 1);
v___x_207_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__6));
lean_inc_ref(v___y_196_);
v___x_208_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec_ref_known(v___x_208_, 1);
v___x_209_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__7));
lean_inc_ref(v___y_196_);
v___x_210_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec_ref_known(v___x_210_, 1);
v___x_211_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__8));
lean_inc_ref(v___y_196_);
v___x_212_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_211_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec_ref_known(v___x_212_, 1);
v___x_213_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__9));
lean_inc_ref(v___y_196_);
v___x_214_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_213_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec_ref_known(v___x_214_, 1);
v___x_215_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__10));
lean_inc_ref(v___y_196_);
v___x_216_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec_ref_known(v___x_216_, 1);
v___x_217_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__11));
lean_inc_ref(v___y_196_);
v___x_218_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_217_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec_ref_known(v___x_218_, 1);
v___x_219_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__12));
lean_inc_ref(v___y_196_);
v___x_220_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_219_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec_ref_known(v___x_220_, 1);
v___x_221_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__13));
lean_inc_ref(v___y_196_);
v___x_222_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec_ref_known(v___x_222_, 1);
v___x_223_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__14));
lean_inc_ref(v___y_196_);
v___x_224_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref_known(v___x_224_, 1);
v___x_225_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__15));
lean_inc_ref(v___y_196_);
v___x_226_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_225_);
if (lean_obj_tag(v___x_226_) == 0)
{
uint8_t v___x_227_; 
lean_dec_ref_known(v___x_226_, 1);
v___x_227_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__16, &l___private_Lean_Shell_0__Lean_displayHelp___closed__16_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
if (v___x_227_ == 0)
{
v___y_192_ = v___y_196_;
goto v___jp_191_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__17));
lean_inc_ref(v___y_196_);
v___x_229_ = l_IO_FS_Stream_putStrLn(v___y_196_, v___x_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_dec_ref_known(v___x_229_, 1);
v___y_192_ = v___y_196_;
goto v___jp_191_;
}
else
{
lean_dec_ref(v___y_196_);
return v___x_229_;
}
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_226_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_224_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_222_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_220_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_218_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_216_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_214_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_212_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_210_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_208_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_206_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_204_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_202_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_200_;
}
}
else
{
lean_dec_ref(v___y_196_);
return v___x_198_;
}
}
v___jp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = l___private_Lean_Shell_0__Lean_versionHeader;
lean_inc_ref(v_out_231_);
v___x_233_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec_ref_known(v___x_233_, 1);
v___x_234_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__18));
lean_inc_ref(v_out_231_);
v___x_235_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_234_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec_ref_known(v___x_235_, 1);
v___x_236_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__19));
lean_inc_ref(v_out_231_);
v___x_237_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_236_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec_ref_known(v___x_237_, 1);
v___x_238_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__20));
lean_inc_ref(v_out_231_);
v___x_239_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_238_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec_ref_known(v___x_239_, 1);
v___x_240_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__21));
lean_inc_ref(v_out_231_);
v___x_241_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_240_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec_ref_known(v___x_241_, 1);
v___x_242_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__22));
lean_inc_ref(v_out_231_);
v___x_243_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_242_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec_ref_known(v___x_243_, 1);
v___x_244_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__23));
lean_inc_ref(v_out_231_);
v___x_245_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_244_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec_ref_known(v___x_245_, 1);
v___x_246_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__24));
lean_inc_ref(v_out_231_);
v___x_247_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_246_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec_ref_known(v___x_247_, 1);
v___x_248_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__25));
lean_inc_ref(v_out_231_);
v___x_249_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_248_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec_ref_known(v___x_249_, 1);
v___x_250_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__26));
lean_inc_ref(v_out_231_);
v___x_251_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_250_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec_ref_known(v___x_251_, 1);
v___x_252_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__27));
lean_inc_ref(v_out_231_);
v___x_253_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_252_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec_ref_known(v___x_253_, 1);
v___x_254_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__28));
lean_inc_ref(v_out_231_);
v___x_255_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_254_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref_known(v___x_255_, 1);
v___x_256_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__29));
lean_inc_ref(v_out_231_);
v___x_257_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_256_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec_ref_known(v___x_257_, 1);
v___x_258_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__30));
lean_inc_ref(v_out_231_);
v___x_259_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_258_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec_ref_known(v___x_259_, 1);
v___x_260_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__31));
lean_inc_ref(v_out_231_);
v___x_261_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_260_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec_ref_known(v___x_261_, 1);
v___x_262_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__32));
lean_inc_ref(v_out_231_);
v___x_263_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_262_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec_ref_known(v___x_263_, 1);
v___x_264_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__33));
lean_inc_ref(v_out_231_);
v___x_265_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_264_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec_ref_known(v___x_265_, 1);
v___x_266_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__34));
lean_inc_ref(v_out_231_);
v___x_267_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_266_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec_ref_known(v___x_267_, 1);
v___x_268_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__35));
lean_inc_ref(v_out_231_);
v___x_269_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_268_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec_ref_known(v___x_269_, 1);
v___x_270_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__36));
lean_inc_ref(v_out_231_);
v___x_271_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_270_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec_ref_known(v___x_271_, 1);
v___x_272_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__37));
lean_inc_ref(v_out_231_);
v___x_273_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_272_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec_ref_known(v___x_273_, 1);
v___x_274_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__38));
lean_inc_ref(v_out_231_);
v___x_275_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_274_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec_ref_known(v___x_275_, 1);
v___x_276_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__39));
lean_inc_ref(v_out_231_);
v___x_277_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_276_);
if (lean_obj_tag(v___x_277_) == 0)
{
uint8_t v___x_278_; 
lean_dec_ref_known(v___x_277_, 1);
v___x_278_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__40, &l___private_Lean_Shell_0__Lean_displayHelp___closed__40_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40);
if (v___x_278_ == 0)
{
v___y_196_ = v_out_231_;
goto v___jp_195_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__41));
lean_inc_ref(v_out_231_);
v___x_280_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec_ref_known(v___x_280_, 1);
v___x_281_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__42));
lean_inc_ref(v_out_231_);
v___x_282_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec_ref_known(v___x_282_, 1);
v___x_283_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__43));
lean_inc_ref(v_out_231_);
v___x_284_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_283_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec_ref_known(v___x_284_, 1);
v___x_285_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__44));
lean_inc_ref(v_out_231_);
v___x_286_ = l_IO_FS_Stream_putStrLn(v_out_231_, v___x_285_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_dec_ref_known(v___x_286_, 1);
v___y_196_ = v_out_231_;
goto v___jp_195_;
}
else
{
lean_dec_ref(v_out_231_);
return v___x_286_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_284_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_282_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_280_;
}
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_277_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_275_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_273_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_271_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_269_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_267_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_265_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_263_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_261_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_259_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_257_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_255_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_253_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_251_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_249_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_247_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_245_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_243_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_241_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_239_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_237_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_235_;
}
}
else
{
lean_dec_ref(v_out_231_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object* v_useStderr_289_, lean_object* v_a_290_){
_start:
{
uint8_t v_useStderr_boxed_291_; lean_object* v_res_292_; 
v_useStderr_boxed_291_ = lean_unbox(v_useStderr_289_);
v_res_292_ = l___private_Lean_Shell_0__Lean_displayHelp(v_useStderr_boxed_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___impl(uint8_t v_x_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_box(v_x_293_);
v___x_295_ = lean_obj_tag_nat(v___x_294_);
lean_dec(v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___impl___boxed(lean_object* v_x_296_){
_start:
{
uint8_t v_x_4__boxed_297_; lean_object* v_res_298_; 
v_x_4__boxed_297_ = lean_unbox(v_x_296_);
v_res_298_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___impl(v_x_4__boxed_297_);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__spec__0(lean_object* v_name_353_, lean_object* v_decl_354_, lean_object* v_ref_355_){
_start:
{
lean_object* v_defValue_357_; lean_object* v_descr_358_; lean_object* v_deprecation_x3f_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_defValue_357_ = lean_ctor_get(v_decl_354_, 0);
v_descr_358_ = lean_ctor_get(v_decl_354_, 1);
v_deprecation_x3f_359_ = lean_ctor_get(v_decl_354_, 2);
lean_inc(v_defValue_357_);
v___x_360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_360_, 0, v_defValue_357_);
lean_inc(v_deprecation_x3f_359_);
lean_inc_ref(v_descr_358_);
lean_inc_n(v_name_353_, 2);
v___x_361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_361_, 0, v_name_353_);
lean_ctor_set(v___x_361_, 1, v_ref_355_);
lean_ctor_set(v___x_361_, 2, v___x_360_);
lean_ctor_set(v___x_361_, 3, v_descr_358_);
lean_ctor_set(v___x_361_, 4, v_deprecation_x3f_359_);
v___x_362_ = lean_register_option(v_name_353_, v___x_361_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_370_; 
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_362_, 0);
lean_dec(v_unused_371_);
v___x_364_ = v___x_362_;
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
else
{
lean_dec(v___x_362_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
lean_inc(v_defValue_357_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_name_353_);
lean_ctor_set(v___x_366_, 1, v_defValue_357_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_368_ = v___x_364_;
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
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_name_353_);
v_a_372_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_362_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_362_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_380_, lean_object* v_decl_381_, lean_object* v_ref_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__spec__0(v_name_380_, v_decl_381_, v_ref_382_);
lean_dec_ref(v_decl_381_);
return v_res_384_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_box(0);
v___x_389_ = lean_internal_get_default_max_memory(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_390_ = lean_box(0);
v___x_391_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_392_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_);
v___x_393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_391_);
lean_ctor_set(v___x_393_, 2, v___x_390_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_417_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_));
v___x_418_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_);
v___x_419_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_));
v___x_420_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__spec__0(v___x_417_, v___x_418_, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2____boxed(lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_();
return v_res_422_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_box(0);
v___x_427_ = lean_internal_get_default_max_heartbeat(v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_428_ = lean_box(0);
v___x_429_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_430_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_);
v___x_431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_429_);
lean_ctor_set(v___x_431_, 2, v___x_428_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_436_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_));
v___x_437_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_);
v___x_438_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_));
v___x_439_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2__spec__0(v___x_436_, v___x_437_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2____boxed(lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_();
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__spec__0(lean_object* v_name_442_, lean_object* v_decl_443_, lean_object* v_ref_444_){
_start:
{
lean_object* v_defValue_446_; lean_object* v_descr_447_; lean_object* v_deprecation_x3f_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_defValue_446_ = lean_ctor_get(v_decl_443_, 0);
v_descr_447_ = lean_ctor_get(v_decl_443_, 1);
v_deprecation_x3f_448_ = lean_ctor_get(v_decl_443_, 2);
v___x_449_ = lean_alloc_ctor(1, 0, 1);
v___x_450_ = lean_unbox(v_defValue_446_);
lean_ctor_set_uint8(v___x_449_, 0, v___x_450_);
lean_inc(v_deprecation_x3f_448_);
lean_inc_ref(v_descr_447_);
lean_inc_n(v_name_442_, 2);
v___x_451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_451_, 0, v_name_442_);
lean_ctor_set(v___x_451_, 1, v_ref_444_);
lean_ctor_set(v___x_451_, 2, v___x_449_);
lean_ctor_set(v___x_451_, 3, v_descr_447_);
lean_ctor_set(v___x_451_, 4, v_deprecation_x3f_448_);
v___x_452_ = lean_register_option(v_name_442_, v___x_451_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_460_; 
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v___x_452_, 0);
lean_dec(v_unused_461_);
v___x_454_ = v___x_452_;
v_isShared_455_ = v_isSharedCheck_460_;
goto v_resetjp_453_;
}
else
{
lean_dec(v___x_452_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_460_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
lean_inc(v_defValue_446_);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v_name_442_);
lean_ctor_set(v___x_456_, 1, v_defValue_446_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_456_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec(v_name_442_);
v_a_462_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_452_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_452_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_470_, lean_object* v_decl_471_, lean_object* v_ref_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__spec__0(v_name_470_, v_decl_471_, v_ref_472_);
lean_dec_ref(v_decl_471_);
return v_res_474_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_box(0);
v___x_479_ = lean_internal_get_default_verbose(v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_480_ = lean_box(0);
v___x_481_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_482_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_);
v___x_483_ = lean_box(v___x_482_);
v___x_484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v___x_481_);
lean_ctor_set(v___x_484_, 2, v___x_480_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_));
v___x_490_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_);
v___x_491_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_));
v___x_492_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2__spec__0(v___x_489_, v___x_490_, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2____boxed(lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_();
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getOptionOverrides___boxed(lean_object* v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = lean_internal_get_option_overrides(v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBelieverTrustLevel___boxed(lean_object* v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_499_){
_start:
{
uint32_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = lean_internal_get_believer_trust_level(v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_499_);
v_r_501_ = lean_box_uint32(v_res_500_);
return v_r_501_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0(void){
_start:
{
lean_object* v___x_502_; uint32_t v___x_503_; 
v___x_502_ = lean_box(0);
v___x_503_ = lean_internal_get_believer_trust_level(v___x_502_);
return v___x_503_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1(void){
_start:
{
uint32_t v___x_504_; uint32_t v___x_505_; uint32_t v___x_506_; 
v___x_504_ = 1;
v___x_505_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0);
v___x_506_ = lean_uint32_add(v___x_505_, v___x_504_);
return v___x_506_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel(void){
_start:
{
uint32_t v___x_507_; 
v___x_507_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1);
return v___x_507_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0(void){
_start:
{
lean_object* v___x_508_; uint32_t v___x_509_; 
v___x_508_ = lean_box(0);
v___x_509_ = lean_internal_get_hardware_concurrency(v___x_508_);
return v___x_509_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads(void){
_start:
{
uint8_t v___x_510_; 
v___x_510_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__40, &l___private_Lean_Shell_0__Lean_displayHelp___closed__40_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40);
if (v___x_510_ == 0)
{
uint32_t v___x_511_; 
v___x_511_ = 0;
return v___x_511_;
}
else
{
uint32_t v___x_512_; 
v___x_512_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0, &l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0);
return v___x_512_;
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_515_; uint32_t v___x_516_; uint32_t v___x_517_; uint8_t v___x_518_; uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_515_ = lean_box(0);
v___x_516_ = l___private_Lean_Shell_0__Lean_defaultNumThreads;
v___x_517_ = l___private_Lean_Shell_0__Lean_defaultTrustLevel;
v___x_518_ = 0;
v___x_519_ = 0;
v___x_520_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__0));
v___x_521_ = l_Lean_Options_empty;
v___x_522_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___x_520_);
lean_ctor_set(v___x_522_, 2, v___x_521_);
lean_ctor_set(v___x_522_, 3, v___x_515_);
lean_ctor_set(v___x_522_, 4, v___x_515_);
lean_ctor_set(v___x_522_, 5, v___x_515_);
lean_ctor_set(v___x_522_, 6, v___x_515_);
lean_ctor_set(v___x_522_, 7, v___x_515_);
lean_ctor_set(v___x_522_, 8, v___x_515_);
lean_ctor_set(v___x_522_, 9, v___x_520_);
lean_ctor_set(v___x_522_, 10, v___x_515_);
lean_ctor_set(v___x_522_, 11, v___x_515_);
lean_ctor_set(v___x_522_, 12, v___x_515_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*13 + 8, v___x_519_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*13 + 9, v___x_518_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*13 + 10, v___x_518_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*13 + 11, v___x_518_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*13 + 12, v___x_518_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*13 + 13, v___x_518_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*13 + 14, v___x_518_);
lean_ctor_set_uint32(v___x_522_, sizeof(void*)*13, v___x_517_);
lean_ctor_set_uint32(v___x_522_, sizeof(void*)*13 + 4, v___x_516_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*13 + 15, v___x_518_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*13 + 16, v___x_518_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*13 + 17, v___x_518_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg(){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1, &l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___boxed(lean_object* v___dummy_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Lean_Shell_0__Lean_mkShellOptions___redArg();
return v_res_526_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0(void){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l___private_Lean_Shell_0__Lean_mkShellOptions___redArg();
return v___x_527_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object* v_x_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0);
return v___x_529_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_run(lean_object* v_opts_530_){
_start:
{
uint8_t v_run_531_; 
v_run_531_ = lean_ctor_get_uint8(v_opts_530_, sizeof(void*)*13 + 17);
lean_dec_ref(v_opts_530_);
return v_run_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getRun___boxed(lean_object* v_opts_532_){
_start:
{
uint8_t v_res_533_; lean_object* v_r_534_; 
v_res_533_ = lean_shell_options_get_run(v_opts_532_);
v_r_534_ = lean_box(v_res_533_);
return v_r_534_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(lean_object* v_opts_535_, lean_object* v_opt_536_){
_start:
{
lean_object* v_name_537_; lean_object* v_defValue_538_; lean_object* v_map_539_; lean_object* v___x_540_; 
v_name_537_ = lean_ctor_get(v_opt_536_, 0);
v_defValue_538_ = lean_ctor_get(v_opt_536_, 1);
v_map_539_ = lean_ctor_get(v_opts_535_, 0);
v___x_540_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_539_, v_name_537_);
if (lean_obj_tag(v___x_540_) == 0)
{
uint8_t v___x_541_; 
v___x_541_ = lean_unbox(v_defValue_538_);
return v___x_541_;
}
else
{
lean_object* v_val_542_; 
v_val_542_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v___x_540_, 1);
if (lean_obj_tag(v_val_542_) == 1)
{
uint8_t v_v_543_; 
v_v_543_ = lean_ctor_get_uint8(v_val_542_, 0);
lean_dec_ref_known(v_val_542_, 0);
return v_v_543_;
}
else
{
uint8_t v___x_544_; 
lean_dec(v_val_542_);
v___x_544_ = lean_unbox(v_defValue_538_);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0___boxed(lean_object* v_opts_545_, lean_object* v_opt_546_){
_start:
{
uint8_t v_res_547_; lean_object* v_r_548_; 
v_res_547_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_opts_545_, v_opt_546_);
lean_dec_ref(v_opt_546_);
lean_dec_ref(v_opts_545_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_profiler(lean_object* v_opts_549_){
_start:
{
lean_object* v_leanOpts_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v_leanOpts_550_ = lean_ctor_get(v_opts_549_, 0);
lean_inc_ref(v_leanOpts_550_);
lean_dec_ref(v_opts_549_);
v___x_551_ = l_Lean_profiler;
v___x_552_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_leanOpts_550_, v___x_551_);
lean_dec_ref(v_leanOpts_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getProfiler___boxed(lean_object* v_opts_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = lean_shell_options_get_profiler(v_opts_553_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT uint32_t lean_shell_options_get_num_threads(lean_object* v_opts_556_){
_start:
{
uint32_t v_numThreads_557_; 
v_numThreads_557_ = lean_ctor_get_uint32(v_opts_556_, sizeof(void*)*13 + 4);
lean_dec_ref(v_opts_556_);
return v_numThreads_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getNumThreads___boxed(lean_object* v_opts_558_){
_start:
{
uint32_t v_res_559_; lean_object* v_r_560_; 
v_res_559_ = lean_shell_options_get_num_threads(v_opts_558_);
v_r_560_ = lean_box_uint32(v_res_559_);
return v_r_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg(lean_object* v_optName_563_, lean_object* v_optArg_x3f_564_){
_start:
{
if (lean_obj_tag(v_optArg_x3f_564_) == 1)
{
lean_object* v_val_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
v_val_566_ = lean_ctor_get(v_optArg_x3f_564_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v_optArg_x3f_564_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v_optArg_x3f_564_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_val_566_);
lean_dec(v_optArg_x3f_564_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 0);
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_val_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_optArg_x3f_564_);
v___x_574_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__0));
v___x_575_ = lean_string_append(v___x_574_, v_optName_563_);
v___x_576_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_577_ = lean_string_append(v___x_575_, v___x_576_);
v___x_578_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg___boxed(lean_object* v_optName_580_, lean_object* v_optArg_x3f_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lean_Shell_0__Lean_checkOptArg(v_optName_580_, v_optArg_x3f_581_);
lean_dec_ref(v_optName_580_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(lean_object* v_o_587_, lean_object* v_k_588_, lean_object* v_v_589_){
_start:
{
lean_object* v_map_590_; uint8_t v_hasTrace_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_605_; 
v_map_590_ = lean_ctor_get(v_o_587_, 0);
v_hasTrace_591_ = lean_ctor_get_uint8(v_o_587_, sizeof(void*)*1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_o_587_);
if (v_isSharedCheck_605_ == 0)
{
v___x_593_ = v_o_587_;
v_isShared_594_ = v_isSharedCheck_605_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_map_590_);
lean_dec(v_o_587_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_605_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v_v_589_);
lean_inc(v_k_588_);
v___x_596_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_588_, v___x_595_, v_map_590_);
if (v_hasTrace_591_ == 0)
{
lean_object* v___x_597_; uint8_t v___x_598_; lean_object* v___x_600_; 
v___x_597_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_598_ = l_Lean_Name_isPrefixOf(v___x_597_, v_k_588_);
lean_dec(v_k_588_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_596_);
v___x_600_ = v___x_593_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_596_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_ctor_set_uint8(v___x_600_, sizeof(void*)*1, v___x_598_);
return v___x_600_;
}
}
else
{
lean_object* v___x_603_; 
lean_dec(v_k_588_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_596_);
v___x_603_ = v___x_593_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_596_);
lean_ctor_set_uint8(v_reuseFailAlloc_604_, sizeof(void*)*1, v_hasTrace_591_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(lean_object* v___x_606_, lean_object* v_arg_607_, lean_object* v_a_608_, lean_object* v_b_609_){
_start:
{
uint8_t v_decide_610_; 
v_decide_610_ = lean_nat_dec_eq(v_a_608_, v___x_606_);
if (v_decide_610_ == 0)
{
uint32_t v___x_611_; uint32_t v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_string_utf8_get_fast(v_arg_607_, v_a_608_);
v___x_612_ = 61;
v___x_613_ = lean_uint32_dec_eq(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_box(0);
v___x_615_ = lean_string_utf8_next_fast(v_arg_607_, v_a_608_);
lean_dec(v_a_608_);
v_a_608_ = v___x_615_;
v_b_609_ = v___x_614_;
goto _start;
}
else
{
lean_object* v___x_617_; 
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v_a_608_);
return v___x_617_;
}
}
else
{
lean_dec(v_a_608_);
lean_inc(v_b_609_);
return v_b_609_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(lean_object* v___x_618_, lean_object* v_arg_619_, lean_object* v_a_620_, lean_object* v_b_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_618_, v_arg_619_, v_a_620_, v_b_621_);
lean_dec(v_b_621_);
lean_dec_ref(v_arg_619_);
lean_dec(v___x_618_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption(lean_object* v_opts_626_, lean_object* v_arg_627_){
_start:
{
lean_object* v___y_630_; lean_object* v_searcher_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_searcher_661_ = lean_unsigned_to_nat(0u);
v___x_662_ = lean_string_utf8_byte_size(v_arg_627_);
v___x_663_ = lean_box(0);
v___x_664_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_662_, v_arg_627_, v_searcher_661_, v___x_663_);
if (lean_obj_tag(v___x_664_) == 0)
{
v___y_630_ = v___x_662_;
goto v___jp_629_;
}
else
{
lean_object* v_val_665_; 
v_val_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_val_665_);
lean_dec_ref_known(v___x_664_, 1);
v___y_630_ = v_val_665_;
goto v___jp_629_;
}
v___jp_629_:
{
lean_object* v___x_631_; uint8_t v_decide_632_; 
v___x_631_ = lean_string_utf8_byte_size(v_arg_627_);
v_decide_632_ = lean_nat_dec_eq(v___y_630_, v___x_631_);
if (v_decide_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v_name_635_; lean_object* v___x_636_; lean_object* v_val_637_; lean_object* v___x_638_; 
v___x_633_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_630_);
lean_inc_ref(v_arg_627_);
v___x_634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_634_, 0, v_arg_627_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
lean_ctor_set(v___x_634_, 2, v___y_630_);
v_name_635_ = l_String_Slice_toName(v___x_634_);
lean_dec_ref_known(v___x_634_, 3);
v___x_636_ = lean_string_utf8_next_fast(v_arg_627_, v___y_630_);
lean_dec(v___y_630_);
v_val_637_ = lean_string_utf8_extract_fast(v_arg_627_, v___x_636_, v___x_631_);
lean_dec_ref(v_arg_627_);
v___x_638_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_650_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_650_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_639_, v_name_635_);
lean_dec(v_a_639_);
if (lean_obj_tag(v___x_643_) == 1)
{
lean_object* v_val_644_; lean_object* v___x_645_; 
lean_del_object(v___x_641_);
v_val_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v___x_643_, 1);
v___x_645_ = l_Lean_Language_Lean_setOption(v_opts_626_, v_val_644_, v_name_635_, v_val_637_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_648_; 
lean_dec(v___x_643_);
v___x_646_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(v_opts_626_, v_name_635_, v_val_637_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_646_);
v___x_648_ = v___x_641_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v_val_637_);
lean_dec(v_name_635_);
lean_dec_ref(v_opts_626_);
v_a_651_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_638_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_638_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; 
lean_dec(v___y_630_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_opts_626_);
v___x_659_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_setConfigOption___closed__1));
v___x_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___boxed(lean_object* v_opts_666_, lean_object* v_arg_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_opts_666_, v_arg_667_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v_arg_672_, lean_object* v_inst_673_, lean_object* v_R_674_, lean_object* v_a_675_, lean_object* v_b_676_, lean_object* v_c_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_670_, v_arg_672_, v_a_675_, v_b_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object* v___x_679_, lean_object* v___x_680_, lean_object* v_arg_681_, lean_object* v_inst_682_, lean_object* v_R_683_, lean_object* v_a_684_, lean_object* v_b_685_, lean_object* v_c_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(v___x_679_, v___x_680_, v_arg_681_, v_inst_682_, v_R_683_, v_a_684_, v_b_685_, v_c_686_);
lean_dec(v_b_685_);
lean_dec_ref(v_arg_681_);
lean_dec_ref(v___x_680_);
lean_dec(v___x_679_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(lean_object* v_msg_689_){
_start:
{
lean_object* v___f_691_; lean_object* v___x_692_; 
v___f_691_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_692_ = l_IO_eprint___redArg(v___f_691_, v_msg_689_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
else
{
lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_708_; 
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v___x_692_, 0);
lean_dec(v_unused_709_);
v___x_702_ = v___x_692_;
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
else
{
lean_dec(v___x_692_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_box(0);
if (v_isShared_703_ == 0)
{
lean_ctor_set_tag(v___x_702_, 0);
lean_ctor_set(v___x_702_, 0, v___x_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(lean_object* v_msg_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(v_msg_710_);
return v_res_712_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_715_; lean_object* v___x_716_; 
v___x_715_ = 1;
v___x_716_ = lean_box_uint32(v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(lean_object* v_x_717_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = lean_apply_1(v_x_717_, lean_box(0));
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_740_; lean_object* v___f_741_; lean_object* v___x_742_; 
v_a_735_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_726_, 1);
v___x_740_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_741_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_742_ = l_IO_eprint___redArg(v___f_741_, v___x_740_);
lean_dec_ref(v___x_742_);
goto v___jp_736_;
v___jp_736_:
{
lean_object* v___x_737_; lean_object* v___f_738_; lean_object* v___x_739_; 
v___x_737_ = lean_io_error_to_string(v_a_735_);
v___f_738_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_739_ = l_IO_eprint___redArg(v___f_738_, v___x_737_);
lean_dec_ref(v___x_739_);
goto v___jp_722_;
}
}
v___jp_719_:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
v___jp_722_:
{
lean_object* v___x_723_; lean_object* v___f_724_; lean_object* v___x_725_; 
v___x_723_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_724_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_725_ = l_IO_eprint___redArg(v___f_724_, v___x_723_);
lean_dec_ref(v___x_725_);
goto v___jp_719_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed(lean_object* v_x_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(v_x_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(lean_object* v_00_u03b1_746_, lean_object* v_x_747_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_apply_1(v_x_747_, lean_box(0));
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_770_; lean_object* v___f_771_; lean_object* v___x_772_; 
v_a_765_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_756_, 1);
v___x_770_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_771_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_772_ = l_IO_eprint___redArg(v___f_771_, v___x_770_);
lean_dec_ref(v___x_772_);
goto v___jp_766_;
v___jp_766_:
{
lean_object* v___x_767_; lean_object* v___f_768_; lean_object* v___x_769_; 
v___x_767_ = lean_io_error_to_string(v_a_765_);
v___f_768_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_769_ = l_IO_eprint___redArg(v___f_768_, v___x_767_);
lean_dec_ref(v___x_769_);
goto v___jp_752_;
}
}
v___jp_749_:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
v___jp_752_:
{
lean_object* v___x_753_; lean_object* v___f_754_; lean_object* v___x_755_; 
v___x_753_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_754_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_755_ = l_IO_eprint___redArg(v___f_754_, v___x_753_);
lean_dec_ref(v___x_755_);
goto v___jp_749_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___boxed(lean_object* v_00_u03b1_773_, lean_object* v_x_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(v_00_u03b1_773_, v_x_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(lean_object* v_opt_779_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___f_788_; lean_object* v___x_789_; 
v___x_784_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0));
v___x_785_ = lean_string_append(v___x_784_, v_opt_779_);
v___x_786_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_787_ = lean_string_append(v___x_785_, v___x_786_);
v___f_788_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_789_ = l_IO_eprint___redArg(v___f_788_, v___x_787_);
lean_dec_ref(v___x_789_);
goto v___jp_781_;
v___jp_781_:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___boxed(lean_object* v_opt_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(v_opt_790_);
lean_dec_ref(v_opt_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(lean_object* v_opt_795_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___f_804_; lean_object* v___x_805_; 
v___x_800_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0));
v___x_801_ = lean_string_append(v___x_800_, v_opt_795_);
v___x_802_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1));
v___x_803_ = lean_string_append(v___x_801_, v___x_802_);
v___f_804_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_805_ = l_IO_eprint___redArg(v___f_804_, v___x_803_);
lean_dec_ref(v___x_805_);
goto v___jp_797_;
v___jp_797_:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___boxed(lean_object* v_opt_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(v_opt_806_);
lean_dec_ref(v_opt_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(lean_object* v_s_809_){
_start:
{
lean_object* v___x_811_; lean_object* v_putStr_812_; lean_object* v___x_813_; 
v___x_811_ = lean_get_stderr();
v_putStr_812_ = lean_ctor_get(v___x_811_, 4);
lean_inc_ref(v_putStr_812_);
lean_dec_ref(v___x_811_);
v___x_813_ = lean_apply_2(v_putStr_812_, v_s_809_, lean_box(0));
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0___boxed(lean_object* v_s_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v_s_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(lean_object* v_s_817_){
_start:
{
lean_object* v___x_819_; lean_object* v_putStr_820_; lean_object* v___x_821_; 
v___x_819_ = lean_get_stdout();
v_putStr_820_ = lean_ctor_get(v___x_819_, 4);
lean_inc_ref(v_putStr_820_);
lean_dec_ref(v___x_819_);
v___x_821_ = lean_apply_2(v_putStr_820_, v_s_817_, lean_box(0));
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5___boxed(lean_object* v_s_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v_s_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object* v_s_825_){
_start:
{
uint32_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = 10;
v___x_828_ = lean_string_push(v_s_825_, v___x_827_);
v___x_829_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3___boxed(lean_object* v_s_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_s_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(lean_object* v_o_833_, lean_object* v_k_834_, uint8_t v_v_835_){
_start:
{
lean_object* v_map_836_; uint8_t v_hasTrace_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_851_; 
v_map_836_ = lean_ctor_get(v_o_833_, 0);
v_hasTrace_837_ = lean_ctor_get_uint8(v_o_833_, sizeof(void*)*1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_o_833_);
if (v_isSharedCheck_851_ == 0)
{
v___x_839_ = v_o_833_;
v_isShared_840_ = v_isSharedCheck_851_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_map_836_);
lean_dec(v_o_833_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_851_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_841_, 0, v_v_835_);
lean_inc(v_k_834_);
v___x_842_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_834_, v___x_841_, v_map_836_);
if (v_hasTrace_837_ == 0)
{
lean_object* v___x_843_; uint8_t v___x_844_; lean_object* v___x_846_; 
v___x_843_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_844_ = l_Lean_Name_isPrefixOf(v___x_843_, v_k_834_);
lean_dec(v_k_834_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_842_);
v___x_846_ = v___x_839_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_842_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*1, v___x_844_);
return v___x_846_;
}
}
else
{
lean_object* v___x_849_; 
lean_dec(v_k_834_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_842_);
v___x_849_ = v___x_839_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_842_);
lean_ctor_set_uint8(v_reuseFailAlloc_850_, sizeof(void*)*1, v_hasTrace_837_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1___boxed(lean_object* v_o_852_, lean_object* v_k_853_, lean_object* v_v_854_){
_start:
{
uint8_t v_v_boxed_855_; lean_object* v_res_856_; 
v_v_boxed_855_ = lean_unbox(v_v_854_);
v_res_856_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_o_852_, v_k_853_, v_v_boxed_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object* v_opts_857_, lean_object* v_opt_858_, uint8_t v_val_859_){
_start:
{
lean_object* v_name_860_; lean_object* v___x_861_; 
v_name_860_ = lean_ctor_get(v_opt_858_, 0);
lean_inc(v_name_860_);
lean_dec_ref(v_opt_858_);
v___x_861_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_opts_857_, v_name_860_, v_val_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object* v_opts_862_, lean_object* v_opt_863_, lean_object* v_val_864_){
_start:
{
uint8_t v_val_boxed_865_; lean_object* v_res_866_; 
v_val_boxed_865_ = lean_unbox(v_val_864_);
v_res_866_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_opts_862_, v_opt_863_, v_val_boxed_865_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(lean_object* v_o_867_, lean_object* v_k_868_, lean_object* v_v_869_){
_start:
{
lean_object* v_map_870_; uint8_t v_hasTrace_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_885_; 
v_map_870_ = lean_ctor_get(v_o_867_, 0);
v_hasTrace_871_ = lean_ctor_get_uint8(v_o_867_, sizeof(void*)*1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_o_867_);
if (v_isSharedCheck_885_ == 0)
{
v___x_873_ = v_o_867_;
v_isShared_874_ = v_isSharedCheck_885_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_map_870_);
lean_dec(v_o_867_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_885_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_875_, 0, v_v_869_);
lean_inc(v_k_868_);
v___x_876_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_868_, v___x_875_, v_map_870_);
if (v_hasTrace_871_ == 0)
{
lean_object* v___x_877_; uint8_t v___x_878_; lean_object* v___x_880_; 
v___x_877_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_878_ = l_Lean_Name_isPrefixOf(v___x_877_, v_k_868_);
lean_dec(v_k_868_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_876_);
v___x_880_ = v___x_873_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_876_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*1, v___x_878_);
return v___x_880_;
}
}
else
{
lean_object* v___x_883_; 
lean_dec(v_k_868_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_876_);
v___x_883_ = v___x_873_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_884_, sizeof(void*)*1, v_hasTrace_871_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object* v_opts_886_, lean_object* v_opt_887_, lean_object* v_val_888_){
_start:
{
lean_object* v_name_889_; lean_object* v___x_890_; 
v_name_889_ = lean_ctor_get(v_opt_887_, 0);
lean_inc(v_name_889_);
lean_dec_ref(v_opt_887_);
v___x_890_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(v_opts_886_, v_name_889_, v_val_888_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = l_System_Platform_numBits;
v___x_920_ = lean_unsigned_to_nat(2u);
v___x_921_ = lean_nat_pow(v___x_920_, v___x_919_);
return v___x_921_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1(void){
_start:
{
uint32_t v___x_931_; lean_object* v___x_932_; 
v___x_931_ = 0;
v___x_932_ = lean_box_uint32(v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object* v_opts_933_, uint32_t v_opt_934_, lean_object* v_optArg_x3f_935_){
_start:
{
lean_object* v___y_1043_; lean_object* v___y_1101_; uint32_t v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = 101;
v___x_1156_ = lean_uint32_dec_eq(v_opt_934_, v___x_1155_);
if (v___x_1156_ == 0)
{
uint32_t v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = 106;
v___x_1158_ = lean_uint32_dec_eq(v_opt_934_, v___x_1157_);
if (v___x_1158_ == 0)
{
uint32_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = 118;
v___x_1160_ = lean_uint32_dec_eq(v_opt_934_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint32_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = 86;
v___x_1162_ = lean_uint32_dec_eq(v_opt_934_, v___x_1161_);
if (v___x_1162_ == 0)
{
uint32_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = 103;
v___x_1164_ = lean_uint32_dec_eq(v_opt_934_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint32_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = 104;
v___x_1166_ = lean_uint32_dec_eq(v_opt_934_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint32_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = 102;
v___x_1168_ = lean_uint32_dec_eq(v_opt_934_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint32_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = 99;
v___x_1170_ = lean_uint32_dec_eq(v_opt_934_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint32_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = 98;
v___x_1172_ = lean_uint32_dec_eq(v_opt_934_, v___x_1171_);
if (v___x_1172_ == 0)
{
uint32_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 115;
v___x_1174_ = lean_uint32_dec_eq(v_opt_934_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint32_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = 73;
v___x_1176_ = lean_uint32_dec_eq(v_opt_934_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint32_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = 114;
v___x_1178_ = lean_uint32_dec_eq(v_opt_934_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint32_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = 111;
v___x_1180_ = lean_uint32_dec_eq(v_opt_934_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint32_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = 105;
v___x_1182_ = lean_uint32_dec_eq(v_opt_934_, v___x_1181_);
if (v___x_1182_ == 0)
{
uint32_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = 82;
v___x_1184_ = lean_uint32_dec_eq(v_opt_934_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint32_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = 77;
v___x_1186_ = lean_uint32_dec_eq(v_opt_934_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint32_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = 84;
v___x_1188_ = lean_uint32_dec_eq(v_opt_934_, v___x_1187_);
if (v___x_1188_ == 0)
{
uint32_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = 116;
v___x_1190_ = lean_uint32_dec_eq(v_opt_934_, v___x_1189_);
if (v___x_1190_ == 0)
{
uint32_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = 113;
v___x_1192_ = lean_uint32_dec_eq(v_opt_934_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint32_t v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = 100;
v___x_1194_ = lean_uint32_dec_eq(v_opt_934_, v___x_1193_);
if (v___x_1194_ == 0)
{
uint32_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = 79;
v___x_1196_ = lean_uint32_dec_eq(v_opt_934_, v___x_1195_);
if (v___x_1196_ == 0)
{
uint32_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = 78;
v___x_1198_ = lean_uint32_dec_eq(v_opt_934_, v___x_1197_);
if (v___x_1198_ == 0)
{
uint32_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 74;
v___x_1200_ = lean_uint32_dec_eq(v_opt_934_, v___x_1199_);
if (v___x_1200_ == 0)
{
uint32_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = 97;
v___x_1202_ = lean_uint32_dec_eq(v_opt_934_, v___x_1201_);
if (v___x_1202_ == 0)
{
uint32_t v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = 120;
v___x_1204_ = lean_uint32_dec_eq(v_opt_934_, v___x_1203_);
if (v___x_1204_ == 0)
{
uint32_t v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = 76;
v___x_1206_ = lean_uint32_dec_eq(v_opt_934_, v___x_1205_);
if (v___x_1206_ == 0)
{
uint32_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = 68;
v___x_1208_ = lean_uint32_dec_eq(v_opt_934_, v___x_1207_);
if (v___x_1208_ == 0)
{
uint32_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = 83;
v___x_1210_ = lean_uint32_dec_eq(v_opt_934_, v___x_1209_);
if (v___x_1210_ == 0)
{
uint32_t v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = 87;
v___x_1212_ = lean_uint32_dec_eq(v_opt_934_, v___x_1211_);
if (v___x_1212_ == 0)
{
uint32_t v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = 80;
v___x_1214_ = lean_uint32_dec_eq(v_opt_934_, v___x_1213_);
if (v___x_1214_ == 0)
{
uint32_t v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = 66;
v___x_1216_ = lean_uint32_dec_eq(v_opt_934_, v___x_1215_);
if (v___x_1216_ == 0)
{
uint32_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = 112;
v___x_1218_ = lean_uint32_dec_eq(v_opt_934_, v___x_1217_);
if (v___x_1218_ == 0)
{
uint32_t v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = 108;
v___x_1220_ = lean_uint32_dec_eq(v_opt_934_, v___x_1219_);
if (v___x_1220_ == 0)
{
uint32_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = 117;
v___x_1222_ = lean_uint32_dec_eq(v_opt_934_, v___x_1221_);
if (v___x_1222_ == 0)
{
uint32_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = 69;
v___x_1224_ = lean_uint32_dec_eq(v_opt_934_, v___x_1223_);
if (v___x_1224_ == 0)
{
uint32_t v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = 89;
v___x_1226_ = lean_uint32_dec_eq(v_opt_934_, v___x_1225_);
if (v___x_1226_ == 0)
{
uint32_t v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = 90;
v___x_1228_ = lean_uint32_dec_eq(v_opt_934_, v___x_1227_);
if (v___x_1228_ == 0)
{
uint32_t v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = 72;
v___x_1230_ = lean_uint32_dec_eq(v_opt_934_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_dec(v_optArg_x3f_935_);
lean_dec_ref(v_opts_933_);
goto v___jp_1061_;
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1232_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1231_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1273_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1273_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1273_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_leanOpts_1237_; lean_object* v_forwardedArgs_1238_; uint8_t v_component_1239_; uint8_t v_printPrefix_1240_; uint8_t v_printLibDir_1241_; uint8_t v_useStdin_1242_; uint8_t v_onlyDeps_1243_; uint8_t v_onlySrcDeps_1244_; uint8_t v_depsJson_1245_; lean_object* v_opts_1246_; uint32_t v_trustLevel_1247_; uint32_t v_numThreads_1248_; lean_object* v_rootDir_x3f_1249_; lean_object* v_setupFileName_x3f_1250_; lean_object* v_oleanFileName_x3f_1251_; lean_object* v_ileanFileName_x3f_1252_; lean_object* v_cFileName_x3f_1253_; lean_object* v_bcFileName_x3f_1254_; uint8_t v_jsonOutput_1255_; lean_object* v_errorOnKinds_1256_; uint8_t v_printStats_1257_; uint8_t v_run_1258_; lean_object* v_incrSaveFileName_x3f_1259_; lean_object* v_incrLoadFileName_x3f_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1271_; 
v_leanOpts_1237_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1238_ = lean_ctor_get(v_opts_933_, 1);
v_component_1239_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1240_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1241_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1242_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1243_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1244_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1245_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1246_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1247_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1248_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1249_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1250_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1251_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1252_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1253_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1254_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1255_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1256_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1257_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1258_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1259_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1260_ = lean_ctor_get(v_opts_933_, 11);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v_opts_933_, 12);
lean_dec(v_unused_1272_);
v___x_1262_ = v_opts_933_;
v_isShared_1263_ = v_isSharedCheck_1271_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_incrLoadFileName_x3f_1260_);
lean_inc(v_incrSaveFileName_x3f_1259_);
lean_inc(v_errorOnKinds_1256_);
lean_inc(v_bcFileName_x3f_1254_);
lean_inc(v_cFileName_x3f_1253_);
lean_inc(v_ileanFileName_x3f_1252_);
lean_inc(v_oleanFileName_x3f_1251_);
lean_inc(v_setupFileName_x3f_1250_);
lean_inc(v_rootDir_x3f_1249_);
lean_inc(v_opts_1246_);
lean_inc(v_forwardedArgs_1238_);
lean_inc(v_leanOpts_1237_);
lean_dec(v_opts_933_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1271_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_a_1233_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 12, v___x_1264_);
v___x_1266_ = v___x_1262_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_leanOpts_1237_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_forwardedArgs_1238_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_opts_1246_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_rootDir_x3f_1249_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_setupFileName_x3f_1250_);
lean_ctor_set(v_reuseFailAlloc_1270_, 5, v_oleanFileName_x3f_1251_);
lean_ctor_set(v_reuseFailAlloc_1270_, 6, v_ileanFileName_x3f_1252_);
lean_ctor_set(v_reuseFailAlloc_1270_, 7, v_cFileName_x3f_1253_);
lean_ctor_set(v_reuseFailAlloc_1270_, 8, v_bcFileName_x3f_1254_);
lean_ctor_set(v_reuseFailAlloc_1270_, 9, v_errorOnKinds_1256_);
lean_ctor_set(v_reuseFailAlloc_1270_, 10, v_incrSaveFileName_x3f_1259_);
lean_ctor_set(v_reuseFailAlloc_1270_, 11, v_incrLoadFileName_x3f_1260_);
lean_ctor_set(v_reuseFailAlloc_1270_, 12, v___x_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 8, v_component_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 9, v_printPrefix_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 10, v_printLibDir_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 11, v_useStdin_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 12, v_onlyDeps_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 13, v_onlySrcDeps_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 14, v_depsJson_1245_);
lean_ctor_set_uint32(v_reuseFailAlloc_1270_, sizeof(void*)*13, v_trustLevel_1247_);
lean_ctor_set_uint32(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 4, v_numThreads_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 15, v_jsonOutput_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 16, v_printStats_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 17, v_run_1258_);
v___x_1266_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1268_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1266_);
v___x_1268_ = v___x_1235_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_dec_ref(v_opts_933_);
v_a_1274_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___x_1232_, 1);
v___x_1278_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1279_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1278_);
lean_dec_ref(v___x_1279_);
goto v___jp_1275_;
v___jp_1275_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_io_error_to_string(v_a_1274_);
v___x_1277_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1276_);
lean_dec_ref(v___x_1277_);
goto v___jp_1033_;
}
}
}
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1281_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1280_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1322_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1322_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1322_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_leanOpts_1286_; lean_object* v_forwardedArgs_1287_; uint8_t v_component_1288_; uint8_t v_printPrefix_1289_; uint8_t v_printLibDir_1290_; uint8_t v_useStdin_1291_; uint8_t v_onlyDeps_1292_; uint8_t v_onlySrcDeps_1293_; uint8_t v_depsJson_1294_; lean_object* v_opts_1295_; uint32_t v_trustLevel_1296_; uint32_t v_numThreads_1297_; lean_object* v_rootDir_x3f_1298_; lean_object* v_setupFileName_x3f_1299_; lean_object* v_oleanFileName_x3f_1300_; lean_object* v_ileanFileName_x3f_1301_; lean_object* v_cFileName_x3f_1302_; lean_object* v_bcFileName_x3f_1303_; uint8_t v_jsonOutput_1304_; lean_object* v_errorOnKinds_1305_; uint8_t v_printStats_1306_; uint8_t v_run_1307_; lean_object* v_incrSaveFileName_x3f_1308_; lean_object* v_incrHeaderSaveFileName_x3f_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1320_; 
v_leanOpts_1286_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1287_ = lean_ctor_get(v_opts_933_, 1);
v_component_1288_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1289_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1290_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1291_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1292_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1293_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1294_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1295_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1296_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1297_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1298_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1299_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1300_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1301_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1302_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1303_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1304_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1305_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1306_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1307_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1308_ = lean_ctor_get(v_opts_933_, 10);
v_incrHeaderSaveFileName_x3f_1309_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v_opts_933_, 11);
lean_dec(v_unused_1321_);
v___x_1311_ = v_opts_933_;
v_isShared_1312_ = v_isSharedCheck_1320_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1309_);
lean_inc(v_incrSaveFileName_x3f_1308_);
lean_inc(v_errorOnKinds_1305_);
lean_inc(v_bcFileName_x3f_1303_);
lean_inc(v_cFileName_x3f_1302_);
lean_inc(v_ileanFileName_x3f_1301_);
lean_inc(v_oleanFileName_x3f_1300_);
lean_inc(v_setupFileName_x3f_1299_);
lean_inc(v_rootDir_x3f_1298_);
lean_inc(v_opts_1295_);
lean_inc(v_forwardedArgs_1287_);
lean_inc(v_leanOpts_1286_);
lean_dec(v_opts_933_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1320_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1313_, 0, v_a_1282_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 11, v___x_1313_);
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_leanOpts_1286_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_forwardedArgs_1287_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_opts_1295_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_rootDir_x3f_1298_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_setupFileName_x3f_1299_);
lean_ctor_set(v_reuseFailAlloc_1319_, 5, v_oleanFileName_x3f_1300_);
lean_ctor_set(v_reuseFailAlloc_1319_, 6, v_ileanFileName_x3f_1301_);
lean_ctor_set(v_reuseFailAlloc_1319_, 7, v_cFileName_x3f_1302_);
lean_ctor_set(v_reuseFailAlloc_1319_, 8, v_bcFileName_x3f_1303_);
lean_ctor_set(v_reuseFailAlloc_1319_, 9, v_errorOnKinds_1305_);
lean_ctor_set(v_reuseFailAlloc_1319_, 10, v_incrSaveFileName_x3f_1308_);
lean_ctor_set(v_reuseFailAlloc_1319_, 11, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1319_, 12, v_incrHeaderSaveFileName_x3f_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*13 + 8, v_component_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*13 + 9, v_printPrefix_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*13 + 10, v_printLibDir_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*13 + 11, v_useStdin_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*13 + 12, v_onlyDeps_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*13 + 13, v_onlySrcDeps_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*13 + 14, v_depsJson_1294_);
lean_ctor_set_uint32(v_reuseFailAlloc_1319_, sizeof(void*)*13, v_trustLevel_1296_);
lean_ctor_set_uint32(v_reuseFailAlloc_1319_, sizeof(void*)*13 + 4, v_numThreads_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*13 + 15, v_jsonOutput_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*13 + 16, v_printStats_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*13 + 17, v_run_1307_);
v___x_1315_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1317_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1315_);
v___x_1317_ = v___x_1284_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec_ref(v_opts_933_);
v_a_1323_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1281_, 1);
v___x_1327_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1328_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1327_);
lean_dec_ref(v___x_1328_);
goto v___jp_1324_;
v___jp_1324_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_io_error_to_string(v_a_1323_);
v___x_1326_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1325_);
lean_dec_ref(v___x_1326_);
goto v___jp_1067_;
}
}
}
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1330_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1329_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1371_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1371_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1371_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_leanOpts_1335_; lean_object* v_forwardedArgs_1336_; uint8_t v_component_1337_; uint8_t v_printPrefix_1338_; uint8_t v_printLibDir_1339_; uint8_t v_useStdin_1340_; uint8_t v_onlyDeps_1341_; uint8_t v_onlySrcDeps_1342_; uint8_t v_depsJson_1343_; lean_object* v_opts_1344_; uint32_t v_trustLevel_1345_; uint32_t v_numThreads_1346_; lean_object* v_rootDir_x3f_1347_; lean_object* v_setupFileName_x3f_1348_; lean_object* v_oleanFileName_x3f_1349_; lean_object* v_ileanFileName_x3f_1350_; lean_object* v_cFileName_x3f_1351_; lean_object* v_bcFileName_x3f_1352_; uint8_t v_jsonOutput_1353_; lean_object* v_errorOnKinds_1354_; uint8_t v_printStats_1355_; uint8_t v_run_1356_; lean_object* v_incrLoadFileName_x3f_1357_; lean_object* v_incrHeaderSaveFileName_x3f_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1369_; 
v_leanOpts_1335_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1336_ = lean_ctor_get(v_opts_933_, 1);
v_component_1337_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1338_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1339_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1340_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1341_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1342_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1343_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1344_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1345_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1346_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1347_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1348_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1349_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1350_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1351_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1352_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1353_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1354_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1355_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1356_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrLoadFileName_x3f_1357_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1358_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; 
v_unused_1370_ = lean_ctor_get(v_opts_933_, 10);
lean_dec(v_unused_1370_);
v___x_1360_ = v_opts_933_;
v_isShared_1361_ = v_isSharedCheck_1369_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1358_);
lean_inc(v_incrLoadFileName_x3f_1357_);
lean_inc(v_errorOnKinds_1354_);
lean_inc(v_bcFileName_x3f_1352_);
lean_inc(v_cFileName_x3f_1351_);
lean_inc(v_ileanFileName_x3f_1350_);
lean_inc(v_oleanFileName_x3f_1349_);
lean_inc(v_setupFileName_x3f_1348_);
lean_inc(v_rootDir_x3f_1347_);
lean_inc(v_opts_1344_);
lean_inc(v_forwardedArgs_1336_);
lean_inc(v_leanOpts_1335_);
lean_dec(v_opts_933_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1369_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_a_1331_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 10, v___x_1362_);
v___x_1364_ = v___x_1360_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_leanOpts_1335_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_forwardedArgs_1336_);
lean_ctor_set(v_reuseFailAlloc_1368_, 2, v_opts_1344_);
lean_ctor_set(v_reuseFailAlloc_1368_, 3, v_rootDir_x3f_1347_);
lean_ctor_set(v_reuseFailAlloc_1368_, 4, v_setupFileName_x3f_1348_);
lean_ctor_set(v_reuseFailAlloc_1368_, 5, v_oleanFileName_x3f_1349_);
lean_ctor_set(v_reuseFailAlloc_1368_, 6, v_ileanFileName_x3f_1350_);
lean_ctor_set(v_reuseFailAlloc_1368_, 7, v_cFileName_x3f_1351_);
lean_ctor_set(v_reuseFailAlloc_1368_, 8, v_bcFileName_x3f_1352_);
lean_ctor_set(v_reuseFailAlloc_1368_, 9, v_errorOnKinds_1354_);
lean_ctor_set(v_reuseFailAlloc_1368_, 10, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1368_, 11, v_incrLoadFileName_x3f_1357_);
lean_ctor_set(v_reuseFailAlloc_1368_, 12, v_incrHeaderSaveFileName_x3f_1358_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 8, v_component_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 9, v_printPrefix_1338_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 10, v_printLibDir_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 11, v_useStdin_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 12, v_onlyDeps_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 13, v_onlySrcDeps_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 14, v_depsJson_1343_);
lean_ctor_set_uint32(v_reuseFailAlloc_1368_, sizeof(void*)*13, v_trustLevel_1345_);
lean_ctor_set_uint32(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 4, v_numThreads_1346_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 15, v_jsonOutput_1353_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 16, v_printStats_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 17, v_run_1356_);
v___x_1364_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1366_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1364_);
v___x_1366_ = v___x_1333_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec_ref(v_opts_933_);
v_a_1372_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1330_, 1);
v___x_1376_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1377_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1376_);
lean_dec_ref(v___x_1377_);
goto v___jp_1373_;
v___jp_1373_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_io_error_to_string(v_a_1372_);
v___x_1375_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1374_);
lean_dec_ref(v___x_1375_);
goto v___jp_1027_;
}
}
}
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1379_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1378_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1421_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1421_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1421_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_leanOpts_1384_; lean_object* v_forwardedArgs_1385_; uint8_t v_component_1386_; uint8_t v_printPrefix_1387_; uint8_t v_printLibDir_1388_; uint8_t v_useStdin_1389_; uint8_t v_onlyDeps_1390_; uint8_t v_onlySrcDeps_1391_; uint8_t v_depsJson_1392_; lean_object* v_opts_1393_; uint32_t v_trustLevel_1394_; uint32_t v_numThreads_1395_; lean_object* v_rootDir_x3f_1396_; lean_object* v_setupFileName_x3f_1397_; lean_object* v_oleanFileName_x3f_1398_; lean_object* v_ileanFileName_x3f_1399_; lean_object* v_cFileName_x3f_1400_; lean_object* v_bcFileName_x3f_1401_; uint8_t v_jsonOutput_1402_; lean_object* v_errorOnKinds_1403_; uint8_t v_printStats_1404_; uint8_t v_run_1405_; lean_object* v_incrSaveFileName_x3f_1406_; lean_object* v_incrLoadFileName_x3f_1407_; lean_object* v_incrHeaderSaveFileName_x3f_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1420_; 
v_leanOpts_1384_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1385_ = lean_ctor_get(v_opts_933_, 1);
v_component_1386_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1387_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1388_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1389_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1390_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1391_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1392_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1393_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1394_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1395_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1396_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1397_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1398_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1399_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1400_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1401_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1402_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1403_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1404_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1405_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1406_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1407_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1408_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1410_ = v_opts_933_;
v_isShared_1411_ = v_isSharedCheck_1420_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1408_);
lean_inc(v_incrLoadFileName_x3f_1407_);
lean_inc(v_incrSaveFileName_x3f_1406_);
lean_inc(v_errorOnKinds_1403_);
lean_inc(v_bcFileName_x3f_1401_);
lean_inc(v_cFileName_x3f_1400_);
lean_inc(v_ileanFileName_x3f_1399_);
lean_inc(v_oleanFileName_x3f_1398_);
lean_inc(v_setupFileName_x3f_1397_);
lean_inc(v_rootDir_x3f_1396_);
lean_inc(v_opts_1393_);
lean_inc(v_forwardedArgs_1385_);
lean_inc(v_leanOpts_1384_);
lean_dec(v_opts_933_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1420_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1412_ = l_String_toName(v_a_1380_);
v___x_1413_ = lean_array_push(v_errorOnKinds_1403_, v___x_1412_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 9, v___x_1413_);
v___x_1415_ = v___x_1410_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_leanOpts_1384_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_forwardedArgs_1385_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_opts_1393_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_rootDir_x3f_1396_);
lean_ctor_set(v_reuseFailAlloc_1419_, 4, v_setupFileName_x3f_1397_);
lean_ctor_set(v_reuseFailAlloc_1419_, 5, v_oleanFileName_x3f_1398_);
lean_ctor_set(v_reuseFailAlloc_1419_, 6, v_ileanFileName_x3f_1399_);
lean_ctor_set(v_reuseFailAlloc_1419_, 7, v_cFileName_x3f_1400_);
lean_ctor_set(v_reuseFailAlloc_1419_, 8, v_bcFileName_x3f_1401_);
lean_ctor_set(v_reuseFailAlloc_1419_, 9, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1419_, 10, v_incrSaveFileName_x3f_1406_);
lean_ctor_set(v_reuseFailAlloc_1419_, 11, v_incrLoadFileName_x3f_1407_);
lean_ctor_set(v_reuseFailAlloc_1419_, 12, v_incrHeaderSaveFileName_x3f_1408_);
lean_ctor_set_uint8(v_reuseFailAlloc_1419_, sizeof(void*)*13 + 8, v_component_1386_);
lean_ctor_set_uint8(v_reuseFailAlloc_1419_, sizeof(void*)*13 + 9, v_printPrefix_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1419_, sizeof(void*)*13 + 10, v_printLibDir_1388_);
lean_ctor_set_uint8(v_reuseFailAlloc_1419_, sizeof(void*)*13 + 11, v_useStdin_1389_);
lean_ctor_set_uint8(v_reuseFailAlloc_1419_, sizeof(void*)*13 + 12, v_onlyDeps_1390_);
lean_ctor_set_uint8(v_reuseFailAlloc_1419_, sizeof(void*)*13 + 13, v_onlySrcDeps_1391_);
lean_ctor_set_uint8(v_reuseFailAlloc_1419_, sizeof(void*)*13 + 14, v_depsJson_1392_);
lean_ctor_set_uint32(v_reuseFailAlloc_1419_, sizeof(void*)*13, v_trustLevel_1394_);
lean_ctor_set_uint32(v_reuseFailAlloc_1419_, sizeof(void*)*13 + 4, v_numThreads_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1419_, sizeof(void*)*13 + 15, v_jsonOutput_1402_);
lean_ctor_set_uint8(v_reuseFailAlloc_1419_, sizeof(void*)*13 + 16, v_printStats_1404_);
lean_ctor_set_uint8(v_reuseFailAlloc_1419_, sizeof(void*)*13 + 17, v_run_1405_);
v___x_1415_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1415_);
v___x_1417_ = v___x_1382_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref(v_opts_933_);
v_a_1422_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1379_, 1);
v___x_1426_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1427_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1426_);
lean_dec_ref(v___x_1427_);
goto v___jp_1423_;
v___jp_1423_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_io_error_to_string(v_a_1422_);
v___x_1425_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1424_);
lean_dec_ref(v___x_1425_);
goto v___jp_1073_;
}
}
}
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1429_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1428_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1470_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1470_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1470_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v_leanOpts_1434_; lean_object* v_forwardedArgs_1435_; uint8_t v_component_1436_; uint8_t v_printPrefix_1437_; uint8_t v_printLibDir_1438_; uint8_t v_useStdin_1439_; uint8_t v_onlyDeps_1440_; uint8_t v_onlySrcDeps_1441_; uint8_t v_depsJson_1442_; lean_object* v_opts_1443_; uint32_t v_trustLevel_1444_; uint32_t v_numThreads_1445_; lean_object* v_rootDir_x3f_1446_; lean_object* v_oleanFileName_x3f_1447_; lean_object* v_ileanFileName_x3f_1448_; lean_object* v_cFileName_x3f_1449_; lean_object* v_bcFileName_x3f_1450_; uint8_t v_jsonOutput_1451_; lean_object* v_errorOnKinds_1452_; uint8_t v_printStats_1453_; uint8_t v_run_1454_; lean_object* v_incrSaveFileName_x3f_1455_; lean_object* v_incrLoadFileName_x3f_1456_; lean_object* v_incrHeaderSaveFileName_x3f_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1468_; 
v_leanOpts_1434_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1435_ = lean_ctor_get(v_opts_933_, 1);
v_component_1436_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1437_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1438_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1439_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1440_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1441_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1442_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1443_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1444_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1445_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1446_ = lean_ctor_get(v_opts_933_, 3);
v_oleanFileName_x3f_1447_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1448_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1449_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1450_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1451_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1452_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1453_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1454_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1455_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1456_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1457_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; 
v_unused_1469_ = lean_ctor_get(v_opts_933_, 4);
lean_dec(v_unused_1469_);
v___x_1459_ = v_opts_933_;
v_isShared_1460_ = v_isSharedCheck_1468_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1457_);
lean_inc(v_incrLoadFileName_x3f_1456_);
lean_inc(v_incrSaveFileName_x3f_1455_);
lean_inc(v_errorOnKinds_1452_);
lean_inc(v_bcFileName_x3f_1450_);
lean_inc(v_cFileName_x3f_1449_);
lean_inc(v_ileanFileName_x3f_1448_);
lean_inc(v_oleanFileName_x3f_1447_);
lean_inc(v_rootDir_x3f_1446_);
lean_inc(v_opts_1443_);
lean_inc(v_forwardedArgs_1435_);
lean_inc(v_leanOpts_1434_);
lean_dec(v_opts_933_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1468_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1461_, 0, v_a_1430_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 4, v___x_1461_);
v___x_1463_ = v___x_1459_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_leanOpts_1434_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_forwardedArgs_1435_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_opts_1443_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v_rootDir_x3f_1446_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1467_, 5, v_oleanFileName_x3f_1447_);
lean_ctor_set(v_reuseFailAlloc_1467_, 6, v_ileanFileName_x3f_1448_);
lean_ctor_set(v_reuseFailAlloc_1467_, 7, v_cFileName_x3f_1449_);
lean_ctor_set(v_reuseFailAlloc_1467_, 8, v_bcFileName_x3f_1450_);
lean_ctor_set(v_reuseFailAlloc_1467_, 9, v_errorOnKinds_1452_);
lean_ctor_set(v_reuseFailAlloc_1467_, 10, v_incrSaveFileName_x3f_1455_);
lean_ctor_set(v_reuseFailAlloc_1467_, 11, v_incrLoadFileName_x3f_1456_);
lean_ctor_set(v_reuseFailAlloc_1467_, 12, v_incrHeaderSaveFileName_x3f_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1467_, sizeof(void*)*13 + 8, v_component_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1467_, sizeof(void*)*13 + 9, v_printPrefix_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1467_, sizeof(void*)*13 + 10, v_printLibDir_1438_);
lean_ctor_set_uint8(v_reuseFailAlloc_1467_, sizeof(void*)*13 + 11, v_useStdin_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1467_, sizeof(void*)*13 + 12, v_onlyDeps_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1467_, sizeof(void*)*13 + 13, v_onlySrcDeps_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1467_, sizeof(void*)*13 + 14, v_depsJson_1442_);
lean_ctor_set_uint32(v_reuseFailAlloc_1467_, sizeof(void*)*13, v_trustLevel_1444_);
lean_ctor_set_uint32(v_reuseFailAlloc_1467_, sizeof(void*)*13 + 4, v_numThreads_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1467_, sizeof(void*)*13 + 15, v_jsonOutput_1451_);
lean_ctor_set_uint8(v_reuseFailAlloc_1467_, sizeof(void*)*13 + 16, v_printStats_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1467_, sizeof(void*)*13 + 17, v_run_1454_);
v___x_1463_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1465_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1463_);
v___x_1465_ = v___x_1432_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_dec_ref(v_opts_933_);
v_a_1471_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1475_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1476_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1475_);
lean_dec_ref(v___x_1476_);
goto v___jp_1472_;
v___jp_1472_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = lean_io_error_to_string(v_a_1471_);
v___x_1474_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1473_);
lean_dec_ref(v___x_1474_);
goto v___jp_1021_;
}
}
}
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1478_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1477_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc_n(v_a_1479_, 2);
lean_dec_ref_known(v___x_1478_, 1);
v___x_1480_ = lean_load_dynlib(v_a_1479_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1522_; 
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v___x_1480_, 0);
lean_dec(v_unused_1523_);
v___x_1482_ = v___x_1480_;
v_isShared_1483_ = v_isSharedCheck_1522_;
goto v_resetjp_1481_;
}
else
{
lean_dec(v___x_1480_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1522_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_leanOpts_1484_; lean_object* v_forwardedArgs_1485_; uint8_t v_component_1486_; uint8_t v_printPrefix_1487_; uint8_t v_printLibDir_1488_; uint8_t v_useStdin_1489_; uint8_t v_onlyDeps_1490_; uint8_t v_onlySrcDeps_1491_; uint8_t v_depsJson_1492_; lean_object* v_opts_1493_; uint32_t v_trustLevel_1494_; uint32_t v_numThreads_1495_; lean_object* v_rootDir_x3f_1496_; lean_object* v_setupFileName_x3f_1497_; lean_object* v_oleanFileName_x3f_1498_; lean_object* v_ileanFileName_x3f_1499_; lean_object* v_cFileName_x3f_1500_; lean_object* v_bcFileName_x3f_1501_; uint8_t v_jsonOutput_1502_; lean_object* v_errorOnKinds_1503_; uint8_t v_printStats_1504_; uint8_t v_run_1505_; lean_object* v_incrSaveFileName_x3f_1506_; lean_object* v_incrLoadFileName_x3f_1507_; lean_object* v_incrHeaderSaveFileName_x3f_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1521_; 
v_leanOpts_1484_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1485_ = lean_ctor_get(v_opts_933_, 1);
v_component_1486_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1487_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1488_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1489_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1490_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1491_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1492_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1493_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1494_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1495_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1496_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1497_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1498_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1499_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1500_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1501_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1502_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1503_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1504_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1505_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1506_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1507_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1508_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1510_ = v_opts_933_;
v_isShared_1511_ = v_isSharedCheck_1521_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1508_);
lean_inc(v_incrLoadFileName_x3f_1507_);
lean_inc(v_incrSaveFileName_x3f_1506_);
lean_inc(v_errorOnKinds_1503_);
lean_inc(v_bcFileName_x3f_1501_);
lean_inc(v_cFileName_x3f_1500_);
lean_inc(v_ileanFileName_x3f_1499_);
lean_inc(v_oleanFileName_x3f_1498_);
lean_inc(v_setupFileName_x3f_1497_);
lean_inc(v_rootDir_x3f_1496_);
lean_inc(v_opts_1493_);
lean_inc(v_forwardedArgs_1485_);
lean_inc(v_leanOpts_1484_);
lean_dec(v_opts_933_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1521_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1512_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1513_ = lean_string_append(v___x_1512_, v_a_1479_);
lean_dec(v_a_1479_);
v___x_1514_ = lean_array_push(v_forwardedArgs_1485_, v___x_1513_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 1, v___x_1514_);
v___x_1516_ = v___x_1510_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_leanOpts_1484_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_opts_1493_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v_rootDir_x3f_1496_);
lean_ctor_set(v_reuseFailAlloc_1520_, 4, v_setupFileName_x3f_1497_);
lean_ctor_set(v_reuseFailAlloc_1520_, 5, v_oleanFileName_x3f_1498_);
lean_ctor_set(v_reuseFailAlloc_1520_, 6, v_ileanFileName_x3f_1499_);
lean_ctor_set(v_reuseFailAlloc_1520_, 7, v_cFileName_x3f_1500_);
lean_ctor_set(v_reuseFailAlloc_1520_, 8, v_bcFileName_x3f_1501_);
lean_ctor_set(v_reuseFailAlloc_1520_, 9, v_errorOnKinds_1503_);
lean_ctor_set(v_reuseFailAlloc_1520_, 10, v_incrSaveFileName_x3f_1506_);
lean_ctor_set(v_reuseFailAlloc_1520_, 11, v_incrLoadFileName_x3f_1507_);
lean_ctor_set(v_reuseFailAlloc_1520_, 12, v_incrHeaderSaveFileName_x3f_1508_);
lean_ctor_set_uint8(v_reuseFailAlloc_1520_, sizeof(void*)*13 + 8, v_component_1486_);
lean_ctor_set_uint8(v_reuseFailAlloc_1520_, sizeof(void*)*13 + 9, v_printPrefix_1487_);
lean_ctor_set_uint8(v_reuseFailAlloc_1520_, sizeof(void*)*13 + 10, v_printLibDir_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1520_, sizeof(void*)*13 + 11, v_useStdin_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1520_, sizeof(void*)*13 + 12, v_onlyDeps_1490_);
lean_ctor_set_uint8(v_reuseFailAlloc_1520_, sizeof(void*)*13 + 13, v_onlySrcDeps_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1520_, sizeof(void*)*13 + 14, v_depsJson_1492_);
lean_ctor_set_uint32(v_reuseFailAlloc_1520_, sizeof(void*)*13, v_trustLevel_1494_);
lean_ctor_set_uint32(v_reuseFailAlloc_1520_, sizeof(void*)*13 + 4, v_numThreads_1495_);
lean_ctor_set_uint8(v_reuseFailAlloc_1520_, sizeof(void*)*13 + 15, v_jsonOutput_1502_);
lean_ctor_set_uint8(v_reuseFailAlloc_1520_, sizeof(void*)*13 + 16, v_printStats_1504_);
lean_ctor_set_uint8(v_reuseFailAlloc_1520_, sizeof(void*)*13 + 17, v_run_1505_);
v___x_1516_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1516_);
v___x_1518_ = v___x_1482_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v_a_1479_);
lean_dec_ref(v_opts_933_);
v_a_1524_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1528_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1529_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1528_);
lean_dec_ref(v___x_1529_);
goto v___jp_1525_;
v___jp_1525_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_io_error_to_string(v_a_1524_);
v___x_1527_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1526_);
lean_dec_ref(v___x_1527_);
goto v___jp_1079_;
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_dec_ref(v_opts_933_);
v_a_1530_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1478_, 1);
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
goto v___jp_1085_;
}
}
}
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1537_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1536_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1609_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1609_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1609_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_fst_1543_; lean_object* v_snd_1544_; lean_object* v___y_1593_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1604_ = lean_unsigned_to_nat(0u);
v___x_1605_ = lean_string_utf8_byte_size(v_a_1538_);
v___x_1606_ = lean_box(0);
v___x_1607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_1605_, v_a_1538_, v___x_1604_, v___x_1606_);
if (lean_obj_tag(v___x_1607_) == 0)
{
v___y_1593_ = v___x_1605_;
goto v___jp_1592_;
}
else
{
lean_object* v_val_1608_; 
v_val_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_val_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v___y_1593_ = v_val_1608_;
goto v___jp_1592_;
}
v___jp_1542_:
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_load_plugin(v_fst_1543_, v_snd_1544_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1587_; 
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; 
v_unused_1588_ = lean_ctor_get(v___x_1545_, 0);
lean_dec(v_unused_1588_);
v___x_1547_ = v___x_1545_;
v_isShared_1548_ = v_isSharedCheck_1587_;
goto v_resetjp_1546_;
}
else
{
lean_dec(v___x_1545_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1587_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v_leanOpts_1549_; lean_object* v_forwardedArgs_1550_; uint8_t v_component_1551_; uint8_t v_printPrefix_1552_; uint8_t v_printLibDir_1553_; uint8_t v_useStdin_1554_; uint8_t v_onlyDeps_1555_; uint8_t v_onlySrcDeps_1556_; uint8_t v_depsJson_1557_; lean_object* v_opts_1558_; uint32_t v_trustLevel_1559_; uint32_t v_numThreads_1560_; lean_object* v_rootDir_x3f_1561_; lean_object* v_setupFileName_x3f_1562_; lean_object* v_oleanFileName_x3f_1563_; lean_object* v_ileanFileName_x3f_1564_; lean_object* v_cFileName_x3f_1565_; lean_object* v_bcFileName_x3f_1566_; uint8_t v_jsonOutput_1567_; lean_object* v_errorOnKinds_1568_; uint8_t v_printStats_1569_; uint8_t v_run_1570_; lean_object* v_incrSaveFileName_x3f_1571_; lean_object* v_incrLoadFileName_x3f_1572_; lean_object* v_incrHeaderSaveFileName_x3f_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1586_; 
v_leanOpts_1549_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1550_ = lean_ctor_get(v_opts_933_, 1);
v_component_1551_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1552_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1553_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1554_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1555_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1556_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1557_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1558_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1559_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1560_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1561_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1562_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1563_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1564_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1565_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1566_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1567_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1568_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1569_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1570_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1571_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1572_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1573_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1575_ = v_opts_933_;
v_isShared_1576_ = v_isSharedCheck_1586_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1573_);
lean_inc(v_incrLoadFileName_x3f_1572_);
lean_inc(v_incrSaveFileName_x3f_1571_);
lean_inc(v_errorOnKinds_1568_);
lean_inc(v_bcFileName_x3f_1566_);
lean_inc(v_cFileName_x3f_1565_);
lean_inc(v_ileanFileName_x3f_1564_);
lean_inc(v_oleanFileName_x3f_1563_);
lean_inc(v_setupFileName_x3f_1562_);
lean_inc(v_rootDir_x3f_1561_);
lean_inc(v_opts_1558_);
lean_inc(v_forwardedArgs_1550_);
lean_inc(v_leanOpts_1549_);
lean_dec(v_opts_933_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1586_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1577_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1578_ = lean_string_append(v___x_1577_, v_a_1538_);
lean_dec(v_a_1538_);
v___x_1579_ = lean_array_push(v_forwardedArgs_1550_, v___x_1578_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 1, v___x_1579_);
v___x_1581_ = v___x_1575_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_leanOpts_1549_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_opts_1558_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_rootDir_x3f_1561_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_setupFileName_x3f_1562_);
lean_ctor_set(v_reuseFailAlloc_1585_, 5, v_oleanFileName_x3f_1563_);
lean_ctor_set(v_reuseFailAlloc_1585_, 6, v_ileanFileName_x3f_1564_);
lean_ctor_set(v_reuseFailAlloc_1585_, 7, v_cFileName_x3f_1565_);
lean_ctor_set(v_reuseFailAlloc_1585_, 8, v_bcFileName_x3f_1566_);
lean_ctor_set(v_reuseFailAlloc_1585_, 9, v_errorOnKinds_1568_);
lean_ctor_set(v_reuseFailAlloc_1585_, 10, v_incrSaveFileName_x3f_1571_);
lean_ctor_set(v_reuseFailAlloc_1585_, 11, v_incrLoadFileName_x3f_1572_);
lean_ctor_set(v_reuseFailAlloc_1585_, 12, v_incrHeaderSaveFileName_x3f_1573_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*13 + 8, v_component_1551_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*13 + 9, v_printPrefix_1552_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*13 + 10, v_printLibDir_1553_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*13 + 11, v_useStdin_1554_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*13 + 12, v_onlyDeps_1555_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*13 + 13, v_onlySrcDeps_1556_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*13 + 14, v_depsJson_1557_);
lean_ctor_set_uint32(v_reuseFailAlloc_1585_, sizeof(void*)*13, v_trustLevel_1559_);
lean_ctor_set_uint32(v_reuseFailAlloc_1585_, sizeof(void*)*13 + 4, v_numThreads_1560_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*13 + 15, v_jsonOutput_1567_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*13 + 16, v_printStats_1569_);
lean_ctor_set_uint8(v_reuseFailAlloc_1585_, sizeof(void*)*13 + 17, v_run_1570_);
v___x_1581_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1581_);
v___x_1583_ = v___x_1547_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_dec(v_a_1538_);
lean_dec_ref(v_opts_933_);
v_a_1589_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1590_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1591_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1590_);
lean_dec_ref(v___x_1591_);
v___y_1101_ = v_a_1589_;
goto v___jp_1100_;
}
}
v___jp_1592_:
{
lean_object* v___x_1594_; uint8_t v_decide_1595_; 
v___x_1594_ = lean_string_utf8_byte_size(v_a_1538_);
v_decide_1595_ = lean_nat_dec_eq(v___y_1593_, v___x_1594_);
if (v_decide_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1596_ = lean_unsigned_to_nat(0u);
v___x_1597_ = lean_string_utf8_next_fast(v_a_1538_, v___y_1593_);
v___x_1598_ = lean_string_utf8_extract_fast(v_a_1538_, v___x_1596_, v___y_1593_);
lean_dec(v___y_1593_);
v___x_1599_ = lean_string_utf8_extract_fast(v_a_1538_, v___x_1597_, v___x_1594_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 1);
lean_ctor_set(v___x_1540_, 0, v___x_1599_);
v___x_1601_ = v___x_1540_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
v_fst_1543_ = v___x_1598_;
v_snd_1544_ = v___x_1601_;
goto v___jp_1542_;
}
}
else
{
lean_object* v___x_1603_; 
lean_dec(v___y_1593_);
lean_del_object(v___x_1540_);
v___x_1603_ = lean_box(0);
lean_inc(v_a_1538_);
v_fst_1543_ = v_a_1538_;
v_snd_1544_ = v___x_1603_;
goto v___jp_1542_;
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
lean_dec_ref(v_opts_933_);
v_a_1610_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1537_, 1);
v___x_1614_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1615_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1614_);
lean_dec_ref(v___x_1615_);
goto v___jp_1611_;
v___jp_1611_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_io_error_to_string(v_a_1610_);
v___x_1613_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1612_);
lean_dec_ref(v___x_1613_);
goto v___jp_1097_;
}
}
}
}
else
{
uint8_t v___x_1616_; 
v___x_1616_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__16, &l___private_Lean_Shell_0__Lean_displayHelp___closed__16_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
if (v___x_1616_ == 0)
{
lean_dec(v_optArg_x3f_935_);
lean_dec_ref(v_opts_933_);
goto v___jp_1061_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1618_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1617_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1627_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1623_ = lean_internal_enable_debug(v_a_1619_);
lean_dec(v_a_1619_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v_opts_933_);
v___x_1625_ = v___x_1621_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_opts_933_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec_ref(v_opts_933_);
v_a_1628_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1632_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1633_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1632_);
lean_dec_ref(v___x_1633_);
goto v___jp_1629_;
v___jp_1629_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = lean_io_error_to_string(v_a_1628_);
v___x_1631_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1630_);
lean_dec_ref(v___x_1631_);
goto v___jp_1107_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1634_; lean_object* v_forwardedArgs_1635_; uint8_t v_component_1636_; uint8_t v_printPrefix_1637_; uint8_t v_printLibDir_1638_; uint8_t v_useStdin_1639_; uint8_t v_onlyDeps_1640_; uint8_t v_onlySrcDeps_1641_; uint8_t v_depsJson_1642_; lean_object* v_opts_1643_; uint32_t v_trustLevel_1644_; uint32_t v_numThreads_1645_; lean_object* v_rootDir_x3f_1646_; lean_object* v_setupFileName_x3f_1647_; lean_object* v_oleanFileName_x3f_1648_; lean_object* v_ileanFileName_x3f_1649_; lean_object* v_cFileName_x3f_1650_; lean_object* v_bcFileName_x3f_1651_; uint8_t v_jsonOutput_1652_; lean_object* v_errorOnKinds_1653_; uint8_t v_printStats_1654_; uint8_t v_run_1655_; lean_object* v_incrSaveFileName_x3f_1656_; lean_object* v_incrLoadFileName_x3f_1657_; lean_object* v_incrHeaderSaveFileName_x3f_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_optArg_x3f_935_);
v_leanOpts_1634_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1635_ = lean_ctor_get(v_opts_933_, 1);
v_component_1636_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1637_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1638_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1639_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1640_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1641_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1642_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1643_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1644_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1645_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1646_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1647_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1648_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1649_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1650_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1651_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1652_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1653_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1654_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1655_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1656_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1657_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1658_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1660_ = v_opts_933_;
v_isShared_1661_ = v_isSharedCheck_1668_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1658_);
lean_inc(v_incrLoadFileName_x3f_1657_);
lean_inc(v_incrSaveFileName_x3f_1656_);
lean_inc(v_errorOnKinds_1653_);
lean_inc(v_bcFileName_x3f_1651_);
lean_inc(v_cFileName_x3f_1650_);
lean_inc(v_ileanFileName_x3f_1649_);
lean_inc(v_oleanFileName_x3f_1648_);
lean_inc(v_setupFileName_x3f_1647_);
lean_inc(v_rootDir_x3f_1646_);
lean_inc(v_opts_1643_);
lean_inc(v_forwardedArgs_1635_);
lean_inc(v_leanOpts_1634_);
lean_dec(v_opts_933_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1668_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1662_ = l_Lean_profiler;
v___x_1663_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1634_, v___x_1662_, v___x_1214_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1663_);
v___x_1665_ = v___x_1660_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_forwardedArgs_1635_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_opts_1643_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_rootDir_x3f_1646_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_setupFileName_x3f_1647_);
lean_ctor_set(v_reuseFailAlloc_1667_, 5, v_oleanFileName_x3f_1648_);
lean_ctor_set(v_reuseFailAlloc_1667_, 6, v_ileanFileName_x3f_1649_);
lean_ctor_set(v_reuseFailAlloc_1667_, 7, v_cFileName_x3f_1650_);
lean_ctor_set(v_reuseFailAlloc_1667_, 8, v_bcFileName_x3f_1651_);
lean_ctor_set(v_reuseFailAlloc_1667_, 9, v_errorOnKinds_1653_);
lean_ctor_set(v_reuseFailAlloc_1667_, 10, v_incrSaveFileName_x3f_1656_);
lean_ctor_set(v_reuseFailAlloc_1667_, 11, v_incrLoadFileName_x3f_1657_);
lean_ctor_set(v_reuseFailAlloc_1667_, 12, v_incrHeaderSaveFileName_x3f_1658_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*13 + 8, v_component_1636_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*13 + 9, v_printPrefix_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*13 + 10, v_printLibDir_1638_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*13 + 11, v_useStdin_1639_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*13 + 12, v_onlyDeps_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*13 + 13, v_onlySrcDeps_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*13 + 14, v_depsJson_1642_);
lean_ctor_set_uint32(v_reuseFailAlloc_1667_, sizeof(void*)*13, v_trustLevel_1644_);
lean_ctor_set_uint32(v_reuseFailAlloc_1667_, sizeof(void*)*13 + 4, v_numThreads_1645_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*13 + 15, v_jsonOutput_1652_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*13 + 16, v_printStats_1654_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*13 + 17, v_run_1655_);
v___x_1665_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_leanOpts_1669_; lean_object* v_forwardedArgs_1670_; uint8_t v_printPrefix_1671_; uint8_t v_printLibDir_1672_; uint8_t v_useStdin_1673_; uint8_t v_onlyDeps_1674_; uint8_t v_onlySrcDeps_1675_; uint8_t v_depsJson_1676_; lean_object* v_opts_1677_; uint32_t v_trustLevel_1678_; uint32_t v_numThreads_1679_; lean_object* v_rootDir_x3f_1680_; lean_object* v_setupFileName_x3f_1681_; lean_object* v_oleanFileName_x3f_1682_; lean_object* v_ileanFileName_x3f_1683_; lean_object* v_cFileName_x3f_1684_; lean_object* v_bcFileName_x3f_1685_; uint8_t v_jsonOutput_1686_; lean_object* v_errorOnKinds_1687_; uint8_t v_printStats_1688_; uint8_t v_run_1689_; lean_object* v_incrSaveFileName_x3f_1690_; lean_object* v_incrLoadFileName_x3f_1691_; lean_object* v_incrHeaderSaveFileName_x3f_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_optArg_x3f_935_);
v_leanOpts_1669_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1670_ = lean_ctor_get(v_opts_933_, 1);
v_printPrefix_1671_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1672_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1673_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1674_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1675_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1676_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1677_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1678_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1679_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1680_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1681_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1682_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1683_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1684_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1685_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1686_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1687_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1688_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1689_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1690_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1691_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1692_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1694_ = v_opts_933_;
v_isShared_1695_ = v_isSharedCheck_1701_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1692_);
lean_inc(v_incrLoadFileName_x3f_1691_);
lean_inc(v_incrSaveFileName_x3f_1690_);
lean_inc(v_errorOnKinds_1687_);
lean_inc(v_bcFileName_x3f_1685_);
lean_inc(v_cFileName_x3f_1684_);
lean_inc(v_ileanFileName_x3f_1683_);
lean_inc(v_oleanFileName_x3f_1682_);
lean_inc(v_setupFileName_x3f_1681_);
lean_inc(v_rootDir_x3f_1680_);
lean_inc(v_opts_1677_);
lean_inc(v_forwardedArgs_1670_);
lean_inc(v_leanOpts_1669_);
lean_dec(v_opts_933_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1701_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
uint8_t v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = 2;
if (v_isShared_1695_ == 0)
{
v___x_1698_ = v___x_1694_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_leanOpts_1669_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_forwardedArgs_1670_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_opts_1677_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v_rootDir_x3f_1680_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v_setupFileName_x3f_1681_);
lean_ctor_set(v_reuseFailAlloc_1700_, 5, v_oleanFileName_x3f_1682_);
lean_ctor_set(v_reuseFailAlloc_1700_, 6, v_ileanFileName_x3f_1683_);
lean_ctor_set(v_reuseFailAlloc_1700_, 7, v_cFileName_x3f_1684_);
lean_ctor_set(v_reuseFailAlloc_1700_, 8, v_bcFileName_x3f_1685_);
lean_ctor_set(v_reuseFailAlloc_1700_, 9, v_errorOnKinds_1687_);
lean_ctor_set(v_reuseFailAlloc_1700_, 10, v_incrSaveFileName_x3f_1690_);
lean_ctor_set(v_reuseFailAlloc_1700_, 11, v_incrLoadFileName_x3f_1691_);
lean_ctor_set(v_reuseFailAlloc_1700_, 12, v_incrHeaderSaveFileName_x3f_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, sizeof(void*)*13 + 9, v_printPrefix_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, sizeof(void*)*13 + 10, v_printLibDir_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, sizeof(void*)*13 + 11, v_useStdin_1673_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, sizeof(void*)*13 + 12, v_onlyDeps_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, sizeof(void*)*13 + 13, v_onlySrcDeps_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, sizeof(void*)*13 + 14, v_depsJson_1676_);
lean_ctor_set_uint32(v_reuseFailAlloc_1700_, sizeof(void*)*13, v_trustLevel_1678_);
lean_ctor_set_uint32(v_reuseFailAlloc_1700_, sizeof(void*)*13 + 4, v_numThreads_1679_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, sizeof(void*)*13 + 15, v_jsonOutput_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, sizeof(void*)*13 + 16, v_printStats_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1700_, sizeof(void*)*13 + 17, v_run_1689_);
v___x_1698_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1699_; 
lean_ctor_set_uint8(v___x_1698_, sizeof(void*)*13 + 8, v___x_1696_);
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
return v___x_1699_;
}
}
}
}
else
{
lean_object* v_leanOpts_1702_; lean_object* v_forwardedArgs_1703_; uint8_t v_printPrefix_1704_; uint8_t v_printLibDir_1705_; uint8_t v_useStdin_1706_; uint8_t v_onlyDeps_1707_; uint8_t v_onlySrcDeps_1708_; uint8_t v_depsJson_1709_; lean_object* v_opts_1710_; uint32_t v_trustLevel_1711_; uint32_t v_numThreads_1712_; lean_object* v_rootDir_x3f_1713_; lean_object* v_setupFileName_x3f_1714_; lean_object* v_oleanFileName_x3f_1715_; lean_object* v_ileanFileName_x3f_1716_; lean_object* v_cFileName_x3f_1717_; lean_object* v_bcFileName_x3f_1718_; uint8_t v_jsonOutput_1719_; lean_object* v_errorOnKinds_1720_; uint8_t v_printStats_1721_; uint8_t v_run_1722_; lean_object* v_incrSaveFileName_x3f_1723_; lean_object* v_incrLoadFileName_x3f_1724_; lean_object* v_incrHeaderSaveFileName_x3f_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_optArg_x3f_935_);
v_leanOpts_1702_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1703_ = lean_ctor_get(v_opts_933_, 1);
v_printPrefix_1704_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1705_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1706_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1707_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1708_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1709_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1710_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1711_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1712_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1713_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1714_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1715_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1716_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1717_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1718_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1719_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1720_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1721_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1722_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1723_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1724_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1725_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1727_ = v_opts_933_;
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1725_);
lean_inc(v_incrLoadFileName_x3f_1724_);
lean_inc(v_incrSaveFileName_x3f_1723_);
lean_inc(v_errorOnKinds_1720_);
lean_inc(v_bcFileName_x3f_1718_);
lean_inc(v_cFileName_x3f_1717_);
lean_inc(v_ileanFileName_x3f_1716_);
lean_inc(v_oleanFileName_x3f_1715_);
lean_inc(v_setupFileName_x3f_1714_);
lean_inc(v_rootDir_x3f_1713_);
lean_inc(v_opts_1710_);
lean_inc(v_forwardedArgs_1703_);
lean_inc(v_leanOpts_1702_);
lean_dec(v_opts_933_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
uint8_t v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = 1;
if (v_isShared_1728_ == 0)
{
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_leanOpts_1702_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_forwardedArgs_1703_);
lean_ctor_set(v_reuseFailAlloc_1733_, 2, v_opts_1710_);
lean_ctor_set(v_reuseFailAlloc_1733_, 3, v_rootDir_x3f_1713_);
lean_ctor_set(v_reuseFailAlloc_1733_, 4, v_setupFileName_x3f_1714_);
lean_ctor_set(v_reuseFailAlloc_1733_, 5, v_oleanFileName_x3f_1715_);
lean_ctor_set(v_reuseFailAlloc_1733_, 6, v_ileanFileName_x3f_1716_);
lean_ctor_set(v_reuseFailAlloc_1733_, 7, v_cFileName_x3f_1717_);
lean_ctor_set(v_reuseFailAlloc_1733_, 8, v_bcFileName_x3f_1718_);
lean_ctor_set(v_reuseFailAlloc_1733_, 9, v_errorOnKinds_1720_);
lean_ctor_set(v_reuseFailAlloc_1733_, 10, v_incrSaveFileName_x3f_1723_);
lean_ctor_set(v_reuseFailAlloc_1733_, 11, v_incrLoadFileName_x3f_1724_);
lean_ctor_set(v_reuseFailAlloc_1733_, 12, v_incrHeaderSaveFileName_x3f_1725_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*13 + 9, v_printPrefix_1704_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*13 + 10, v_printLibDir_1705_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*13 + 11, v_useStdin_1706_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*13 + 12, v_onlyDeps_1707_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*13 + 13, v_onlySrcDeps_1708_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*13 + 14, v_depsJson_1709_);
lean_ctor_set_uint32(v_reuseFailAlloc_1733_, sizeof(void*)*13, v_trustLevel_1711_);
lean_ctor_set_uint32(v_reuseFailAlloc_1733_, sizeof(void*)*13 + 4, v_numThreads_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*13 + 15, v_jsonOutput_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*13 + 16, v_printStats_1721_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*13 + 17, v_run_1722_);
v___x_1731_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; 
lean_ctor_set_uint8(v___x_1731_, sizeof(void*)*13 + 8, v___x_1729_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
}
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1736_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1735_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v_leanOpts_1738_; lean_object* v_forwardedArgs_1739_; uint8_t v_component_1740_; uint8_t v_printPrefix_1741_; uint8_t v_printLibDir_1742_; uint8_t v_useStdin_1743_; uint8_t v_onlyDeps_1744_; uint8_t v_onlySrcDeps_1745_; uint8_t v_depsJson_1746_; lean_object* v_opts_1747_; uint32_t v_trustLevel_1748_; uint32_t v_numThreads_1749_; lean_object* v_rootDir_x3f_1750_; lean_object* v_setupFileName_x3f_1751_; lean_object* v_oleanFileName_x3f_1752_; lean_object* v_ileanFileName_x3f_1753_; lean_object* v_cFileName_x3f_1754_; lean_object* v_bcFileName_x3f_1755_; uint8_t v_jsonOutput_1756_; lean_object* v_errorOnKinds_1757_; uint8_t v_printStats_1758_; uint8_t v_run_1759_; lean_object* v_incrSaveFileName_x3f_1760_; lean_object* v_incrLoadFileName_x3f_1761_; lean_object* v_incrHeaderSaveFileName_x3f_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1787_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1736_, 1);
v_leanOpts_1738_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1739_ = lean_ctor_get(v_opts_933_, 1);
v_component_1740_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1741_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1742_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1743_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1744_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1745_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1746_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1747_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1748_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1749_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1750_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1751_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1752_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1753_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1754_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1755_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1756_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1757_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1758_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1759_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1760_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1761_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1762_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1764_ = v_opts_933_;
v_isShared_1765_ = v_isSharedCheck_1787_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1762_);
lean_inc(v_incrLoadFileName_x3f_1761_);
lean_inc(v_incrSaveFileName_x3f_1760_);
lean_inc(v_errorOnKinds_1757_);
lean_inc(v_bcFileName_x3f_1755_);
lean_inc(v_cFileName_x3f_1754_);
lean_inc(v_ileanFileName_x3f_1753_);
lean_inc(v_oleanFileName_x3f_1752_);
lean_inc(v_setupFileName_x3f_1751_);
lean_inc(v_rootDir_x3f_1750_);
lean_inc(v_opts_1747_);
lean_inc(v_forwardedArgs_1739_);
lean_inc(v_leanOpts_1738_);
lean_dec(v_opts_933_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1787_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; 
lean_inc(v_a_1737_);
v___x_1766_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1738_, v_a_1737_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1780_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1780_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1780_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1772_ = lean_string_append(v___x_1771_, v_a_1737_);
lean_dec(v_a_1737_);
v___x_1773_ = lean_array_push(v_forwardedArgs_1739_, v___x_1772_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 1, v___x_1773_);
lean_ctor_set(v___x_1764_, 0, v_a_1767_);
v___x_1775_ = v___x_1764_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1767_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_opts_1747_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_rootDir_x3f_1750_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v_setupFileName_x3f_1751_);
lean_ctor_set(v_reuseFailAlloc_1779_, 5, v_oleanFileName_x3f_1752_);
lean_ctor_set(v_reuseFailAlloc_1779_, 6, v_ileanFileName_x3f_1753_);
lean_ctor_set(v_reuseFailAlloc_1779_, 7, v_cFileName_x3f_1754_);
lean_ctor_set(v_reuseFailAlloc_1779_, 8, v_bcFileName_x3f_1755_);
lean_ctor_set(v_reuseFailAlloc_1779_, 9, v_errorOnKinds_1757_);
lean_ctor_set(v_reuseFailAlloc_1779_, 10, v_incrSaveFileName_x3f_1760_);
lean_ctor_set(v_reuseFailAlloc_1779_, 11, v_incrLoadFileName_x3f_1761_);
lean_ctor_set(v_reuseFailAlloc_1779_, 12, v_incrHeaderSaveFileName_x3f_1762_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*13 + 8, v_component_1740_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*13 + 9, v_printPrefix_1741_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*13 + 10, v_printLibDir_1742_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*13 + 11, v_useStdin_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*13 + 12, v_onlyDeps_1744_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*13 + 13, v_onlySrcDeps_1745_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*13 + 14, v_depsJson_1746_);
lean_ctor_set_uint32(v_reuseFailAlloc_1779_, sizeof(void*)*13, v_trustLevel_1748_);
lean_ctor_set_uint32(v_reuseFailAlloc_1779_, sizeof(void*)*13 + 4, v_numThreads_1749_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*13 + 15, v_jsonOutput_1756_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*13 + 16, v_printStats_1758_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*13 + 17, v_run_1759_);
v___x_1775_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1775_);
v___x_1777_ = v___x_1769_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_del_object(v___x_1764_);
lean_dec(v_incrHeaderSaveFileName_x3f_1762_);
lean_dec(v_incrLoadFileName_x3f_1761_);
lean_dec(v_incrSaveFileName_x3f_1760_);
lean_dec_ref(v_errorOnKinds_1757_);
lean_dec(v_bcFileName_x3f_1755_);
lean_dec(v_cFileName_x3f_1754_);
lean_dec(v_ileanFileName_x3f_1753_);
lean_dec(v_oleanFileName_x3f_1752_);
lean_dec(v_setupFileName_x3f_1751_);
lean_dec(v_rootDir_x3f_1750_);
lean_dec_ref(v_opts_1747_);
lean_dec_ref(v_forwardedArgs_1739_);
lean_dec(v_a_1737_);
v_a_1781_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1785_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1786_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1785_);
lean_dec_ref(v___x_1786_);
goto v___jp_1782_;
v___jp_1782_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_io_error_to_string(v_a_1781_);
v___x_1784_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1783_);
lean_dec_ref(v___x_1784_);
goto v___jp_1009_;
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec_ref(v_opts_933_);
v_a_1788_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1736_, 1);
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
lean_object* v_leanOpts_1794_; lean_object* v_forwardedArgs_1795_; uint8_t v_component_1796_; uint8_t v_printPrefix_1797_; uint8_t v_useStdin_1798_; uint8_t v_onlyDeps_1799_; uint8_t v_onlySrcDeps_1800_; uint8_t v_depsJson_1801_; lean_object* v_opts_1802_; uint32_t v_trustLevel_1803_; uint32_t v_numThreads_1804_; lean_object* v_rootDir_x3f_1805_; lean_object* v_setupFileName_x3f_1806_; lean_object* v_oleanFileName_x3f_1807_; lean_object* v_ileanFileName_x3f_1808_; lean_object* v_cFileName_x3f_1809_; lean_object* v_bcFileName_x3f_1810_; uint8_t v_jsonOutput_1811_; lean_object* v_errorOnKinds_1812_; uint8_t v_printStats_1813_; uint8_t v_run_1814_; lean_object* v_incrSaveFileName_x3f_1815_; lean_object* v_incrLoadFileName_x3f_1816_; lean_object* v_incrHeaderSaveFileName_x3f_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_optArg_x3f_935_);
v_leanOpts_1794_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1795_ = lean_ctor_get(v_opts_933_, 1);
v_component_1796_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1797_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_useStdin_1798_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1799_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1800_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1801_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1802_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1803_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1804_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1805_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1806_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1807_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1808_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1809_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1810_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1811_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1812_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1813_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1814_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1815_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1816_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1817_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1819_ = v_opts_933_;
v_isShared_1820_ = v_isSharedCheck_1825_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1817_);
lean_inc(v_incrLoadFileName_x3f_1816_);
lean_inc(v_incrSaveFileName_x3f_1815_);
lean_inc(v_errorOnKinds_1812_);
lean_inc(v_bcFileName_x3f_1810_);
lean_inc(v_cFileName_x3f_1809_);
lean_inc(v_ileanFileName_x3f_1808_);
lean_inc(v_oleanFileName_x3f_1807_);
lean_inc(v_setupFileName_x3f_1806_);
lean_inc(v_rootDir_x3f_1805_);
lean_inc(v_opts_1802_);
lean_inc(v_forwardedArgs_1795_);
lean_inc(v_leanOpts_1794_);
lean_dec(v_opts_933_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1825_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_leanOpts_1794_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_forwardedArgs_1795_);
lean_ctor_set(v_reuseFailAlloc_1824_, 2, v_opts_1802_);
lean_ctor_set(v_reuseFailAlloc_1824_, 3, v_rootDir_x3f_1805_);
lean_ctor_set(v_reuseFailAlloc_1824_, 4, v_setupFileName_x3f_1806_);
lean_ctor_set(v_reuseFailAlloc_1824_, 5, v_oleanFileName_x3f_1807_);
lean_ctor_set(v_reuseFailAlloc_1824_, 6, v_ileanFileName_x3f_1808_);
lean_ctor_set(v_reuseFailAlloc_1824_, 7, v_cFileName_x3f_1809_);
lean_ctor_set(v_reuseFailAlloc_1824_, 8, v_bcFileName_x3f_1810_);
lean_ctor_set(v_reuseFailAlloc_1824_, 9, v_errorOnKinds_1812_);
lean_ctor_set(v_reuseFailAlloc_1824_, 10, v_incrSaveFileName_x3f_1815_);
lean_ctor_set(v_reuseFailAlloc_1824_, 11, v_incrLoadFileName_x3f_1816_);
lean_ctor_set(v_reuseFailAlloc_1824_, 12, v_incrHeaderSaveFileName_x3f_1817_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 8, v_component_1796_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 9, v_printPrefix_1797_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 11, v_useStdin_1798_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 12, v_onlyDeps_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 13, v_onlySrcDeps_1800_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 14, v_depsJson_1801_);
lean_ctor_set_uint32(v_reuseFailAlloc_1824_, sizeof(void*)*13, v_trustLevel_1803_);
lean_ctor_set_uint32(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 4, v_numThreads_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 15, v_jsonOutput_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 16, v_printStats_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 17, v_run_1814_);
v___x_1822_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1823_; 
lean_ctor_set_uint8(v___x_1822_, sizeof(void*)*13 + 10, v___x_1206_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
}
}
}
else
{
lean_object* v_leanOpts_1826_; lean_object* v_forwardedArgs_1827_; uint8_t v_component_1828_; uint8_t v_printLibDir_1829_; uint8_t v_useStdin_1830_; uint8_t v_onlyDeps_1831_; uint8_t v_onlySrcDeps_1832_; uint8_t v_depsJson_1833_; lean_object* v_opts_1834_; uint32_t v_trustLevel_1835_; uint32_t v_numThreads_1836_; lean_object* v_rootDir_x3f_1837_; lean_object* v_setupFileName_x3f_1838_; lean_object* v_oleanFileName_x3f_1839_; lean_object* v_ileanFileName_x3f_1840_; lean_object* v_cFileName_x3f_1841_; lean_object* v_bcFileName_x3f_1842_; uint8_t v_jsonOutput_1843_; lean_object* v_errorOnKinds_1844_; uint8_t v_printStats_1845_; uint8_t v_run_1846_; lean_object* v_incrSaveFileName_x3f_1847_; lean_object* v_incrLoadFileName_x3f_1848_; lean_object* v_incrHeaderSaveFileName_x3f_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1857_; 
lean_dec(v_optArg_x3f_935_);
v_leanOpts_1826_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1827_ = lean_ctor_get(v_opts_933_, 1);
v_component_1828_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printLibDir_1829_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1830_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1831_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1832_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1833_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1834_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1835_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1836_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1837_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1838_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1839_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1840_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1841_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1842_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1843_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1844_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1845_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1846_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1847_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1848_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1849_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1851_ = v_opts_933_;
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1849_);
lean_inc(v_incrLoadFileName_x3f_1848_);
lean_inc(v_incrSaveFileName_x3f_1847_);
lean_inc(v_errorOnKinds_1844_);
lean_inc(v_bcFileName_x3f_1842_);
lean_inc(v_cFileName_x3f_1841_);
lean_inc(v_ileanFileName_x3f_1840_);
lean_inc(v_oleanFileName_x3f_1839_);
lean_inc(v_setupFileName_x3f_1838_);
lean_inc(v_rootDir_x3f_1837_);
lean_inc(v_opts_1834_);
lean_inc(v_forwardedArgs_1827_);
lean_inc(v_leanOpts_1826_);
lean_dec(v_opts_933_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_leanOpts_1826_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_forwardedArgs_1827_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_opts_1834_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v_rootDir_x3f_1837_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v_setupFileName_x3f_1838_);
lean_ctor_set(v_reuseFailAlloc_1856_, 5, v_oleanFileName_x3f_1839_);
lean_ctor_set(v_reuseFailAlloc_1856_, 6, v_ileanFileName_x3f_1840_);
lean_ctor_set(v_reuseFailAlloc_1856_, 7, v_cFileName_x3f_1841_);
lean_ctor_set(v_reuseFailAlloc_1856_, 8, v_bcFileName_x3f_1842_);
lean_ctor_set(v_reuseFailAlloc_1856_, 9, v_errorOnKinds_1844_);
lean_ctor_set(v_reuseFailAlloc_1856_, 10, v_incrSaveFileName_x3f_1847_);
lean_ctor_set(v_reuseFailAlloc_1856_, 11, v_incrLoadFileName_x3f_1848_);
lean_ctor_set(v_reuseFailAlloc_1856_, 12, v_incrHeaderSaveFileName_x3f_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1856_, sizeof(void*)*13 + 8, v_component_1828_);
lean_ctor_set_uint8(v_reuseFailAlloc_1856_, sizeof(void*)*13 + 10, v_printLibDir_1829_);
lean_ctor_set_uint8(v_reuseFailAlloc_1856_, sizeof(void*)*13 + 11, v_useStdin_1830_);
lean_ctor_set_uint8(v_reuseFailAlloc_1856_, sizeof(void*)*13 + 12, v_onlyDeps_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1856_, sizeof(void*)*13 + 13, v_onlySrcDeps_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1856_, sizeof(void*)*13 + 14, v_depsJson_1833_);
lean_ctor_set_uint32(v_reuseFailAlloc_1856_, sizeof(void*)*13, v_trustLevel_1835_);
lean_ctor_set_uint32(v_reuseFailAlloc_1856_, sizeof(void*)*13 + 4, v_numThreads_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1856_, sizeof(void*)*13 + 15, v_jsonOutput_1843_);
lean_ctor_set_uint8(v_reuseFailAlloc_1856_, sizeof(void*)*13 + 16, v_printStats_1845_);
lean_ctor_set_uint8(v_reuseFailAlloc_1856_, sizeof(void*)*13 + 17, v_run_1846_);
v___x_1854_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; 
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*13 + 9, v___x_1204_);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
}
}
}
else
{
lean_object* v_leanOpts_1858_; lean_object* v_forwardedArgs_1859_; uint8_t v_component_1860_; uint8_t v_printPrefix_1861_; uint8_t v_printLibDir_1862_; uint8_t v_useStdin_1863_; uint8_t v_onlyDeps_1864_; uint8_t v_onlySrcDeps_1865_; uint8_t v_depsJson_1866_; lean_object* v_opts_1867_; uint32_t v_trustLevel_1868_; uint32_t v_numThreads_1869_; lean_object* v_rootDir_x3f_1870_; lean_object* v_setupFileName_x3f_1871_; lean_object* v_oleanFileName_x3f_1872_; lean_object* v_ileanFileName_x3f_1873_; lean_object* v_cFileName_x3f_1874_; lean_object* v_bcFileName_x3f_1875_; uint8_t v_jsonOutput_1876_; lean_object* v_errorOnKinds_1877_; uint8_t v_run_1878_; lean_object* v_incrSaveFileName_x3f_1879_; lean_object* v_incrLoadFileName_x3f_1880_; lean_object* v_incrHeaderSaveFileName_x3f_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_optArg_x3f_935_);
v_leanOpts_1858_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1859_ = lean_ctor_get(v_opts_933_, 1);
v_component_1860_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1861_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1862_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1863_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1864_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1865_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1866_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1867_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1868_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1869_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1870_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1871_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1872_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1873_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1874_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1875_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1876_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1877_ = lean_ctor_get(v_opts_933_, 9);
v_run_1878_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1879_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1880_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1881_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1883_ = v_opts_933_;
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1881_);
lean_inc(v_incrLoadFileName_x3f_1880_);
lean_inc(v_incrSaveFileName_x3f_1879_);
lean_inc(v_errorOnKinds_1877_);
lean_inc(v_bcFileName_x3f_1875_);
lean_inc(v_cFileName_x3f_1874_);
lean_inc(v_ileanFileName_x3f_1873_);
lean_inc(v_oleanFileName_x3f_1872_);
lean_inc(v_setupFileName_x3f_1871_);
lean_inc(v_rootDir_x3f_1870_);
lean_inc(v_opts_1867_);
lean_inc(v_forwardedArgs_1859_);
lean_inc(v_leanOpts_1858_);
lean_dec(v_opts_933_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_leanOpts_1858_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_forwardedArgs_1859_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_opts_1867_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_rootDir_x3f_1870_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v_setupFileName_x3f_1871_);
lean_ctor_set(v_reuseFailAlloc_1888_, 5, v_oleanFileName_x3f_1872_);
lean_ctor_set(v_reuseFailAlloc_1888_, 6, v_ileanFileName_x3f_1873_);
lean_ctor_set(v_reuseFailAlloc_1888_, 7, v_cFileName_x3f_1874_);
lean_ctor_set(v_reuseFailAlloc_1888_, 8, v_bcFileName_x3f_1875_);
lean_ctor_set(v_reuseFailAlloc_1888_, 9, v_errorOnKinds_1877_);
lean_ctor_set(v_reuseFailAlloc_1888_, 10, v_incrSaveFileName_x3f_1879_);
lean_ctor_set(v_reuseFailAlloc_1888_, 11, v_incrLoadFileName_x3f_1880_);
lean_ctor_set(v_reuseFailAlloc_1888_, 12, v_incrHeaderSaveFileName_x3f_1881_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*13 + 8, v_component_1860_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*13 + 9, v_printPrefix_1861_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*13 + 10, v_printLibDir_1862_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*13 + 11, v_useStdin_1863_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*13 + 12, v_onlyDeps_1864_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*13 + 13, v_onlySrcDeps_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*13 + 14, v_depsJson_1866_);
lean_ctor_set_uint32(v_reuseFailAlloc_1888_, sizeof(void*)*13, v_trustLevel_1868_);
lean_ctor_set_uint32(v_reuseFailAlloc_1888_, sizeof(void*)*13 + 4, v_numThreads_1869_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*13 + 15, v_jsonOutput_1876_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*13 + 17, v_run_1878_);
v___x_1886_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; 
lean_ctor_set_uint8(v___x_1886_, sizeof(void*)*13 + 16, v___x_1202_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
}
}
}
else
{
lean_object* v_leanOpts_1890_; lean_object* v_forwardedArgs_1891_; uint8_t v_component_1892_; uint8_t v_printPrefix_1893_; uint8_t v_printLibDir_1894_; uint8_t v_useStdin_1895_; uint8_t v_onlyDeps_1896_; uint8_t v_onlySrcDeps_1897_; uint8_t v_depsJson_1898_; lean_object* v_opts_1899_; uint32_t v_trustLevel_1900_; uint32_t v_numThreads_1901_; lean_object* v_rootDir_x3f_1902_; lean_object* v_setupFileName_x3f_1903_; lean_object* v_oleanFileName_x3f_1904_; lean_object* v_ileanFileName_x3f_1905_; lean_object* v_cFileName_x3f_1906_; lean_object* v_bcFileName_x3f_1907_; lean_object* v_errorOnKinds_1908_; uint8_t v_printStats_1909_; uint8_t v_run_1910_; lean_object* v_incrSaveFileName_x3f_1911_; lean_object* v_incrLoadFileName_x3f_1912_; lean_object* v_incrHeaderSaveFileName_x3f_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v_optArg_x3f_935_);
v_leanOpts_1890_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1891_ = lean_ctor_get(v_opts_933_, 1);
v_component_1892_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1893_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1894_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1895_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1896_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1897_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1898_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1899_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1900_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1901_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1902_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1903_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1904_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1905_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1906_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1907_ = lean_ctor_get(v_opts_933_, 8);
v_errorOnKinds_1908_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1909_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1910_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1911_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1912_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1913_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1915_ = v_opts_933_;
v_isShared_1916_ = v_isSharedCheck_1921_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1913_);
lean_inc(v_incrLoadFileName_x3f_1912_);
lean_inc(v_incrSaveFileName_x3f_1911_);
lean_inc(v_errorOnKinds_1908_);
lean_inc(v_bcFileName_x3f_1907_);
lean_inc(v_cFileName_x3f_1906_);
lean_inc(v_ileanFileName_x3f_1905_);
lean_inc(v_oleanFileName_x3f_1904_);
lean_inc(v_setupFileName_x3f_1903_);
lean_inc(v_rootDir_x3f_1902_);
lean_inc(v_opts_1899_);
lean_inc(v_forwardedArgs_1891_);
lean_inc(v_leanOpts_1890_);
lean_dec(v_opts_933_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1921_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_leanOpts_1890_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_forwardedArgs_1891_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_opts_1899_);
lean_ctor_set(v_reuseFailAlloc_1920_, 3, v_rootDir_x3f_1902_);
lean_ctor_set(v_reuseFailAlloc_1920_, 4, v_setupFileName_x3f_1903_);
lean_ctor_set(v_reuseFailAlloc_1920_, 5, v_oleanFileName_x3f_1904_);
lean_ctor_set(v_reuseFailAlloc_1920_, 6, v_ileanFileName_x3f_1905_);
lean_ctor_set(v_reuseFailAlloc_1920_, 7, v_cFileName_x3f_1906_);
lean_ctor_set(v_reuseFailAlloc_1920_, 8, v_bcFileName_x3f_1907_);
lean_ctor_set(v_reuseFailAlloc_1920_, 9, v_errorOnKinds_1908_);
lean_ctor_set(v_reuseFailAlloc_1920_, 10, v_incrSaveFileName_x3f_1911_);
lean_ctor_set(v_reuseFailAlloc_1920_, 11, v_incrLoadFileName_x3f_1912_);
lean_ctor_set(v_reuseFailAlloc_1920_, 12, v_incrHeaderSaveFileName_x3f_1913_);
lean_ctor_set_uint8(v_reuseFailAlloc_1920_, sizeof(void*)*13 + 8, v_component_1892_);
lean_ctor_set_uint8(v_reuseFailAlloc_1920_, sizeof(void*)*13 + 9, v_printPrefix_1893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1920_, sizeof(void*)*13 + 10, v_printLibDir_1894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1920_, sizeof(void*)*13 + 11, v_useStdin_1895_);
lean_ctor_set_uint8(v_reuseFailAlloc_1920_, sizeof(void*)*13 + 12, v_onlyDeps_1896_);
lean_ctor_set_uint8(v_reuseFailAlloc_1920_, sizeof(void*)*13 + 13, v_onlySrcDeps_1897_);
lean_ctor_set_uint8(v_reuseFailAlloc_1920_, sizeof(void*)*13 + 14, v_depsJson_1898_);
lean_ctor_set_uint32(v_reuseFailAlloc_1920_, sizeof(void*)*13, v_trustLevel_1900_);
lean_ctor_set_uint32(v_reuseFailAlloc_1920_, sizeof(void*)*13 + 4, v_numThreads_1901_);
lean_ctor_set_uint8(v_reuseFailAlloc_1920_, sizeof(void*)*13 + 16, v_printStats_1909_);
lean_ctor_set_uint8(v_reuseFailAlloc_1920_, sizeof(void*)*13 + 17, v_run_1910_);
v___x_1918_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; 
lean_ctor_set_uint8(v___x_1918_, sizeof(void*)*13 + 15, v___x_1200_);
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_leanOpts_1922_; lean_object* v_forwardedArgs_1923_; uint8_t v_component_1924_; uint8_t v_printPrefix_1925_; uint8_t v_printLibDir_1926_; uint8_t v_useStdin_1927_; uint8_t v_onlySrcDeps_1928_; lean_object* v_opts_1929_; uint32_t v_trustLevel_1930_; uint32_t v_numThreads_1931_; lean_object* v_rootDir_x3f_1932_; lean_object* v_setupFileName_x3f_1933_; lean_object* v_oleanFileName_x3f_1934_; lean_object* v_ileanFileName_x3f_1935_; lean_object* v_cFileName_x3f_1936_; lean_object* v_bcFileName_x3f_1937_; uint8_t v_jsonOutput_1938_; lean_object* v_errorOnKinds_1939_; uint8_t v_printStats_1940_; uint8_t v_run_1941_; lean_object* v_incrSaveFileName_x3f_1942_; lean_object* v_incrLoadFileName_x3f_1943_; lean_object* v_incrHeaderSaveFileName_x3f_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v_optArg_x3f_935_);
v_leanOpts_1922_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1923_ = lean_ctor_get(v_opts_933_, 1);
v_component_1924_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1925_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1926_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1927_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1928_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_opts_1929_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1930_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1931_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1932_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1933_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1934_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1935_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1936_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1937_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1938_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1939_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1940_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1941_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1942_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1943_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1944_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1946_ = v_opts_933_;
v_isShared_1947_ = v_isSharedCheck_1952_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1944_);
lean_inc(v_incrLoadFileName_x3f_1943_);
lean_inc(v_incrSaveFileName_x3f_1942_);
lean_inc(v_errorOnKinds_1939_);
lean_inc(v_bcFileName_x3f_1937_);
lean_inc(v_cFileName_x3f_1936_);
lean_inc(v_ileanFileName_x3f_1935_);
lean_inc(v_oleanFileName_x3f_1934_);
lean_inc(v_setupFileName_x3f_1933_);
lean_inc(v_rootDir_x3f_1932_);
lean_inc(v_opts_1929_);
lean_inc(v_forwardedArgs_1923_);
lean_inc(v_leanOpts_1922_);
lean_dec(v_opts_933_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1952_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_leanOpts_1922_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_forwardedArgs_1923_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v_opts_1929_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v_rootDir_x3f_1932_);
lean_ctor_set(v_reuseFailAlloc_1951_, 4, v_setupFileName_x3f_1933_);
lean_ctor_set(v_reuseFailAlloc_1951_, 5, v_oleanFileName_x3f_1934_);
lean_ctor_set(v_reuseFailAlloc_1951_, 6, v_ileanFileName_x3f_1935_);
lean_ctor_set(v_reuseFailAlloc_1951_, 7, v_cFileName_x3f_1936_);
lean_ctor_set(v_reuseFailAlloc_1951_, 8, v_bcFileName_x3f_1937_);
lean_ctor_set(v_reuseFailAlloc_1951_, 9, v_errorOnKinds_1939_);
lean_ctor_set(v_reuseFailAlloc_1951_, 10, v_incrSaveFileName_x3f_1942_);
lean_ctor_set(v_reuseFailAlloc_1951_, 11, v_incrLoadFileName_x3f_1943_);
lean_ctor_set(v_reuseFailAlloc_1951_, 12, v_incrHeaderSaveFileName_x3f_1944_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*13 + 8, v_component_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*13 + 9, v_printPrefix_1925_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*13 + 10, v_printLibDir_1926_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*13 + 11, v_useStdin_1927_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*13 + 13, v_onlySrcDeps_1928_);
lean_ctor_set_uint32(v_reuseFailAlloc_1951_, sizeof(void*)*13, v_trustLevel_1930_);
lean_ctor_set_uint32(v_reuseFailAlloc_1951_, sizeof(void*)*13 + 4, v_numThreads_1931_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*13 + 15, v_jsonOutput_1938_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*13 + 16, v_printStats_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*13 + 17, v_run_1941_);
v___x_1949_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; 
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*13 + 12, v___x_1198_);
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*13 + 14, v___x_1198_);
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
return v___x_1950_;
}
}
}
}
else
{
lean_object* v_leanOpts_1953_; lean_object* v_forwardedArgs_1954_; uint8_t v_component_1955_; uint8_t v_printPrefix_1956_; uint8_t v_printLibDir_1957_; uint8_t v_useStdin_1958_; uint8_t v_onlyDeps_1959_; uint8_t v_depsJson_1960_; lean_object* v_opts_1961_; uint32_t v_trustLevel_1962_; uint32_t v_numThreads_1963_; lean_object* v_rootDir_x3f_1964_; lean_object* v_setupFileName_x3f_1965_; lean_object* v_oleanFileName_x3f_1966_; lean_object* v_ileanFileName_x3f_1967_; lean_object* v_cFileName_x3f_1968_; lean_object* v_bcFileName_x3f_1969_; uint8_t v_jsonOutput_1970_; lean_object* v_errorOnKinds_1971_; uint8_t v_printStats_1972_; uint8_t v_run_1973_; lean_object* v_incrSaveFileName_x3f_1974_; lean_object* v_incrLoadFileName_x3f_1975_; lean_object* v_incrHeaderSaveFileName_x3f_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1984_; 
lean_dec(v_optArg_x3f_935_);
v_leanOpts_1953_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1954_ = lean_ctor_get(v_opts_933_, 1);
v_component_1955_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1956_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1957_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1958_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_1959_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_depsJson_1960_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1961_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1962_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1963_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1964_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1965_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1966_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1967_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_1968_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_1969_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_1970_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_1971_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_1972_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_1973_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1974_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_1975_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_1976_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1978_ = v_opts_933_;
v_isShared_1979_ = v_isSharedCheck_1984_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1976_);
lean_inc(v_incrLoadFileName_x3f_1975_);
lean_inc(v_incrSaveFileName_x3f_1974_);
lean_inc(v_errorOnKinds_1971_);
lean_inc(v_bcFileName_x3f_1969_);
lean_inc(v_cFileName_x3f_1968_);
lean_inc(v_ileanFileName_x3f_1967_);
lean_inc(v_oleanFileName_x3f_1966_);
lean_inc(v_setupFileName_x3f_1965_);
lean_inc(v_rootDir_x3f_1964_);
lean_inc(v_opts_1961_);
lean_inc(v_forwardedArgs_1954_);
lean_inc(v_leanOpts_1953_);
lean_dec(v_opts_933_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1984_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_leanOpts_1953_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_forwardedArgs_1954_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_opts_1961_);
lean_ctor_set(v_reuseFailAlloc_1983_, 3, v_rootDir_x3f_1964_);
lean_ctor_set(v_reuseFailAlloc_1983_, 4, v_setupFileName_x3f_1965_);
lean_ctor_set(v_reuseFailAlloc_1983_, 5, v_oleanFileName_x3f_1966_);
lean_ctor_set(v_reuseFailAlloc_1983_, 6, v_ileanFileName_x3f_1967_);
lean_ctor_set(v_reuseFailAlloc_1983_, 7, v_cFileName_x3f_1968_);
lean_ctor_set(v_reuseFailAlloc_1983_, 8, v_bcFileName_x3f_1969_);
lean_ctor_set(v_reuseFailAlloc_1983_, 9, v_errorOnKinds_1971_);
lean_ctor_set(v_reuseFailAlloc_1983_, 10, v_incrSaveFileName_x3f_1974_);
lean_ctor_set(v_reuseFailAlloc_1983_, 11, v_incrLoadFileName_x3f_1975_);
lean_ctor_set(v_reuseFailAlloc_1983_, 12, v_incrHeaderSaveFileName_x3f_1976_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*13 + 8, v_component_1955_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*13 + 9, v_printPrefix_1956_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*13 + 10, v_printLibDir_1957_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*13 + 11, v_useStdin_1958_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*13 + 12, v_onlyDeps_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*13 + 14, v_depsJson_1960_);
lean_ctor_set_uint32(v_reuseFailAlloc_1983_, sizeof(void*)*13, v_trustLevel_1962_);
lean_ctor_set_uint32(v_reuseFailAlloc_1983_, sizeof(void*)*13 + 4, v_numThreads_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*13 + 15, v_jsonOutput_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*13 + 16, v_printStats_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*13 + 17, v_run_1973_);
v___x_1981_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; 
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*13 + 13, v___x_1196_);
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
return v___x_1982_;
}
}
}
}
else
{
lean_object* v_leanOpts_1985_; lean_object* v_forwardedArgs_1986_; uint8_t v_component_1987_; uint8_t v_printPrefix_1988_; uint8_t v_printLibDir_1989_; uint8_t v_useStdin_1990_; uint8_t v_onlySrcDeps_1991_; uint8_t v_depsJson_1992_; lean_object* v_opts_1993_; uint32_t v_trustLevel_1994_; uint32_t v_numThreads_1995_; lean_object* v_rootDir_x3f_1996_; lean_object* v_setupFileName_x3f_1997_; lean_object* v_oleanFileName_x3f_1998_; lean_object* v_ileanFileName_x3f_1999_; lean_object* v_cFileName_x3f_2000_; lean_object* v_bcFileName_x3f_2001_; uint8_t v_jsonOutput_2002_; lean_object* v_errorOnKinds_2003_; uint8_t v_printStats_2004_; uint8_t v_run_2005_; lean_object* v_incrSaveFileName_x3f_2006_; lean_object* v_incrLoadFileName_x3f_2007_; lean_object* v_incrHeaderSaveFileName_x3f_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_optArg_x3f_935_);
v_leanOpts_1985_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_1986_ = lean_ctor_get(v_opts_933_, 1);
v_component_1987_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_1988_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_1989_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_1990_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1991_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_1992_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_1993_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_1994_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_1995_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1996_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_1997_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_1998_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_1999_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_2000_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_2001_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_2002_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2003_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2004_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_2005_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2006_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2007_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2008_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2010_ = v_opts_933_;
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2008_);
lean_inc(v_incrLoadFileName_x3f_2007_);
lean_inc(v_incrSaveFileName_x3f_2006_);
lean_inc(v_errorOnKinds_2003_);
lean_inc(v_bcFileName_x3f_2001_);
lean_inc(v_cFileName_x3f_2000_);
lean_inc(v_ileanFileName_x3f_1999_);
lean_inc(v_oleanFileName_x3f_1998_);
lean_inc(v_setupFileName_x3f_1997_);
lean_inc(v_rootDir_x3f_1996_);
lean_inc(v_opts_1993_);
lean_inc(v_forwardedArgs_1986_);
lean_inc(v_leanOpts_1985_);
lean_dec(v_opts_933_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_leanOpts_1985_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_forwardedArgs_1986_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_opts_1993_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_rootDir_x3f_1996_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v_setupFileName_x3f_1997_);
lean_ctor_set(v_reuseFailAlloc_2015_, 5, v_oleanFileName_x3f_1998_);
lean_ctor_set(v_reuseFailAlloc_2015_, 6, v_ileanFileName_x3f_1999_);
lean_ctor_set(v_reuseFailAlloc_2015_, 7, v_cFileName_x3f_2000_);
lean_ctor_set(v_reuseFailAlloc_2015_, 8, v_bcFileName_x3f_2001_);
lean_ctor_set(v_reuseFailAlloc_2015_, 9, v_errorOnKinds_2003_);
lean_ctor_set(v_reuseFailAlloc_2015_, 10, v_incrSaveFileName_x3f_2006_);
lean_ctor_set(v_reuseFailAlloc_2015_, 11, v_incrLoadFileName_x3f_2007_);
lean_ctor_set(v_reuseFailAlloc_2015_, 12, v_incrHeaderSaveFileName_x3f_2008_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*13 + 8, v_component_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*13 + 9, v_printPrefix_1988_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*13 + 10, v_printLibDir_1989_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*13 + 11, v_useStdin_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*13 + 13, v_onlySrcDeps_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*13 + 14, v_depsJson_1992_);
lean_ctor_set_uint32(v_reuseFailAlloc_2015_, sizeof(void*)*13, v_trustLevel_1994_);
lean_ctor_set_uint32(v_reuseFailAlloc_2015_, sizeof(void*)*13 + 4, v_numThreads_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*13 + 15, v_jsonOutput_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*13 + 16, v_printStats_2004_);
lean_ctor_set_uint8(v_reuseFailAlloc_2015_, sizeof(void*)*13 + 17, v_run_2005_);
v___x_2013_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2014_; 
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*13 + 12, v___x_1194_);
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
return v___x_2014_;
}
}
}
}
else
{
lean_object* v_leanOpts_2017_; lean_object* v_forwardedArgs_2018_; uint8_t v_component_2019_; uint8_t v_printPrefix_2020_; uint8_t v_printLibDir_2021_; uint8_t v_useStdin_2022_; uint8_t v_onlyDeps_2023_; uint8_t v_onlySrcDeps_2024_; uint8_t v_depsJson_2025_; lean_object* v_opts_2026_; uint32_t v_trustLevel_2027_; uint32_t v_numThreads_2028_; lean_object* v_rootDir_x3f_2029_; lean_object* v_setupFileName_x3f_2030_; lean_object* v_oleanFileName_x3f_2031_; lean_object* v_ileanFileName_x3f_2032_; lean_object* v_cFileName_x3f_2033_; lean_object* v_bcFileName_x3f_2034_; uint8_t v_jsonOutput_2035_; lean_object* v_errorOnKinds_2036_; uint8_t v_printStats_2037_; uint8_t v_run_2038_; lean_object* v_incrSaveFileName_x3f_2039_; lean_object* v_incrLoadFileName_x3f_2040_; lean_object* v_incrHeaderSaveFileName_x3f_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v_optArg_x3f_935_);
v_leanOpts_2017_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_2018_ = lean_ctor_get(v_opts_933_, 1);
v_component_2019_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_2020_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_2021_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_2022_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_2023_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2024_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_2025_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_2026_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_2027_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_2028_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2029_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_2030_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_2031_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_2032_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_2033_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_2034_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_2035_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2036_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2037_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_2038_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2039_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2040_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2041_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2043_ = v_opts_933_;
v_isShared_2044_ = v_isSharedCheck_2051_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2041_);
lean_inc(v_incrLoadFileName_x3f_2040_);
lean_inc(v_incrSaveFileName_x3f_2039_);
lean_inc(v_errorOnKinds_2036_);
lean_inc(v_bcFileName_x3f_2034_);
lean_inc(v_cFileName_x3f_2033_);
lean_inc(v_ileanFileName_x3f_2032_);
lean_inc(v_oleanFileName_x3f_2031_);
lean_inc(v_setupFileName_x3f_2030_);
lean_inc(v_rootDir_x3f_2029_);
lean_inc(v_opts_2026_);
lean_inc(v_forwardedArgs_2018_);
lean_inc(v_leanOpts_2017_);
lean_dec(v_opts_933_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2051_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2045_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_2046_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2017_, v___x_2045_, v___x_1190_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2046_);
v___x_2048_ = v___x_2043_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_forwardedArgs_2018_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_opts_2026_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_rootDir_x3f_2029_);
lean_ctor_set(v_reuseFailAlloc_2050_, 4, v_setupFileName_x3f_2030_);
lean_ctor_set(v_reuseFailAlloc_2050_, 5, v_oleanFileName_x3f_2031_);
lean_ctor_set(v_reuseFailAlloc_2050_, 6, v_ileanFileName_x3f_2032_);
lean_ctor_set(v_reuseFailAlloc_2050_, 7, v_cFileName_x3f_2033_);
lean_ctor_set(v_reuseFailAlloc_2050_, 8, v_bcFileName_x3f_2034_);
lean_ctor_set(v_reuseFailAlloc_2050_, 9, v_errorOnKinds_2036_);
lean_ctor_set(v_reuseFailAlloc_2050_, 10, v_incrSaveFileName_x3f_2039_);
lean_ctor_set(v_reuseFailAlloc_2050_, 11, v_incrLoadFileName_x3f_2040_);
lean_ctor_set(v_reuseFailAlloc_2050_, 12, v_incrHeaderSaveFileName_x3f_2041_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 8, v_component_2019_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 9, v_printPrefix_2020_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 10, v_printLibDir_2021_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 11, v_useStdin_2022_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 12, v_onlyDeps_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 13, v_onlySrcDeps_2024_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 14, v_depsJson_2025_);
lean_ctor_set_uint32(v_reuseFailAlloc_2050_, sizeof(void*)*13, v_trustLevel_2027_);
lean_ctor_set_uint32(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 4, v_numThreads_2028_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 15, v_jsonOutput_2035_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 16, v_printStats_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2050_, sizeof(void*)*13 + 17, v_run_2038_);
v___x_2048_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
return v___x_2049_;
}
}
}
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_2053_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2052_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2107_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2107_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2107_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = lean_string_utf8_byte_size(v_a_2054_);
lean_inc(v_a_2054_);
v___x_2060_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2060_, 0, v_a_2054_);
lean_ctor_set(v___x_2060_, 1, v___x_2058_);
lean_ctor_set(v___x_2060_, 2, v___x_2059_);
v___x_2061_ = l_String_Slice_toNat_x3f(v___x_2060_);
lean_dec_ref_known(v___x_2060_, 3);
if (lean_obj_tag(v___x_2061_) == 1)
{
lean_object* v_val_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_val_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_val_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = lean_cstr_to_nat("4294967296");
v___x_2064_ = lean_nat_dec_lt(v_val_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec(v_val_2062_);
lean_del_object(v___x_2056_);
lean_dec(v_a_2054_);
lean_dec_ref(v_opts_933_);
v___x_2065_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_2066_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2065_);
lean_dec_ref(v___x_2066_);
goto v___jp_997_;
}
else
{
lean_object* v_leanOpts_2067_; lean_object* v_forwardedArgs_2068_; uint8_t v_component_2069_; uint8_t v_printPrefix_2070_; uint8_t v_printLibDir_2071_; uint8_t v_useStdin_2072_; uint8_t v_onlyDeps_2073_; uint8_t v_onlySrcDeps_2074_; uint8_t v_depsJson_2075_; lean_object* v_opts_2076_; uint32_t v_numThreads_2077_; lean_object* v_rootDir_x3f_2078_; lean_object* v_setupFileName_x3f_2079_; lean_object* v_oleanFileName_x3f_2080_; lean_object* v_ileanFileName_x3f_2081_; lean_object* v_cFileName_x3f_2082_; lean_object* v_bcFileName_x3f_2083_; uint8_t v_jsonOutput_2084_; lean_object* v_errorOnKinds_2085_; uint8_t v_printStats_2086_; uint8_t v_run_2087_; lean_object* v_incrSaveFileName_x3f_2088_; lean_object* v_incrLoadFileName_x3f_2089_; lean_object* v_incrHeaderSaveFileName_x3f_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2104_; 
v_leanOpts_2067_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_2068_ = lean_ctor_get(v_opts_933_, 1);
v_component_2069_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_2070_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_2071_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_2072_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_2073_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2074_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_2075_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_2076_ = lean_ctor_get(v_opts_933_, 2);
v_numThreads_2077_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2078_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_2079_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_2080_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_2081_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_2082_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_2083_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_2084_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2085_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2086_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_2087_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2088_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2089_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2090_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2092_ = v_opts_933_;
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2090_);
lean_inc(v_incrLoadFileName_x3f_2089_);
lean_inc(v_incrSaveFileName_x3f_2088_);
lean_inc(v_errorOnKinds_2085_);
lean_inc(v_bcFileName_x3f_2083_);
lean_inc(v_cFileName_x3f_2082_);
lean_inc(v_ileanFileName_x3f_2081_);
lean_inc(v_oleanFileName_x3f_2080_);
lean_inc(v_setupFileName_x3f_2079_);
lean_inc(v_rootDir_x3f_2078_);
lean_inc(v_opts_2076_);
lean_inc(v_forwardedArgs_2068_);
lean_inc(v_leanOpts_2067_);
lean_dec(v_opts_933_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
uint32_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2094_ = lean_uint32_of_nat(v_val_2062_);
lean_dec(v_val_2062_);
v___x_2095_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_2096_ = lean_string_append(v___x_2095_, v_a_2054_);
lean_dec(v_a_2054_);
v___x_2097_ = lean_array_push(v_forwardedArgs_2068_, v___x_2096_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v___x_2097_);
v___x_2099_ = v___x_2092_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_leanOpts_2067_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_opts_2076_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_rootDir_x3f_2078_);
lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_setupFileName_x3f_2079_);
lean_ctor_set(v_reuseFailAlloc_2103_, 5, v_oleanFileName_x3f_2080_);
lean_ctor_set(v_reuseFailAlloc_2103_, 6, v_ileanFileName_x3f_2081_);
lean_ctor_set(v_reuseFailAlloc_2103_, 7, v_cFileName_x3f_2082_);
lean_ctor_set(v_reuseFailAlloc_2103_, 8, v_bcFileName_x3f_2083_);
lean_ctor_set(v_reuseFailAlloc_2103_, 9, v_errorOnKinds_2085_);
lean_ctor_set(v_reuseFailAlloc_2103_, 10, v_incrSaveFileName_x3f_2088_);
lean_ctor_set(v_reuseFailAlloc_2103_, 11, v_incrLoadFileName_x3f_2089_);
lean_ctor_set(v_reuseFailAlloc_2103_, 12, v_incrHeaderSaveFileName_x3f_2090_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 8, v_component_2069_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 9, v_printPrefix_2070_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 10, v_printLibDir_2071_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 11, v_useStdin_2072_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 12, v_onlyDeps_2073_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 13, v_onlySrcDeps_2074_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 14, v_depsJson_2075_);
lean_ctor_set_uint32(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 4, v_numThreads_2077_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 15, v_jsonOutput_2084_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 16, v_printStats_2086_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 17, v_run_2087_);
v___x_2099_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2101_; 
lean_ctor_set_uint32(v___x_2099_, sizeof(void*)*13, v___x_2094_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2099_);
v___x_2101_ = v___x_2056_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
lean_dec(v___x_2061_);
lean_del_object(v___x_2056_);
lean_dec(v_a_2054_);
lean_dec_ref(v_opts_933_);
v___x_2105_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_2106_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2105_);
lean_dec_ref(v___x_2106_);
goto v___jp_994_;
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec_ref(v_opts_933_);
v_a_2108_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2053_, 1);
v___x_2112_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2113_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2112_);
lean_dec_ref(v___x_2113_);
goto v___jp_2109_;
v___jp_2109_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_io_error_to_string(v_a_2108_);
v___x_2111_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2110_);
lean_dec_ref(v___x_2111_);
goto v___jp_1003_;
}
}
}
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_2115_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2114_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2167_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2167_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2167_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = lean_string_utf8_byte_size(v_a_2116_);
lean_inc(v_a_2116_);
v___x_2122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2122_, 0, v_a_2116_);
lean_ctor_set(v___x_2122_, 1, v___x_2120_);
lean_ctor_set(v___x_2122_, 2, v___x_2121_);
v___x_2123_ = l_String_Slice_toNat_x3f(v___x_2122_);
lean_dec_ref_known(v___x_2122_, 3);
if (lean_obj_tag(v___x_2123_) == 1)
{
lean_object* v_val_2124_; lean_object* v_leanOpts_2125_; lean_object* v_forwardedArgs_2126_; uint8_t v_component_2127_; uint8_t v_printPrefix_2128_; uint8_t v_printLibDir_2129_; uint8_t v_useStdin_2130_; uint8_t v_onlyDeps_2131_; uint8_t v_onlySrcDeps_2132_; uint8_t v_depsJson_2133_; lean_object* v_opts_2134_; uint32_t v_trustLevel_2135_; uint32_t v_numThreads_2136_; lean_object* v_rootDir_x3f_2137_; lean_object* v_setupFileName_x3f_2138_; lean_object* v_oleanFileName_x3f_2139_; lean_object* v_ileanFileName_x3f_2140_; lean_object* v_cFileName_x3f_2141_; lean_object* v_bcFileName_x3f_2142_; uint8_t v_jsonOutput_2143_; lean_object* v_errorOnKinds_2144_; uint8_t v_printStats_2145_; uint8_t v_run_2146_; lean_object* v_incrSaveFileName_x3f_2147_; lean_object* v_incrLoadFileName_x3f_2148_; lean_object* v_incrHeaderSaveFileName_x3f_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2164_; 
v_val_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_val_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v_leanOpts_2125_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_2126_ = lean_ctor_get(v_opts_933_, 1);
v_component_2127_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_2128_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_2129_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_2130_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_2131_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2132_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_2133_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_2134_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_2135_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_2136_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2137_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_2138_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_2139_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_2140_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_2141_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_2142_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_2143_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2144_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2145_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_2146_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2147_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2148_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2149_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2151_ = v_opts_933_;
v_isShared_2152_ = v_isSharedCheck_2164_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2149_);
lean_inc(v_incrLoadFileName_x3f_2148_);
lean_inc(v_incrSaveFileName_x3f_2147_);
lean_inc(v_errorOnKinds_2144_);
lean_inc(v_bcFileName_x3f_2142_);
lean_inc(v_cFileName_x3f_2141_);
lean_inc(v_ileanFileName_x3f_2140_);
lean_inc(v_oleanFileName_x3f_2139_);
lean_inc(v_setupFileName_x3f_2138_);
lean_inc(v_rootDir_x3f_2137_);
lean_inc(v_opts_2134_);
lean_inc(v_forwardedArgs_2126_);
lean_inc(v_leanOpts_2125_);
lean_dec(v_opts_933_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2164_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2153_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_2154_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2125_, v___x_2153_, v_val_2124_);
v___x_2155_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_2156_ = lean_string_append(v___x_2155_, v_a_2116_);
lean_dec(v_a_2116_);
v___x_2157_ = lean_array_push(v_forwardedArgs_2126_, v___x_2156_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v___x_2157_);
lean_ctor_set(v___x_2151_, 0, v___x_2154_);
v___x_2159_ = v___x_2151_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_opts_2134_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_rootDir_x3f_2137_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_setupFileName_x3f_2138_);
lean_ctor_set(v_reuseFailAlloc_2163_, 5, v_oleanFileName_x3f_2139_);
lean_ctor_set(v_reuseFailAlloc_2163_, 6, v_ileanFileName_x3f_2140_);
lean_ctor_set(v_reuseFailAlloc_2163_, 7, v_cFileName_x3f_2141_);
lean_ctor_set(v_reuseFailAlloc_2163_, 8, v_bcFileName_x3f_2142_);
lean_ctor_set(v_reuseFailAlloc_2163_, 9, v_errorOnKinds_2144_);
lean_ctor_set(v_reuseFailAlloc_2163_, 10, v_incrSaveFileName_x3f_2147_);
lean_ctor_set(v_reuseFailAlloc_2163_, 11, v_incrLoadFileName_x3f_2148_);
lean_ctor_set(v_reuseFailAlloc_2163_, 12, v_incrHeaderSaveFileName_x3f_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 8, v_component_2127_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 9, v_printPrefix_2128_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 10, v_printLibDir_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 11, v_useStdin_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 12, v_onlyDeps_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 13, v_onlySrcDeps_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 14, v_depsJson_2133_);
lean_ctor_set_uint32(v_reuseFailAlloc_2163_, sizeof(void*)*13, v_trustLevel_2135_);
lean_ctor_set_uint32(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 4, v_numThreads_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 15, v_jsonOutput_2143_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 16, v_printStats_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 17, v_run_2146_);
v___x_2159_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2161_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2159_);
v___x_2161_ = v___x_2118_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v___x_2123_);
lean_del_object(v___x_2118_);
lean_dec(v_a_2116_);
lean_dec_ref(v_opts_933_);
v___x_2165_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_2166_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2165_);
lean_dec_ref(v___x_2166_);
goto v___jp_1110_;
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec_ref(v_opts_933_);
v_a_2168_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2115_, 1);
v___x_2172_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2173_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2172_);
lean_dec_ref(v___x_2173_);
goto v___jp_2169_;
v___jp_2169_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = lean_io_error_to_string(v_a_2168_);
v___x_2171_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2170_);
lean_dec_ref(v___x_2171_);
goto v___jp_1116_;
}
}
}
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_2175_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2174_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2227_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2227_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2227_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2180_ = lean_unsigned_to_nat(0u);
v___x_2181_ = lean_string_utf8_byte_size(v_a_2176_);
lean_inc(v_a_2176_);
v___x_2182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2182_, 0, v_a_2176_);
lean_ctor_set(v___x_2182_, 1, v___x_2180_);
lean_ctor_set(v___x_2182_, 2, v___x_2181_);
v___x_2183_ = l_String_Slice_toNat_x3f(v___x_2182_);
lean_dec_ref_known(v___x_2182_, 3);
if (lean_obj_tag(v___x_2183_) == 1)
{
lean_object* v_val_2184_; lean_object* v_leanOpts_2185_; lean_object* v_forwardedArgs_2186_; uint8_t v_component_2187_; uint8_t v_printPrefix_2188_; uint8_t v_printLibDir_2189_; uint8_t v_useStdin_2190_; uint8_t v_onlyDeps_2191_; uint8_t v_onlySrcDeps_2192_; uint8_t v_depsJson_2193_; lean_object* v_opts_2194_; uint32_t v_trustLevel_2195_; uint32_t v_numThreads_2196_; lean_object* v_rootDir_x3f_2197_; lean_object* v_setupFileName_x3f_2198_; lean_object* v_oleanFileName_x3f_2199_; lean_object* v_ileanFileName_x3f_2200_; lean_object* v_cFileName_x3f_2201_; lean_object* v_bcFileName_x3f_2202_; uint8_t v_jsonOutput_2203_; lean_object* v_errorOnKinds_2204_; uint8_t v_printStats_2205_; uint8_t v_run_2206_; lean_object* v_incrSaveFileName_x3f_2207_; lean_object* v_incrLoadFileName_x3f_2208_; lean_object* v_incrHeaderSaveFileName_x3f_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2224_; 
v_val_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v_leanOpts_2185_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_2186_ = lean_ctor_get(v_opts_933_, 1);
v_component_2187_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_2188_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_2189_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_2190_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_2191_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2192_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_2193_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_2194_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_2195_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_2196_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2197_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_2198_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_2199_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_2200_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_2201_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_2202_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_2203_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2204_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2205_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_2206_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2207_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2208_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2209_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2211_ = v_opts_933_;
v_isShared_2212_ = v_isSharedCheck_2224_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2209_);
lean_inc(v_incrLoadFileName_x3f_2208_);
lean_inc(v_incrSaveFileName_x3f_2207_);
lean_inc(v_errorOnKinds_2204_);
lean_inc(v_bcFileName_x3f_2202_);
lean_inc(v_cFileName_x3f_2201_);
lean_inc(v_ileanFileName_x3f_2200_);
lean_inc(v_oleanFileName_x3f_2199_);
lean_inc(v_setupFileName_x3f_2198_);
lean_inc(v_rootDir_x3f_2197_);
lean_inc(v_opts_2194_);
lean_inc(v_forwardedArgs_2186_);
lean_inc(v_leanOpts_2185_);
lean_dec(v_opts_933_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2224_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2213_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_2214_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2185_, v___x_2213_, v_val_2184_);
v___x_2215_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2216_ = lean_string_append(v___x_2215_, v_a_2176_);
lean_dec(v_a_2176_);
v___x_2217_ = lean_array_push(v_forwardedArgs_2186_, v___x_2216_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 1, v___x_2217_);
lean_ctor_set(v___x_2211_, 0, v___x_2214_);
v___x_2219_ = v___x_2211_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_opts_2194_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v_rootDir_x3f_2197_);
lean_ctor_set(v_reuseFailAlloc_2223_, 4, v_setupFileName_x3f_2198_);
lean_ctor_set(v_reuseFailAlloc_2223_, 5, v_oleanFileName_x3f_2199_);
lean_ctor_set(v_reuseFailAlloc_2223_, 6, v_ileanFileName_x3f_2200_);
lean_ctor_set(v_reuseFailAlloc_2223_, 7, v_cFileName_x3f_2201_);
lean_ctor_set(v_reuseFailAlloc_2223_, 8, v_bcFileName_x3f_2202_);
lean_ctor_set(v_reuseFailAlloc_2223_, 9, v_errorOnKinds_2204_);
lean_ctor_set(v_reuseFailAlloc_2223_, 10, v_incrSaveFileName_x3f_2207_);
lean_ctor_set(v_reuseFailAlloc_2223_, 11, v_incrLoadFileName_x3f_2208_);
lean_ctor_set(v_reuseFailAlloc_2223_, 12, v_incrHeaderSaveFileName_x3f_2209_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, sizeof(void*)*13 + 8, v_component_2187_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, sizeof(void*)*13 + 9, v_printPrefix_2188_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, sizeof(void*)*13 + 10, v_printLibDir_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, sizeof(void*)*13 + 11, v_useStdin_2190_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, sizeof(void*)*13 + 12, v_onlyDeps_2191_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, sizeof(void*)*13 + 13, v_onlySrcDeps_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, sizeof(void*)*13 + 14, v_depsJson_2193_);
lean_ctor_set_uint32(v_reuseFailAlloc_2223_, sizeof(void*)*13, v_trustLevel_2195_);
lean_ctor_set_uint32(v_reuseFailAlloc_2223_, sizeof(void*)*13 + 4, v_numThreads_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, sizeof(void*)*13 + 15, v_jsonOutput_2203_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, sizeof(void*)*13 + 16, v_printStats_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2223_, sizeof(void*)*13 + 17, v_run_2206_);
v___x_2219_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2221_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2219_);
v___x_2221_ = v___x_2178_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec(v___x_2183_);
lean_del_object(v___x_2178_);
lean_dec(v_a_2176_);
lean_dec_ref(v_opts_933_);
v___x_2225_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2226_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2225_);
lean_dec_ref(v___x_2226_);
goto v___jp_985_;
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_dec_ref(v_opts_933_);
v_a_2228_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2232_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2233_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2232_);
lean_dec_ref(v___x_2233_);
goto v___jp_2229_;
v___jp_2229_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_io_error_to_string(v_a_2228_);
v___x_2231_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2230_);
lean_dec_ref(v___x_2231_);
goto v___jp_991_;
}
}
}
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2235_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2234_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2279_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2279_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2279_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v_leanOpts_2240_; lean_object* v_forwardedArgs_2241_; uint8_t v_component_2242_; uint8_t v_printPrefix_2243_; uint8_t v_printLibDir_2244_; uint8_t v_useStdin_2245_; uint8_t v_onlyDeps_2246_; uint8_t v_onlySrcDeps_2247_; uint8_t v_depsJson_2248_; lean_object* v_opts_2249_; uint32_t v_trustLevel_2250_; uint32_t v_numThreads_2251_; lean_object* v_setupFileName_x3f_2252_; lean_object* v_oleanFileName_x3f_2253_; lean_object* v_ileanFileName_x3f_2254_; lean_object* v_cFileName_x3f_2255_; lean_object* v_bcFileName_x3f_2256_; uint8_t v_jsonOutput_2257_; lean_object* v_errorOnKinds_2258_; uint8_t v_printStats_2259_; uint8_t v_run_2260_; lean_object* v_incrSaveFileName_x3f_2261_; lean_object* v_incrLoadFileName_x3f_2262_; lean_object* v_incrHeaderSaveFileName_x3f_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2277_; 
v_leanOpts_2240_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_2241_ = lean_ctor_get(v_opts_933_, 1);
v_component_2242_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_2243_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_2244_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_2245_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_2246_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2247_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_2248_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_2249_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_2250_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_2251_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_setupFileName_x3f_2252_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_2253_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_2254_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_2255_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_2256_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_2257_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2258_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2259_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_2260_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2261_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2262_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2263_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2277_ == 0)
{
lean_object* v_unused_2278_; 
v_unused_2278_ = lean_ctor_get(v_opts_933_, 3);
lean_dec(v_unused_2278_);
v___x_2265_ = v_opts_933_;
v_isShared_2266_ = v_isSharedCheck_2277_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2263_);
lean_inc(v_incrLoadFileName_x3f_2262_);
lean_inc(v_incrSaveFileName_x3f_2261_);
lean_inc(v_errorOnKinds_2258_);
lean_inc(v_bcFileName_x3f_2256_);
lean_inc(v_cFileName_x3f_2255_);
lean_inc(v_ileanFileName_x3f_2254_);
lean_inc(v_oleanFileName_x3f_2253_);
lean_inc(v_setupFileName_x3f_2252_);
lean_inc(v_opts_2249_);
lean_inc(v_forwardedArgs_2241_);
lean_inc(v_leanOpts_2240_);
lean_dec(v_opts_933_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2277_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2267_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2268_ = lean_string_append(v___x_2267_, v_a_2236_);
v___x_2269_ = lean_array_push(v_forwardedArgs_2241_, v___x_2268_);
v___x_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2270_, 0, v_a_2236_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 3, v___x_2270_);
lean_ctor_set(v___x_2265_, 1, v___x_2269_);
v___x_2272_ = v___x_2265_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_leanOpts_2240_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v___x_2269_);
lean_ctor_set(v_reuseFailAlloc_2276_, 2, v_opts_2249_);
lean_ctor_set(v_reuseFailAlloc_2276_, 3, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2276_, 4, v_setupFileName_x3f_2252_);
lean_ctor_set(v_reuseFailAlloc_2276_, 5, v_oleanFileName_x3f_2253_);
lean_ctor_set(v_reuseFailAlloc_2276_, 6, v_ileanFileName_x3f_2254_);
lean_ctor_set(v_reuseFailAlloc_2276_, 7, v_cFileName_x3f_2255_);
lean_ctor_set(v_reuseFailAlloc_2276_, 8, v_bcFileName_x3f_2256_);
lean_ctor_set(v_reuseFailAlloc_2276_, 9, v_errorOnKinds_2258_);
lean_ctor_set(v_reuseFailAlloc_2276_, 10, v_incrSaveFileName_x3f_2261_);
lean_ctor_set(v_reuseFailAlloc_2276_, 11, v_incrLoadFileName_x3f_2262_);
lean_ctor_set(v_reuseFailAlloc_2276_, 12, v_incrHeaderSaveFileName_x3f_2263_);
lean_ctor_set_uint8(v_reuseFailAlloc_2276_, sizeof(void*)*13 + 8, v_component_2242_);
lean_ctor_set_uint8(v_reuseFailAlloc_2276_, sizeof(void*)*13 + 9, v_printPrefix_2243_);
lean_ctor_set_uint8(v_reuseFailAlloc_2276_, sizeof(void*)*13 + 10, v_printLibDir_2244_);
lean_ctor_set_uint8(v_reuseFailAlloc_2276_, sizeof(void*)*13 + 11, v_useStdin_2245_);
lean_ctor_set_uint8(v_reuseFailAlloc_2276_, sizeof(void*)*13 + 12, v_onlyDeps_2246_);
lean_ctor_set_uint8(v_reuseFailAlloc_2276_, sizeof(void*)*13 + 13, v_onlySrcDeps_2247_);
lean_ctor_set_uint8(v_reuseFailAlloc_2276_, sizeof(void*)*13 + 14, v_depsJson_2248_);
lean_ctor_set_uint32(v_reuseFailAlloc_2276_, sizeof(void*)*13, v_trustLevel_2250_);
lean_ctor_set_uint32(v_reuseFailAlloc_2276_, sizeof(void*)*13 + 4, v_numThreads_2251_);
lean_ctor_set_uint8(v_reuseFailAlloc_2276_, sizeof(void*)*13 + 15, v_jsonOutput_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2276_, sizeof(void*)*13 + 16, v_printStats_2259_);
lean_ctor_set_uint8(v_reuseFailAlloc_2276_, sizeof(void*)*13 + 17, v_run_2260_);
v___x_2272_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2274_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2272_);
v___x_2274_ = v___x_2238_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec_ref(v_opts_933_);
v_a_2280_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2235_, 1);
v___x_2284_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2285_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2284_);
lean_dec_ref(v___x_2285_);
goto v___jp_2281_;
v___jp_2281_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_io_error_to_string(v_a_2280_);
v___x_2283_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2282_);
lean_dec_ref(v___x_2283_);
goto v___jp_1122_;
}
}
}
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25));
v___x_2287_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2286_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2328_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2290_ = v___x_2287_;
v_isShared_2291_ = v_isSharedCheck_2328_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2287_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2328_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v_leanOpts_2292_; lean_object* v_forwardedArgs_2293_; uint8_t v_component_2294_; uint8_t v_printPrefix_2295_; uint8_t v_printLibDir_2296_; uint8_t v_useStdin_2297_; uint8_t v_onlyDeps_2298_; uint8_t v_onlySrcDeps_2299_; uint8_t v_depsJson_2300_; lean_object* v_opts_2301_; uint32_t v_trustLevel_2302_; uint32_t v_numThreads_2303_; lean_object* v_rootDir_x3f_2304_; lean_object* v_setupFileName_x3f_2305_; lean_object* v_oleanFileName_x3f_2306_; lean_object* v_cFileName_x3f_2307_; lean_object* v_bcFileName_x3f_2308_; uint8_t v_jsonOutput_2309_; lean_object* v_errorOnKinds_2310_; uint8_t v_printStats_2311_; uint8_t v_run_2312_; lean_object* v_incrSaveFileName_x3f_2313_; lean_object* v_incrLoadFileName_x3f_2314_; lean_object* v_incrHeaderSaveFileName_x3f_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2326_; 
v_leanOpts_2292_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_2293_ = lean_ctor_get(v_opts_933_, 1);
v_component_2294_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_2295_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_2296_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_2297_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_2298_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2299_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_2300_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_2301_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_2302_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_2303_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2304_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_2305_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_2306_ = lean_ctor_get(v_opts_933_, 5);
v_cFileName_x3f_2307_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_2308_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_2309_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2310_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2311_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_2312_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2313_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2314_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2315_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2326_ == 0)
{
lean_object* v_unused_2327_; 
v_unused_2327_ = lean_ctor_get(v_opts_933_, 6);
lean_dec(v_unused_2327_);
v___x_2317_ = v_opts_933_;
v_isShared_2318_ = v_isSharedCheck_2326_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2315_);
lean_inc(v_incrLoadFileName_x3f_2314_);
lean_inc(v_incrSaveFileName_x3f_2313_);
lean_inc(v_errorOnKinds_2310_);
lean_inc(v_bcFileName_x3f_2308_);
lean_inc(v_cFileName_x3f_2307_);
lean_inc(v_oleanFileName_x3f_2306_);
lean_inc(v_setupFileName_x3f_2305_);
lean_inc(v_rootDir_x3f_2304_);
lean_inc(v_opts_2301_);
lean_inc(v_forwardedArgs_2293_);
lean_inc(v_leanOpts_2292_);
lean_dec(v_opts_933_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2326_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2319_, 0, v_a_2288_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 6, v___x_2319_);
v___x_2321_ = v___x_2317_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_leanOpts_2292_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_forwardedArgs_2293_);
lean_ctor_set(v_reuseFailAlloc_2325_, 2, v_opts_2301_);
lean_ctor_set(v_reuseFailAlloc_2325_, 3, v_rootDir_x3f_2304_);
lean_ctor_set(v_reuseFailAlloc_2325_, 4, v_setupFileName_x3f_2305_);
lean_ctor_set(v_reuseFailAlloc_2325_, 5, v_oleanFileName_x3f_2306_);
lean_ctor_set(v_reuseFailAlloc_2325_, 6, v___x_2319_);
lean_ctor_set(v_reuseFailAlloc_2325_, 7, v_cFileName_x3f_2307_);
lean_ctor_set(v_reuseFailAlloc_2325_, 8, v_bcFileName_x3f_2308_);
lean_ctor_set(v_reuseFailAlloc_2325_, 9, v_errorOnKinds_2310_);
lean_ctor_set(v_reuseFailAlloc_2325_, 10, v_incrSaveFileName_x3f_2313_);
lean_ctor_set(v_reuseFailAlloc_2325_, 11, v_incrLoadFileName_x3f_2314_);
lean_ctor_set(v_reuseFailAlloc_2325_, 12, v_incrHeaderSaveFileName_x3f_2315_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*13 + 8, v_component_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*13 + 9, v_printPrefix_2295_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*13 + 10, v_printLibDir_2296_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*13 + 11, v_useStdin_2297_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*13 + 12, v_onlyDeps_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*13 + 13, v_onlySrcDeps_2299_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*13 + 14, v_depsJson_2300_);
lean_ctor_set_uint32(v_reuseFailAlloc_2325_, sizeof(void*)*13, v_trustLevel_2302_);
lean_ctor_set_uint32(v_reuseFailAlloc_2325_, sizeof(void*)*13 + 4, v_numThreads_2303_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*13 + 15, v_jsonOutput_2309_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*13 + 16, v_printStats_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*13 + 17, v_run_2312_);
v___x_2321_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2323_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2321_);
v___x_2323_ = v___x_2290_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec_ref(v_opts_933_);
v_a_2329_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2333_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2334_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2333_);
lean_dec_ref(v___x_2334_);
goto v___jp_2330_;
v___jp_2330_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = lean_io_error_to_string(v_a_2329_);
v___x_2332_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2331_);
lean_dec_ref(v___x_2332_);
goto v___jp_982_;
}
}
}
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2336_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2335_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2377_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2377_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2377_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_leanOpts_2341_; lean_object* v_forwardedArgs_2342_; uint8_t v_component_2343_; uint8_t v_printPrefix_2344_; uint8_t v_printLibDir_2345_; uint8_t v_useStdin_2346_; uint8_t v_onlyDeps_2347_; uint8_t v_onlySrcDeps_2348_; uint8_t v_depsJson_2349_; lean_object* v_opts_2350_; uint32_t v_trustLevel_2351_; uint32_t v_numThreads_2352_; lean_object* v_rootDir_x3f_2353_; lean_object* v_setupFileName_x3f_2354_; lean_object* v_ileanFileName_x3f_2355_; lean_object* v_cFileName_x3f_2356_; lean_object* v_bcFileName_x3f_2357_; uint8_t v_jsonOutput_2358_; lean_object* v_errorOnKinds_2359_; uint8_t v_printStats_2360_; uint8_t v_run_2361_; lean_object* v_incrSaveFileName_x3f_2362_; lean_object* v_incrLoadFileName_x3f_2363_; lean_object* v_incrHeaderSaveFileName_x3f_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2375_; 
v_leanOpts_2341_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_2342_ = lean_ctor_get(v_opts_933_, 1);
v_component_2343_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_2344_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_2345_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_2346_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_2347_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2348_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_2349_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_2350_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_2351_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_2352_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2353_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_2354_ = lean_ctor_get(v_opts_933_, 4);
v_ileanFileName_x3f_2355_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_2356_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_2357_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_2358_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2359_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2360_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_2361_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2362_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2363_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2364_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; 
v_unused_2376_ = lean_ctor_get(v_opts_933_, 5);
lean_dec(v_unused_2376_);
v___x_2366_ = v_opts_933_;
v_isShared_2367_ = v_isSharedCheck_2375_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2364_);
lean_inc(v_incrLoadFileName_x3f_2363_);
lean_inc(v_incrSaveFileName_x3f_2362_);
lean_inc(v_errorOnKinds_2359_);
lean_inc(v_bcFileName_x3f_2357_);
lean_inc(v_cFileName_x3f_2356_);
lean_inc(v_ileanFileName_x3f_2355_);
lean_inc(v_setupFileName_x3f_2354_);
lean_inc(v_rootDir_x3f_2353_);
lean_inc(v_opts_2350_);
lean_inc(v_forwardedArgs_2342_);
lean_inc(v_leanOpts_2341_);
lean_dec(v_opts_933_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2375_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2368_, 0, v_a_2337_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 5, v___x_2368_);
v___x_2370_ = v___x_2366_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_leanOpts_2341_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_forwardedArgs_2342_);
lean_ctor_set(v_reuseFailAlloc_2374_, 2, v_opts_2350_);
lean_ctor_set(v_reuseFailAlloc_2374_, 3, v_rootDir_x3f_2353_);
lean_ctor_set(v_reuseFailAlloc_2374_, 4, v_setupFileName_x3f_2354_);
lean_ctor_set(v_reuseFailAlloc_2374_, 5, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2374_, 6, v_ileanFileName_x3f_2355_);
lean_ctor_set(v_reuseFailAlloc_2374_, 7, v_cFileName_x3f_2356_);
lean_ctor_set(v_reuseFailAlloc_2374_, 8, v_bcFileName_x3f_2357_);
lean_ctor_set(v_reuseFailAlloc_2374_, 9, v_errorOnKinds_2359_);
lean_ctor_set(v_reuseFailAlloc_2374_, 10, v_incrSaveFileName_x3f_2362_);
lean_ctor_set(v_reuseFailAlloc_2374_, 11, v_incrLoadFileName_x3f_2363_);
lean_ctor_set(v_reuseFailAlloc_2374_, 12, v_incrHeaderSaveFileName_x3f_2364_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*13 + 8, v_component_2343_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*13 + 9, v_printPrefix_2344_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*13 + 10, v_printLibDir_2345_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*13 + 11, v_useStdin_2346_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*13 + 12, v_onlyDeps_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*13 + 13, v_onlySrcDeps_2348_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*13 + 14, v_depsJson_2349_);
lean_ctor_set_uint32(v_reuseFailAlloc_2374_, sizeof(void*)*13, v_trustLevel_2351_);
lean_ctor_set_uint32(v_reuseFailAlloc_2374_, sizeof(void*)*13 + 4, v_numThreads_2352_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*13 + 15, v_jsonOutput_2358_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*13 + 16, v_printStats_2360_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*13 + 17, v_run_2361_);
v___x_2370_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2372_; 
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2370_);
v___x_2372_ = v___x_2339_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
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
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_dec_ref(v_opts_933_);
v_a_2378_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2382_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2383_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2382_);
lean_dec_ref(v___x_2383_);
goto v___jp_2379_;
v___jp_2379_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = lean_io_error_to_string(v_a_2378_);
v___x_2381_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2380_);
lean_dec_ref(v___x_2381_);
goto v___jp_1128_;
}
}
}
}
else
{
lean_object* v_leanOpts_2384_; lean_object* v_forwardedArgs_2385_; uint8_t v_component_2386_; uint8_t v_printPrefix_2387_; uint8_t v_printLibDir_2388_; uint8_t v_useStdin_2389_; uint8_t v_onlyDeps_2390_; uint8_t v_onlySrcDeps_2391_; uint8_t v_depsJson_2392_; lean_object* v_opts_2393_; uint32_t v_trustLevel_2394_; uint32_t v_numThreads_2395_; lean_object* v_rootDir_x3f_2396_; lean_object* v_setupFileName_x3f_2397_; lean_object* v_oleanFileName_x3f_2398_; lean_object* v_ileanFileName_x3f_2399_; lean_object* v_cFileName_x3f_2400_; lean_object* v_bcFileName_x3f_2401_; uint8_t v_jsonOutput_2402_; lean_object* v_errorOnKinds_2403_; uint8_t v_printStats_2404_; lean_object* v_incrSaveFileName_x3f_2405_; lean_object* v_incrLoadFileName_x3f_2406_; lean_object* v_incrHeaderSaveFileName_x3f_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2417_; 
lean_dec(v_optArg_x3f_935_);
v_leanOpts_2384_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_2385_ = lean_ctor_get(v_opts_933_, 1);
v_component_2386_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_2387_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_2388_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_2389_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_2390_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2391_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_2392_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_2393_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_2394_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_2395_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2396_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_2397_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_2398_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_2399_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_2400_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_2401_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_2402_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2403_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2404_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_incrSaveFileName_x3f_2405_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2406_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2407_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2409_ = v_opts_933_;
v_isShared_2410_ = v_isSharedCheck_2417_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2407_);
lean_inc(v_incrLoadFileName_x3f_2406_);
lean_inc(v_incrSaveFileName_x3f_2405_);
lean_inc(v_errorOnKinds_2403_);
lean_inc(v_bcFileName_x3f_2401_);
lean_inc(v_cFileName_x3f_2400_);
lean_inc(v_ileanFileName_x3f_2399_);
lean_inc(v_oleanFileName_x3f_2398_);
lean_inc(v_setupFileName_x3f_2397_);
lean_inc(v_rootDir_x3f_2396_);
lean_inc(v_opts_2393_);
lean_inc(v_forwardedArgs_2385_);
lean_inc(v_leanOpts_2384_);
lean_dec(v_opts_933_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2417_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2411_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2412_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2384_, v___x_2411_, v___x_1176_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v___x_2412_);
v___x_2414_ = v___x_2409_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_forwardedArgs_2385_);
lean_ctor_set(v_reuseFailAlloc_2416_, 2, v_opts_2393_);
lean_ctor_set(v_reuseFailAlloc_2416_, 3, v_rootDir_x3f_2396_);
lean_ctor_set(v_reuseFailAlloc_2416_, 4, v_setupFileName_x3f_2397_);
lean_ctor_set(v_reuseFailAlloc_2416_, 5, v_oleanFileName_x3f_2398_);
lean_ctor_set(v_reuseFailAlloc_2416_, 6, v_ileanFileName_x3f_2399_);
lean_ctor_set(v_reuseFailAlloc_2416_, 7, v_cFileName_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2416_, 8, v_bcFileName_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2416_, 9, v_errorOnKinds_2403_);
lean_ctor_set(v_reuseFailAlloc_2416_, 10, v_incrSaveFileName_x3f_2405_);
lean_ctor_set(v_reuseFailAlloc_2416_, 11, v_incrLoadFileName_x3f_2406_);
lean_ctor_set(v_reuseFailAlloc_2416_, 12, v_incrHeaderSaveFileName_x3f_2407_);
lean_ctor_set_uint8(v_reuseFailAlloc_2416_, sizeof(void*)*13 + 8, v_component_2386_);
lean_ctor_set_uint8(v_reuseFailAlloc_2416_, sizeof(void*)*13 + 9, v_printPrefix_2387_);
lean_ctor_set_uint8(v_reuseFailAlloc_2416_, sizeof(void*)*13 + 10, v_printLibDir_2388_);
lean_ctor_set_uint8(v_reuseFailAlloc_2416_, sizeof(void*)*13 + 11, v_useStdin_2389_);
lean_ctor_set_uint8(v_reuseFailAlloc_2416_, sizeof(void*)*13 + 12, v_onlyDeps_2390_);
lean_ctor_set_uint8(v_reuseFailAlloc_2416_, sizeof(void*)*13 + 13, v_onlySrcDeps_2391_);
lean_ctor_set_uint8(v_reuseFailAlloc_2416_, sizeof(void*)*13 + 14, v_depsJson_2392_);
lean_ctor_set_uint32(v_reuseFailAlloc_2416_, sizeof(void*)*13, v_trustLevel_2394_);
lean_ctor_set_uint32(v_reuseFailAlloc_2416_, sizeof(void*)*13 + 4, v_numThreads_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2416_, sizeof(void*)*13 + 15, v_jsonOutput_2402_);
lean_ctor_set_uint8(v_reuseFailAlloc_2416_, sizeof(void*)*13 + 16, v_printStats_2404_);
v___x_2414_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2415_; 
lean_ctor_set_uint8(v___x_2414_, sizeof(void*)*13 + 17, v___x_1178_);
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
return v___x_2415_;
}
}
}
}
else
{
lean_object* v_leanOpts_2418_; lean_object* v_forwardedArgs_2419_; uint8_t v_component_2420_; uint8_t v_printPrefix_2421_; uint8_t v_printLibDir_2422_; uint8_t v_onlyDeps_2423_; uint8_t v_onlySrcDeps_2424_; uint8_t v_depsJson_2425_; lean_object* v_opts_2426_; uint32_t v_trustLevel_2427_; uint32_t v_numThreads_2428_; lean_object* v_rootDir_x3f_2429_; lean_object* v_setupFileName_x3f_2430_; lean_object* v_oleanFileName_x3f_2431_; lean_object* v_ileanFileName_x3f_2432_; lean_object* v_cFileName_x3f_2433_; lean_object* v_bcFileName_x3f_2434_; uint8_t v_jsonOutput_2435_; lean_object* v_errorOnKinds_2436_; uint8_t v_printStats_2437_; uint8_t v_run_2438_; lean_object* v_incrSaveFileName_x3f_2439_; lean_object* v_incrLoadFileName_x3f_2440_; lean_object* v_incrHeaderSaveFileName_x3f_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_optArg_x3f_935_);
v_leanOpts_2418_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_2419_ = lean_ctor_get(v_opts_933_, 1);
v_component_2420_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_2421_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_2422_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_onlyDeps_2423_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2424_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_2425_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_2426_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_2427_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_2428_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2429_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_2430_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_2431_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_2432_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_2433_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_2434_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_2435_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2436_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2437_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_2438_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2439_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2440_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2441_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2443_ = v_opts_933_;
v_isShared_2444_ = v_isSharedCheck_2449_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2441_);
lean_inc(v_incrLoadFileName_x3f_2440_);
lean_inc(v_incrSaveFileName_x3f_2439_);
lean_inc(v_errorOnKinds_2436_);
lean_inc(v_bcFileName_x3f_2434_);
lean_inc(v_cFileName_x3f_2433_);
lean_inc(v_ileanFileName_x3f_2432_);
lean_inc(v_oleanFileName_x3f_2431_);
lean_inc(v_setupFileName_x3f_2430_);
lean_inc(v_rootDir_x3f_2429_);
lean_inc(v_opts_2426_);
lean_inc(v_forwardedArgs_2419_);
lean_inc(v_leanOpts_2418_);
lean_dec(v_opts_933_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2449_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_leanOpts_2418_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_forwardedArgs_2419_);
lean_ctor_set(v_reuseFailAlloc_2448_, 2, v_opts_2426_);
lean_ctor_set(v_reuseFailAlloc_2448_, 3, v_rootDir_x3f_2429_);
lean_ctor_set(v_reuseFailAlloc_2448_, 4, v_setupFileName_x3f_2430_);
lean_ctor_set(v_reuseFailAlloc_2448_, 5, v_oleanFileName_x3f_2431_);
lean_ctor_set(v_reuseFailAlloc_2448_, 6, v_ileanFileName_x3f_2432_);
lean_ctor_set(v_reuseFailAlloc_2448_, 7, v_cFileName_x3f_2433_);
lean_ctor_set(v_reuseFailAlloc_2448_, 8, v_bcFileName_x3f_2434_);
lean_ctor_set(v_reuseFailAlloc_2448_, 9, v_errorOnKinds_2436_);
lean_ctor_set(v_reuseFailAlloc_2448_, 10, v_incrSaveFileName_x3f_2439_);
lean_ctor_set(v_reuseFailAlloc_2448_, 11, v_incrLoadFileName_x3f_2440_);
lean_ctor_set(v_reuseFailAlloc_2448_, 12, v_incrHeaderSaveFileName_x3f_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2448_, sizeof(void*)*13 + 8, v_component_2420_);
lean_ctor_set_uint8(v_reuseFailAlloc_2448_, sizeof(void*)*13 + 9, v_printPrefix_2421_);
lean_ctor_set_uint8(v_reuseFailAlloc_2448_, sizeof(void*)*13 + 10, v_printLibDir_2422_);
lean_ctor_set_uint8(v_reuseFailAlloc_2448_, sizeof(void*)*13 + 12, v_onlyDeps_2423_);
lean_ctor_set_uint8(v_reuseFailAlloc_2448_, sizeof(void*)*13 + 13, v_onlySrcDeps_2424_);
lean_ctor_set_uint8(v_reuseFailAlloc_2448_, sizeof(void*)*13 + 14, v_depsJson_2425_);
lean_ctor_set_uint32(v_reuseFailAlloc_2448_, sizeof(void*)*13, v_trustLevel_2427_);
lean_ctor_set_uint32(v_reuseFailAlloc_2448_, sizeof(void*)*13 + 4, v_numThreads_2428_);
lean_ctor_set_uint8(v_reuseFailAlloc_2448_, sizeof(void*)*13 + 15, v_jsonOutput_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2448_, sizeof(void*)*13 + 16, v_printStats_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2448_, sizeof(void*)*13 + 17, v_run_2438_);
v___x_2446_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; 
lean_ctor_set_uint8(v___x_2446_, sizeof(void*)*13 + 11, v___x_1176_);
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
return v___x_2447_;
}
}
}
}
else
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2451_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2450_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2513_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2513_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2513_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2456_ = lean_unsigned_to_nat(0u);
v___x_2457_ = lean_string_utf8_byte_size(v_a_2452_);
lean_inc(v_a_2452_);
v___x_2458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2458_, 0, v_a_2452_);
lean_ctor_set(v___x_2458_, 1, v___x_2456_);
lean_ctor_set(v___x_2458_, 2, v___x_2457_);
v___x_2459_ = l_String_Slice_toNat_x3f(v___x_2458_);
lean_dec_ref_known(v___x_2458_, 3);
if (lean_obj_tag(v___x_2459_) == 1)
{
lean_object* v_val_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; uint8_t v___x_2468_; 
v_val_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_val_2460_);
lean_dec_ref_known(v___x_2459_, 1);
v___x_2461_ = lean_unsigned_to_nat(4u);
v___x_2462_ = lean_unsigned_to_nat(2u);
v___x_2463_ = lean_nat_shiftr(v_val_2460_, v___x_2462_);
lean_dec(v_val_2460_);
v___x_2464_ = lean_nat_mul(v___x_2463_, v___x_2461_);
lean_dec(v___x_2463_);
v___x_2465_ = lean_unsigned_to_nat(1024u);
v___x_2466_ = lean_nat_mul(v___x_2464_, v___x_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28);
v___x_2468_ = lean_nat_dec_lt(v___x_2466_, v___x_2467_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_dec(v___x_2466_);
lean_del_object(v___x_2454_);
lean_dec(v_a_2452_);
lean_dec_ref(v_opts_933_);
v___x_2469_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2470_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2469_);
lean_dec_ref(v___x_2470_);
goto v___jp_970_;
}
else
{
size_t v___x_2471_; lean_object* v___x_2472_; lean_object* v_leanOpts_2473_; lean_object* v_forwardedArgs_2474_; uint8_t v_component_2475_; uint8_t v_printPrefix_2476_; uint8_t v_printLibDir_2477_; uint8_t v_useStdin_2478_; uint8_t v_onlyDeps_2479_; uint8_t v_onlySrcDeps_2480_; uint8_t v_depsJson_2481_; lean_object* v_opts_2482_; uint32_t v_trustLevel_2483_; uint32_t v_numThreads_2484_; lean_object* v_rootDir_x3f_2485_; lean_object* v_setupFileName_x3f_2486_; lean_object* v_oleanFileName_x3f_2487_; lean_object* v_ileanFileName_x3f_2488_; lean_object* v_cFileName_x3f_2489_; lean_object* v_bcFileName_x3f_2490_; uint8_t v_jsonOutput_2491_; lean_object* v_errorOnKinds_2492_; uint8_t v_printStats_2493_; uint8_t v_run_2494_; lean_object* v_incrSaveFileName_x3f_2495_; lean_object* v_incrLoadFileName_x3f_2496_; lean_object* v_incrHeaderSaveFileName_x3f_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2510_; 
v___x_2471_ = lean_usize_of_nat(v___x_2466_);
lean_dec(v___x_2466_);
v___x_2472_ = lean_internal_set_thread_stack_size(v___x_2471_);
v_leanOpts_2473_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_2474_ = lean_ctor_get(v_opts_933_, 1);
v_component_2475_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_2476_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_2477_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_2478_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_2479_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2480_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_2481_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_2482_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_2483_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_2484_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2485_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_2486_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_2487_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_2488_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_2489_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_2490_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_2491_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2492_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2493_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_2494_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2495_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2496_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2497_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2499_ = v_opts_933_;
v_isShared_2500_ = v_isSharedCheck_2510_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2497_);
lean_inc(v_incrLoadFileName_x3f_2496_);
lean_inc(v_incrSaveFileName_x3f_2495_);
lean_inc(v_errorOnKinds_2492_);
lean_inc(v_bcFileName_x3f_2490_);
lean_inc(v_cFileName_x3f_2489_);
lean_inc(v_ileanFileName_x3f_2488_);
lean_inc(v_oleanFileName_x3f_2487_);
lean_inc(v_setupFileName_x3f_2486_);
lean_inc(v_rootDir_x3f_2485_);
lean_inc(v_opts_2482_);
lean_inc(v_forwardedArgs_2474_);
lean_inc(v_leanOpts_2473_);
lean_dec(v_opts_933_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2510_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2501_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2502_ = lean_string_append(v___x_2501_, v_a_2452_);
lean_dec(v_a_2452_);
v___x_2503_ = lean_array_push(v_forwardedArgs_2474_, v___x_2502_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 1, v___x_2503_);
v___x_2505_ = v___x_2499_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_leanOpts_2473_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_opts_2482_);
lean_ctor_set(v_reuseFailAlloc_2509_, 3, v_rootDir_x3f_2485_);
lean_ctor_set(v_reuseFailAlloc_2509_, 4, v_setupFileName_x3f_2486_);
lean_ctor_set(v_reuseFailAlloc_2509_, 5, v_oleanFileName_x3f_2487_);
lean_ctor_set(v_reuseFailAlloc_2509_, 6, v_ileanFileName_x3f_2488_);
lean_ctor_set(v_reuseFailAlloc_2509_, 7, v_cFileName_x3f_2489_);
lean_ctor_set(v_reuseFailAlloc_2509_, 8, v_bcFileName_x3f_2490_);
lean_ctor_set(v_reuseFailAlloc_2509_, 9, v_errorOnKinds_2492_);
lean_ctor_set(v_reuseFailAlloc_2509_, 10, v_incrSaveFileName_x3f_2495_);
lean_ctor_set(v_reuseFailAlloc_2509_, 11, v_incrLoadFileName_x3f_2496_);
lean_ctor_set(v_reuseFailAlloc_2509_, 12, v_incrHeaderSaveFileName_x3f_2497_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*13 + 8, v_component_2475_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*13 + 9, v_printPrefix_2476_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*13 + 10, v_printLibDir_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*13 + 11, v_useStdin_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*13 + 12, v_onlyDeps_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*13 + 13, v_onlySrcDeps_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*13 + 14, v_depsJson_2481_);
lean_ctor_set_uint32(v_reuseFailAlloc_2509_, sizeof(void*)*13, v_trustLevel_2483_);
lean_ctor_set_uint32(v_reuseFailAlloc_2509_, sizeof(void*)*13 + 4, v_numThreads_2484_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*13 + 15, v_jsonOutput_2491_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*13 + 16, v_printStats_2493_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*13 + 17, v_run_2494_);
v___x_2505_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2507_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2505_);
v___x_2507_ = v___x_2454_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
lean_dec(v___x_2459_);
lean_del_object(v___x_2454_);
lean_dec(v_a_2452_);
lean_dec_ref(v_opts_933_);
v___x_2511_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2512_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2511_);
lean_dec_ref(v___x_2512_);
goto v___jp_967_;
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec_ref(v_opts_933_);
v_a_2514_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___x_2451_, 1);
v___x_2518_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2519_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2518_);
lean_dec_ref(v___x_2519_);
goto v___jp_2515_;
v___jp_2515_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_io_error_to_string(v_a_2514_);
v___x_2517_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2516_);
lean_dec_ref(v___x_2517_);
goto v___jp_976_;
}
}
}
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2521_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2520_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2562_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2562_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2562_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v_leanOpts_2526_; lean_object* v_forwardedArgs_2527_; uint8_t v_component_2528_; uint8_t v_printPrefix_2529_; uint8_t v_printLibDir_2530_; uint8_t v_useStdin_2531_; uint8_t v_onlyDeps_2532_; uint8_t v_onlySrcDeps_2533_; uint8_t v_depsJson_2534_; lean_object* v_opts_2535_; uint32_t v_trustLevel_2536_; uint32_t v_numThreads_2537_; lean_object* v_rootDir_x3f_2538_; lean_object* v_setupFileName_x3f_2539_; lean_object* v_oleanFileName_x3f_2540_; lean_object* v_ileanFileName_x3f_2541_; lean_object* v_cFileName_x3f_2542_; uint8_t v_jsonOutput_2543_; lean_object* v_errorOnKinds_2544_; uint8_t v_printStats_2545_; uint8_t v_run_2546_; lean_object* v_incrSaveFileName_x3f_2547_; lean_object* v_incrLoadFileName_x3f_2548_; lean_object* v_incrHeaderSaveFileName_x3f_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2560_; 
v_leanOpts_2526_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_2527_ = lean_ctor_get(v_opts_933_, 1);
v_component_2528_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_2529_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_2530_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_2531_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_2532_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2533_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_2534_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_2535_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_2536_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_2537_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2538_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_2539_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_2540_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_2541_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_2542_ = lean_ctor_get(v_opts_933_, 7);
v_jsonOutput_2543_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2544_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2545_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_2546_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2547_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2548_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2549_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2560_ == 0)
{
lean_object* v_unused_2561_; 
v_unused_2561_ = lean_ctor_get(v_opts_933_, 8);
lean_dec(v_unused_2561_);
v___x_2551_ = v_opts_933_;
v_isShared_2552_ = v_isSharedCheck_2560_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2549_);
lean_inc(v_incrLoadFileName_x3f_2548_);
lean_inc(v_incrSaveFileName_x3f_2547_);
lean_inc(v_errorOnKinds_2544_);
lean_inc(v_cFileName_x3f_2542_);
lean_inc(v_ileanFileName_x3f_2541_);
lean_inc(v_oleanFileName_x3f_2540_);
lean_inc(v_setupFileName_x3f_2539_);
lean_inc(v_rootDir_x3f_2538_);
lean_inc(v_opts_2535_);
lean_inc(v_forwardedArgs_2527_);
lean_inc(v_leanOpts_2526_);
lean_dec(v_opts_933_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2560_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_a_2522_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 8, v___x_2553_);
v___x_2555_ = v___x_2551_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_leanOpts_2526_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_forwardedArgs_2527_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_opts_2535_);
lean_ctor_set(v_reuseFailAlloc_2559_, 3, v_rootDir_x3f_2538_);
lean_ctor_set(v_reuseFailAlloc_2559_, 4, v_setupFileName_x3f_2539_);
lean_ctor_set(v_reuseFailAlloc_2559_, 5, v_oleanFileName_x3f_2540_);
lean_ctor_set(v_reuseFailAlloc_2559_, 6, v_ileanFileName_x3f_2541_);
lean_ctor_set(v_reuseFailAlloc_2559_, 7, v_cFileName_x3f_2542_);
lean_ctor_set(v_reuseFailAlloc_2559_, 8, v___x_2553_);
lean_ctor_set(v_reuseFailAlloc_2559_, 9, v_errorOnKinds_2544_);
lean_ctor_set(v_reuseFailAlloc_2559_, 10, v_incrSaveFileName_x3f_2547_);
lean_ctor_set(v_reuseFailAlloc_2559_, 11, v_incrLoadFileName_x3f_2548_);
lean_ctor_set(v_reuseFailAlloc_2559_, 12, v_incrHeaderSaveFileName_x3f_2549_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*13 + 8, v_component_2528_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*13 + 9, v_printPrefix_2529_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*13 + 10, v_printLibDir_2530_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*13 + 11, v_useStdin_2531_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*13 + 12, v_onlyDeps_2532_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*13 + 13, v_onlySrcDeps_2533_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*13 + 14, v_depsJson_2534_);
lean_ctor_set_uint32(v_reuseFailAlloc_2559_, sizeof(void*)*13, v_trustLevel_2536_);
lean_ctor_set_uint32(v_reuseFailAlloc_2559_, sizeof(void*)*13 + 4, v_numThreads_2537_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*13 + 15, v_jsonOutput_2543_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*13 + 16, v_printStats_2545_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*13 + 17, v_run_2546_);
v___x_2555_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2557_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2555_);
v___x_2557_ = v___x_2524_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_dec_ref(v_opts_933_);
v_a_2563_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2521_, 1);
v___x_2567_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2568_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2567_);
lean_dec_ref(v___x_2568_);
goto v___jp_2564_;
v___jp_2564_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = lean_io_error_to_string(v_a_2563_);
v___x_2566_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2565_);
lean_dec_ref(v___x_2566_);
goto v___jp_1134_;
}
}
}
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2570_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2569_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2611_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2573_ = v___x_2570_;
v_isShared_2574_ = v_isSharedCheck_2611_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2570_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2611_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v_leanOpts_2575_; lean_object* v_forwardedArgs_2576_; uint8_t v_component_2577_; uint8_t v_printPrefix_2578_; uint8_t v_printLibDir_2579_; uint8_t v_useStdin_2580_; uint8_t v_onlyDeps_2581_; uint8_t v_onlySrcDeps_2582_; uint8_t v_depsJson_2583_; lean_object* v_opts_2584_; uint32_t v_trustLevel_2585_; uint32_t v_numThreads_2586_; lean_object* v_rootDir_x3f_2587_; lean_object* v_setupFileName_x3f_2588_; lean_object* v_oleanFileName_x3f_2589_; lean_object* v_ileanFileName_x3f_2590_; lean_object* v_bcFileName_x3f_2591_; uint8_t v_jsonOutput_2592_; lean_object* v_errorOnKinds_2593_; uint8_t v_printStats_2594_; uint8_t v_run_2595_; lean_object* v_incrSaveFileName_x3f_2596_; lean_object* v_incrLoadFileName_x3f_2597_; lean_object* v_incrHeaderSaveFileName_x3f_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2609_; 
v_leanOpts_2575_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_2576_ = lean_ctor_get(v_opts_933_, 1);
v_component_2577_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_2578_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_2579_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_2580_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_2581_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2582_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_2583_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_2584_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_2585_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_numThreads_2586_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2587_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_2588_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_2589_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_2590_ = lean_ctor_get(v_opts_933_, 6);
v_bcFileName_x3f_2591_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_2592_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2593_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2594_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_2595_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2596_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2597_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2598_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2609_ == 0)
{
lean_object* v_unused_2610_; 
v_unused_2610_ = lean_ctor_get(v_opts_933_, 7);
lean_dec(v_unused_2610_);
v___x_2600_ = v_opts_933_;
v_isShared_2601_ = v_isSharedCheck_2609_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2598_);
lean_inc(v_incrLoadFileName_x3f_2597_);
lean_inc(v_incrSaveFileName_x3f_2596_);
lean_inc(v_errorOnKinds_2593_);
lean_inc(v_bcFileName_x3f_2591_);
lean_inc(v_ileanFileName_x3f_2590_);
lean_inc(v_oleanFileName_x3f_2589_);
lean_inc(v_setupFileName_x3f_2588_);
lean_inc(v_rootDir_x3f_2587_);
lean_inc(v_opts_2584_);
lean_inc(v_forwardedArgs_2576_);
lean_inc(v_leanOpts_2575_);
lean_dec(v_opts_933_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2609_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; lean_object* v___x_2604_; 
v___x_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2602_, 0, v_a_2571_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 7, v___x_2602_);
v___x_2604_ = v___x_2600_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_leanOpts_2575_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_forwardedArgs_2576_);
lean_ctor_set(v_reuseFailAlloc_2608_, 2, v_opts_2584_);
lean_ctor_set(v_reuseFailAlloc_2608_, 3, v_rootDir_x3f_2587_);
lean_ctor_set(v_reuseFailAlloc_2608_, 4, v_setupFileName_x3f_2588_);
lean_ctor_set(v_reuseFailAlloc_2608_, 5, v_oleanFileName_x3f_2589_);
lean_ctor_set(v_reuseFailAlloc_2608_, 6, v_ileanFileName_x3f_2590_);
lean_ctor_set(v_reuseFailAlloc_2608_, 7, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2608_, 8, v_bcFileName_x3f_2591_);
lean_ctor_set(v_reuseFailAlloc_2608_, 9, v_errorOnKinds_2593_);
lean_ctor_set(v_reuseFailAlloc_2608_, 10, v_incrSaveFileName_x3f_2596_);
lean_ctor_set(v_reuseFailAlloc_2608_, 11, v_incrLoadFileName_x3f_2597_);
lean_ctor_set(v_reuseFailAlloc_2608_, 12, v_incrHeaderSaveFileName_x3f_2598_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*13 + 8, v_component_2577_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*13 + 9, v_printPrefix_2578_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*13 + 10, v_printLibDir_2579_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*13 + 11, v_useStdin_2580_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*13 + 12, v_onlyDeps_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*13 + 13, v_onlySrcDeps_2582_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*13 + 14, v_depsJson_2583_);
lean_ctor_set_uint32(v_reuseFailAlloc_2608_, sizeof(void*)*13, v_trustLevel_2585_);
lean_ctor_set_uint32(v_reuseFailAlloc_2608_, sizeof(void*)*13 + 4, v_numThreads_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*13 + 15, v_jsonOutput_2592_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*13 + 16, v_printStats_2594_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*13 + 17, v_run_2595_);
v___x_2604_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2606_; 
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2604_);
v___x_2606_ = v___x_2573_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_dec_ref(v_opts_933_);
v_a_2612_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2570_, 1);
v___x_2616_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2617_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2616_);
lean_dec_ref(v___x_2617_);
goto v___jp_2613_;
v___jp_2613_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = lean_io_error_to_string(v_a_2612_);
v___x_2615_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2614_);
lean_dec_ref(v___x_2615_);
goto v___jp_964_;
}
}
}
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
lean_dec(v_optArg_x3f_935_);
lean_dec_ref(v_opts_933_);
v___x_2618_ = l___private_Lean_Shell_0__Lean_featuresString;
v___x_2619_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2618_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2627_; 
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; 
v_unused_2628_ = lean_ctor_get(v___x_2619_, 0);
lean_dec(v_unused_2628_);
v___x_2621_ = v___x_2619_;
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
else
{
lean_dec(v___x_2619_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2623_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2622_ == 0)
{
lean_ctor_set_tag(v___x_2621_, 1);
lean_ctor_set(v___x_2621_, 0, v___x_2623_);
v___x_2625_ = v___x_2621_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v_a_2629_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2619_, 1);
v___x_2633_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2634_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2633_);
lean_dec_ref(v___x_2634_);
goto v___jp_2630_;
v___jp_2630_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_io_error_to_string(v_a_2629_);
v___x_2632_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2631_);
lean_dec_ref(v___x_2632_);
goto v___jp_1140_;
}
}
}
}
else
{
lean_object* v___x_2635_; 
lean_dec(v_optArg_x3f_935_);
lean_dec_ref(v_opts_933_);
v___x_2635_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1164_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2643_; 
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; 
v_unused_2644_ = lean_ctor_get(v___x_2635_, 0);
lean_dec(v_unused_2644_);
v___x_2637_ = v___x_2635_;
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
else
{
lean_dec(v___x_2635_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2639_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2638_ == 0)
{
lean_ctor_set_tag(v___x_2637_, 1);
lean_ctor_set(v___x_2637_, 0, v___x_2639_);
v___x_2641_ = v___x_2637_;
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
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_a_2645_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2649_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2650_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2649_);
lean_dec_ref(v___x_2650_);
goto v___jp_2646_;
v___jp_2646_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = lean_io_error_to_string(v_a_2645_);
v___x_2648_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2647_);
lean_dec_ref(v___x_2648_);
goto v___jp_958_;
}
}
}
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_dec(v_optArg_x3f_935_);
lean_dec_ref(v_opts_933_);
v___x_2651_ = l_Lean_githash;
v___x_2652_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2651_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2660_; 
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; 
v_unused_2661_ = lean_ctor_get(v___x_2652_, 0);
lean_dec(v_unused_2661_);
v___x_2654_ = v___x_2652_;
v_isShared_2655_ = v_isSharedCheck_2660_;
goto v_resetjp_2653_;
}
else
{
lean_dec(v___x_2652_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2660_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2656_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2655_ == 0)
{
lean_ctor_set_tag(v___x_2654_, 1);
lean_ctor_set(v___x_2654_, 0, v___x_2656_);
v___x_2658_ = v___x_2654_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v_a_2662_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2652_, 1);
v___x_2666_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2667_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2666_);
lean_dec_ref(v___x_2667_);
goto v___jp_2663_;
v___jp_2663_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_io_error_to_string(v_a_2662_);
v___x_2665_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2664_);
lean_dec_ref(v___x_2665_);
goto v___jp_1146_;
}
}
}
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_dec(v_optArg_x3f_935_);
lean_dec_ref(v_opts_933_);
v___x_2668_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2669_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2668_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2677_; 
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; 
v_unused_2678_ = lean_ctor_get(v___x_2669_, 0);
lean_dec(v_unused_2678_);
v___x_2671_ = v___x_2669_;
v_isShared_2672_ = v_isSharedCheck_2677_;
goto v_resetjp_2670_;
}
else
{
lean_dec(v___x_2669_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2677_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2673_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2672_ == 0)
{
lean_ctor_set_tag(v___x_2671_, 1);
lean_ctor_set(v___x_2671_, 0, v___x_2673_);
v___x_2675_ = v___x_2671_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v_a_2679_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2683_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2684_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2683_);
lean_dec_ref(v___x_2684_);
goto v___jp_2680_;
v___jp_2680_:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2681_ = lean_io_error_to_string(v_a_2679_);
v___x_2682_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2681_);
lean_dec_ref(v___x_2682_);
goto v___jp_952_;
}
}
}
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
lean_dec(v_optArg_x3f_935_);
lean_dec_ref(v_opts_933_);
v___x_2685_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2686_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2685_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2694_; 
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; 
v_unused_2695_ = lean_ctor_get(v___x_2686_, 0);
lean_dec(v_unused_2695_);
v___x_2688_ = v___x_2686_;
v_isShared_2689_ = v_isSharedCheck_2694_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v___x_2686_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2694_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2690_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2689_ == 0)
{
lean_ctor_set_tag(v___x_2688_, 1);
lean_ctor_set(v___x_2688_, 0, v___x_2690_);
v___x_2692_ = v___x_2688_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v_a_2696_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2686_, 1);
v___x_2700_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2701_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2700_);
lean_dec_ref(v___x_2701_);
goto v___jp_2697_;
v___jp_2697_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_io_error_to_string(v_a_2696_);
v___x_2699_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2698_);
lean_dec_ref(v___x_2699_);
goto v___jp_1152_;
}
}
}
}
else
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2703_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2702_, v_optArg_x3f_935_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2757_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2757_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2757_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2708_ = lean_unsigned_to_nat(0u);
v___x_2709_ = lean_string_utf8_byte_size(v_a_2704_);
lean_inc(v_a_2704_);
v___x_2710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2710_, 0, v_a_2704_);
lean_ctor_set(v___x_2710_, 1, v___x_2708_);
lean_ctor_set(v___x_2710_, 2, v___x_2709_);
v___x_2711_ = l_String_Slice_toNat_x3f(v___x_2710_);
lean_dec_ref_known(v___x_2710_, 3);
if (lean_obj_tag(v___x_2711_) == 1)
{
lean_object* v_val_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v_val_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_val_2712_);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2713_ = lean_cstr_to_nat("4294967296");
v___x_2714_ = lean_nat_dec_lt(v_val_2712_, v___x_2713_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_dec(v_val_2712_);
lean_del_object(v___x_2706_);
lean_dec(v_a_2704_);
lean_dec_ref(v_opts_933_);
v___x_2715_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__35));
v___x_2716_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2715_);
lean_dec_ref(v___x_2716_);
goto v___jp_940_;
}
else
{
lean_object* v_leanOpts_2717_; lean_object* v_forwardedArgs_2718_; uint8_t v_component_2719_; uint8_t v_printPrefix_2720_; uint8_t v_printLibDir_2721_; uint8_t v_useStdin_2722_; uint8_t v_onlyDeps_2723_; uint8_t v_onlySrcDeps_2724_; uint8_t v_depsJson_2725_; lean_object* v_opts_2726_; uint32_t v_trustLevel_2727_; lean_object* v_rootDir_x3f_2728_; lean_object* v_setupFileName_x3f_2729_; lean_object* v_oleanFileName_x3f_2730_; lean_object* v_ileanFileName_x3f_2731_; lean_object* v_cFileName_x3f_2732_; lean_object* v_bcFileName_x3f_2733_; uint8_t v_jsonOutput_2734_; lean_object* v_errorOnKinds_2735_; uint8_t v_printStats_2736_; uint8_t v_run_2737_; lean_object* v_incrSaveFileName_x3f_2738_; lean_object* v_incrLoadFileName_x3f_2739_; lean_object* v_incrHeaderSaveFileName_x3f_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2754_; 
v_leanOpts_2717_ = lean_ctor_get(v_opts_933_, 0);
v_forwardedArgs_2718_ = lean_ctor_get(v_opts_933_, 1);
v_component_2719_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 8);
v_printPrefix_2720_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 9);
v_printLibDir_2721_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 10);
v_useStdin_2722_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 11);
v_onlyDeps_2723_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2724_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 13);
v_depsJson_2725_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 14);
v_opts_2726_ = lean_ctor_get(v_opts_933_, 2);
v_trustLevel_2727_ = lean_ctor_get_uint32(v_opts_933_, sizeof(void*)*13);
v_rootDir_x3f_2728_ = lean_ctor_get(v_opts_933_, 3);
v_setupFileName_x3f_2729_ = lean_ctor_get(v_opts_933_, 4);
v_oleanFileName_x3f_2730_ = lean_ctor_get(v_opts_933_, 5);
v_ileanFileName_x3f_2731_ = lean_ctor_get(v_opts_933_, 6);
v_cFileName_x3f_2732_ = lean_ctor_get(v_opts_933_, 7);
v_bcFileName_x3f_2733_ = lean_ctor_get(v_opts_933_, 8);
v_jsonOutput_2734_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 15);
v_errorOnKinds_2735_ = lean_ctor_get(v_opts_933_, 9);
v_printStats_2736_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 16);
v_run_2737_ = lean_ctor_get_uint8(v_opts_933_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2738_ = lean_ctor_get(v_opts_933_, 10);
v_incrLoadFileName_x3f_2739_ = lean_ctor_get(v_opts_933_, 11);
v_incrHeaderSaveFileName_x3f_2740_ = lean_ctor_get(v_opts_933_, 12);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_opts_933_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2742_ = v_opts_933_;
v_isShared_2743_ = v_isSharedCheck_2754_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2740_);
lean_inc(v_incrLoadFileName_x3f_2739_);
lean_inc(v_incrSaveFileName_x3f_2738_);
lean_inc(v_errorOnKinds_2735_);
lean_inc(v_bcFileName_x3f_2733_);
lean_inc(v_cFileName_x3f_2732_);
lean_inc(v_ileanFileName_x3f_2731_);
lean_inc(v_oleanFileName_x3f_2730_);
lean_inc(v_setupFileName_x3f_2729_);
lean_inc(v_rootDir_x3f_2728_);
lean_inc(v_opts_2726_);
lean_inc(v_forwardedArgs_2718_);
lean_inc(v_leanOpts_2717_);
lean_dec(v_opts_933_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2754_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
uint32_t v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2749_; 
v___x_2744_ = lean_uint32_of_nat(v_val_2712_);
lean_dec(v_val_2712_);
v___x_2745_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__36));
v___x_2746_ = lean_string_append(v___x_2745_, v_a_2704_);
lean_dec(v_a_2704_);
v___x_2747_ = lean_array_push(v_forwardedArgs_2718_, v___x_2746_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 1, v___x_2747_);
v___x_2749_ = v___x_2742_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_leanOpts_2717_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2753_, 2, v_opts_2726_);
lean_ctor_set(v_reuseFailAlloc_2753_, 3, v_rootDir_x3f_2728_);
lean_ctor_set(v_reuseFailAlloc_2753_, 4, v_setupFileName_x3f_2729_);
lean_ctor_set(v_reuseFailAlloc_2753_, 5, v_oleanFileName_x3f_2730_);
lean_ctor_set(v_reuseFailAlloc_2753_, 6, v_ileanFileName_x3f_2731_);
lean_ctor_set(v_reuseFailAlloc_2753_, 7, v_cFileName_x3f_2732_);
lean_ctor_set(v_reuseFailAlloc_2753_, 8, v_bcFileName_x3f_2733_);
lean_ctor_set(v_reuseFailAlloc_2753_, 9, v_errorOnKinds_2735_);
lean_ctor_set(v_reuseFailAlloc_2753_, 10, v_incrSaveFileName_x3f_2738_);
lean_ctor_set(v_reuseFailAlloc_2753_, 11, v_incrLoadFileName_x3f_2739_);
lean_ctor_set(v_reuseFailAlloc_2753_, 12, v_incrHeaderSaveFileName_x3f_2740_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*13 + 8, v_component_2719_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*13 + 9, v_printPrefix_2720_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*13 + 10, v_printLibDir_2721_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*13 + 11, v_useStdin_2722_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*13 + 12, v_onlyDeps_2723_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*13 + 13, v_onlySrcDeps_2724_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*13 + 14, v_depsJson_2725_);
lean_ctor_set_uint32(v_reuseFailAlloc_2753_, sizeof(void*)*13, v_trustLevel_2727_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*13 + 15, v_jsonOutput_2734_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*13 + 16, v_printStats_2736_);
lean_ctor_set_uint8(v_reuseFailAlloc_2753_, sizeof(void*)*13 + 17, v_run_2737_);
v___x_2749_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2751_; 
lean_ctor_set_uint32(v___x_2749_, sizeof(void*)*13 + 4, v___x_2744_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2749_);
v___x_2751_ = v___x_2706_;
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
else
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
lean_dec(v___x_2711_);
lean_del_object(v___x_2706_);
lean_dec(v_a_2704_);
lean_dec_ref(v_opts_933_);
v___x_2755_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__37));
v___x_2756_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2755_);
lean_dec_ref(v___x_2756_);
goto v___jp_937_;
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_dec_ref(v_opts_933_);
v_a_2758_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2758_);
lean_dec_ref_known(v___x_2703_, 1);
v___x_2762_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2763_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2762_);
lean_dec_ref(v___x_2763_);
goto v___jp_2759_;
v___jp_2759_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_io_error_to_string(v_a_2758_);
v___x_2761_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2760_);
lean_dec_ref(v___x_2761_);
goto v___jp_946_;
}
}
}
}
else
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
lean_dec(v_optArg_x3f_935_);
v___x_2764_ = lean_internal_set_exit_on_panic(v___x_1156_);
v___x_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2765_, 0, v_opts_933_);
return v___x_2765_;
}
v___jp_937_:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
v___jp_940_:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
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
v___x_953_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_954_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_953_);
lean_dec_ref(v___x_954_);
goto v___jp_949_;
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
v___x_971_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
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
v___x_1010_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1011_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1010_);
lean_dec_ref(v___x_1011_);
goto v___jp_1006_;
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
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_io_error_to_string(v___y_1043_);
v___x_1045_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1044_);
lean_dec_ref(v___x_1045_);
goto v___jp_1039_;
}
v___jp_1046_:
{
uint8_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = 1;
v___x_1048_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1047_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1056_; 
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; 
v_unused_1057_ = lean_ctor_get(v___x_1048_, 0);
lean_dec(v_unused_1057_);
v___x_1050_ = v___x_1048_;
v_isShared_1051_ = v_isSharedCheck_1056_;
goto v_resetjp_1049_;
}
else
{
lean_dec(v___x_1048_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1056_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1052_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 1);
lean_ctor_set(v___x_1050_, 0, v___x_1052_);
v___x_1054_ = v___x_1050_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_a_1058_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1059_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1060_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1059_);
lean_dec_ref(v___x_1060_);
v___y_1043_ = v_a_1058_;
goto v___jp_1042_;
}
}
v___jp_1061_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
v___x_1063_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1062_);
lean_dec_ref(v___x_1063_);
goto v___jp_1046_;
}
v___jp_1064_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
v___jp_1067_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1069_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1068_);
lean_dec_ref(v___x_1069_);
goto v___jp_1064_;
}
v___jp_1070_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
v___jp_1073_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1075_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1074_);
lean_dec_ref(v___x_1075_);
goto v___jp_1070_;
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
goto v___jp_1091_;
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2766_, lean_object* v_opt_2767_, lean_object* v_optArg_x3f_2768_, lean_object* v_a_2769_){
_start:
{
uint32_t v_opt_boxed_2770_; lean_object* v_res_2771_; 
v_opt_boxed_2770_ = lean_unbox_uint32(v_opt_2767_);
lean_dec(v_opt_2767_);
v_res_2771_ = lean_shell_options_process(v_opts_2766_, v_opt_boxed_2770_, v_optArg_x3f_2768_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(lean_object* v_name_2773_, lean_object* v_f_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = lean_uv_os_getpid();
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2812_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2812_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2812_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; uint64_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v_a_2788_; uint8_t v___x_2802_; lean_object* v___x_2803_; 
v___x_2781_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___closed__0));
v___x_2782_ = lean_unbox_uint64(v_a_2777_);
lean_dec(v_a_2777_);
v___x_2783_ = lean_uint64_to_nat(v___x_2782_);
v___x_2784_ = l_Nat_reprFast(v___x_2783_);
v___x_2785_ = lean_string_append(v___x_2781_, v___x_2784_);
lean_dec_ref(v___x_2784_);
lean_inc_ref(v_name_2773_);
v___x_2786_ = l_System_FilePath_addExtension(v_name_2773_, v___x_2785_);
lean_dec_ref(v___x_2785_);
v___x_2802_ = 1;
v___x_2803_ = lean_io_prim_handle_mk(v___x_2786_, v___x_2802_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2805_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc_n(v_a_2804_, 2);
lean_dec_ref_known(v___x_2803_, 1);
v___x_2805_ = lean_apply_2(v_f_2774_, v_a_2804_, lean_box(0));
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v___x_2806_; 
lean_dec_ref_known(v___x_2805_, 1);
v___x_2806_ = lean_io_prim_handle_flush(v_a_2804_);
lean_dec(v_a_2804_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v___x_2807_; 
lean_dec_ref_known(v___x_2806_, 1);
v___x_2807_ = lean_io_rename(v___x_2786_, v_name_2773_);
lean_dec_ref(v_name_2773_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_dec_ref(v___x_2786_);
lean_del_object(v___x_2779_);
return v___x_2807_;
}
else
{
lean_object* v_a_2808_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v_a_2788_ = v_a_2808_;
goto v___jp_2787_;
}
}
else
{
lean_object* v_a_2809_; 
lean_dec_ref(v_name_2773_);
v_a_2809_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2806_, 1);
v_a_2788_ = v_a_2809_;
goto v___jp_2787_;
}
}
else
{
lean_object* v_a_2810_; 
lean_dec(v_a_2804_);
lean_dec_ref(v_name_2773_);
v_a_2810_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v___x_2805_, 1);
v_a_2788_ = v_a_2810_;
goto v___jp_2787_;
}
}
else
{
lean_object* v_a_2811_; 
lean_dec_ref(v_f_2774_);
lean_dec_ref(v_name_2773_);
v_a_2811_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2803_, 1);
v_a_2788_ = v_a_2811_;
goto v___jp_2787_;
}
v___jp_2787_:
{
uint8_t v___x_2789_; 
v___x_2789_ = l_System_FilePath_pathExists(v___x_2786_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2791_; 
lean_dec_ref(v___x_2786_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set_tag(v___x_2779_, 1);
lean_ctor_set(v___x_2779_, 0, v_a_2788_);
v___x_2791_ = v___x_2779_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2788_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
else
{
lean_object* v___x_2793_; 
lean_del_object(v___x_2779_);
v___x_2793_ = lean_io_remove_file(v___x_2786_);
lean_dec_ref(v___x_2786_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2800_ == 0)
{
lean_object* v_unused_2801_; 
v_unused_2801_ = lean_ctor_get(v___x_2793_, 0);
lean_dec(v_unused_2801_);
v___x_2795_ = v___x_2793_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_dec(v___x_2793_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set_tag(v___x_2795_, 1);
lean_ctor_set(v___x_2795_, 0, v_a_2788_);
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2788_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
else
{
lean_dec(v_a_2788_);
return v___x_2793_;
}
}
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec_ref(v_f_2774_);
lean_dec_ref(v_name_2773_);
v_a_2813_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2776_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2776_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___boxed(lean_object* v_name_2821_, lean_object* v_f_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(v_name_2821_, v_f_2822_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_opts_2825_, lean_object* v_opt_2826_){
_start:
{
lean_object* v_name_2827_; lean_object* v_defValue_2828_; lean_object* v_map_2829_; lean_object* v___x_2830_; 
v_name_2827_ = lean_ctor_get(v_opt_2826_, 0);
v_defValue_2828_ = lean_ctor_get(v_opt_2826_, 1);
v_map_2829_ = lean_ctor_get(v_opts_2825_, 0);
v___x_2830_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2829_, v_name_2827_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_inc(v_defValue_2828_);
return v_defValue_2828_;
}
else
{
lean_object* v_val_2831_; 
v_val_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_val_2831_);
lean_dec_ref_known(v___x_2830_, 1);
if (lean_obj_tag(v_val_2831_) == 3)
{
lean_object* v_v_2832_; 
v_v_2832_ = lean_ctor_get(v_val_2831_, 0);
lean_inc(v_v_2832_);
lean_dec_ref_known(v_val_2831_, 1);
return v_v_2832_;
}
else
{
lean_dec(v_val_2831_);
lean_inc(v_defValue_2828_);
return v_defValue_2828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_opts_2833_, lean_object* v_opt_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_opts_2833_, v_opt_2834_);
lean_dec_ref(v_opt_2834_);
lean_dec_ref(v_opts_2833_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2837_){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2838_ = lean_string_utf8_byte_size(v_s_2837_);
v___x_2839_ = lean_unsigned_to_nat(5u);
v___x_2840_ = lean_nat_dec_le(v___x_2839_, v___x_2838_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; 
lean_dec_ref(v_s_2837_);
v___x_2841_ = lean_box(0);
return v___x_2841_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2842_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2843_ = lean_unsigned_to_nat(0u);
v___x_2844_ = lean_string_memcmp(v_s_2837_, v___x_2842_, v___x_2843_, v___x_2843_, v___x_2839_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; 
lean_dec_ref(v_s_2837_);
v___x_2845_ = lean_box(0);
return v___x_2845_;
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
lean_inc_ref(v_s_2837_);
v___x_2846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2846_, 0, v_s_2837_);
lean_ctor_set(v___x_2846_, 1, v___x_2843_);
lean_ctor_set(v___x_2846_, 2, v___x_2838_);
v___x_2847_ = l_String_Slice_pos_x21(v___x_2846_, v___x_2839_);
lean_dec_ref_known(v___x_2846_, 3);
v___x_2848_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2848_, 0, v_s_2837_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
lean_ctor_set(v___x_2848_, 2, v___x_2838_);
v___x_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2850_, lean_object* v_pat_2851_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2850_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2853_, lean_object* v_pat_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2853_, v_pat_2854_);
lean_dec_ref(v_pat_2854_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v_x_2856_, lean_object* v_x_2857_, lean_object* v_v_2858_){
_start:
{
lean_inc_ref(v_v_2858_);
return v_v_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* v_x_2859_, lean_object* v_x_2860_, lean_object* v_v_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v_x_2859_, v_x_2860_, v_v_2861_);
lean_dec_ref(v_v_2861_);
lean_dec_ref(v_x_2860_);
lean_dec(v_x_2859_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object* v___x_2866_, lean_object* v_mainModuleName_2867_, lean_object* v_out_2868_, uint8_t v___x_2869_, lean_object* v___x_2870_, lean_object* v_fileName_2871_, lean_object* v___x_2872_, lean_object* v___x_2873_, lean_object* v___x_2874_, lean_object* v___x_2875_, lean_object* v___x_2876_, lean_object* v___x_2877_, lean_object* v___x_2878_, lean_object* v___x_2879_, uint8_t v_run_2880_, lean_object* v___x_2881_, uint8_t v_printLibDir_2882_){
_start:
{
lean_object* v_a_2885_; lean_object* v___x_2888_; lean_object* v___x_2889_; uint16_t v___y_2891_; lean_object* v___y_2892_; lean_object* v_fileName_2893_; lean_object* v_fileMap_2894_; lean_object* v_currNamespace_2895_; lean_object* v_openDecls_2896_; lean_object* v_initHeartbeats_2897_; lean_object* v_maxHeartbeats_2898_; lean_object* v_quotContext_2899_; lean_object* v_currMacroScope_2900_; lean_object* v_cancelTk_x3f_2901_; lean_object* v_inheritedTraceOptions_2902_; lean_object* v_currRecDepth_2903_; lean_object* v_ref_2904_; uint8_t v_suppressElabErrors_2905_; uint8_t v_isRecordingDeps_2906_; lean_object* v___x_2938_; lean_object* v___x_2939_; uint16_t v___y_2941_; uint8_t v___y_2942_; lean_object* v___y_2943_; uint16_t v___x_2964_; lean_object* v___x_2965_; lean_object* v_env_2966_; uint8_t v___x_2967_; uint16_t v___x_2968_; uint16_t v___x_2969_; uint16_t v___x_2970_; uint8_t v___x_2971_; 
v___x_2888_ = lean_io_get_num_heartbeats();
v___x_2889_ = lean_st_mk_ref(v___x_2866_);
v___x_2938_ = l_Lean_inheritedTraceOptions;
v___x_2939_ = lean_st_ref_get(v___x_2938_);
v___x_2964_ = l_Lean_OptionFlags_ofOptions(v___x_2881_);
v___x_2965_ = lean_st_ref_get(v___x_2889_);
v_env_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc_ref(v_env_2966_);
lean_dec(v___x_2965_);
v___x_2967_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2966_);
lean_dec_ref(v_env_2966_);
v___x_2968_ = 512;
v___x_2969_ = lean_uint16_land(v___x_2964_, v___x_2968_);
v___x_2970_ = 0;
v___x_2971_ = lean_uint16_dec_eq(v___x_2969_, v___x_2970_);
if (v___x_2971_ == 0)
{
if (v___x_2967_ == 0)
{
v___y_2941_ = v___x_2964_;
v___y_2942_ = v___x_2869_;
v___y_2943_ = v___x_2881_;
goto v___jp_2940_;
}
else
{
lean_dec_ref(v___x_2870_);
lean_inc(v___x_2873_);
v___y_2891_ = v___x_2964_;
v___y_2892_ = v___x_2881_;
v_fileName_2893_ = v_fileName_2871_;
v_fileMap_2894_ = v___x_2872_;
v_currNamespace_2895_ = v___x_2873_;
v_openDecls_2896_ = v___x_2874_;
v_initHeartbeats_2897_ = v___x_2888_;
v_maxHeartbeats_2898_ = v___x_2875_;
v_quotContext_2899_ = v___x_2873_;
v_currMacroScope_2900_ = v___x_2876_;
v_cancelTk_x3f_2901_ = v___x_2877_;
v_inheritedTraceOptions_2902_ = v___x_2939_;
v_currRecDepth_2903_ = v___x_2878_;
v_ref_2904_ = v___x_2879_;
v_suppressElabErrors_2905_ = v_run_2880_;
v_isRecordingDeps_2906_ = v_run_2880_;
goto v___jp_2890_;
}
}
else
{
if (v___x_2967_ == 0)
{
lean_dec_ref(v___x_2870_);
lean_inc(v___x_2873_);
v___y_2891_ = v___x_2964_;
v___y_2892_ = v___x_2881_;
v_fileName_2893_ = v_fileName_2871_;
v_fileMap_2894_ = v___x_2872_;
v_currNamespace_2895_ = v___x_2873_;
v_openDecls_2896_ = v___x_2874_;
v_initHeartbeats_2897_ = v___x_2888_;
v_maxHeartbeats_2898_ = v___x_2875_;
v_quotContext_2899_ = v___x_2873_;
v_currMacroScope_2900_ = v___x_2876_;
v_cancelTk_x3f_2901_ = v___x_2877_;
v_inheritedTraceOptions_2902_ = v___x_2939_;
v_currRecDepth_2903_ = v___x_2878_;
v_ref_2904_ = v___x_2879_;
v_suppressElabErrors_2905_ = v_run_2880_;
v_isRecordingDeps_2906_ = v_run_2880_;
goto v___jp_2890_;
}
else
{
v___y_2941_ = v___x_2964_;
v___y_2942_ = v_printLibDir_2882_;
v___y_2943_ = v___x_2881_;
goto v___jp_2940_;
}
}
v___jp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = lean_mk_io_user_error(v_a_2885_);
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
return v___x_2887_;
}
v___jp_2890_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2907_ = l_Lean_maxRecDepth;
v___x_2908_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___y_2892_, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2909_, 0, v_fileName_2893_);
lean_ctor_set(v___x_2909_, 1, v_fileMap_2894_);
lean_ctor_set(v___x_2909_, 2, v___y_2892_);
lean_ctor_set(v___x_2909_, 3, v___x_2908_);
lean_ctor_set(v___x_2909_, 4, v_currNamespace_2895_);
lean_ctor_set(v___x_2909_, 5, v_openDecls_2896_);
lean_ctor_set(v___x_2909_, 6, v_initHeartbeats_2897_);
lean_ctor_set(v___x_2909_, 7, v_maxHeartbeats_2898_);
lean_ctor_set(v___x_2909_, 8, v_quotContext_2899_);
lean_ctor_set(v___x_2909_, 9, v_currMacroScope_2900_);
lean_ctor_set(v___x_2909_, 10, v_cancelTk_x3f_2901_);
lean_ctor_set(v___x_2909_, 11, v_inheritedTraceOptions_2902_);
v___x_2910_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v_currRecDepth_2903_);
lean_ctor_set(v___x_2910_, 2, v_ref_2904_);
lean_ctor_set_uint16(v___x_2910_, sizeof(void*)*3, v___y_2891_);
lean_ctor_set_uint8(v___x_2910_, sizeof(void*)*3 + 2, v_suppressElabErrors_2905_);
lean_ctor_set_uint8(v___x_2910_, sizeof(void*)*3 + 3, v_isRecordingDeps_2906_);
v___x_2911_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2867_, v___x_2910_, v___x_2889_);
lean_dec_ref_known(v___x_2910_, 3);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2911_, 1);
v___x_2913_ = lean_st_ref_get(v___x_2889_);
lean_dec(v___x_2889_);
lean_dec(v___x_2913_);
v___x_2914_ = lean_string_to_utf8(v_a_2912_);
v___x_2915_ = lean_io_prim_handle_write(v_out_2868_, v___x_2914_);
lean_dec_ref(v___x_2914_);
return v___x_2915_;
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v___x_2889_);
v_a_2916_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2918_ = v___x_2911_;
v_isShared_2919_ = v_isSharedCheck_2937_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2911_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2937_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
if (lean_obj_tag(v_a_2916_) == 0)
{
lean_object* v_msg_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2924_; 
v_msg_2920_ = lean_ctor_get(v_a_2916_, 1);
lean_inc_ref(v_msg_2920_);
lean_dec_ref_known(v_a_2916_, 2);
v___x_2921_ = l_Lean_MessageData_toString(v_msg_2920_);
v___x_2922_ = lean_mk_io_user_error(v___x_2921_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v___x_2922_);
v___x_2924_ = v___x_2918_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
else
{
lean_object* v_id_2926_; lean_object* v___x_2927_; 
lean_del_object(v___x_2918_);
v_id_2926_ = lean_ctor_get(v_a_2916_, 0);
lean_inc(v_id_2926_);
lean_dec_ref_known(v_a_2916_, 2);
v___x_2927_ = l_Lean_InternalExceptionId_getName(v_id_2926_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_dec(v_id_2926_);
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v___x_2929_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0));
v___x_2930_ = l_Lean_Name_toString(v_a_2928_, v___x_2869_);
v___x_2931_ = lean_string_append(v___x_2929_, v___x_2930_);
lean_dec_ref(v___x_2930_);
v_a_2885_ = v___x_2931_;
goto v___jp_2884_;
}
else
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
lean_dec_ref_known(v___x_2927_, 1);
v___x_2932_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1));
v___x_2933_ = l_Nat_reprFast(v_id_2926_);
v___x_2934_ = lean_string_append(v___x_2932_, v___x_2933_);
lean_dec_ref(v___x_2933_);
v___x_2935_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2));
v___x_2936_ = lean_string_append(v___x_2934_, v___x_2935_);
v_a_2885_ = v___x_2936_;
goto v___jp_2884_;
}
}
}
}
}
v___jp_2940_:
{
lean_object* v___x_2944_; lean_object* v_env_2945_; lean_object* v_nextMacroScope_2946_; lean_object* v_ngen_2947_; lean_object* v_auxDeclNGen_2948_; lean_object* v_traceState_2949_; lean_object* v_recordedDeps_2950_; lean_object* v_messages_2951_; lean_object* v_infoState_2952_; lean_object* v_snapshotTasks_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2962_; 
v___x_2944_ = lean_st_ref_take(v___x_2889_);
v_env_2945_ = lean_ctor_get(v___x_2944_, 0);
v_nextMacroScope_2946_ = lean_ctor_get(v___x_2944_, 1);
v_ngen_2947_ = lean_ctor_get(v___x_2944_, 2);
v_auxDeclNGen_2948_ = lean_ctor_get(v___x_2944_, 3);
v_traceState_2949_ = lean_ctor_get(v___x_2944_, 4);
v_recordedDeps_2950_ = lean_ctor_get(v___x_2944_, 6);
v_messages_2951_ = lean_ctor_get(v___x_2944_, 7);
v_infoState_2952_ = lean_ctor_get(v___x_2944_, 8);
v_snapshotTasks_2953_ = lean_ctor_get(v___x_2944_, 9);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; 
v_unused_2963_ = lean_ctor_get(v___x_2944_, 5);
lean_dec(v_unused_2963_);
v___x_2955_ = v___x_2944_;
v_isShared_2956_ = v_isSharedCheck_2962_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_snapshotTasks_2953_);
lean_inc(v_infoState_2952_);
lean_inc(v_messages_2951_);
lean_inc(v_recordedDeps_2950_);
lean_inc(v_traceState_2949_);
lean_inc(v_auxDeclNGen_2948_);
lean_inc(v_ngen_2947_);
lean_inc(v_nextMacroScope_2946_);
lean_inc(v_env_2945_);
lean_dec(v___x_2944_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2962_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2957_ = l_Lean_Kernel_enableDiag(v_env_2945_, v___y_2942_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 5, v___x_2870_);
lean_ctor_set(v___x_2955_, 0, v___x_2957_);
v___x_2959_ = v___x_2955_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2957_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_nextMacroScope_2946_);
lean_ctor_set(v_reuseFailAlloc_2961_, 2, v_ngen_2947_);
lean_ctor_set(v_reuseFailAlloc_2961_, 3, v_auxDeclNGen_2948_);
lean_ctor_set(v_reuseFailAlloc_2961_, 4, v_traceState_2949_);
lean_ctor_set(v_reuseFailAlloc_2961_, 5, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2961_, 6, v_recordedDeps_2950_);
lean_ctor_set(v_reuseFailAlloc_2961_, 7, v_messages_2951_);
lean_ctor_set(v_reuseFailAlloc_2961_, 8, v_infoState_2952_);
lean_ctor_set(v_reuseFailAlloc_2961_, 9, v_snapshotTasks_2953_);
v___x_2959_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_st_ref_put(v___x_2889_, v___x_2959_);
lean_inc(v___x_2873_);
v___y_2891_ = v___y_2941_;
v___y_2892_ = v___y_2943_;
v_fileName_2893_ = v_fileName_2871_;
v_fileMap_2894_ = v___x_2872_;
v_currNamespace_2895_ = v___x_2873_;
v_openDecls_2896_ = v___x_2874_;
v_initHeartbeats_2897_ = v___x_2888_;
v_maxHeartbeats_2898_ = v___x_2875_;
v_quotContext_2899_ = v___x_2873_;
v_currMacroScope_2900_ = v___x_2876_;
v_cancelTk_x3f_2901_ = v___x_2877_;
v_inheritedTraceOptions_2902_ = v___x_2939_;
v_currRecDepth_2903_ = v___x_2878_;
v_ref_2904_ = v___x_2879_;
v_suppressElabErrors_2905_ = v_run_2880_;
v_isRecordingDeps_2906_ = v_run_2880_;
goto v___jp_2890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object** _args){
lean_object* v___x_2972_ = _args[0];
lean_object* v_mainModuleName_2973_ = _args[1];
lean_object* v_out_2974_ = _args[2];
lean_object* v___x_2975_ = _args[3];
lean_object* v___x_2976_ = _args[4];
lean_object* v_fileName_2977_ = _args[5];
lean_object* v___x_2978_ = _args[6];
lean_object* v___x_2979_ = _args[7];
lean_object* v___x_2980_ = _args[8];
lean_object* v___x_2981_ = _args[9];
lean_object* v___x_2982_ = _args[10];
lean_object* v___x_2983_ = _args[11];
lean_object* v___x_2984_ = _args[12];
lean_object* v___x_2985_ = _args[13];
lean_object* v_run_2986_ = _args[14];
lean_object* v___x_2987_ = _args[15];
lean_object* v_printLibDir_2988_ = _args[16];
lean_object* v___y_2989_ = _args[17];
_start:
{
uint8_t v___x_12847__boxed_2990_; uint8_t v_run_boxed_2991_; uint8_t v_printLibDir_boxed_2992_; lean_object* v_res_2993_; 
v___x_12847__boxed_2990_ = lean_unbox(v___x_2975_);
v_run_boxed_2991_ = lean_unbox(v_run_2986_);
v_printLibDir_boxed_2992_ = lean_unbox(v_printLibDir_2988_);
v_res_2993_ = l___private_Lean_Shell_0__Lean_shellMain___lam__1(v___x_2972_, v_mainModuleName_2973_, v_out_2974_, v___x_12847__boxed_2990_, v___x_2976_, v_fileName_2977_, v___x_2978_, v___x_2979_, v___x_2980_, v___x_2981_, v___x_2982_, v___x_2983_, v___x_2984_, v___x_2985_, v_run_boxed_2991_, v___x_2987_, v_printLibDir_boxed_2992_);
lean_dec(v_out_2974_);
return v_res_2993_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = l_Lean_Options_empty;
v___x_2996_ = l_Lean_Core_getMaxHeartbeats(v___x_2995_);
return v___x_2996_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2997_ = lean_unsigned_to_nat(1u);
v___x_2998_ = l_Lean_firstFrontendMacroScope;
v___x_2999_ = lean_nat_add(v___x_2998_, v___x_2997_);
return v___x_2999_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3010_ = lean_unsigned_to_nat(32u);
v___x_3011_ = lean_mk_empty_array_with_capacity(v___x_3010_);
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
return v___x_3012_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8(void){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_3013_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8);
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
return v___x_3015_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10(void){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9);
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2(lean_object* v___x_3018_, uint8_t v___x_3019_, lean_object* v_val_3020_, lean_object* v_mainModuleName_3021_, lean_object* v_fileName_3022_, uint8_t v_run_3023_, uint8_t v_printLibDir_3024_, lean_object* v___x_3025_, lean_object* v_out_3026_){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; uint64_t v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; size_t v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___f_3058_; lean_object* v___x_3059_; 
v___x_3028_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__0));
v___x_3029_ = l_Lean_instInhabitedFileMap_default;
v___x_3030_ = l_Lean_Options_empty;
v___x_3031_ = lean_box(0);
v___x_3032_ = lean_box(0);
v___x_3033_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1);
v___x_3034_ = l_Lean_firstFrontendMacroScope;
v___x_3035_ = lean_box(0);
v___x_3036_ = lean_box(0);
v___x_3037_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2);
v___x_3038_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__5));
v___x_3039_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__6));
v___x_3040_ = 0ULL;
v___x_3041_ = lean_unsigned_to_nat(32u);
v___x_3042_ = lean_mk_empty_array_with_capacity(v___x_3041_);
v___x_3043_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7);
v___x_3044_ = ((size_t)5ULL);
lean_inc_n(v___x_3018_, 5);
v___x_3045_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3045_, 0, v___x_3043_);
lean_ctor_set(v___x_3045_, 1, v___x_3042_);
lean_ctor_set(v___x_3045_, 2, v___x_3018_);
lean_ctor_set(v___x_3045_, 3, v___x_3018_);
lean_ctor_set_usize(v___x_3045_, 4, v___x_3044_);
lean_inc_ref_n(v___x_3045_, 3);
v___x_3046_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
lean_ctor_set_uint64(v___x_3046_, sizeof(void*)*1, v___x_3040_);
v___x_3047_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9);
v___x_3048_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10);
v___x_3049_ = lean_mk_empty_array_with_capacity(v___x_3018_);
lean_inc_ref_n(v___x_3049_, 2);
v___x_3050_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
lean_ctor_set(v___x_3050_, 1, v___x_3030_);
lean_ctor_set(v___x_3050_, 2, v___x_3049_);
lean_ctor_set(v___x_3050_, 3, v___x_3018_);
lean_ctor_set(v___x_3050_, 4, v___x_3018_);
lean_ctor_set(v___x_3050_, 5, v___x_3018_);
v___x_3051_ = l_Lean_NameSet_empty;
v___x_3052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3045_);
lean_ctor_set(v___x_3052_, 1, v___x_3045_);
lean_ctor_set(v___x_3052_, 2, v___x_3051_);
v___x_3053_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3053_, 0, v___x_3047_);
lean_ctor_set(v___x_3053_, 1, v___x_3047_);
lean_ctor_set(v___x_3053_, 2, v___x_3045_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*3, v___x_3019_);
v___x_3054_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3054_, 0, v_val_3020_);
lean_ctor_set(v___x_3054_, 1, v___x_3037_);
lean_ctor_set(v___x_3054_, 2, v___x_3038_);
lean_ctor_set(v___x_3054_, 3, v___x_3039_);
lean_ctor_set(v___x_3054_, 4, v___x_3046_);
lean_ctor_set(v___x_3054_, 5, v___x_3048_);
lean_ctor_set(v___x_3054_, 6, v___x_3050_);
lean_ctor_set(v___x_3054_, 7, v___x_3052_);
lean_ctor_set(v___x_3054_, 8, v___x_3053_);
lean_ctor_set(v___x_3054_, 9, v___x_3049_);
v___x_3055_ = lean_box(v___x_3019_);
v___x_3056_ = lean_box(v_run_3023_);
v___x_3057_ = lean_box(v_printLibDir_3024_);
v___f_3058_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 18, 17);
lean_closure_set(v___f_3058_, 0, v___x_3054_);
lean_closure_set(v___f_3058_, 1, v_mainModuleName_3021_);
lean_closure_set(v___f_3058_, 2, v_out_3026_);
lean_closure_set(v___f_3058_, 3, v___x_3055_);
lean_closure_set(v___f_3058_, 4, v___x_3048_);
lean_closure_set(v___f_3058_, 5, v_fileName_3022_);
lean_closure_set(v___f_3058_, 6, v___x_3029_);
lean_closure_set(v___f_3058_, 7, v___x_3031_);
lean_closure_set(v___f_3058_, 8, v___x_3032_);
lean_closure_set(v___f_3058_, 9, v___x_3033_);
lean_closure_set(v___f_3058_, 10, v___x_3034_);
lean_closure_set(v___f_3058_, 11, v___x_3035_);
lean_closure_set(v___f_3058_, 12, v___x_3018_);
lean_closure_set(v___f_3058_, 13, v___x_3036_);
lean_closure_set(v___f_3058_, 14, v___x_3056_);
lean_closure_set(v___f_3058_, 15, v___x_3030_);
lean_closure_set(v___f_3058_, 16, v___x_3057_);
v___x_3059_ = l_Lean_profileitIOUnsafe___redArg(v___x_3028_, v___x_3025_, v___f_3058_, v___x_3031_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___boxed(lean_object* v___x_3060_, lean_object* v___x_3061_, lean_object* v_val_3062_, lean_object* v_mainModuleName_3063_, lean_object* v_fileName_3064_, lean_object* v_run_3065_, lean_object* v_printLibDir_3066_, lean_object* v___x_3067_, lean_object* v_out_3068_, lean_object* v___y_3069_){
_start:
{
uint8_t v___x_13070__boxed_3070_; uint8_t v_run_boxed_3071_; uint8_t v_printLibDir_boxed_3072_; lean_object* v_res_3073_; 
v___x_13070__boxed_3070_ = lean_unbox(v___x_3061_);
v_run_boxed_3071_ = lean_unbox(v_run_3065_);
v_printLibDir_boxed_3072_ = lean_unbox(v_printLibDir_3066_);
v_res_3073_ = l___private_Lean_Shell_0__Lean_shellMain___lam__2(v___x_3060_, v___x_13070__boxed_3070_, v_val_3062_, v_mainModuleName_3063_, v_fileName_3064_, v_run_boxed_3071_, v_printLibDir_boxed_3072_, v___x_3067_, v_out_3068_);
lean_dec_ref(v___x_3067_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_3074_, lean_object* v_a_3075_, lean_object* v_b_3076_){
_start:
{
lean_object* v_str_3077_; lean_object* v_startInclusive_3078_; lean_object* v_endExclusive_3079_; lean_object* v___x_3080_; uint8_t v_decide_3081_; 
v_str_3077_ = lean_ctor_get(v_val_3074_, 0);
v_startInclusive_3078_ = lean_ctor_get(v_val_3074_, 1);
v_endExclusive_3079_ = lean_ctor_get(v_val_3074_, 2);
v___x_3080_ = lean_nat_sub(v_endExclusive_3079_, v_startInclusive_3078_);
v_decide_3081_ = lean_nat_dec_eq(v_a_3075_, v___x_3080_);
lean_dec(v___x_3080_);
if (v_decide_3081_ == 0)
{
lean_object* v___x_3082_; uint32_t v___x_3083_; uint32_t v___x_3084_; uint8_t v___x_3085_; 
v___x_3082_ = lean_nat_add(v_startInclusive_3078_, v_a_3075_);
v___x_3083_ = lean_string_utf8_get_fast(v_str_3077_, v___x_3082_);
v___x_3084_ = 10;
v___x_3085_ = lean_uint32_dec_eq(v___x_3083_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
lean_dec(v_a_3075_);
v___x_3086_ = lean_box(0);
v___x_3087_ = lean_string_utf8_next_fast(v_str_3077_, v___x_3082_);
lean_dec(v___x_3082_);
v___x_3088_ = lean_nat_sub(v___x_3087_, v_startInclusive_3078_);
v_a_3075_ = v___x_3088_;
v_b_3076_ = v___x_3086_;
goto _start;
}
else
{
lean_object* v___x_3090_; 
lean_dec(v___x_3082_);
v___x_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3090_, 0, v_a_3075_);
return v___x_3090_;
}
}
else
{
lean_dec(v_a_3075_);
lean_inc(v_b_3076_);
return v_b_3076_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_3091_, lean_object* v_a_3092_, lean_object* v_b_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3091_, v_a_3092_, v_b_3093_);
lean_dec(v_b_3093_);
lean_dec_ref(v_val_3091_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_s_3095_){
_start:
{
uint32_t v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = 10;
v___x_3098_ = lean_string_push(v_s_3095_, v___x_3097_);
v___x_3099_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_s_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_s_3100_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_3103_){
_start:
{
uint32_t v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = 10;
v___x_3106_ = lean_string_push(v_s_3103_, v___x_3105_);
v___x_3107_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_3108_);
return v_res_3110_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1(void){
_start:
{
lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = lean_box(0);
v___x_3113_ = lean_internal_has_address_sanitizer(v___x_3112_);
return v___x_3113_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2(void){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = lean_box(0);
v___x_3115_ = lean_internal_get_option_overrides(v___x_3114_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* v_args_3126_, lean_object* v_opts_3127_){
_start:
{
lean_object* v_fns_3130_; uint8_t v_printPrefix_3149_; 
v_printPrefix_3149_ = lean_ctor_get_uint8(v_opts_3127_, sizeof(void*)*13 + 9);
if (v_printPrefix_3149_ == 0)
{
uint8_t v_printLibDir_3150_; 
v_printLibDir_3150_ = lean_ctor_get_uint8(v_opts_3127_, sizeof(void*)*13 + 10);
if (v_printLibDir_3150_ == 0)
{
lean_object* v_leanOpts_3151_; lean_object* v_forwardedArgs_3152_; uint8_t v_component_3153_; uint8_t v_useStdin_3154_; uint8_t v_onlyDeps_3155_; uint8_t v_onlySrcDeps_3156_; uint8_t v_depsJson_3157_; uint32_t v_trustLevel_3158_; lean_object* v_rootDir_x3f_3159_; lean_object* v_setupFileName_x3f_3160_; lean_object* v_oleanFileName_x3f_3161_; lean_object* v_ileanFileName_x3f_3162_; lean_object* v_cFileName_x3f_3163_; lean_object* v_bcFileName_x3f_3164_; uint8_t v_jsonOutput_3165_; lean_object* v_errorOnKinds_3166_; uint8_t v_printStats_3167_; uint8_t v_run_3168_; lean_object* v_incrSaveFileName_x3f_3169_; lean_object* v_incrLoadFileName_x3f_3170_; lean_object* v_incrHeaderSaveFileName_x3f_3171_; lean_object* v___f_3172_; lean_object* v___y_3174_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; uint8_t v___x_3220_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v_mainModuleName_3256_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v_contents_3300_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v_str_3348_; lean_object* v_startInclusive_3349_; lean_object* v_endExclusive_3350_; lean_object* v___y_3351_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v_fileName_3453_; lean_object* v___y_3458_; lean_object* v___y_3459_; uint8_t v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; uint8_t v___y_3496_; lean_object* v_fst_3497_; lean_object* v_snd_3498_; uint8_t v___y_3500_; lean_object* v___x_3530_; lean_object* v_maxMemory_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; 
v_leanOpts_3151_ = lean_ctor_get(v_opts_3127_, 0);
lean_inc_ref(v_leanOpts_3151_);
v_forwardedArgs_3152_ = lean_ctor_get(v_opts_3127_, 1);
lean_inc_ref(v_forwardedArgs_3152_);
v_component_3153_ = lean_ctor_get_uint8(v_opts_3127_, sizeof(void*)*13 + 8);
v_useStdin_3154_ = lean_ctor_get_uint8(v_opts_3127_, sizeof(void*)*13 + 11);
v_onlyDeps_3155_ = lean_ctor_get_uint8(v_opts_3127_, sizeof(void*)*13 + 12);
v_onlySrcDeps_3156_ = lean_ctor_get_uint8(v_opts_3127_, sizeof(void*)*13 + 13);
v_depsJson_3157_ = lean_ctor_get_uint8(v_opts_3127_, sizeof(void*)*13 + 14);
v_trustLevel_3158_ = lean_ctor_get_uint32(v_opts_3127_, sizeof(void*)*13);
v_rootDir_x3f_3159_ = lean_ctor_get(v_opts_3127_, 3);
lean_inc(v_rootDir_x3f_3159_);
v_setupFileName_x3f_3160_ = lean_ctor_get(v_opts_3127_, 4);
lean_inc(v_setupFileName_x3f_3160_);
v_oleanFileName_x3f_3161_ = lean_ctor_get(v_opts_3127_, 5);
lean_inc(v_oleanFileName_x3f_3161_);
v_ileanFileName_x3f_3162_ = lean_ctor_get(v_opts_3127_, 6);
lean_inc(v_ileanFileName_x3f_3162_);
v_cFileName_x3f_3163_ = lean_ctor_get(v_opts_3127_, 7);
lean_inc(v_cFileName_x3f_3163_);
v_bcFileName_x3f_3164_ = lean_ctor_get(v_opts_3127_, 8);
lean_inc(v_bcFileName_x3f_3164_);
v_jsonOutput_3165_ = lean_ctor_get_uint8(v_opts_3127_, sizeof(void*)*13 + 15);
v_errorOnKinds_3166_ = lean_ctor_get(v_opts_3127_, 9);
lean_inc_ref(v_errorOnKinds_3166_);
v_printStats_3167_ = lean_ctor_get_uint8(v_opts_3127_, sizeof(void*)*13 + 16);
v_run_3168_ = lean_ctor_get_uint8(v_opts_3127_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_3169_ = lean_ctor_get(v_opts_3127_, 10);
lean_inc(v_incrSaveFileName_x3f_3169_);
v_incrLoadFileName_x3f_3170_ = lean_ctor_get(v_opts_3127_, 11);
lean_inc(v_incrLoadFileName_x3f_3170_);
v_incrHeaderSaveFileName_x3f_3171_ = lean_ctor_get(v_opts_3127_, 12);
lean_inc(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec_ref(v_opts_3127_);
v___f_3172_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__0));
v___x_3192_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__2, &l___private_Lean_Shell_0__Lean_shellMain___closed__2_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2);
v___x_3193_ = l_Lean_Options_mergeBy(v___f_3172_, v_leanOpts_3151_, v___x_3192_);
v___x_3220_ = 1;
v___x_3530_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3531_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3193_, v___x_3530_);
v___x_3532_ = lean_unsigned_to_nat(0u);
v___x_3533_ = lean_nat_dec_eq(v_maxMemory_3531_, v___x_3532_);
if (v___x_3533_ == 0)
{
size_t v___x_3534_; size_t v___x_3535_; size_t v___x_3536_; size_t v___x_3537_; lean_object* v___x_3538_; 
v___x_3534_ = lean_usize_of_nat(v_maxMemory_3531_);
lean_dec(v_maxMemory_3531_);
v___x_3535_ = ((size_t)10ULL);
v___x_3536_ = lean_usize_shift_left(v___x_3534_, v___x_3535_);
v___x_3537_ = lean_usize_shift_left(v___x_3536_, v___x_3535_);
v___x_3538_ = lean_internal_set_max_memory(v___x_3537_);
goto v___jp_3521_;
}
else
{
lean_dec(v_maxMemory_3531_);
goto v___jp_3521_;
}
v___jp_3173_:
{
lean_object* v___x_3175_; uint8_t v___x_3176_; 
v___x_3175_ = lean_display_cumulative_profiling_times();
v___x_3176_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__1, &l___private_Lean_Shell_0__Lean_shellMain___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1);
if (v___x_3176_ == 0)
{
if (lean_obj_tag(v___y_3174_) == 0)
{
uint8_t v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = 1;
v___x_3178_ = lean_io_exit(v___x_3177_);
return v___x_3178_;
}
else
{
uint8_t v___x_3179_; lean_object* v___x_3180_; 
lean_dec_ref_known(v___y_3174_, 1);
v___x_3179_ = 0;
v___x_3180_ = lean_io_exit(v___x_3179_);
return v___x_3180_;
}
}
else
{
if (lean_obj_tag(v___y_3174_) == 0)
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
return v___x_3182_;
}
else
{
lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3190_; 
v_isSharedCheck_3190_ = !lean_is_exclusive(v___y_3174_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; 
v_unused_3191_ = lean_ctor_get(v___y_3174_, 0);
lean_dec(v_unused_3191_);
v___x_3184_ = v___y_3174_;
v_isShared_3185_ = v_isSharedCheck_3190_;
goto v_resetjp_3183_;
}
else
{
lean_dec(v___y_3174_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3190_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3186_; lean_object* v___x_3188_; 
v___x_3186_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3185_ == 0)
{
lean_ctor_set_tag(v___x_3184_, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3186_);
v___x_3188_ = v___x_3184_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3186_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
}
v___jp_3194_:
{
if (lean_obj_tag(v_bcFileName_x3f_3164_) == 1)
{
lean_object* v_val_3198_; lean_object* v___x_3199_; 
v_val_3198_ = lean_ctor_get(v_bcFileName_x3f_3164_, 0);
lean_inc(v_val_3198_);
lean_dec_ref_known(v_bcFileName_x3f_3164_, 1);
v___x_3199_ = lean_init_llvm();
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
lean_dec_ref_known(v___x_3199_, 1);
v___x_3200_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__3));
v___x_3201_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(v___x_3201_, 0, v___y_3196_);
lean_closure_set(v___x_3201_, 1, v___y_3195_);
lean_closure_set(v___x_3201_, 2, v_val_3198_);
v___x_3202_ = lean_box(0);
v___x_3203_ = l_Lean_profileitIOUnsafe___redArg(v___x_3200_, v___x_3193_, v___x_3201_, v___x_3202_);
lean_dec_ref(v___x_3193_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_dec_ref_known(v___x_3203_, 1);
v___y_3174_ = v___y_3197_;
goto v___jp_3173_;
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec(v___y_3197_);
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v_val_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___x_3193_);
v_a_3212_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3199_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3199_);
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
else
{
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___x_3193_);
lean_dec(v_bcFileName_x3f_3164_);
v___y_3174_ = v___y_3197_;
goto v___jp_3173_;
}
}
v___jp_3221_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__4));
v___x_3223_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3222_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v___x_3224_; 
lean_dec_ref_known(v___x_3223_, 1);
v___x_3224_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3220_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3232_; 
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; 
v_unused_3233_ = lean_ctor_get(v___x_3224_, 0);
lean_dec(v_unused_3233_);
v___x_3226_ = v___x_3224_;
v_isShared_3227_ = v_isSharedCheck_3232_;
goto v_resetjp_3225_;
}
else
{
lean_dec(v___x_3224_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3232_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3228_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3228_);
v___x_3230_ = v___x_3226_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3228_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
v_a_3234_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3224_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3224_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
v_a_3242_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3223_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3223_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
v___jp_3250_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = lean_unsigned_to_nat(0u);
v___x_3258_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__5));
lean_inc(v_mainModuleName_3256_);
lean_inc_ref(v___x_3193_);
v___x_3259_ = l_Lean_Elab_runFrontend(v___y_3253_, v___x_3193_, v___y_3254_, v_mainModuleName_3256_, v_trustLevel_3158_, v_oleanFileName_x3f_3161_, v_ileanFileName_x3f_3162_, v_jsonOutput_3165_, v_errorOnKinds_3166_, v___x_3258_, v_printStats_3167_, v___y_3255_, v_incrSaveFileName_x3f_3169_, v_incrLoadFileName_x3f_3170_, v_incrHeaderSaveFileName_x3f_3171_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_ileanFileName_x3f_3162_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3286_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3262_ = v___x_3259_;
v_isShared_3263_ = v_isSharedCheck_3286_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3259_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3286_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
if (lean_obj_tag(v_a_3260_) == 1)
{
if (v_run_3168_ == 0)
{
lean_del_object(v___x_3262_);
lean_dec(v___y_3252_);
if (lean_obj_tag(v_cFileName_x3f_3163_) == 1)
{
lean_object* v_val_3264_; lean_object* v_val_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___f_3269_; lean_object* v___x_3270_; 
v_val_3264_ = lean_ctor_get(v_a_3260_, 0);
lean_inc_n(v_val_3264_, 2);
v_val_3265_ = lean_ctor_get(v_cFileName_x3f_3163_, 0);
lean_inc(v_val_3265_);
lean_dec_ref_known(v_cFileName_x3f_3163_, 1);
v___x_3266_ = lean_box(v___x_3220_);
v___x_3267_ = lean_box(v_run_3168_);
v___x_3268_ = lean_box(v_printLibDir_3150_);
lean_inc_ref(v___x_3193_);
lean_inc(v_mainModuleName_3256_);
v___f_3269_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___boxed), 10, 8);
lean_closure_set(v___f_3269_, 0, v___x_3257_);
lean_closure_set(v___f_3269_, 1, v___x_3266_);
lean_closure_set(v___f_3269_, 2, v_val_3264_);
lean_closure_set(v___f_3269_, 3, v_mainModuleName_3256_);
lean_closure_set(v___f_3269_, 4, v___y_3251_);
lean_closure_set(v___f_3269_, 5, v___x_3267_);
lean_closure_set(v___f_3269_, 6, v___x_3268_);
lean_closure_set(v___f_3269_, 7, v___x_3193_);
v___x_3270_ = l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(v_val_3265_, v___f_3269_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_dec_ref_known(v___x_3270_, 1);
v___y_3195_ = v_mainModuleName_3256_;
v___y_3196_ = v_val_3264_;
v___y_3197_ = v_a_3260_;
goto v___jp_3194_;
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v_val_3264_);
lean_dec_ref_known(v_a_3260_, 1);
lean_dec(v_mainModuleName_3256_);
lean_dec_ref(v___x_3193_);
lean_dec(v_bcFileName_x3f_3164_);
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
else
{
lean_object* v_val_3279_; 
lean_dec_ref(v___y_3251_);
lean_dec(v_cFileName_x3f_3163_);
v_val_3279_ = lean_ctor_get(v_a_3260_, 0);
lean_inc(v_val_3279_);
v___y_3195_ = v_mainModuleName_3256_;
v___y_3196_ = v_val_3279_;
v___y_3197_ = v_a_3260_;
goto v___jp_3194_;
}
}
else
{
lean_object* v_val_3280_; uint32_t v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3284_; 
lean_dec(v_mainModuleName_3256_);
lean_dec_ref(v___y_3251_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
v_val_3280_ = lean_ctor_get(v_a_3260_, 0);
lean_inc(v_val_3280_);
lean_dec_ref_known(v_a_3260_, 1);
v___x_3281_ = lean_eval_main(v_val_3280_, v___x_3193_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___x_3193_);
lean_dec(v_val_3280_);
v___x_3282_ = lean_box_uint32(v___x_3281_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v___x_3282_);
v___x_3284_ = v___x_3262_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3282_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
else
{
lean_del_object(v___x_3262_);
lean_dec(v_mainModuleName_3256_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec_ref(v___x_3193_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
v___y_3174_ = v_a_3260_;
goto v___jp_3173_;
}
}
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_dec(v_mainModuleName_3256_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec_ref(v___x_3193_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
v_a_3287_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3289_ = v___x_3259_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3259_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
v___jp_3295_:
{
if (lean_obj_tag(v_setupFileName_x3f_3160_) == 0)
{
lean_object* v___x_3301_; 
v___x_3301_ = lean_box(0);
if (lean_obj_tag(v___y_3298_) == 1)
{
lean_object* v_val_3302_; lean_object* v___x_3303_; 
v_val_3302_ = lean_ctor_get(v___y_3298_, 0);
lean_inc(v_val_3302_);
lean_dec_ref_known(v___y_3298_, 1);
v___x_3303_ = l_Lean_moduleNameOfFileName(v_val_3302_, v_rootDir_x3f_3159_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref_known(v___x_3303_, 1);
v___y_3251_ = v___y_3296_;
v___y_3252_ = v___y_3297_;
v___y_3253_ = v_contents_3300_;
v___y_3254_ = v___y_3299_;
v___y_3255_ = v___x_3301_;
v_mainModuleName_3256_ = v_a_3304_;
goto v___jp_3250_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_3161_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_3163_) == 0)
{
lean_object* v___x_3305_; 
lean_dec_ref_known(v___x_3303_, 1);
v___x_3305_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__7));
v___y_3251_ = v___y_3296_;
v___y_3252_ = v___y_3297_;
v___y_3253_ = v_contents_3300_;
v___y_3254_ = v___y_3299_;
v___y_3255_ = v___x_3301_;
v_mainModuleName_3256_ = v___x_3305_;
goto v___jp_3250_;
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec_ref_known(v_cFileName_x3f_3163_, 1);
lean_dec_ref(v_contents_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v___x_3193_);
lean_dec(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec(v_incrLoadFileName_x3f_3170_);
lean_dec(v_incrSaveFileName_x3f_3169_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_ileanFileName_x3f_3162_);
v_a_3306_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3303_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3303_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec_ref_known(v_oleanFileName_x3f_3161_, 1);
lean_dec_ref(v_contents_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v___x_3193_);
lean_dec(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec(v_incrLoadFileName_x3f_3170_);
lean_dec(v_incrSaveFileName_x3f_3169_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
lean_dec(v_ileanFileName_x3f_3162_);
v_a_3314_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3303_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3303_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
}
else
{
lean_object* v___x_3322_; 
lean_dec(v___y_3298_);
lean_dec(v_rootDir_x3f_3159_);
v___x_3322_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__7));
v___y_3251_ = v___y_3296_;
v___y_3252_ = v___y_3297_;
v___y_3253_ = v_contents_3300_;
v___y_3254_ = v___y_3299_;
v___y_3255_ = v___x_3301_;
v_mainModuleName_3256_ = v___x_3322_;
goto v___jp_3250_;
}
}
else
{
lean_object* v_val_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3341_; 
lean_dec(v___y_3298_);
lean_dec(v_rootDir_x3f_3159_);
v_val_3323_ = lean_ctor_get(v_setupFileName_x3f_3160_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_setupFileName_x3f_3160_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3325_ = v_setupFileName_x3f_3160_;
v_isShared_3326_ = v_isSharedCheck_3341_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_val_3323_);
lean_dec(v_setupFileName_x3f_3160_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3341_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_ModuleSetup_load(v_val_3323_);
lean_dec(v_val_3323_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v_name_3329_; lean_object* v___x_3331_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v_name_3329_ = lean_ctor_get(v_a_3328_, 0);
lean_inc(v_name_3329_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 0, v_a_3328_);
v___x_3331_ = v___x_3325_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3328_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
v___y_3251_ = v___y_3296_;
v___y_3252_ = v___y_3297_;
v___y_3253_ = v_contents_3300_;
v___y_3254_ = v___y_3299_;
v___y_3255_ = v___x_3331_;
v_mainModuleName_3256_ = v_name_3329_;
goto v___jp_3250_;
}
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_del_object(v___x_3325_);
lean_dec_ref(v_contents_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v___x_3193_);
lean_dec(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec(v_incrLoadFileName_x3f_3170_);
lean_dec(v_incrSaveFileName_x3f_3169_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
lean_dec(v_ileanFileName_x3f_3162_);
lean_dec(v_oleanFileName_x3f_3161_);
v_a_3333_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3327_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3327_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
}
}
v___jp_3342_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3352_ = lean_nat_add(v_startInclusive_3349_, v___y_3351_);
lean_dec(v___y_3351_);
lean_inc(v___x_3352_);
lean_inc_ref(v_str_3348_);
v___x_3353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3353_, 0, v_str_3348_);
lean_ctor_set(v___x_3353_, 1, v_startInclusive_3349_);
lean_ctor_set(v___x_3353_, 2, v___x_3352_);
v___x_3354_ = l_String_Slice_trimAscii(v___x_3353_);
v___x_3355_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__8));
v___x_3356_ = lean_unsigned_to_nat(5u);
v___x_3357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3355_);
lean_ctor_set(v___x_3357_, 1, v___y_3346_);
lean_ctor_set(v___x_3357_, 2, v___x_3356_);
v___x_3358_ = l_String_Slice_beq(v___x_3354_, v___x_3357_);
lean_dec_ref_known(v___x_3357_, 3);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec(v___x_3352_);
lean_dec(v_endExclusive_3350_);
lean_dec_ref(v_str_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec_ref(v___x_3193_);
lean_dec(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec(v_incrLoadFileName_x3f_3170_);
lean_dec(v_incrSaveFileName_x3f_3169_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
lean_dec(v_ileanFileName_x3f_3162_);
lean_dec(v_oleanFileName_x3f_3161_);
lean_dec(v_setupFileName_x3f_3160_);
lean_dec(v_rootDir_x3f_3159_);
v___x_3359_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__9));
v___x_3360_ = l_String_Slice_toString(v___x_3354_);
lean_dec_ref(v___x_3354_);
v___x_3361_ = lean_string_append(v___x_3359_, v___x_3360_);
lean_dec_ref(v___x_3360_);
v___x_3362_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_3363_ = lean_string_append(v___x_3361_, v___x_3362_);
v___x_3364_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3363_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3372_; 
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3372_ == 0)
{
lean_object* v_unused_3373_; 
v_unused_3373_ = lean_ctor_get(v___x_3364_, 0);
lean_dec(v_unused_3373_);
v___x_3366_ = v___x_3364_;
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
else
{
lean_dec(v___x_3364_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3368_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3368_);
v___x_3370_ = v___x_3366_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
v_a_3374_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3364_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3364_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_object* v___x_3382_; 
lean_dec_ref(v___x_3354_);
v___x_3382_ = lean_string_utf8_extract_fast(v_str_3348_, v___x_3352_, v_endExclusive_3350_);
lean_dec(v_endExclusive_3350_);
lean_dec(v___x_3352_);
lean_dec_ref(v_str_3348_);
v___y_3296_ = v___y_3343_;
v___y_3297_ = v___y_3345_;
v___y_3298_ = v___y_3344_;
v___y_3299_ = v___y_3347_;
v_contents_3300_ = v___x_3382_;
goto v___jp_3295_;
}
}
v___jp_3383_:
{
if (lean_obj_tag(v___y_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v_a_3388_ = lean_ctor_get(v___y_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___y_3387_, 1);
v___x_3389_ = lean_unsigned_to_nat(0u);
v___x_3390_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_3391_ = l___private_Init_Data_String_Lossy_0__String_fromUTF8Lossy_go(v_a_3388_, v___x_3389_, v___x_3390_);
lean_dec(v_a_3388_);
if (v_onlyDeps_3155_ == 0)
{
if (v_onlySrcDeps_3156_ == 0)
{
lean_object* v___x_3392_; 
lean_inc_ref(v___x_3391_);
v___x_3392_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_3391_);
if (lean_obj_tag(v___x_3392_) == 1)
{
lean_object* v_val_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
lean_dec_ref(v___x_3391_);
v_val_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_val_3393_);
lean_dec_ref_known(v___x_3392_, 1);
v___x_3394_ = lean_box(0);
v___x_3395_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3393_, v___x_3389_, v___x_3394_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_str_3396_; lean_object* v_startInclusive_3397_; lean_object* v_endExclusive_3398_; lean_object* v___x_3399_; 
v_str_3396_ = lean_ctor_get(v_val_3393_, 0);
lean_inc_ref(v_str_3396_);
v_startInclusive_3397_ = lean_ctor_get(v_val_3393_, 1);
lean_inc(v_startInclusive_3397_);
v_endExclusive_3398_ = lean_ctor_get(v_val_3393_, 2);
lean_inc(v_endExclusive_3398_);
lean_dec(v_val_3393_);
v___x_3399_ = lean_nat_sub(v_endExclusive_3398_, v_startInclusive_3397_);
lean_inc_ref(v___y_3385_);
v___y_3343_ = v___y_3385_;
v___y_3344_ = v___y_3384_;
v___y_3345_ = v___y_3386_;
v___y_3346_ = v___x_3389_;
v___y_3347_ = v___y_3385_;
v_str_3348_ = v_str_3396_;
v_startInclusive_3349_ = v_startInclusive_3397_;
v_endExclusive_3350_ = v_endExclusive_3398_;
v___y_3351_ = v___x_3399_;
goto v___jp_3342_;
}
else
{
lean_object* v_val_3400_; lean_object* v_str_3401_; lean_object* v_startInclusive_3402_; lean_object* v_endExclusive_3403_; 
v_val_3400_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_val_3400_);
lean_dec_ref_known(v___x_3395_, 1);
v_str_3401_ = lean_ctor_get(v_val_3393_, 0);
lean_inc_ref(v_str_3401_);
v_startInclusive_3402_ = lean_ctor_get(v_val_3393_, 1);
lean_inc(v_startInclusive_3402_);
v_endExclusive_3403_ = lean_ctor_get(v_val_3393_, 2);
lean_inc(v_endExclusive_3403_);
lean_dec(v_val_3393_);
lean_inc_ref(v___y_3385_);
v___y_3343_ = v___y_3385_;
v___y_3344_ = v___y_3384_;
v___y_3345_ = v___y_3386_;
v___y_3346_ = v___x_3389_;
v___y_3347_ = v___y_3385_;
v_str_3348_ = v_str_3401_;
v_startInclusive_3349_ = v_startInclusive_3402_;
v_endExclusive_3350_ = v_endExclusive_3403_;
v___y_3351_ = v_val_3400_;
goto v___jp_3342_;
}
}
else
{
lean_dec(v___x_3392_);
lean_inc_ref(v___y_3385_);
v___y_3296_ = v___y_3385_;
v___y_3297_ = v___y_3386_;
v___y_3298_ = v___y_3384_;
v___y_3299_ = v___y_3385_;
v_contents_3300_ = v___x_3391_;
goto v___jp_3295_;
}
}
else
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_dec(v___y_3386_);
lean_dec(v___y_3384_);
lean_dec_ref(v___x_3193_);
lean_dec(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec(v_incrLoadFileName_x3f_3170_);
lean_dec(v_incrSaveFileName_x3f_3169_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
lean_dec(v_ileanFileName_x3f_3162_);
lean_dec(v_oleanFileName_x3f_3161_);
lean_dec(v_setupFileName_x3f_3160_);
lean_dec(v_rootDir_x3f_3159_);
v___x_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___y_3385_);
v___x_3405_ = l_Lean_Elab_printImportSrcs(v___x_3391_, v___x_3404_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3413_; 
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; 
v_unused_3414_ = lean_ctor_get(v___x_3405_, 0);
lean_dec(v_unused_3414_);
v___x_3407_ = v___x_3405_;
v_isShared_3408_ = v_isSharedCheck_3413_;
goto v_resetjp_3406_;
}
else
{
lean_dec(v___x_3405_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3413_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3409_; lean_object* v___x_3411_; 
v___x_3409_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3409_);
v___x_3411_ = v___x_3407_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3409_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
v_a_3415_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3405_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3405_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
lean_dec(v___y_3386_);
lean_dec(v___y_3384_);
lean_dec_ref(v___x_3193_);
lean_dec(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec(v_incrLoadFileName_x3f_3170_);
lean_dec(v_incrSaveFileName_x3f_3169_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
lean_dec(v_ileanFileName_x3f_3162_);
lean_dec(v_oleanFileName_x3f_3161_);
lean_dec(v_setupFileName_x3f_3160_);
lean_dec(v_rootDir_x3f_3159_);
v___x_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___y_3385_);
v___x_3424_ = l_Lean_Elab_printImports(v___x_3391_, v___x_3423_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3432_; 
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3432_ == 0)
{
lean_object* v_unused_3433_; 
v_unused_3433_ = lean_ctor_get(v___x_3424_, 0);
lean_dec(v_unused_3433_);
v___x_3426_ = v___x_3424_;
v_isShared_3427_ = v_isSharedCheck_3432_;
goto v_resetjp_3425_;
}
else
{
lean_dec(v___x_3424_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3432_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; lean_object* v___x_3430_; 
v___x_3428_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v___x_3428_);
v___x_3430_ = v___x_3426_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
v_a_3434_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3424_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3424_);
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
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___x_3193_);
lean_dec(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec(v_incrLoadFileName_x3f_3170_);
lean_dec(v_incrSaveFileName_x3f_3169_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
lean_dec(v_ileanFileName_x3f_3162_);
lean_dec(v_oleanFileName_x3f_3161_);
lean_dec(v_setupFileName_x3f_3160_);
lean_dec(v_rootDir_x3f_3159_);
v_a_3442_ = lean_ctor_get(v___y_3387_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___y_3387_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___y_3387_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___y_3387_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
v___jp_3450_:
{
if (v_useStdin_3154_ == 0)
{
lean_object* v___x_3454_; 
v___x_3454_ = l_IO_FS_readBinFile(v_fileName_3453_);
v___y_3384_ = v___y_3451_;
v___y_3385_ = v_fileName_3453_;
v___y_3386_ = v___y_3452_;
v___y_3387_ = v___x_3454_;
goto v___jp_3383_;
}
else
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_get_stdin();
v___x_3456_ = l_IO_FS_Stream_readBinToEnd(v___x_3455_);
v___y_3384_ = v___y_3451_;
v___y_3385_ = v_fileName_3453_;
v___y_3386_ = v___y_3452_;
v___y_3387_ = v___x_3456_;
goto v___jp_3383_;
}
}
v___jp_3457_:
{
if (lean_obj_tag(v___y_3459_) == 1)
{
lean_object* v_val_3460_; 
v_val_3460_ = lean_ctor_get(v___y_3459_, 0);
lean_inc(v_val_3460_);
v___y_3451_ = v___y_3459_;
v___y_3452_ = v___y_3458_;
v_fileName_3453_ = v_val_3460_;
goto v___jp_3450_;
}
else
{
if (v_useStdin_3154_ == 0)
{
lean_object* v___x_3461_; lean_object* v___x_3462_; 
lean_dec(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec_ref(v___x_3193_);
lean_dec(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec(v_incrLoadFileName_x3f_3170_);
lean_dec(v_incrSaveFileName_x3f_3169_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
lean_dec(v_ileanFileName_x3f_3162_);
lean_dec(v_oleanFileName_x3f_3161_);
lean_dec(v_setupFileName_x3f_3160_);
lean_dec(v_rootDir_x3f_3159_);
v___x_3461_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__4));
v___x_3462_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3461_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v___x_3463_; 
lean_dec_ref_known(v___x_3462_, 1);
v___x_3463_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3220_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3471_; 
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; 
v_unused_3472_ = lean_ctor_get(v___x_3463_, 0);
lean_dec(v_unused_3472_);
v___x_3465_ = v___x_3463_;
v_isShared_3466_ = v_isSharedCheck_3471_;
goto v_resetjp_3464_;
}
else
{
lean_dec(v___x_3463_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3471_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3467_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3467_);
v___x_3469_ = v___x_3465_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
v_a_3473_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3463_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3463_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
v_a_3481_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3462_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3462_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_object* v___x_3489_; 
v___x_3489_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__10));
v___y_3451_ = v___y_3459_;
v___y_3452_ = v___y_3458_;
v_fileName_3453_ = v___x_3489_;
goto v___jp_3450_;
}
}
}
v___jp_3490_:
{
uint8_t v___x_3494_; 
v___x_3494_ = l_List_isEmpty___redArg(v___y_3493_);
if (v___x_3494_ == 0)
{
lean_dec(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___x_3193_);
lean_dec(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec(v_incrLoadFileName_x3f_3170_);
lean_dec(v_incrSaveFileName_x3f_3169_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
lean_dec(v_ileanFileName_x3f_3162_);
lean_dec(v_oleanFileName_x3f_3161_);
lean_dec(v_setupFileName_x3f_3160_);
lean_dec(v_rootDir_x3f_3159_);
goto v___jp_3221_;
}
else
{
if (v___y_3491_ == 0)
{
v___y_3458_ = v___y_3493_;
v___y_3459_ = v___y_3492_;
goto v___jp_3457_;
}
else
{
lean_dec(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___x_3193_);
lean_dec(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec(v_incrLoadFileName_x3f_3170_);
lean_dec(v_incrSaveFileName_x3f_3169_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
lean_dec(v_ileanFileName_x3f_3162_);
lean_dec(v_oleanFileName_x3f_3161_);
lean_dec(v_setupFileName_x3f_3160_);
lean_dec(v_rootDir_x3f_3159_);
goto v___jp_3221_;
}
}
}
v___jp_3495_:
{
if (v_run_3168_ == 0)
{
v___y_3491_ = v___y_3496_;
v___y_3492_ = v_fst_3497_;
v___y_3493_ = v_snd_3498_;
goto v___jp_3490_;
}
else
{
if (v___y_3496_ == 0)
{
v___y_3458_ = v_snd_3498_;
v___y_3459_ = v_fst_3497_;
goto v___jp_3457_;
}
else
{
v___y_3491_ = v___y_3496_;
v___y_3492_ = v_fst_3497_;
v___y_3493_ = v_snd_3498_;
goto v___jp_3490_;
}
}
}
v___jp_3499_:
{
if (lean_obj_tag(v_args_3126_) == 0)
{
lean_object* v___x_3501_; 
v___x_3501_ = lean_box(0);
v___y_3496_ = v___y_3500_;
v_fst_3497_ = v___x_3501_;
v_snd_3498_ = v_args_3126_;
goto v___jp_3495_;
}
else
{
lean_object* v_head_3502_; lean_object* v_tail_3503_; lean_object* v___x_3504_; 
v_head_3502_ = lean_ctor_get(v_args_3126_, 0);
lean_inc(v_head_3502_);
v_tail_3503_ = lean_ctor_get(v_args_3126_, 1);
lean_inc(v_tail_3503_);
lean_dec_ref_known(v_args_3126_, 2);
v___x_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3504_, 0, v_head_3502_);
v___y_3496_ = v___y_3500_;
v_fst_3497_ = v___x_3504_;
v_snd_3498_ = v_tail_3503_;
goto v___jp_3495_;
}
}
v___jp_3505_:
{
switch(v_component_3153_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_3152_);
if (v_onlyDeps_3155_ == 0)
{
v___y_3500_ = v_printLibDir_3150_;
goto v___jp_3499_;
}
else
{
if (v_depsJson_3157_ == 0)
{
v___y_3500_ = v_depsJson_3157_;
goto v___jp_3499_;
}
else
{
lean_dec_ref(v___x_3193_);
lean_dec(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec(v_incrLoadFileName_x3f_3170_);
lean_dec(v_incrSaveFileName_x3f_3169_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
lean_dec(v_ileanFileName_x3f_3162_);
lean_dec(v_oleanFileName_x3f_3161_);
lean_dec(v_setupFileName_x3f_3160_);
lean_dec(v_rootDir_x3f_3159_);
if (v_useStdin_3154_ == 0)
{
lean_object* v___x_3506_; 
v___x_3506_ = lean_array_mk(v_args_3126_);
v_fns_3130_ = v___x_3506_;
goto v___jp_3129_;
}
else
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
lean_dec(v_args_3126_);
v___x_3507_ = lean_get_stdin();
v___x_3508_ = l_IO_FS_Stream_lines(v___x_3507_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3509_; 
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_a_3509_);
lean_dec_ref_known(v___x_3508_, 1);
v_fns_3130_ = v_a_3509_;
goto v___jp_3129_;
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
v_a_3510_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3508_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3508_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
lean_dec_ref(v___x_3193_);
lean_dec(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec(v_incrLoadFileName_x3f_3170_);
lean_dec(v_incrSaveFileName_x3f_3169_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
lean_dec(v_ileanFileName_x3f_3162_);
lean_dec(v_oleanFileName_x3f_3161_);
lean_dec(v_setupFileName_x3f_3160_);
lean_dec(v_rootDir_x3f_3159_);
lean_dec(v_args_3126_);
v___x_3518_ = lean_array_to_list(v_forwardedArgs_3152_);
v___x_3519_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3518_);
return v___x_3519_;
}
default: 
{
lean_object* v___x_3520_; 
lean_dec(v_incrHeaderSaveFileName_x3f_3171_);
lean_dec(v_incrLoadFileName_x3f_3170_);
lean_dec(v_incrSaveFileName_x3f_3169_);
lean_dec_ref(v_errorOnKinds_3166_);
lean_dec(v_bcFileName_x3f_3164_);
lean_dec(v_cFileName_x3f_3163_);
lean_dec(v_ileanFileName_x3f_3162_);
lean_dec(v_oleanFileName_x3f_3161_);
lean_dec(v_setupFileName_x3f_3160_);
lean_dec(v_rootDir_x3f_3159_);
lean_dec_ref(v_forwardedArgs_3152_);
lean_dec(v_args_3126_);
v___x_3520_ = l_Lean_Server_FileWorker_workerMain(v___x_3193_);
return v___x_3520_;
}
}
}
v___jp_3521_:
{
lean_object* v___x_3522_; lean_object* v_timeout_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v___x_3522_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3523_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3193_, v___x_3522_);
v___x_3524_ = lean_unsigned_to_nat(0u);
v___x_3525_ = lean_nat_dec_eq(v_timeout_3523_, v___x_3524_);
if (v___x_3525_ == 0)
{
size_t v___x_3526_; size_t v___x_3527_; size_t v___x_3528_; lean_object* v___x_3529_; 
v___x_3526_ = lean_usize_of_nat(v_timeout_3523_);
lean_dec(v_timeout_3523_);
v___x_3527_ = ((size_t)1000ULL);
v___x_3528_ = lean_usize_mul(v___x_3526_, v___x_3527_);
v___x_3529_ = lean_internal_set_max_heartbeat(v___x_3528_);
goto v___jp_3505_;
}
else
{
lean_dec(v_timeout_3523_);
goto v___jp_3505_;
}
}
}
else
{
lean_object* v___x_3539_; 
lean_dec_ref(v_opts_3127_);
lean_dec(v_args_3126_);
v___x_3539_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3541_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref_known(v___x_3539_, 1);
v___x_3541_ = l_Lean_getLibDir(v_a_3540_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___x_3543_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3541_, 1);
v___x_3543_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3542_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3551_; 
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3551_ == 0)
{
lean_object* v_unused_3552_; 
v_unused_3552_ = lean_ctor_get(v___x_3543_, 0);
lean_dec(v_unused_3552_);
v___x_3545_ = v___x_3543_;
v_isShared_3546_ = v_isSharedCheck_3551_;
goto v_resetjp_3544_;
}
else
{
lean_dec(v___x_3543_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3551_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3547_; lean_object* v___x_3549_; 
v___x_3547_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 0, v___x_3547_);
v___x_3549_ = v___x_3545_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
v_a_3553_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3543_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3543_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
v_a_3561_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3541_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3541_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
v_a_3569_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3539_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3539_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
else
{
lean_object* v___x_3577_; 
lean_dec_ref(v_opts_3127_);
lean_dec(v_args_3126_);
v___x_3577_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3579_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___x_3577_, 1);
v___x_3579_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3578_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3587_; 
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3587_ == 0)
{
lean_object* v_unused_3588_; 
v_unused_3588_ = lean_ctor_get(v___x_3579_, 0);
lean_dec(v_unused_3588_);
v___x_3581_ = v___x_3579_;
v_isShared_3582_ = v_isSharedCheck_3587_;
goto v_resetjp_3580_;
}
else
{
lean_dec(v___x_3579_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3587_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; lean_object* v___x_3585_; 
v___x_3583_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 0, v___x_3583_);
v___x_3585_ = v___x_3581_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
v_a_3589_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3579_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3579_);
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
v_a_3597_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3577_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3577_);
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
v___jp_3129_:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_printImportsJson(v_fns_3130_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3139_; 
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; 
v_unused_3140_ = lean_ctor_get(v___x_3131_, 0);
lean_dec(v_unused_3140_);
v___x_3133_ = v___x_3131_;
v_isShared_3134_ = v_isSharedCheck_3139_;
goto v_resetjp_3132_;
}
else
{
lean_dec(v___x_3131_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3139_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
v___x_3135_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v___x_3135_);
v___x_3137_ = v___x_3133_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
v_a_3141_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3131_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3131_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3605_, lean_object* v_opts_3606_, lean_object* v_a_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = lean_shell_main(v_args_3605_, v_opts_3606_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3609_, lean_object* v_inst_3610_, lean_object* v_R_3611_, lean_object* v_a_3612_, lean_object* v_b_3613_, lean_object* v_c_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3609_, v_a_3612_, v_b_3613_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3616_, lean_object* v_inst_3617_, lean_object* v_R_3618_, lean_object* v_a_3619_, lean_object* v_b_3620_, lean_object* v_c_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3616_, v_inst_3617_, v_R_3618_, v_a_3619_, v_b_3620_, v_c_3621_);
lean_dec(v_b_3620_);
lean_dec_ref(v_val_3616_);
return v_res_3622_;
}
}
lean_object* runtime_initialize_Lean_Elab_Frontend(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ParseImportsFast(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Watchdog(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileWorker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_EmitC(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lossy(uint8_t builtin);
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
res = runtime_initialize_Init_Data_String_Lossy(builtin);
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
res = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1059550402____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Shell_0__Lean_maxMemory = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Shell_0__Lean_maxMemory);
lean_dec_ref(res);
res = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_2938679178____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Shell_0__Lean_timeout = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Shell_0__Lean_timeout);
lean_dec_ref(res);
res = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1321479241____hygCtx___hyg_2_();
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
lean_object* initialize_Init_Data_String_Lossy(uint8_t builtin);
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
res = initialize_Init_Data_String_Lossy(builtin);
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
