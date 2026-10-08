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
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__9 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__9_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown language '"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__10 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__10_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<stdin>"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__11 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__11_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___impl(uint8_t v_x_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_box(v_x_296_);
v___x_298_ = lean_obj_tag_nat(v___x_297_);
lean_dec(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___impl___boxed(lean_object* v_x_299_){
_start:
{
uint8_t v_x_4__boxed_300_; lean_object* v_res_301_; 
v_x_4__boxed_300_ = lean_unbox(v_x_299_);
v_res_301_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___impl(v_x_4__boxed_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(lean_object* v_k_302_){
_start:
{
lean_inc(v_k_302_);
return v_k_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg___boxed(lean_object* v_k_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(v_k_303_);
lean_dec(v_k_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(lean_object* v_motive_305_, lean_object* v_ctorIdx_306_, uint8_t v_t_307_, lean_object* v_h_308_, lean_object* v_k_309_){
_start:
{
lean_inc(v_k_309_);
return v_k_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___boxed(lean_object* v_motive_310_, lean_object* v_ctorIdx_311_, lean_object* v_t_312_, lean_object* v_h_313_, lean_object* v_k_314_){
_start:
{
uint8_t v_t_boxed_315_; lean_object* v_res_316_; 
v_t_boxed_315_ = lean_unbox(v_t_312_);
v_res_316_ = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(v_motive_310_, v_ctorIdx_311_, v_t_boxed_315_, v_h_313_, v_k_314_);
lean_dec(v_k_314_);
lean_dec(v_ctorIdx_311_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(lean_object* v_frontend_317_){
_start:
{
lean_inc(v_frontend_317_);
return v_frontend_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg___boxed(lean_object* v_frontend_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(v_frontend_318_);
lean_dec(v_frontend_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(lean_object* v_motive_320_, uint8_t v_t_321_, lean_object* v_h_322_, lean_object* v_frontend_323_){
_start:
{
lean_inc(v_frontend_323_);
return v_frontend_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___boxed(lean_object* v_motive_324_, lean_object* v_t_325_, lean_object* v_h_326_, lean_object* v_frontend_327_){
_start:
{
uint8_t v_t_boxed_328_; lean_object* v_res_329_; 
v_t_boxed_328_ = lean_unbox(v_t_325_);
v_res_329_ = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(v_motive_324_, v_t_boxed_328_, v_h_326_, v_frontend_327_);
lean_dec(v_frontend_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(lean_object* v_watchdog_330_){
_start:
{
lean_inc(v_watchdog_330_);
return v_watchdog_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg___boxed(lean_object* v_watchdog_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(v_watchdog_331_);
lean_dec(v_watchdog_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(lean_object* v_motive_333_, uint8_t v_t_334_, lean_object* v_h_335_, lean_object* v_watchdog_336_){
_start:
{
lean_inc(v_watchdog_336_);
return v_watchdog_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___boxed(lean_object* v_motive_337_, lean_object* v_t_338_, lean_object* v_h_339_, lean_object* v_watchdog_340_){
_start:
{
uint8_t v_t_boxed_341_; lean_object* v_res_342_; 
v_t_boxed_341_ = lean_unbox(v_t_338_);
v_res_342_ = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(v_motive_337_, v_t_boxed_341_, v_h_339_, v_watchdog_340_);
lean_dec(v_watchdog_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(lean_object* v_worker_343_){
_start:
{
lean_inc(v_worker_343_);
return v_worker_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg___boxed(lean_object* v_worker_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(v_worker_344_);
lean_dec(v_worker_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(lean_object* v_motive_346_, uint8_t v_t_347_, lean_object* v_h_348_, lean_object* v_worker_349_){
_start:
{
lean_inc(v_worker_349_);
return v_worker_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___boxed(lean_object* v_motive_350_, lean_object* v_t_351_, lean_object* v_h_352_, lean_object* v_worker_353_){
_start:
{
uint8_t v_t_boxed_354_; lean_object* v_res_355_; 
v_t_boxed_354_ = lean_unbox(v_t_351_);
v_res_355_ = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(v_motive_350_, v_t_boxed_354_, v_h_352_, v_worker_353_);
lean_dec(v_worker_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object* v_name_356_, lean_object* v_decl_357_, lean_object* v_ref_358_){
_start:
{
lean_object* v_defValue_360_; lean_object* v_descr_361_; lean_object* v_deprecation_x3f_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_defValue_360_ = lean_ctor_get(v_decl_357_, 0);
v_descr_361_ = lean_ctor_get(v_decl_357_, 1);
v_deprecation_x3f_362_ = lean_ctor_get(v_decl_357_, 2);
lean_inc(v_defValue_360_);
v___x_363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_363_, 0, v_defValue_360_);
lean_inc(v_deprecation_x3f_362_);
lean_inc_ref(v_descr_361_);
lean_inc_n(v_name_356_, 2);
v___x_364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_364_, 0, v_name_356_);
lean_ctor_set(v___x_364_, 1, v_ref_358_);
lean_ctor_set(v___x_364_, 2, v___x_363_);
lean_ctor_set(v___x_364_, 3, v_descr_361_);
lean_ctor_set(v___x_364_, 4, v_deprecation_x3f_362_);
v___x_365_ = lean_register_option(v_name_356_, v___x_364_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v___x_365_, 0);
lean_dec(v_unused_374_);
v___x_367_ = v___x_365_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_dec(v___x_365_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
lean_inc(v_defValue_360_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_name_356_);
lean_ctor_set(v___x_369_, 1, v_defValue_360_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_name_356_);
v_a_375_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_365_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_365_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_383_, lean_object* v_decl_384_, lean_object* v_ref_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v_name_383_, v_decl_384_, v_ref_385_);
lean_dec_ref(v_decl_384_);
return v_res_387_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_box(0);
v___x_392_ = lean_internal_get_default_max_memory(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_393_ = lean_box(0);
v___x_394_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_395_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_394_);
lean_ctor_set(v___x_396_, 2, v___x_393_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_421_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
v___x_422_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
v___x_423_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_420_, v___x_421_, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2____boxed(lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
return v_res_425_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_box(0);
v___x_430_ = lean_internal_get_default_max_heartbeat(v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_431_ = lean_box(0);
v___x_432_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_433_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
lean_ctor_set(v___x_434_, 2, v___x_431_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_439_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_440_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
v___x_441_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
v___x_442_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(v___x_439_, v___x_440_, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2____boxed(lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(lean_object* v_name_445_, lean_object* v_decl_446_, lean_object* v_ref_447_){
_start:
{
lean_object* v_defValue_449_; lean_object* v_descr_450_; lean_object* v_deprecation_x3f_451_; lean_object* v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_defValue_449_ = lean_ctor_get(v_decl_446_, 0);
v_descr_450_ = lean_ctor_get(v_decl_446_, 1);
v_deprecation_x3f_451_ = lean_ctor_get(v_decl_446_, 2);
v___x_452_ = lean_alloc_ctor(1, 0, 1);
v___x_453_ = lean_unbox(v_defValue_449_);
lean_ctor_set_uint8(v___x_452_, 0, v___x_453_);
lean_inc(v_deprecation_x3f_451_);
lean_inc_ref(v_descr_450_);
lean_inc_n(v_name_445_, 2);
v___x_454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_454_, 0, v_name_445_);
lean_ctor_set(v___x_454_, 1, v_ref_447_);
lean_ctor_set(v___x_454_, 2, v___x_452_);
lean_ctor_set(v___x_454_, 3, v_descr_450_);
lean_ctor_set(v___x_454_, 4, v_deprecation_x3f_451_);
v___x_455_ = lean_register_option(v_name_445_, v___x_454_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_463_; 
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v___x_455_, 0);
lean_dec(v_unused_464_);
v___x_457_ = v___x_455_;
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
else
{
lean_dec(v___x_455_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
lean_inc(v_defValue_449_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_name_445_);
lean_ctor_set(v___x_459_, 1, v_defValue_449_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_459_);
v___x_461_ = v___x_457_;
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
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_name_445_);
v_a_465_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_455_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_455_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0___boxed(lean_object* v_name_473_, lean_object* v_decl_474_, lean_object* v_ref_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v_name_473_, v_decl_474_, v_ref_475_);
lean_dec_ref(v_decl_474_);
return v_res_477_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_box(0);
v___x_482_ = lean_internal_get_default_verbose(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_483_ = lean_box(0);
v___x_484_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
v___x_485_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_486_ = lean_box(v___x_485_);
v___x_487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_484_);
lean_ctor_set(v___x_487_, 2, v___x_483_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_492_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_493_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
v___x_494_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
v___x_495_ = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(v___x_492_, v___x_493_, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2____boxed(lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_();
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getOptionOverrides___boxed(lean_object* v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = lean_internal_get_option_overrides(v_x_00___x40_Lean_Shell_1930944040____hygCtx___hyg_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBelieverTrustLevel___boxed(lean_object* v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_502_){
_start:
{
uint32_t v_res_503_; lean_object* v_r_504_; 
v_res_503_ = lean_internal_get_believer_trust_level(v_x_00___x40_Lean_Shell_1075205639____hygCtx___hyg_502_);
v_r_504_ = lean_box_uint32(v_res_503_);
return v_r_504_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0(void){
_start:
{
lean_object* v___x_505_; uint32_t v___x_506_; 
v___x_505_ = lean_box(0);
v___x_506_ = lean_internal_get_believer_trust_level(v___x_505_);
return v___x_506_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1(void){
_start:
{
uint32_t v___x_507_; uint32_t v___x_508_; uint32_t v___x_509_; 
v___x_507_ = 1;
v___x_508_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0);
v___x_509_ = lean_uint32_add(v___x_508_, v___x_507_);
return v___x_509_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel(void){
_start:
{
uint32_t v___x_510_; 
v___x_510_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1);
return v___x_510_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0(void){
_start:
{
lean_object* v___x_511_; uint32_t v___x_512_; 
v___x_511_ = lean_box(0);
v___x_512_ = lean_internal_get_hardware_concurrency(v___x_511_);
return v___x_512_;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads(void){
_start:
{
uint8_t v___x_513_; 
v___x_513_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__40, &l___private_Lean_Shell_0__Lean_displayHelp___closed__40_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40);
if (v___x_513_ == 0)
{
uint32_t v___x_514_; 
v___x_514_ = 0;
return v___x_514_;
}
else
{
uint32_t v___x_515_; 
v___x_515_ = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0, &l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0);
return v___x_515_;
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1(void){
_start:
{
lean_object* v___x_518_; uint32_t v___x_519_; uint32_t v___x_520_; uint8_t v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_518_ = lean_box(0);
v___x_519_ = l___private_Lean_Shell_0__Lean_defaultNumThreads;
v___x_520_ = l___private_Lean_Shell_0__Lean_defaultTrustLevel;
v___x_521_ = 0;
v___x_522_ = 0;
v___x_523_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__0));
v___x_524_ = l_Lean_Options_empty;
v___x_525_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v___x_523_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
lean_ctor_set(v___x_525_, 3, v___x_518_);
lean_ctor_set(v___x_525_, 4, v___x_518_);
lean_ctor_set(v___x_525_, 5, v___x_518_);
lean_ctor_set(v___x_525_, 6, v___x_518_);
lean_ctor_set(v___x_525_, 7, v___x_518_);
lean_ctor_set(v___x_525_, 8, v___x_518_);
lean_ctor_set(v___x_525_, 9, v___x_523_);
lean_ctor_set(v___x_525_, 10, v___x_518_);
lean_ctor_set(v___x_525_, 11, v___x_518_);
lean_ctor_set(v___x_525_, 12, v___x_518_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*13 + 8, v___x_522_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*13 + 9, v___x_521_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*13 + 10, v___x_521_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*13 + 11, v___x_521_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*13 + 12, v___x_521_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*13 + 13, v___x_521_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*13 + 14, v___x_521_);
lean_ctor_set_uint32(v___x_525_, sizeof(void*)*13, v___x_520_);
lean_ctor_set_uint32(v___x_525_, sizeof(void*)*13 + 4, v___x_519_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*13 + 15, v___x_521_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*13 + 16, v___x_521_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*13 + 17, v___x_521_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg(){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1, &l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___closed__1);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___redArg___boxed(lean_object* v___dummy_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Lean_Shell_0__Lean_mkShellOptions___redArg();
return v_res_529_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0(void){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l___private_Lean_Shell_0__Lean_mkShellOptions___redArg();
return v___x_530_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object* v_x_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0);
return v___x_532_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_run(lean_object* v_opts_533_){
_start:
{
uint8_t v_run_534_; 
v_run_534_ = lean_ctor_get_uint8(v_opts_533_, sizeof(void*)*13 + 17);
lean_dec_ref(v_opts_533_);
return v_run_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getRun___boxed(lean_object* v_opts_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = lean_shell_options_get_run(v_opts_535_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(lean_object* v_opts_538_, lean_object* v_opt_539_){
_start:
{
lean_object* v_name_540_; lean_object* v_defValue_541_; lean_object* v_map_542_; lean_object* v___x_543_; 
v_name_540_ = lean_ctor_get(v_opt_539_, 0);
v_defValue_541_ = lean_ctor_get(v_opt_539_, 1);
v_map_542_ = lean_ctor_get(v_opts_538_, 0);
v___x_543_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_542_, v_name_540_);
if (lean_obj_tag(v___x_543_) == 0)
{
uint8_t v___x_544_; 
v___x_544_ = lean_unbox(v_defValue_541_);
return v___x_544_;
}
else
{
lean_object* v_val_545_; 
v_val_545_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v___x_543_, 1);
if (lean_obj_tag(v_val_545_) == 1)
{
uint8_t v_v_546_; 
v_v_546_ = lean_ctor_get_uint8(v_val_545_, 0);
lean_dec_ref_known(v_val_545_, 0);
return v_v_546_;
}
else
{
uint8_t v___x_547_; 
lean_dec(v_val_545_);
v___x_547_ = lean_unbox(v_defValue_541_);
return v___x_547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0___boxed(lean_object* v_opts_548_, lean_object* v_opt_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_opts_548_, v_opt_549_);
lean_dec_ref(v_opt_549_);
lean_dec_ref(v_opts_548_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_profiler(lean_object* v_opts_552_){
_start:
{
lean_object* v_leanOpts_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_leanOpts_553_ = lean_ctor_get(v_opts_552_, 0);
lean_inc_ref(v_leanOpts_553_);
lean_dec_ref(v_opts_552_);
v___x_554_ = l_Lean_profiler;
v___x_555_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(v_leanOpts_553_, v___x_554_);
lean_dec_ref(v_leanOpts_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getProfiler___boxed(lean_object* v_opts_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = lean_shell_options_get_profiler(v_opts_556_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT uint32_t lean_shell_options_get_num_threads(lean_object* v_opts_559_){
_start:
{
uint32_t v_numThreads_560_; 
v_numThreads_560_ = lean_ctor_get_uint32(v_opts_559_, sizeof(void*)*13 + 4);
lean_dec_ref(v_opts_559_);
return v_numThreads_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getNumThreads___boxed(lean_object* v_opts_561_){
_start:
{
uint32_t v_res_562_; lean_object* v_r_563_; 
v_res_562_ = lean_shell_options_get_num_threads(v_opts_561_);
v_r_563_ = lean_box_uint32(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg(lean_object* v_optName_566_, lean_object* v_optArg_x3f_567_){
_start:
{
if (lean_obj_tag(v_optArg_x3f_567_) == 1)
{
lean_object* v_val_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
v_val_569_ = lean_ctor_get(v_optArg_x3f_567_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v_optArg_x3f_567_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v_optArg_x3f_567_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_val_569_);
lean_dec(v_optArg_x3f_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 0);
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_val_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec(v_optArg_x3f_567_);
v___x_577_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__0));
v___x_578_ = lean_string_append(v___x_577_, v_optName_566_);
v___x_579_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
v___x_580_ = lean_string_append(v___x_578_, v___x_579_);
v___x_581_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg___boxed(lean_object* v_optName_583_, lean_object* v_optArg_x3f_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Shell_0__Lean_checkOptArg(v_optName_583_, v_optArg_x3f_584_);
lean_dec_ref(v_optName_583_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(lean_object* v_o_590_, lean_object* v_k_591_, lean_object* v_v_592_){
_start:
{
lean_object* v_map_593_; uint8_t v_hasTrace_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_608_; 
v_map_593_ = lean_ctor_get(v_o_590_, 0);
v_hasTrace_594_ = lean_ctor_get_uint8(v_o_590_, sizeof(void*)*1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_o_590_);
if (v_isSharedCheck_608_ == 0)
{
v___x_596_ = v_o_590_;
v_isShared_597_ = v_isSharedCheck_608_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_map_593_);
lean_dec(v_o_590_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_608_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v_v_592_);
lean_inc(v_k_591_);
v___x_599_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_591_, v___x_598_, v_map_593_);
if (v_hasTrace_594_ == 0)
{
lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_603_; 
v___x_600_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_601_ = l_Lean_Name_isPrefixOf(v___x_600_, v_k_591_);
lean_dec(v_k_591_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_599_);
v___x_603_ = v___x_596_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_599_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_ctor_set_uint8(v___x_603_, sizeof(void*)*1, v___x_601_);
return v___x_603_;
}
}
else
{
lean_object* v___x_606_; 
lean_dec(v_k_591_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_599_);
v___x_606_ = v___x_596_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_599_);
lean_ctor_set_uint8(v_reuseFailAlloc_607_, sizeof(void*)*1, v_hasTrace_594_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(lean_object* v___x_609_, lean_object* v_arg_610_, lean_object* v_a_611_, lean_object* v_b_612_){
_start:
{
uint8_t v_decide_613_; 
v_decide_613_ = lean_nat_dec_eq(v_a_611_, v___x_609_);
if (v_decide_613_ == 0)
{
uint32_t v___x_614_; uint32_t v___x_615_; uint8_t v___x_616_; 
v___x_614_ = lean_string_utf8_get_fast(v_arg_610_, v_a_611_);
v___x_615_ = 61;
v___x_616_ = lean_uint32_dec_eq(v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_box(0);
v___x_618_ = lean_string_utf8_next_fast(v_arg_610_, v_a_611_);
lean_dec(v_a_611_);
v_a_611_ = v___x_618_;
v_b_612_ = v___x_617_;
goto _start;
}
else
{
lean_object* v___x_620_; 
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v_a_611_);
return v___x_620_;
}
}
else
{
lean_dec(v_a_611_);
lean_inc(v_b_612_);
return v_b_612_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(lean_object* v___x_621_, lean_object* v_arg_622_, lean_object* v_a_623_, lean_object* v_b_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_621_, v_arg_622_, v_a_623_, v_b_624_);
lean_dec(v_b_624_);
lean_dec_ref(v_arg_622_);
lean_dec(v___x_621_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption(lean_object* v_opts_629_, lean_object* v_arg_630_){
_start:
{
lean_object* v___y_633_; lean_object* v_searcher_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_searcher_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_string_utf8_byte_size(v_arg_630_);
v___x_666_ = lean_box(0);
v___x_667_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_665_, v_arg_630_, v_searcher_664_, v___x_666_);
if (lean_obj_tag(v___x_667_) == 0)
{
v___y_633_ = v___x_665_;
goto v___jp_632_;
}
else
{
lean_object* v_val_668_; 
v_val_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v___x_667_, 1);
v___y_633_ = v_val_668_;
goto v___jp_632_;
}
v___jp_632_:
{
lean_object* v___x_634_; uint8_t v_decide_635_; 
v___x_634_ = lean_string_utf8_byte_size(v_arg_630_);
v_decide_635_ = lean_nat_dec_eq(v___y_633_, v___x_634_);
if (v_decide_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_name_638_; lean_object* v___x_639_; lean_object* v_val_640_; lean_object* v___x_641_; 
v___x_636_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_633_);
lean_inc_ref(v_arg_630_);
v___x_637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_637_, 0, v_arg_630_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
lean_ctor_set(v___x_637_, 2, v___y_633_);
v_name_638_ = l_String_Slice_toName(v___x_637_);
lean_dec_ref_known(v___x_637_, 3);
v___x_639_ = lean_string_utf8_next_fast(v_arg_630_, v___y_633_);
lean_dec(v___y_633_);
v_val_640_ = lean_string_utf8_extract_fast(v_arg_630_, v___x_639_, v___x_634_);
lean_dec_ref(v_arg_630_);
v___x_641_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_653_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_653_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; 
v___x_646_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_642_, v_name_638_);
lean_dec(v_a_642_);
if (lean_obj_tag(v___x_646_) == 1)
{
lean_object* v_val_647_; lean_object* v___x_648_; 
lean_del_object(v___x_644_);
v_val_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = l_Lean_Language_Lean_setOption(v_opts_629_, v_val_647_, v_name_638_, v_val_640_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_651_; 
lean_dec(v___x_646_);
v___x_649_ = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(v_opts_629_, v_name_638_, v_val_640_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_649_);
v___x_651_ = v___x_644_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v_val_640_);
lean_dec(v_name_638_);
lean_dec_ref(v_opts_629_);
v_a_654_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_641_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_641_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec(v___y_633_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_opts_629_);
v___x_662_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_setConfigOption___closed__1));
v___x_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object* v___x_673_, lean_object* v___x_674_, lean_object* v_arg_675_, lean_object* v_inst_676_, lean_object* v_R_677_, lean_object* v_a_678_, lean_object* v_b_679_, lean_object* v_c_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_673_, v_arg_675_, v_a_678_, v_b_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object* v___x_682_, lean_object* v___x_683_, lean_object* v_arg_684_, lean_object* v_inst_685_, lean_object* v_R_686_, lean_object* v_a_687_, lean_object* v_b_688_, lean_object* v_c_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(v___x_682_, v___x_683_, v_arg_684_, v_inst_685_, v_R_686_, v_a_687_, v_b_688_, v_c_689_);
lean_dec(v_b_688_);
lean_dec_ref(v_arg_684_);
lean_dec_ref(v___x_683_);
lean_dec(v___x_682_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(lean_object* v_msg_692_){
_start:
{
lean_object* v___f_694_; lean_object* v___x_695_; 
v___f_694_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_695_ = l_IO_eprint___redArg(v___f_694_, v_msg_692_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
else
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_711_; 
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; 
v_unused_712_ = lean_ctor_get(v___x_695_, 0);
lean_dec(v_unused_712_);
v___x_705_ = v___x_695_;
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
else
{
lean_dec(v___x_695_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = lean_box(0);
if (v_isShared_706_ == 0)
{
lean_ctor_set_tag(v___x_705_, 0);
lean_ctor_set(v___x_705_, 0, v___x_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(lean_object* v_msg_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(v_msg_713_);
return v_res_715_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_718_; lean_object* v___x_719_; 
v___x_718_ = 1;
v___x_719_ = lean_box_uint32(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(lean_object* v_x_720_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = lean_apply_1(v_x_720_, lean_box(0));
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_743_; lean_object* v___f_744_; lean_object* v___x_745_; 
v_a_738_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_729_, 1);
v___x_743_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_744_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_745_ = l_IO_eprint___redArg(v___f_744_, v___x_743_);
lean_dec_ref(v___x_745_);
goto v___jp_739_;
v___jp_739_:
{
lean_object* v___x_740_; lean_object* v___f_741_; lean_object* v___x_742_; 
v___x_740_ = lean_io_error_to_string(v_a_738_);
v___f_741_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_742_ = l_IO_eprint___redArg(v___f_741_, v___x_740_);
lean_dec_ref(v___x_742_);
goto v___jp_725_;
}
}
v___jp_722_:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
v___jp_725_:
{
lean_object* v___x_726_; lean_object* v___f_727_; lean_object* v___x_728_; 
v___x_726_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_727_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_728_ = l_IO_eprint___redArg(v___f_727_, v___x_726_);
lean_dec_ref(v___x_728_);
goto v___jp_722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed(lean_object* v_x_746_, lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(v_x_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(lean_object* v_00_u03b1_749_, lean_object* v_x_750_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = lean_apply_1(v_x_750_, lean_box(0));
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___x_775_; 
v_a_768_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_759_, 1);
v___x_773_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___f_774_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_775_ = l_IO_eprint___redArg(v___f_774_, v___x_773_);
lean_dec_ref(v___x_775_);
goto v___jp_769_;
v___jp_769_:
{
lean_object* v___x_770_; lean_object* v___f_771_; lean_object* v___x_772_; 
v___x_770_ = lean_io_error_to_string(v_a_768_);
v___f_771_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_772_ = l_IO_eprint___redArg(v___f_771_, v___x_770_);
lean_dec_ref(v___x_772_);
goto v___jp_755_;
}
}
v___jp_752_:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
v___jp_755_:
{
lean_object* v___x_756_; lean_object* v___f_757_; lean_object* v___x_758_; 
v___x_756_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___f_757_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_758_ = l_IO_eprint___redArg(v___f_757_, v___x_756_);
lean_dec_ref(v___x_758_);
goto v___jp_752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___boxed(lean_object* v_00_u03b1_776_, lean_object* v_x_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(v_00_u03b1_776_, v_x_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(lean_object* v_opt_782_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___f_791_; lean_object* v___x_792_; 
v___x_787_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0));
v___x_788_ = lean_string_append(v___x_787_, v_opt_782_);
v___x_789_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_790_ = lean_string_append(v___x_788_, v___x_789_);
v___f_791_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_792_ = l_IO_eprint___redArg(v___f_791_, v___x_790_);
lean_dec_ref(v___x_792_);
goto v___jp_784_;
v___jp_784_:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___boxed(lean_object* v_opt_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(v_opt_793_);
lean_dec_ref(v_opt_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(lean_object* v_opt_798_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___f_807_; lean_object* v___x_808_; 
v___x_803_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0));
v___x_804_ = lean_string_append(v___x_803_, v_opt_798_);
v___x_805_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1));
v___x_806_ = lean_string_append(v___x_804_, v___x_805_);
v___f_807_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
v___x_808_ = l_IO_eprint___redArg(v___f_807_, v___x_806_);
lean_dec_ref(v___x_808_);
goto v___jp_800_;
v___jp_800_:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___boxed(lean_object* v_opt_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(v_opt_809_);
lean_dec_ref(v_opt_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(lean_object* v_s_812_){
_start:
{
lean_object* v___x_814_; lean_object* v_putStr_815_; lean_object* v___x_816_; 
v___x_814_ = lean_get_stderr();
v_putStr_815_ = lean_ctor_get(v___x_814_, 4);
lean_inc_ref(v_putStr_815_);
lean_dec_ref(v___x_814_);
v___x_816_ = lean_apply_2(v_putStr_815_, v_s_812_, lean_box(0));
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0___boxed(lean_object* v_s_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v_s_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(lean_object* v_s_820_){
_start:
{
lean_object* v___x_822_; lean_object* v_putStr_823_; lean_object* v___x_824_; 
v___x_822_ = lean_get_stdout();
v_putStr_823_ = lean_ctor_get(v___x_822_, 4);
lean_inc_ref(v_putStr_823_);
lean_dec_ref(v___x_822_);
v___x_824_ = lean_apply_2(v_putStr_823_, v_s_820_, lean_box(0));
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5___boxed(lean_object* v_s_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v_s_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object* v_s_828_){
_start:
{
uint32_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = 10;
v___x_831_ = lean_string_push(v_s_828_, v___x_830_);
v___x_832_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3___boxed(lean_object* v_s_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v_s_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(lean_object* v_o_836_, lean_object* v_k_837_, uint8_t v_v_838_){
_start:
{
lean_object* v_map_839_; uint8_t v_hasTrace_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_854_; 
v_map_839_ = lean_ctor_get(v_o_836_, 0);
v_hasTrace_840_ = lean_ctor_get_uint8(v_o_836_, sizeof(void*)*1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_o_836_);
if (v_isSharedCheck_854_ == 0)
{
v___x_842_ = v_o_836_;
v_isShared_843_ = v_isSharedCheck_854_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_map_839_);
lean_dec(v_o_836_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_854_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_844_, 0, v_v_838_);
lean_inc(v_k_837_);
v___x_845_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_837_, v___x_844_, v_map_839_);
if (v_hasTrace_840_ == 0)
{
lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_849_; 
v___x_846_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_847_ = l_Lean_Name_isPrefixOf(v___x_846_, v_k_837_);
lean_dec(v_k_837_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_845_);
v___x_849_ = v___x_842_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_845_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*1, v___x_847_);
return v___x_849_;
}
}
else
{
lean_object* v___x_852_; 
lean_dec(v_k_837_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_845_);
v___x_852_ = v___x_842_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, sizeof(void*)*1, v_hasTrace_840_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1___boxed(lean_object* v_o_855_, lean_object* v_k_856_, lean_object* v_v_857_){
_start:
{
uint8_t v_v_boxed_858_; lean_object* v_res_859_; 
v_v_boxed_858_ = lean_unbox(v_v_857_);
v_res_859_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_o_855_, v_k_856_, v_v_boxed_858_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object* v_opts_860_, lean_object* v_opt_861_, uint8_t v_val_862_){
_start:
{
lean_object* v_name_863_; lean_object* v___x_864_; 
v_name_863_ = lean_ctor_get(v_opt_861_, 0);
lean_inc(v_name_863_);
lean_dec_ref(v_opt_861_);
v___x_864_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(v_opts_860_, v_name_863_, v_val_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object* v_opts_865_, lean_object* v_opt_866_, lean_object* v_val_867_){
_start:
{
uint8_t v_val_boxed_868_; lean_object* v_res_869_; 
v_val_boxed_868_ = lean_unbox(v_val_867_);
v_res_869_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_opts_865_, v_opt_866_, v_val_boxed_868_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(lean_object* v_o_870_, lean_object* v_k_871_, lean_object* v_v_872_){
_start:
{
lean_object* v_map_873_; uint8_t v_hasTrace_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_888_; 
v_map_873_ = lean_ctor_get(v_o_870_, 0);
v_hasTrace_874_ = lean_ctor_get_uint8(v_o_870_, sizeof(void*)*1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_o_870_);
if (v_isSharedCheck_888_ == 0)
{
v___x_876_ = v_o_870_;
v_isShared_877_ = v_isSharedCheck_888_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_map_873_);
lean_dec(v_o_870_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_888_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_878_, 0, v_v_872_);
lean_inc(v_k_871_);
v___x_879_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_871_, v___x_878_, v_map_873_);
if (v_hasTrace_874_ == 0)
{
lean_object* v___x_880_; uint8_t v___x_881_; lean_object* v___x_883_; 
v___x_880_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
v___x_881_ = l_Lean_Name_isPrefixOf(v___x_880_, v_k_871_);
lean_dec(v_k_871_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_879_);
v___x_883_ = v___x_876_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_879_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1, v___x_881_);
return v___x_883_;
}
}
else
{
lean_object* v___x_886_; 
lean_dec(v_k_871_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_879_);
v___x_886_ = v___x_876_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_887_, sizeof(void*)*1, v_hasTrace_874_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object* v_opts_889_, lean_object* v_opt_890_, lean_object* v_val_891_){
_start:
{
lean_object* v_name_892_; lean_object* v___x_893_; 
v_name_892_ = lean_ctor_get(v_opt_890_, 0);
lean_inc(v_name_892_);
lean_dec_ref(v_opt_890_);
v___x_893_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(v_opts_889_, v_name_892_, v_val_891_);
return v___x_893_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = l_System_Platform_numBits;
v___x_923_ = lean_unsigned_to_nat(2u);
v___x_924_ = lean_nat_pow(v___x_923_, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1(void){
_start:
{
uint32_t v___x_934_; lean_object* v___x_935_; 
v___x_934_ = 0;
v___x_935_ = lean_box_uint32(v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object* v_opts_936_, uint32_t v_opt_937_, lean_object* v_optArg_x3f_938_){
_start:
{
lean_object* v___y_1046_; lean_object* v___y_1104_; uint32_t v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = 101;
v___x_1159_ = lean_uint32_dec_eq(v_opt_937_, v___x_1158_);
if (v___x_1159_ == 0)
{
uint32_t v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = 106;
v___x_1161_ = lean_uint32_dec_eq(v_opt_937_, v___x_1160_);
if (v___x_1161_ == 0)
{
uint32_t v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = 118;
v___x_1163_ = lean_uint32_dec_eq(v_opt_937_, v___x_1162_);
if (v___x_1163_ == 0)
{
uint32_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = 86;
v___x_1165_ = lean_uint32_dec_eq(v_opt_937_, v___x_1164_);
if (v___x_1165_ == 0)
{
uint32_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = 103;
v___x_1167_ = lean_uint32_dec_eq(v_opt_937_, v___x_1166_);
if (v___x_1167_ == 0)
{
uint32_t v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = 104;
v___x_1169_ = lean_uint32_dec_eq(v_opt_937_, v___x_1168_);
if (v___x_1169_ == 0)
{
uint32_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = 102;
v___x_1171_ = lean_uint32_dec_eq(v_opt_937_, v___x_1170_);
if (v___x_1171_ == 0)
{
uint32_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = 99;
v___x_1173_ = lean_uint32_dec_eq(v_opt_937_, v___x_1172_);
if (v___x_1173_ == 0)
{
uint32_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = 98;
v___x_1175_ = lean_uint32_dec_eq(v_opt_937_, v___x_1174_);
if (v___x_1175_ == 0)
{
uint32_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = 115;
v___x_1177_ = lean_uint32_dec_eq(v_opt_937_, v___x_1176_);
if (v___x_1177_ == 0)
{
uint32_t v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = 73;
v___x_1179_ = lean_uint32_dec_eq(v_opt_937_, v___x_1178_);
if (v___x_1179_ == 0)
{
uint32_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = 114;
v___x_1181_ = lean_uint32_dec_eq(v_opt_937_, v___x_1180_);
if (v___x_1181_ == 0)
{
uint32_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = 111;
v___x_1183_ = lean_uint32_dec_eq(v_opt_937_, v___x_1182_);
if (v___x_1183_ == 0)
{
uint32_t v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = 105;
v___x_1185_ = lean_uint32_dec_eq(v_opt_937_, v___x_1184_);
if (v___x_1185_ == 0)
{
uint32_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = 82;
v___x_1187_ = lean_uint32_dec_eq(v_opt_937_, v___x_1186_);
if (v___x_1187_ == 0)
{
uint32_t v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = 77;
v___x_1189_ = lean_uint32_dec_eq(v_opt_937_, v___x_1188_);
if (v___x_1189_ == 0)
{
uint32_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = 84;
v___x_1191_ = lean_uint32_dec_eq(v_opt_937_, v___x_1190_);
if (v___x_1191_ == 0)
{
uint32_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = 116;
v___x_1193_ = lean_uint32_dec_eq(v_opt_937_, v___x_1192_);
if (v___x_1193_ == 0)
{
uint32_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = 113;
v___x_1195_ = lean_uint32_dec_eq(v_opt_937_, v___x_1194_);
if (v___x_1195_ == 0)
{
uint32_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = 100;
v___x_1197_ = lean_uint32_dec_eq(v_opt_937_, v___x_1196_);
if (v___x_1197_ == 0)
{
uint32_t v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = 79;
v___x_1199_ = lean_uint32_dec_eq(v_opt_937_, v___x_1198_);
if (v___x_1199_ == 0)
{
uint32_t v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = 78;
v___x_1201_ = lean_uint32_dec_eq(v_opt_937_, v___x_1200_);
if (v___x_1201_ == 0)
{
uint32_t v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = 74;
v___x_1203_ = lean_uint32_dec_eq(v_opt_937_, v___x_1202_);
if (v___x_1203_ == 0)
{
uint32_t v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = 97;
v___x_1205_ = lean_uint32_dec_eq(v_opt_937_, v___x_1204_);
if (v___x_1205_ == 0)
{
uint32_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = 120;
v___x_1207_ = lean_uint32_dec_eq(v_opt_937_, v___x_1206_);
if (v___x_1207_ == 0)
{
uint32_t v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = 76;
v___x_1209_ = lean_uint32_dec_eq(v_opt_937_, v___x_1208_);
if (v___x_1209_ == 0)
{
uint32_t v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = 68;
v___x_1211_ = lean_uint32_dec_eq(v_opt_937_, v___x_1210_);
if (v___x_1211_ == 0)
{
uint32_t v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = 83;
v___x_1213_ = lean_uint32_dec_eq(v_opt_937_, v___x_1212_);
if (v___x_1213_ == 0)
{
uint32_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = 87;
v___x_1215_ = lean_uint32_dec_eq(v_opt_937_, v___x_1214_);
if (v___x_1215_ == 0)
{
uint32_t v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = 80;
v___x_1217_ = lean_uint32_dec_eq(v_opt_937_, v___x_1216_);
if (v___x_1217_ == 0)
{
uint32_t v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = 66;
v___x_1219_ = lean_uint32_dec_eq(v_opt_937_, v___x_1218_);
if (v___x_1219_ == 0)
{
uint32_t v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = 112;
v___x_1221_ = lean_uint32_dec_eq(v_opt_937_, v___x_1220_);
if (v___x_1221_ == 0)
{
uint32_t v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = 108;
v___x_1223_ = lean_uint32_dec_eq(v_opt_937_, v___x_1222_);
if (v___x_1223_ == 0)
{
uint32_t v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = 117;
v___x_1225_ = lean_uint32_dec_eq(v_opt_937_, v___x_1224_);
if (v___x_1225_ == 0)
{
uint32_t v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = 69;
v___x_1227_ = lean_uint32_dec_eq(v_opt_937_, v___x_1226_);
if (v___x_1227_ == 0)
{
uint32_t v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = 89;
v___x_1229_ = lean_uint32_dec_eq(v_opt_937_, v___x_1228_);
if (v___x_1229_ == 0)
{
uint32_t v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = 90;
v___x_1231_ = lean_uint32_dec_eq(v_opt_937_, v___x_1230_);
if (v___x_1231_ == 0)
{
uint32_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = 72;
v___x_1233_ = lean_uint32_dec_eq(v_opt_937_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_dec(v_optArg_x3f_938_);
lean_dec_ref(v_opts_936_);
goto v___jp_1064_;
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
v___x_1235_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1234_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1276_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1276_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1276_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v_leanOpts_1240_; lean_object* v_forwardedArgs_1241_; uint8_t v_component_1242_; uint8_t v_printPrefix_1243_; uint8_t v_printLibDir_1244_; uint8_t v_useStdin_1245_; uint8_t v_onlyDeps_1246_; uint8_t v_onlySrcDeps_1247_; uint8_t v_depsJson_1248_; lean_object* v_opts_1249_; uint32_t v_trustLevel_1250_; uint32_t v_numThreads_1251_; lean_object* v_rootDir_x3f_1252_; lean_object* v_setupFileName_x3f_1253_; lean_object* v_oleanFileName_x3f_1254_; lean_object* v_ileanFileName_x3f_1255_; lean_object* v_cFileName_x3f_1256_; lean_object* v_bcFileName_x3f_1257_; uint8_t v_jsonOutput_1258_; lean_object* v_errorOnKinds_1259_; uint8_t v_printStats_1260_; uint8_t v_run_1261_; lean_object* v_incrSaveFileName_x3f_1262_; lean_object* v_incrLoadFileName_x3f_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1274_; 
v_leanOpts_1240_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1241_ = lean_ctor_get(v_opts_936_, 1);
v_component_1242_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1243_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1244_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1245_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1246_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1247_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1248_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1249_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1250_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1251_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1252_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1253_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1254_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1255_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1256_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1257_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1258_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1259_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1260_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1261_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1262_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1263_ = lean_ctor_get(v_opts_936_, 11);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v_opts_936_, 12);
lean_dec(v_unused_1275_);
v___x_1265_ = v_opts_936_;
v_isShared_1266_ = v_isSharedCheck_1274_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_incrLoadFileName_x3f_1263_);
lean_inc(v_incrSaveFileName_x3f_1262_);
lean_inc(v_errorOnKinds_1259_);
lean_inc(v_bcFileName_x3f_1257_);
lean_inc(v_cFileName_x3f_1256_);
lean_inc(v_ileanFileName_x3f_1255_);
lean_inc(v_oleanFileName_x3f_1254_);
lean_inc(v_setupFileName_x3f_1253_);
lean_inc(v_rootDir_x3f_1252_);
lean_inc(v_opts_1249_);
lean_inc(v_forwardedArgs_1241_);
lean_inc(v_leanOpts_1240_);
lean_dec(v_opts_936_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1274_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_a_1236_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 12, v___x_1267_);
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_leanOpts_1240_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_forwardedArgs_1241_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_opts_1249_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_rootDir_x3f_1252_);
lean_ctor_set(v_reuseFailAlloc_1273_, 4, v_setupFileName_x3f_1253_);
lean_ctor_set(v_reuseFailAlloc_1273_, 5, v_oleanFileName_x3f_1254_);
lean_ctor_set(v_reuseFailAlloc_1273_, 6, v_ileanFileName_x3f_1255_);
lean_ctor_set(v_reuseFailAlloc_1273_, 7, v_cFileName_x3f_1256_);
lean_ctor_set(v_reuseFailAlloc_1273_, 8, v_bcFileName_x3f_1257_);
lean_ctor_set(v_reuseFailAlloc_1273_, 9, v_errorOnKinds_1259_);
lean_ctor_set(v_reuseFailAlloc_1273_, 10, v_incrSaveFileName_x3f_1262_);
lean_ctor_set(v_reuseFailAlloc_1273_, 11, v_incrLoadFileName_x3f_1263_);
lean_ctor_set(v_reuseFailAlloc_1273_, 12, v___x_1267_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*13 + 8, v_component_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*13 + 9, v_printPrefix_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*13 + 10, v_printLibDir_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*13 + 11, v_useStdin_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*13 + 12, v_onlyDeps_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*13 + 13, v_onlySrcDeps_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*13 + 14, v_depsJson_1248_);
lean_ctor_set_uint32(v_reuseFailAlloc_1273_, sizeof(void*)*13, v_trustLevel_1250_);
lean_ctor_set_uint32(v_reuseFailAlloc_1273_, sizeof(void*)*13 + 4, v_numThreads_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*13 + 15, v_jsonOutput_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*13 + 16, v_printStats_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*13 + 17, v_run_1261_);
v___x_1269_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1271_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1269_);
v___x_1271_ = v___x_1238_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec_ref(v_opts_936_);
v_a_1277_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1281_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1282_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1281_);
lean_dec_ref(v___x_1282_);
goto v___jp_1278_;
v___jp_1278_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_io_error_to_string(v_a_1277_);
v___x_1280_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1279_);
lean_dec_ref(v___x_1280_);
goto v___jp_1036_;
}
}
}
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
v___x_1284_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1283_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1325_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1325_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1325_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v_leanOpts_1289_; lean_object* v_forwardedArgs_1290_; uint8_t v_component_1291_; uint8_t v_printPrefix_1292_; uint8_t v_printLibDir_1293_; uint8_t v_useStdin_1294_; uint8_t v_onlyDeps_1295_; uint8_t v_onlySrcDeps_1296_; uint8_t v_depsJson_1297_; lean_object* v_opts_1298_; uint32_t v_trustLevel_1299_; uint32_t v_numThreads_1300_; lean_object* v_rootDir_x3f_1301_; lean_object* v_setupFileName_x3f_1302_; lean_object* v_oleanFileName_x3f_1303_; lean_object* v_ileanFileName_x3f_1304_; lean_object* v_cFileName_x3f_1305_; lean_object* v_bcFileName_x3f_1306_; uint8_t v_jsonOutput_1307_; lean_object* v_errorOnKinds_1308_; uint8_t v_printStats_1309_; uint8_t v_run_1310_; lean_object* v_incrSaveFileName_x3f_1311_; lean_object* v_incrHeaderSaveFileName_x3f_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1323_; 
v_leanOpts_1289_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1290_ = lean_ctor_get(v_opts_936_, 1);
v_component_1291_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1292_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1293_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1294_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1295_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1296_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1297_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1298_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1299_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1300_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1301_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1302_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1303_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1304_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1305_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1306_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1307_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1308_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1309_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1310_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1311_ = lean_ctor_get(v_opts_936_, 10);
v_incrHeaderSaveFileName_x3f_1312_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v_opts_936_, 11);
lean_dec(v_unused_1324_);
v___x_1314_ = v_opts_936_;
v_isShared_1315_ = v_isSharedCheck_1323_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1312_);
lean_inc(v_incrSaveFileName_x3f_1311_);
lean_inc(v_errorOnKinds_1308_);
lean_inc(v_bcFileName_x3f_1306_);
lean_inc(v_cFileName_x3f_1305_);
lean_inc(v_ileanFileName_x3f_1304_);
lean_inc(v_oleanFileName_x3f_1303_);
lean_inc(v_setupFileName_x3f_1302_);
lean_inc(v_rootDir_x3f_1301_);
lean_inc(v_opts_1298_);
lean_inc(v_forwardedArgs_1290_);
lean_inc(v_leanOpts_1289_);
lean_dec(v_opts_936_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1323_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_a_1285_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 11, v___x_1316_);
v___x_1318_ = v___x_1314_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_leanOpts_1289_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_forwardedArgs_1290_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_opts_1298_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v_rootDir_x3f_1301_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_setupFileName_x3f_1302_);
lean_ctor_set(v_reuseFailAlloc_1322_, 5, v_oleanFileName_x3f_1303_);
lean_ctor_set(v_reuseFailAlloc_1322_, 6, v_ileanFileName_x3f_1304_);
lean_ctor_set(v_reuseFailAlloc_1322_, 7, v_cFileName_x3f_1305_);
lean_ctor_set(v_reuseFailAlloc_1322_, 8, v_bcFileName_x3f_1306_);
lean_ctor_set(v_reuseFailAlloc_1322_, 9, v_errorOnKinds_1308_);
lean_ctor_set(v_reuseFailAlloc_1322_, 10, v_incrSaveFileName_x3f_1311_);
lean_ctor_set(v_reuseFailAlloc_1322_, 11, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1322_, 12, v_incrHeaderSaveFileName_x3f_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*13 + 8, v_component_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*13 + 9, v_printPrefix_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*13 + 10, v_printLibDir_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*13 + 11, v_useStdin_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*13 + 12, v_onlyDeps_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*13 + 13, v_onlySrcDeps_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*13 + 14, v_depsJson_1297_);
lean_ctor_set_uint32(v_reuseFailAlloc_1322_, sizeof(void*)*13, v_trustLevel_1299_);
lean_ctor_set_uint32(v_reuseFailAlloc_1322_, sizeof(void*)*13 + 4, v_numThreads_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*13 + 15, v_jsonOutput_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*13 + 16, v_printStats_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*13 + 17, v_run_1310_);
v___x_1318_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1320_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1318_);
v___x_1320_ = v___x_1287_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec_ref(v_opts_936_);
v_a_1326_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1330_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1331_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1330_);
lean_dec_ref(v___x_1331_);
goto v___jp_1327_;
v___jp_1327_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_io_error_to_string(v_a_1326_);
v___x_1329_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1328_);
lean_dec_ref(v___x_1329_);
goto v___jp_1070_;
}
}
}
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
v___x_1333_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1332_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1374_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1374_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1374_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_leanOpts_1338_; lean_object* v_forwardedArgs_1339_; uint8_t v_component_1340_; uint8_t v_printPrefix_1341_; uint8_t v_printLibDir_1342_; uint8_t v_useStdin_1343_; uint8_t v_onlyDeps_1344_; uint8_t v_onlySrcDeps_1345_; uint8_t v_depsJson_1346_; lean_object* v_opts_1347_; uint32_t v_trustLevel_1348_; uint32_t v_numThreads_1349_; lean_object* v_rootDir_x3f_1350_; lean_object* v_setupFileName_x3f_1351_; lean_object* v_oleanFileName_x3f_1352_; lean_object* v_ileanFileName_x3f_1353_; lean_object* v_cFileName_x3f_1354_; lean_object* v_bcFileName_x3f_1355_; uint8_t v_jsonOutput_1356_; lean_object* v_errorOnKinds_1357_; uint8_t v_printStats_1358_; uint8_t v_run_1359_; lean_object* v_incrLoadFileName_x3f_1360_; lean_object* v_incrHeaderSaveFileName_x3f_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1372_; 
v_leanOpts_1338_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1339_ = lean_ctor_get(v_opts_936_, 1);
v_component_1340_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1341_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1342_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1343_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1344_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1345_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1346_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1347_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1348_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1349_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1350_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1351_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1352_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1353_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1354_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1355_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1356_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1357_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1358_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1359_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrLoadFileName_x3f_1360_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1361_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v_opts_936_, 10);
lean_dec(v_unused_1373_);
v___x_1363_ = v_opts_936_;
v_isShared_1364_ = v_isSharedCheck_1372_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1361_);
lean_inc(v_incrLoadFileName_x3f_1360_);
lean_inc(v_errorOnKinds_1357_);
lean_inc(v_bcFileName_x3f_1355_);
lean_inc(v_cFileName_x3f_1354_);
lean_inc(v_ileanFileName_x3f_1353_);
lean_inc(v_oleanFileName_x3f_1352_);
lean_inc(v_setupFileName_x3f_1351_);
lean_inc(v_rootDir_x3f_1350_);
lean_inc(v_opts_1347_);
lean_inc(v_forwardedArgs_1339_);
lean_inc(v_leanOpts_1338_);
lean_dec(v_opts_936_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1372_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1365_, 0, v_a_1334_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 10, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_leanOpts_1338_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_forwardedArgs_1339_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_opts_1347_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v_rootDir_x3f_1350_);
lean_ctor_set(v_reuseFailAlloc_1371_, 4, v_setupFileName_x3f_1351_);
lean_ctor_set(v_reuseFailAlloc_1371_, 5, v_oleanFileName_x3f_1352_);
lean_ctor_set(v_reuseFailAlloc_1371_, 6, v_ileanFileName_x3f_1353_);
lean_ctor_set(v_reuseFailAlloc_1371_, 7, v_cFileName_x3f_1354_);
lean_ctor_set(v_reuseFailAlloc_1371_, 8, v_bcFileName_x3f_1355_);
lean_ctor_set(v_reuseFailAlloc_1371_, 9, v_errorOnKinds_1357_);
lean_ctor_set(v_reuseFailAlloc_1371_, 10, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1371_, 11, v_incrLoadFileName_x3f_1360_);
lean_ctor_set(v_reuseFailAlloc_1371_, 12, v_incrHeaderSaveFileName_x3f_1361_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 8, v_component_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 9, v_printPrefix_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 10, v_printLibDir_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 11, v_useStdin_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 12, v_onlyDeps_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 13, v_onlySrcDeps_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 14, v_depsJson_1346_);
lean_ctor_set_uint32(v_reuseFailAlloc_1371_, sizeof(void*)*13, v_trustLevel_1348_);
lean_ctor_set_uint32(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 4, v_numThreads_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 15, v_jsonOutput_1356_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 16, v_printStats_1358_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 17, v_run_1359_);
v___x_1367_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1369_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1367_);
v___x_1369_ = v___x_1336_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec_ref(v_opts_936_);
v_a_1375_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1333_, 1);
v___x_1379_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1380_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1379_);
lean_dec_ref(v___x_1380_);
goto v___jp_1376_;
v___jp_1376_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_io_error_to_string(v_a_1375_);
v___x_1378_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1377_);
lean_dec_ref(v___x_1378_);
goto v___jp_1030_;
}
}
}
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
v___x_1382_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1381_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1424_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1424_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1424_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v_leanOpts_1387_; lean_object* v_forwardedArgs_1388_; uint8_t v_component_1389_; uint8_t v_printPrefix_1390_; uint8_t v_printLibDir_1391_; uint8_t v_useStdin_1392_; uint8_t v_onlyDeps_1393_; uint8_t v_onlySrcDeps_1394_; uint8_t v_depsJson_1395_; lean_object* v_opts_1396_; uint32_t v_trustLevel_1397_; uint32_t v_numThreads_1398_; lean_object* v_rootDir_x3f_1399_; lean_object* v_setupFileName_x3f_1400_; lean_object* v_oleanFileName_x3f_1401_; lean_object* v_ileanFileName_x3f_1402_; lean_object* v_cFileName_x3f_1403_; lean_object* v_bcFileName_x3f_1404_; uint8_t v_jsonOutput_1405_; lean_object* v_errorOnKinds_1406_; uint8_t v_printStats_1407_; uint8_t v_run_1408_; lean_object* v_incrSaveFileName_x3f_1409_; lean_object* v_incrLoadFileName_x3f_1410_; lean_object* v_incrHeaderSaveFileName_x3f_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1423_; 
v_leanOpts_1387_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1388_ = lean_ctor_get(v_opts_936_, 1);
v_component_1389_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1390_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1391_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1392_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1393_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1394_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1395_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1396_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1397_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1398_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1399_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1400_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1401_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1402_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1403_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1404_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1405_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1406_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1407_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1408_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1409_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1410_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1411_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1413_ = v_opts_936_;
v_isShared_1414_ = v_isSharedCheck_1423_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1411_);
lean_inc(v_incrLoadFileName_x3f_1410_);
lean_inc(v_incrSaveFileName_x3f_1409_);
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
lean_dec(v_opts_936_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1423_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1415_ = l_String_toName(v_a_1383_);
v___x_1416_ = lean_array_push(v_errorOnKinds_1406_, v___x_1415_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 9, v___x_1416_);
v___x_1418_ = v___x_1413_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_leanOpts_1387_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_forwardedArgs_1388_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_opts_1396_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_rootDir_x3f_1399_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_setupFileName_x3f_1400_);
lean_ctor_set(v_reuseFailAlloc_1422_, 5, v_oleanFileName_x3f_1401_);
lean_ctor_set(v_reuseFailAlloc_1422_, 6, v_ileanFileName_x3f_1402_);
lean_ctor_set(v_reuseFailAlloc_1422_, 7, v_cFileName_x3f_1403_);
lean_ctor_set(v_reuseFailAlloc_1422_, 8, v_bcFileName_x3f_1404_);
lean_ctor_set(v_reuseFailAlloc_1422_, 9, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1422_, 10, v_incrSaveFileName_x3f_1409_);
lean_ctor_set(v_reuseFailAlloc_1422_, 11, v_incrLoadFileName_x3f_1410_);
lean_ctor_set(v_reuseFailAlloc_1422_, 12, v_incrHeaderSaveFileName_x3f_1411_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*13 + 8, v_component_1389_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*13 + 9, v_printPrefix_1390_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*13 + 10, v_printLibDir_1391_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*13 + 11, v_useStdin_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*13 + 12, v_onlyDeps_1393_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*13 + 13, v_onlySrcDeps_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*13 + 14, v_depsJson_1395_);
lean_ctor_set_uint32(v_reuseFailAlloc_1422_, sizeof(void*)*13, v_trustLevel_1397_);
lean_ctor_set_uint32(v_reuseFailAlloc_1422_, sizeof(void*)*13 + 4, v_numThreads_1398_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*13 + 15, v_jsonOutput_1405_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*13 + 16, v_printStats_1407_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*13 + 17, v_run_1408_);
v___x_1418_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; 
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1418_);
v___x_1420_ = v___x_1385_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec_ref(v_opts_936_);
v_a_1425_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1382_, 1);
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
goto v___jp_1076_;
}
}
}
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
v___x_1432_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1431_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1473_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1473_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1473_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_leanOpts_1437_; lean_object* v_forwardedArgs_1438_; uint8_t v_component_1439_; uint8_t v_printPrefix_1440_; uint8_t v_printLibDir_1441_; uint8_t v_useStdin_1442_; uint8_t v_onlyDeps_1443_; uint8_t v_onlySrcDeps_1444_; uint8_t v_depsJson_1445_; lean_object* v_opts_1446_; uint32_t v_trustLevel_1447_; uint32_t v_numThreads_1448_; lean_object* v_rootDir_x3f_1449_; lean_object* v_oleanFileName_x3f_1450_; lean_object* v_ileanFileName_x3f_1451_; lean_object* v_cFileName_x3f_1452_; lean_object* v_bcFileName_x3f_1453_; uint8_t v_jsonOutput_1454_; lean_object* v_errorOnKinds_1455_; uint8_t v_printStats_1456_; uint8_t v_run_1457_; lean_object* v_incrSaveFileName_x3f_1458_; lean_object* v_incrLoadFileName_x3f_1459_; lean_object* v_incrHeaderSaveFileName_x3f_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1471_; 
v_leanOpts_1437_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1438_ = lean_ctor_get(v_opts_936_, 1);
v_component_1439_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1440_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1441_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1442_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1443_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1444_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1445_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1446_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1447_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1448_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1449_ = lean_ctor_get(v_opts_936_, 3);
v_oleanFileName_x3f_1450_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1451_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1452_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1453_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1454_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1455_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1456_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1457_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1458_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1459_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1460_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; 
v_unused_1472_ = lean_ctor_get(v_opts_936_, 4);
lean_dec(v_unused_1472_);
v___x_1462_ = v_opts_936_;
v_isShared_1463_ = v_isSharedCheck_1471_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1460_);
lean_inc(v_incrLoadFileName_x3f_1459_);
lean_inc(v_incrSaveFileName_x3f_1458_);
lean_inc(v_errorOnKinds_1455_);
lean_inc(v_bcFileName_x3f_1453_);
lean_inc(v_cFileName_x3f_1452_);
lean_inc(v_ileanFileName_x3f_1451_);
lean_inc(v_oleanFileName_x3f_1450_);
lean_inc(v_rootDir_x3f_1449_);
lean_inc(v_opts_1446_);
lean_inc(v_forwardedArgs_1438_);
lean_inc(v_leanOpts_1437_);
lean_dec(v_opts_936_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1471_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_a_1433_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 4, v___x_1464_);
v___x_1466_ = v___x_1462_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_leanOpts_1437_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_forwardedArgs_1438_);
lean_ctor_set(v_reuseFailAlloc_1470_, 2, v_opts_1446_);
lean_ctor_set(v_reuseFailAlloc_1470_, 3, v_rootDir_x3f_1449_);
lean_ctor_set(v_reuseFailAlloc_1470_, 4, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1470_, 5, v_oleanFileName_x3f_1450_);
lean_ctor_set(v_reuseFailAlloc_1470_, 6, v_ileanFileName_x3f_1451_);
lean_ctor_set(v_reuseFailAlloc_1470_, 7, v_cFileName_x3f_1452_);
lean_ctor_set(v_reuseFailAlloc_1470_, 8, v_bcFileName_x3f_1453_);
lean_ctor_set(v_reuseFailAlloc_1470_, 9, v_errorOnKinds_1455_);
lean_ctor_set(v_reuseFailAlloc_1470_, 10, v_incrSaveFileName_x3f_1458_);
lean_ctor_set(v_reuseFailAlloc_1470_, 11, v_incrLoadFileName_x3f_1459_);
lean_ctor_set(v_reuseFailAlloc_1470_, 12, v_incrHeaderSaveFileName_x3f_1460_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*13 + 8, v_component_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*13 + 9, v_printPrefix_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*13 + 10, v_printLibDir_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*13 + 11, v_useStdin_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*13 + 12, v_onlyDeps_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*13 + 13, v_onlySrcDeps_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*13 + 14, v_depsJson_1445_);
lean_ctor_set_uint32(v_reuseFailAlloc_1470_, sizeof(void*)*13, v_trustLevel_1447_);
lean_ctor_set_uint32(v_reuseFailAlloc_1470_, sizeof(void*)*13 + 4, v_numThreads_1448_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*13 + 15, v_jsonOutput_1454_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*13 + 16, v_printStats_1456_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*13 + 17, v_run_1457_);
v___x_1466_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1468_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1466_);
v___x_1468_ = v___x_1435_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec_ref(v_opts_936_);
v_a_1474_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1432_, 1);
v___x_1478_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1479_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1478_);
lean_dec_ref(v___x_1479_);
goto v___jp_1475_;
v___jp_1475_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = lean_io_error_to_string(v_a_1474_);
v___x_1477_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1476_);
lean_dec_ref(v___x_1477_);
goto v___jp_1024_;
}
}
}
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
v___x_1481_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1480_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1483_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc_n(v_a_1482_, 2);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1483_ = lean_load_dynlib(v_a_1482_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1525_; 
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; 
v_unused_1526_ = lean_ctor_get(v___x_1483_, 0);
lean_dec(v_unused_1526_);
v___x_1485_ = v___x_1483_;
v_isShared_1486_ = v_isSharedCheck_1525_;
goto v_resetjp_1484_;
}
else
{
lean_dec(v___x_1483_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1525_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v_leanOpts_1487_; lean_object* v_forwardedArgs_1488_; uint8_t v_component_1489_; uint8_t v_printPrefix_1490_; uint8_t v_printLibDir_1491_; uint8_t v_useStdin_1492_; uint8_t v_onlyDeps_1493_; uint8_t v_onlySrcDeps_1494_; uint8_t v_depsJson_1495_; lean_object* v_opts_1496_; uint32_t v_trustLevel_1497_; uint32_t v_numThreads_1498_; lean_object* v_rootDir_x3f_1499_; lean_object* v_setupFileName_x3f_1500_; lean_object* v_oleanFileName_x3f_1501_; lean_object* v_ileanFileName_x3f_1502_; lean_object* v_cFileName_x3f_1503_; lean_object* v_bcFileName_x3f_1504_; uint8_t v_jsonOutput_1505_; lean_object* v_errorOnKinds_1506_; uint8_t v_printStats_1507_; uint8_t v_run_1508_; lean_object* v_incrSaveFileName_x3f_1509_; lean_object* v_incrLoadFileName_x3f_1510_; lean_object* v_incrHeaderSaveFileName_x3f_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1524_; 
v_leanOpts_1487_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1488_ = lean_ctor_get(v_opts_936_, 1);
v_component_1489_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1490_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1491_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1492_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1493_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1494_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1495_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1496_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1497_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1498_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1499_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1500_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1501_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1502_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1503_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1504_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1505_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1506_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1507_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1508_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1509_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1510_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1511_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1513_ = v_opts_936_;
v_isShared_1514_ = v_isSharedCheck_1524_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1511_);
lean_inc(v_incrLoadFileName_x3f_1510_);
lean_inc(v_incrSaveFileName_x3f_1509_);
lean_inc(v_errorOnKinds_1506_);
lean_inc(v_bcFileName_x3f_1504_);
lean_inc(v_cFileName_x3f_1503_);
lean_inc(v_ileanFileName_x3f_1502_);
lean_inc(v_oleanFileName_x3f_1501_);
lean_inc(v_setupFileName_x3f_1500_);
lean_inc(v_rootDir_x3f_1499_);
lean_inc(v_opts_1496_);
lean_inc(v_forwardedArgs_1488_);
lean_inc(v_leanOpts_1487_);
lean_dec(v_opts_936_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1524_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1515_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
v___x_1516_ = lean_string_append(v___x_1515_, v_a_1482_);
lean_dec(v_a_1482_);
v___x_1517_ = lean_array_push(v_forwardedArgs_1488_, v___x_1516_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 1, v___x_1517_);
v___x_1519_ = v___x_1513_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_leanOpts_1487_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_opts_1496_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_rootDir_x3f_1499_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v_setupFileName_x3f_1500_);
lean_ctor_set(v_reuseFailAlloc_1523_, 5, v_oleanFileName_x3f_1501_);
lean_ctor_set(v_reuseFailAlloc_1523_, 6, v_ileanFileName_x3f_1502_);
lean_ctor_set(v_reuseFailAlloc_1523_, 7, v_cFileName_x3f_1503_);
lean_ctor_set(v_reuseFailAlloc_1523_, 8, v_bcFileName_x3f_1504_);
lean_ctor_set(v_reuseFailAlloc_1523_, 9, v_errorOnKinds_1506_);
lean_ctor_set(v_reuseFailAlloc_1523_, 10, v_incrSaveFileName_x3f_1509_);
lean_ctor_set(v_reuseFailAlloc_1523_, 11, v_incrLoadFileName_x3f_1510_);
lean_ctor_set(v_reuseFailAlloc_1523_, 12, v_incrHeaderSaveFileName_x3f_1511_);
lean_ctor_set_uint8(v_reuseFailAlloc_1523_, sizeof(void*)*13 + 8, v_component_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1523_, sizeof(void*)*13 + 9, v_printPrefix_1490_);
lean_ctor_set_uint8(v_reuseFailAlloc_1523_, sizeof(void*)*13 + 10, v_printLibDir_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1523_, sizeof(void*)*13 + 11, v_useStdin_1492_);
lean_ctor_set_uint8(v_reuseFailAlloc_1523_, sizeof(void*)*13 + 12, v_onlyDeps_1493_);
lean_ctor_set_uint8(v_reuseFailAlloc_1523_, sizeof(void*)*13 + 13, v_onlySrcDeps_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1523_, sizeof(void*)*13 + 14, v_depsJson_1495_);
lean_ctor_set_uint32(v_reuseFailAlloc_1523_, sizeof(void*)*13, v_trustLevel_1497_);
lean_ctor_set_uint32(v_reuseFailAlloc_1523_, sizeof(void*)*13 + 4, v_numThreads_1498_);
lean_ctor_set_uint8(v_reuseFailAlloc_1523_, sizeof(void*)*13 + 15, v_jsonOutput_1505_);
lean_ctor_set_uint8(v_reuseFailAlloc_1523_, sizeof(void*)*13 + 16, v_printStats_1507_);
lean_ctor_set_uint8(v_reuseFailAlloc_1523_, sizeof(void*)*13 + 17, v_run_1508_);
v___x_1519_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1521_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1519_);
v___x_1521_ = v___x_1485_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec(v_a_1482_);
lean_dec_ref(v_opts_936_);
v_a_1527_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1531_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1532_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1531_);
lean_dec_ref(v___x_1532_);
goto v___jp_1528_;
v___jp_1528_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_io_error_to_string(v_a_1527_);
v___x_1530_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1529_);
lean_dec_ref(v___x_1530_);
goto v___jp_1082_;
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec_ref(v_opts_936_);
v_a_1533_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1481_, 1);
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
goto v___jp_1088_;
}
}
}
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
v___x_1540_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1539_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1612_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1612_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1612_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_fst_1546_; lean_object* v_snd_1547_; lean_object* v___y_1596_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1607_ = lean_unsigned_to_nat(0u);
v___x_1608_ = lean_string_utf8_byte_size(v_a_1541_);
v___x_1609_ = lean_box(0);
v___x_1610_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(v___x_1608_, v_a_1541_, v___x_1607_, v___x_1609_);
if (lean_obj_tag(v___x_1610_) == 0)
{
v___y_1596_ = v___x_1608_;
goto v___jp_1595_;
}
else
{
lean_object* v_val_1611_; 
v_val_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_val_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v___y_1596_ = v_val_1611_;
goto v___jp_1595_;
}
v___jp_1545_:
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_load_plugin(v_fst_1546_, v_snd_1547_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1590_; 
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v___x_1548_, 0);
lean_dec(v_unused_1591_);
v___x_1550_ = v___x_1548_;
v_isShared_1551_ = v_isSharedCheck_1590_;
goto v_resetjp_1549_;
}
else
{
lean_dec(v___x_1548_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1590_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v_leanOpts_1552_; lean_object* v_forwardedArgs_1553_; uint8_t v_component_1554_; uint8_t v_printPrefix_1555_; uint8_t v_printLibDir_1556_; uint8_t v_useStdin_1557_; uint8_t v_onlyDeps_1558_; uint8_t v_onlySrcDeps_1559_; uint8_t v_depsJson_1560_; lean_object* v_opts_1561_; uint32_t v_trustLevel_1562_; uint32_t v_numThreads_1563_; lean_object* v_rootDir_x3f_1564_; lean_object* v_setupFileName_x3f_1565_; lean_object* v_oleanFileName_x3f_1566_; lean_object* v_ileanFileName_x3f_1567_; lean_object* v_cFileName_x3f_1568_; lean_object* v_bcFileName_x3f_1569_; uint8_t v_jsonOutput_1570_; lean_object* v_errorOnKinds_1571_; uint8_t v_printStats_1572_; uint8_t v_run_1573_; lean_object* v_incrSaveFileName_x3f_1574_; lean_object* v_incrLoadFileName_x3f_1575_; lean_object* v_incrHeaderSaveFileName_x3f_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1589_; 
v_leanOpts_1552_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1553_ = lean_ctor_get(v_opts_936_, 1);
v_component_1554_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1555_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1556_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1557_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1558_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1559_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1560_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1561_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1562_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1563_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1564_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1565_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1566_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1567_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1568_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1569_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1570_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1571_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1572_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1573_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1574_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1575_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1576_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1578_ = v_opts_936_;
v_isShared_1579_ = v_isSharedCheck_1589_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1576_);
lean_inc(v_incrLoadFileName_x3f_1575_);
lean_inc(v_incrSaveFileName_x3f_1574_);
lean_inc(v_errorOnKinds_1571_);
lean_inc(v_bcFileName_x3f_1569_);
lean_inc(v_cFileName_x3f_1568_);
lean_inc(v_ileanFileName_x3f_1567_);
lean_inc(v_oleanFileName_x3f_1566_);
lean_inc(v_setupFileName_x3f_1565_);
lean_inc(v_rootDir_x3f_1564_);
lean_inc(v_opts_1561_);
lean_inc(v_forwardedArgs_1553_);
lean_inc(v_leanOpts_1552_);
lean_dec(v_opts_936_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1589_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1580_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
v___x_1581_ = lean_string_append(v___x_1580_, v_a_1541_);
lean_dec(v_a_1541_);
v___x_1582_ = lean_array_push(v_forwardedArgs_1553_, v___x_1581_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 1, v___x_1582_);
v___x_1584_ = v___x_1578_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_leanOpts_1552_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_opts_1561_);
lean_ctor_set(v_reuseFailAlloc_1588_, 3, v_rootDir_x3f_1564_);
lean_ctor_set(v_reuseFailAlloc_1588_, 4, v_setupFileName_x3f_1565_);
lean_ctor_set(v_reuseFailAlloc_1588_, 5, v_oleanFileName_x3f_1566_);
lean_ctor_set(v_reuseFailAlloc_1588_, 6, v_ileanFileName_x3f_1567_);
lean_ctor_set(v_reuseFailAlloc_1588_, 7, v_cFileName_x3f_1568_);
lean_ctor_set(v_reuseFailAlloc_1588_, 8, v_bcFileName_x3f_1569_);
lean_ctor_set(v_reuseFailAlloc_1588_, 9, v_errorOnKinds_1571_);
lean_ctor_set(v_reuseFailAlloc_1588_, 10, v_incrSaveFileName_x3f_1574_);
lean_ctor_set(v_reuseFailAlloc_1588_, 11, v_incrLoadFileName_x3f_1575_);
lean_ctor_set(v_reuseFailAlloc_1588_, 12, v_incrHeaderSaveFileName_x3f_1576_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*13 + 8, v_component_1554_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*13 + 9, v_printPrefix_1555_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*13 + 10, v_printLibDir_1556_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*13 + 11, v_useStdin_1557_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*13 + 12, v_onlyDeps_1558_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*13 + 13, v_onlySrcDeps_1559_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*13 + 14, v_depsJson_1560_);
lean_ctor_set_uint32(v_reuseFailAlloc_1588_, sizeof(void*)*13, v_trustLevel_1562_);
lean_ctor_set_uint32(v_reuseFailAlloc_1588_, sizeof(void*)*13 + 4, v_numThreads_1563_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*13 + 15, v_jsonOutput_1570_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*13 + 16, v_printStats_1572_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*13 + 17, v_run_1573_);
v___x_1584_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1586_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1584_);
v___x_1586_ = v___x_1550_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec(v_a_1541_);
lean_dec_ref(v_opts_936_);
v_a_1592_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1593_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1594_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1593_);
lean_dec_ref(v___x_1594_);
v___y_1104_ = v_a_1592_;
goto v___jp_1103_;
}
}
v___jp_1595_:
{
lean_object* v___x_1597_; uint8_t v_decide_1598_; 
v___x_1597_ = lean_string_utf8_byte_size(v_a_1541_);
v_decide_1598_ = lean_nat_dec_eq(v___y_1596_, v___x_1597_);
if (v_decide_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1599_ = lean_unsigned_to_nat(0u);
v___x_1600_ = lean_string_utf8_next_fast(v_a_1541_, v___y_1596_);
v___x_1601_ = lean_string_utf8_extract_fast(v_a_1541_, v___x_1599_, v___y_1596_);
lean_dec(v___y_1596_);
v___x_1602_ = lean_string_utf8_extract_fast(v_a_1541_, v___x_1600_, v___x_1597_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set_tag(v___x_1543_, 1);
lean_ctor_set(v___x_1543_, 0, v___x_1602_);
v___x_1604_ = v___x_1543_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
v_fst_1546_ = v___x_1601_;
v_snd_1547_ = v___x_1604_;
goto v___jp_1545_;
}
}
else
{
lean_object* v___x_1606_; 
lean_dec(v___y_1596_);
lean_del_object(v___x_1543_);
v___x_1606_ = lean_box(0);
lean_inc(v_a_1541_);
v_fst_1546_ = v_a_1541_;
v_snd_1547_ = v___x_1606_;
goto v___jp_1545_;
}
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_dec_ref(v_opts_936_);
v_a_1613_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1617_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1618_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1617_);
lean_dec_ref(v___x_1618_);
goto v___jp_1614_;
v___jp_1614_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = lean_io_error_to_string(v_a_1613_);
v___x_1616_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1615_);
lean_dec_ref(v___x_1616_);
goto v___jp_1100_;
}
}
}
}
else
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__16, &l___private_Lean_Shell_0__Lean_displayHelp___closed__16_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
if (v___x_1619_ == 0)
{
lean_dec(v_optArg_x3f_938_);
lean_dec_ref(v_opts_936_);
goto v___jp_1064_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
v___x_1621_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1620_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1630_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1630_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1630_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1626_ = lean_internal_enable_debug(v_a_1622_);
lean_dec(v_a_1622_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v_opts_936_);
v___x_1628_ = v___x_1624_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_opts_936_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec_ref(v_opts_936_);
v_a_1631_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1635_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1636_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1635_);
lean_dec_ref(v___x_1636_);
goto v___jp_1632_;
v___jp_1632_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = lean_io_error_to_string(v_a_1631_);
v___x_1634_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1633_);
lean_dec_ref(v___x_1634_);
goto v___jp_1110_;
}
}
}
}
}
else
{
lean_object* v_leanOpts_1637_; lean_object* v_forwardedArgs_1638_; uint8_t v_component_1639_; uint8_t v_printPrefix_1640_; uint8_t v_printLibDir_1641_; uint8_t v_useStdin_1642_; uint8_t v_onlyDeps_1643_; uint8_t v_onlySrcDeps_1644_; uint8_t v_depsJson_1645_; lean_object* v_opts_1646_; uint32_t v_trustLevel_1647_; uint32_t v_numThreads_1648_; lean_object* v_rootDir_x3f_1649_; lean_object* v_setupFileName_x3f_1650_; lean_object* v_oleanFileName_x3f_1651_; lean_object* v_ileanFileName_x3f_1652_; lean_object* v_cFileName_x3f_1653_; lean_object* v_bcFileName_x3f_1654_; uint8_t v_jsonOutput_1655_; lean_object* v_errorOnKinds_1656_; uint8_t v_printStats_1657_; uint8_t v_run_1658_; lean_object* v_incrSaveFileName_x3f_1659_; lean_object* v_incrLoadFileName_x3f_1660_; lean_object* v_incrHeaderSaveFileName_x3f_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1671_; 
lean_dec(v_optArg_x3f_938_);
v_leanOpts_1637_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1638_ = lean_ctor_get(v_opts_936_, 1);
v_component_1639_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1640_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1641_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1642_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1643_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1644_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1645_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1646_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1647_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1648_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1649_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1650_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1651_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1652_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1653_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1654_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1655_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1656_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1657_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1658_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1659_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1660_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1661_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1663_ = v_opts_936_;
v_isShared_1664_ = v_isSharedCheck_1671_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1661_);
lean_inc(v_incrLoadFileName_x3f_1660_);
lean_inc(v_incrSaveFileName_x3f_1659_);
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
lean_dec(v_opts_936_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1671_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1665_ = l_Lean_profiler;
v___x_1666_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_1637_, v___x_1665_, v___x_1217_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1666_);
v___x_1668_ = v___x_1663_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1666_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_forwardedArgs_1638_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_opts_1646_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v_rootDir_x3f_1649_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v_setupFileName_x3f_1650_);
lean_ctor_set(v_reuseFailAlloc_1670_, 5, v_oleanFileName_x3f_1651_);
lean_ctor_set(v_reuseFailAlloc_1670_, 6, v_ileanFileName_x3f_1652_);
lean_ctor_set(v_reuseFailAlloc_1670_, 7, v_cFileName_x3f_1653_);
lean_ctor_set(v_reuseFailAlloc_1670_, 8, v_bcFileName_x3f_1654_);
lean_ctor_set(v_reuseFailAlloc_1670_, 9, v_errorOnKinds_1656_);
lean_ctor_set(v_reuseFailAlloc_1670_, 10, v_incrSaveFileName_x3f_1659_);
lean_ctor_set(v_reuseFailAlloc_1670_, 11, v_incrLoadFileName_x3f_1660_);
lean_ctor_set(v_reuseFailAlloc_1670_, 12, v_incrHeaderSaveFileName_x3f_1661_);
lean_ctor_set_uint8(v_reuseFailAlloc_1670_, sizeof(void*)*13 + 8, v_component_1639_);
lean_ctor_set_uint8(v_reuseFailAlloc_1670_, sizeof(void*)*13 + 9, v_printPrefix_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1670_, sizeof(void*)*13 + 10, v_printLibDir_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1670_, sizeof(void*)*13 + 11, v_useStdin_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1670_, sizeof(void*)*13 + 12, v_onlyDeps_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1670_, sizeof(void*)*13 + 13, v_onlySrcDeps_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1670_, sizeof(void*)*13 + 14, v_depsJson_1645_);
lean_ctor_set_uint32(v_reuseFailAlloc_1670_, sizeof(void*)*13, v_trustLevel_1647_);
lean_ctor_set_uint32(v_reuseFailAlloc_1670_, sizeof(void*)*13 + 4, v_numThreads_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1670_, sizeof(void*)*13 + 15, v_jsonOutput_1655_);
lean_ctor_set_uint8(v_reuseFailAlloc_1670_, sizeof(void*)*13 + 16, v_printStats_1657_);
lean_ctor_set_uint8(v_reuseFailAlloc_1670_, sizeof(void*)*13 + 17, v_run_1658_);
v___x_1668_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_leanOpts_1672_; lean_object* v_forwardedArgs_1673_; uint8_t v_printPrefix_1674_; uint8_t v_printLibDir_1675_; uint8_t v_useStdin_1676_; uint8_t v_onlyDeps_1677_; uint8_t v_onlySrcDeps_1678_; uint8_t v_depsJson_1679_; lean_object* v_opts_1680_; uint32_t v_trustLevel_1681_; uint32_t v_numThreads_1682_; lean_object* v_rootDir_x3f_1683_; lean_object* v_setupFileName_x3f_1684_; lean_object* v_oleanFileName_x3f_1685_; lean_object* v_ileanFileName_x3f_1686_; lean_object* v_cFileName_x3f_1687_; lean_object* v_bcFileName_x3f_1688_; uint8_t v_jsonOutput_1689_; lean_object* v_errorOnKinds_1690_; uint8_t v_printStats_1691_; uint8_t v_run_1692_; lean_object* v_incrSaveFileName_x3f_1693_; lean_object* v_incrLoadFileName_x3f_1694_; lean_object* v_incrHeaderSaveFileName_x3f_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v_optArg_x3f_938_);
v_leanOpts_1672_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1673_ = lean_ctor_get(v_opts_936_, 1);
v_printPrefix_1674_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1675_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1676_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1677_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1678_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1679_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1680_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1681_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1682_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1683_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1684_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1685_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1686_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1687_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1688_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1689_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1690_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1691_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1692_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1693_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1694_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1695_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1697_ = v_opts_936_;
v_isShared_1698_ = v_isSharedCheck_1704_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1695_);
lean_inc(v_incrLoadFileName_x3f_1694_);
lean_inc(v_incrSaveFileName_x3f_1693_);
lean_inc(v_errorOnKinds_1690_);
lean_inc(v_bcFileName_x3f_1688_);
lean_inc(v_cFileName_x3f_1687_);
lean_inc(v_ileanFileName_x3f_1686_);
lean_inc(v_oleanFileName_x3f_1685_);
lean_inc(v_setupFileName_x3f_1684_);
lean_inc(v_rootDir_x3f_1683_);
lean_inc(v_opts_1680_);
lean_inc(v_forwardedArgs_1673_);
lean_inc(v_leanOpts_1672_);
lean_dec(v_opts_936_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1704_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
uint8_t v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = 2;
if (v_isShared_1698_ == 0)
{
v___x_1701_ = v___x_1697_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_leanOpts_1672_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_forwardedArgs_1673_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_opts_1680_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v_rootDir_x3f_1683_);
lean_ctor_set(v_reuseFailAlloc_1703_, 4, v_setupFileName_x3f_1684_);
lean_ctor_set(v_reuseFailAlloc_1703_, 5, v_oleanFileName_x3f_1685_);
lean_ctor_set(v_reuseFailAlloc_1703_, 6, v_ileanFileName_x3f_1686_);
lean_ctor_set(v_reuseFailAlloc_1703_, 7, v_cFileName_x3f_1687_);
lean_ctor_set(v_reuseFailAlloc_1703_, 8, v_bcFileName_x3f_1688_);
lean_ctor_set(v_reuseFailAlloc_1703_, 9, v_errorOnKinds_1690_);
lean_ctor_set(v_reuseFailAlloc_1703_, 10, v_incrSaveFileName_x3f_1693_);
lean_ctor_set(v_reuseFailAlloc_1703_, 11, v_incrLoadFileName_x3f_1694_);
lean_ctor_set(v_reuseFailAlloc_1703_, 12, v_incrHeaderSaveFileName_x3f_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*13 + 9, v_printPrefix_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*13 + 10, v_printLibDir_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*13 + 11, v_useStdin_1676_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*13 + 12, v_onlyDeps_1677_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*13 + 13, v_onlySrcDeps_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*13 + 14, v_depsJson_1679_);
lean_ctor_set_uint32(v_reuseFailAlloc_1703_, sizeof(void*)*13, v_trustLevel_1681_);
lean_ctor_set_uint32(v_reuseFailAlloc_1703_, sizeof(void*)*13 + 4, v_numThreads_1682_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*13 + 15, v_jsonOutput_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*13 + 16, v_printStats_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1703_, sizeof(void*)*13 + 17, v_run_1692_);
v___x_1701_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1702_; 
lean_ctor_set_uint8(v___x_1701_, sizeof(void*)*13 + 8, v___x_1699_);
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
return v___x_1702_;
}
}
}
}
else
{
lean_object* v_leanOpts_1705_; lean_object* v_forwardedArgs_1706_; uint8_t v_printPrefix_1707_; uint8_t v_printLibDir_1708_; uint8_t v_useStdin_1709_; uint8_t v_onlyDeps_1710_; uint8_t v_onlySrcDeps_1711_; uint8_t v_depsJson_1712_; lean_object* v_opts_1713_; uint32_t v_trustLevel_1714_; uint32_t v_numThreads_1715_; lean_object* v_rootDir_x3f_1716_; lean_object* v_setupFileName_x3f_1717_; lean_object* v_oleanFileName_x3f_1718_; lean_object* v_ileanFileName_x3f_1719_; lean_object* v_cFileName_x3f_1720_; lean_object* v_bcFileName_x3f_1721_; uint8_t v_jsonOutput_1722_; lean_object* v_errorOnKinds_1723_; uint8_t v_printStats_1724_; uint8_t v_run_1725_; lean_object* v_incrSaveFileName_x3f_1726_; lean_object* v_incrLoadFileName_x3f_1727_; lean_object* v_incrHeaderSaveFileName_x3f_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_optArg_x3f_938_);
v_leanOpts_1705_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1706_ = lean_ctor_get(v_opts_936_, 1);
v_printPrefix_1707_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1708_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1709_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1710_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1711_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1712_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1713_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1714_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1715_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1716_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1717_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1718_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1719_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1720_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1721_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1722_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1723_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1724_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1725_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1726_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1727_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1728_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1730_ = v_opts_936_;
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1728_);
lean_inc(v_incrLoadFileName_x3f_1727_);
lean_inc(v_incrSaveFileName_x3f_1726_);
lean_inc(v_errorOnKinds_1723_);
lean_inc(v_bcFileName_x3f_1721_);
lean_inc(v_cFileName_x3f_1720_);
lean_inc(v_ileanFileName_x3f_1719_);
lean_inc(v_oleanFileName_x3f_1718_);
lean_inc(v_setupFileName_x3f_1717_);
lean_inc(v_rootDir_x3f_1716_);
lean_inc(v_opts_1713_);
lean_inc(v_forwardedArgs_1706_);
lean_inc(v_leanOpts_1705_);
lean_dec(v_opts_936_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
uint8_t v___x_1732_; lean_object* v___x_1734_; 
v___x_1732_ = 1;
if (v_isShared_1731_ == 0)
{
v___x_1734_ = v___x_1730_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_leanOpts_1705_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_forwardedArgs_1706_);
lean_ctor_set(v_reuseFailAlloc_1736_, 2, v_opts_1713_);
lean_ctor_set(v_reuseFailAlloc_1736_, 3, v_rootDir_x3f_1716_);
lean_ctor_set(v_reuseFailAlloc_1736_, 4, v_setupFileName_x3f_1717_);
lean_ctor_set(v_reuseFailAlloc_1736_, 5, v_oleanFileName_x3f_1718_);
lean_ctor_set(v_reuseFailAlloc_1736_, 6, v_ileanFileName_x3f_1719_);
lean_ctor_set(v_reuseFailAlloc_1736_, 7, v_cFileName_x3f_1720_);
lean_ctor_set(v_reuseFailAlloc_1736_, 8, v_bcFileName_x3f_1721_);
lean_ctor_set(v_reuseFailAlloc_1736_, 9, v_errorOnKinds_1723_);
lean_ctor_set(v_reuseFailAlloc_1736_, 10, v_incrSaveFileName_x3f_1726_);
lean_ctor_set(v_reuseFailAlloc_1736_, 11, v_incrLoadFileName_x3f_1727_);
lean_ctor_set(v_reuseFailAlloc_1736_, 12, v_incrHeaderSaveFileName_x3f_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*13 + 9, v_printPrefix_1707_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*13 + 10, v_printLibDir_1708_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*13 + 11, v_useStdin_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*13 + 12, v_onlyDeps_1710_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*13 + 13, v_onlySrcDeps_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*13 + 14, v_depsJson_1712_);
lean_ctor_set_uint32(v_reuseFailAlloc_1736_, sizeof(void*)*13, v_trustLevel_1714_);
lean_ctor_set_uint32(v_reuseFailAlloc_1736_, sizeof(void*)*13 + 4, v_numThreads_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*13 + 15, v_jsonOutput_1722_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*13 + 16, v_printStats_1724_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*13 + 17, v_run_1725_);
v___x_1734_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; 
lean_ctor_set_uint8(v___x_1734_, sizeof(void*)*13 + 8, v___x_1732_);
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
}
}
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
v___x_1739_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_1738_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v_leanOpts_1741_; lean_object* v_forwardedArgs_1742_; uint8_t v_component_1743_; uint8_t v_printPrefix_1744_; uint8_t v_printLibDir_1745_; uint8_t v_useStdin_1746_; uint8_t v_onlyDeps_1747_; uint8_t v_onlySrcDeps_1748_; uint8_t v_depsJson_1749_; lean_object* v_opts_1750_; uint32_t v_trustLevel_1751_; uint32_t v_numThreads_1752_; lean_object* v_rootDir_x3f_1753_; lean_object* v_setupFileName_x3f_1754_; lean_object* v_oleanFileName_x3f_1755_; lean_object* v_ileanFileName_x3f_1756_; lean_object* v_cFileName_x3f_1757_; lean_object* v_bcFileName_x3f_1758_; uint8_t v_jsonOutput_1759_; lean_object* v_errorOnKinds_1760_; uint8_t v_printStats_1761_; uint8_t v_run_1762_; lean_object* v_incrSaveFileName_x3f_1763_; lean_object* v_incrLoadFileName_x3f_1764_; lean_object* v_incrHeaderSaveFileName_x3f_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1790_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v_leanOpts_1741_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1742_ = lean_ctor_get(v_opts_936_, 1);
v_component_1743_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1744_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1745_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1746_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1747_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1748_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1749_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1750_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1751_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1752_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1753_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1754_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1755_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1756_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1757_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1758_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1759_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1760_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1761_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1762_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1763_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1764_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1765_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1767_ = v_opts_936_;
v_isShared_1768_ = v_isSharedCheck_1790_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1765_);
lean_inc(v_incrLoadFileName_x3f_1764_);
lean_inc(v_incrSaveFileName_x3f_1763_);
lean_inc(v_errorOnKinds_1760_);
lean_inc(v_bcFileName_x3f_1758_);
lean_inc(v_cFileName_x3f_1757_);
lean_inc(v_ileanFileName_x3f_1756_);
lean_inc(v_oleanFileName_x3f_1755_);
lean_inc(v_setupFileName_x3f_1754_);
lean_inc(v_rootDir_x3f_1753_);
lean_inc(v_opts_1750_);
lean_inc(v_forwardedArgs_1742_);
lean_inc(v_leanOpts_1741_);
lean_dec(v_opts_936_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1790_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; 
lean_inc(v_a_1740_);
v___x_1769_ = l___private_Lean_Shell_0__Lean_setConfigOption(v_leanOpts_1741_, v_a_1740_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1783_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1783_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1783_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1774_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
v___x_1775_ = lean_string_append(v___x_1774_, v_a_1740_);
lean_dec(v_a_1740_);
v___x_1776_ = lean_array_push(v_forwardedArgs_1742_, v___x_1775_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v___x_1776_);
lean_ctor_set(v___x_1767_, 0, v_a_1770_);
v___x_1778_ = v___x_1767_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1770_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_opts_1750_);
lean_ctor_set(v_reuseFailAlloc_1782_, 3, v_rootDir_x3f_1753_);
lean_ctor_set(v_reuseFailAlloc_1782_, 4, v_setupFileName_x3f_1754_);
lean_ctor_set(v_reuseFailAlloc_1782_, 5, v_oleanFileName_x3f_1755_);
lean_ctor_set(v_reuseFailAlloc_1782_, 6, v_ileanFileName_x3f_1756_);
lean_ctor_set(v_reuseFailAlloc_1782_, 7, v_cFileName_x3f_1757_);
lean_ctor_set(v_reuseFailAlloc_1782_, 8, v_bcFileName_x3f_1758_);
lean_ctor_set(v_reuseFailAlloc_1782_, 9, v_errorOnKinds_1760_);
lean_ctor_set(v_reuseFailAlloc_1782_, 10, v_incrSaveFileName_x3f_1763_);
lean_ctor_set(v_reuseFailAlloc_1782_, 11, v_incrLoadFileName_x3f_1764_);
lean_ctor_set(v_reuseFailAlloc_1782_, 12, v_incrHeaderSaveFileName_x3f_1765_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*13 + 8, v_component_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*13 + 9, v_printPrefix_1744_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*13 + 10, v_printLibDir_1745_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*13 + 11, v_useStdin_1746_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*13 + 12, v_onlyDeps_1747_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*13 + 13, v_onlySrcDeps_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*13 + 14, v_depsJson_1749_);
lean_ctor_set_uint32(v_reuseFailAlloc_1782_, sizeof(void*)*13, v_trustLevel_1751_);
lean_ctor_set_uint32(v_reuseFailAlloc_1782_, sizeof(void*)*13 + 4, v_numThreads_1752_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*13 + 15, v_jsonOutput_1759_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*13 + 16, v_printStats_1761_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*13 + 17, v_run_1762_);
v___x_1778_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1780_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1778_);
v___x_1780_ = v___x_1772_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_del_object(v___x_1767_);
lean_dec(v_incrHeaderSaveFileName_x3f_1765_);
lean_dec(v_incrLoadFileName_x3f_1764_);
lean_dec(v_incrSaveFileName_x3f_1763_);
lean_dec_ref(v_errorOnKinds_1760_);
lean_dec(v_bcFileName_x3f_1758_);
lean_dec(v_cFileName_x3f_1757_);
lean_dec(v_ileanFileName_x3f_1756_);
lean_dec(v_oleanFileName_x3f_1755_);
lean_dec(v_setupFileName_x3f_1754_);
lean_dec(v_rootDir_x3f_1753_);
lean_dec_ref(v_opts_1750_);
lean_dec_ref(v_forwardedArgs_1742_);
lean_dec(v_a_1740_);
v_a_1784_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1769_, 1);
v___x_1788_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1789_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1788_);
lean_dec_ref(v___x_1789_);
goto v___jp_1785_;
v___jp_1785_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_io_error_to_string(v_a_1784_);
v___x_1787_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1786_);
lean_dec_ref(v___x_1787_);
goto v___jp_1012_;
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec_ref(v_opts_936_);
v_a_1791_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1739_, 1);
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
lean_object* v_leanOpts_1797_; lean_object* v_forwardedArgs_1798_; uint8_t v_component_1799_; uint8_t v_printPrefix_1800_; uint8_t v_useStdin_1801_; uint8_t v_onlyDeps_1802_; uint8_t v_onlySrcDeps_1803_; uint8_t v_depsJson_1804_; lean_object* v_opts_1805_; uint32_t v_trustLevel_1806_; uint32_t v_numThreads_1807_; lean_object* v_rootDir_x3f_1808_; lean_object* v_setupFileName_x3f_1809_; lean_object* v_oleanFileName_x3f_1810_; lean_object* v_ileanFileName_x3f_1811_; lean_object* v_cFileName_x3f_1812_; lean_object* v_bcFileName_x3f_1813_; uint8_t v_jsonOutput_1814_; lean_object* v_errorOnKinds_1815_; uint8_t v_printStats_1816_; uint8_t v_run_1817_; lean_object* v_incrSaveFileName_x3f_1818_; lean_object* v_incrLoadFileName_x3f_1819_; lean_object* v_incrHeaderSaveFileName_x3f_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1828_; 
lean_dec(v_optArg_x3f_938_);
v_leanOpts_1797_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1798_ = lean_ctor_get(v_opts_936_, 1);
v_component_1799_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1800_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_useStdin_1801_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1802_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1803_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1804_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1805_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1806_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1807_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1808_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1809_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1810_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1811_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1812_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1813_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1814_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1815_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1816_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1817_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1818_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1819_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1820_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1822_ = v_opts_936_;
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1820_);
lean_inc(v_incrLoadFileName_x3f_1819_);
lean_inc(v_incrSaveFileName_x3f_1818_);
lean_inc(v_errorOnKinds_1815_);
lean_inc(v_bcFileName_x3f_1813_);
lean_inc(v_cFileName_x3f_1812_);
lean_inc(v_ileanFileName_x3f_1811_);
lean_inc(v_oleanFileName_x3f_1810_);
lean_inc(v_setupFileName_x3f_1809_);
lean_inc(v_rootDir_x3f_1808_);
lean_inc(v_opts_1805_);
lean_inc(v_forwardedArgs_1798_);
lean_inc(v_leanOpts_1797_);
lean_dec(v_opts_936_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_leanOpts_1797_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_forwardedArgs_1798_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_opts_1805_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_rootDir_x3f_1808_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_setupFileName_x3f_1809_);
lean_ctor_set(v_reuseFailAlloc_1827_, 5, v_oleanFileName_x3f_1810_);
lean_ctor_set(v_reuseFailAlloc_1827_, 6, v_ileanFileName_x3f_1811_);
lean_ctor_set(v_reuseFailAlloc_1827_, 7, v_cFileName_x3f_1812_);
lean_ctor_set(v_reuseFailAlloc_1827_, 8, v_bcFileName_x3f_1813_);
lean_ctor_set(v_reuseFailAlloc_1827_, 9, v_errorOnKinds_1815_);
lean_ctor_set(v_reuseFailAlloc_1827_, 10, v_incrSaveFileName_x3f_1818_);
lean_ctor_set(v_reuseFailAlloc_1827_, 11, v_incrLoadFileName_x3f_1819_);
lean_ctor_set(v_reuseFailAlloc_1827_, 12, v_incrHeaderSaveFileName_x3f_1820_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*13 + 8, v_component_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*13 + 9, v_printPrefix_1800_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*13 + 11, v_useStdin_1801_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*13 + 12, v_onlyDeps_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*13 + 13, v_onlySrcDeps_1803_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*13 + 14, v_depsJson_1804_);
lean_ctor_set_uint32(v_reuseFailAlloc_1827_, sizeof(void*)*13, v_trustLevel_1806_);
lean_ctor_set_uint32(v_reuseFailAlloc_1827_, sizeof(void*)*13 + 4, v_numThreads_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*13 + 15, v_jsonOutput_1814_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*13 + 16, v_printStats_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*13 + 17, v_run_1817_);
v___x_1825_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; 
lean_ctor_set_uint8(v___x_1825_, sizeof(void*)*13 + 10, v___x_1209_);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
return v___x_1826_;
}
}
}
}
else
{
lean_object* v_leanOpts_1829_; lean_object* v_forwardedArgs_1830_; uint8_t v_component_1831_; uint8_t v_printLibDir_1832_; uint8_t v_useStdin_1833_; uint8_t v_onlyDeps_1834_; uint8_t v_onlySrcDeps_1835_; uint8_t v_depsJson_1836_; lean_object* v_opts_1837_; uint32_t v_trustLevel_1838_; uint32_t v_numThreads_1839_; lean_object* v_rootDir_x3f_1840_; lean_object* v_setupFileName_x3f_1841_; lean_object* v_oleanFileName_x3f_1842_; lean_object* v_ileanFileName_x3f_1843_; lean_object* v_cFileName_x3f_1844_; lean_object* v_bcFileName_x3f_1845_; uint8_t v_jsonOutput_1846_; lean_object* v_errorOnKinds_1847_; uint8_t v_printStats_1848_; uint8_t v_run_1849_; lean_object* v_incrSaveFileName_x3f_1850_; lean_object* v_incrLoadFileName_x3f_1851_; lean_object* v_incrHeaderSaveFileName_x3f_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v_optArg_x3f_938_);
v_leanOpts_1829_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1830_ = lean_ctor_get(v_opts_936_, 1);
v_component_1831_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printLibDir_1832_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1833_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1834_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1835_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1836_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1837_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1838_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1839_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1840_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1841_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1842_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1843_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1844_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1845_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1846_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1847_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1848_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1849_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1850_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1851_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1852_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1854_ = v_opts_936_;
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
lean_dec(v_opts_936_);
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
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*13 + 10, v_printLibDir_1832_);
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
lean_ctor_set_uint8(v___x_1857_, sizeof(void*)*13 + 9, v___x_1207_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
}
}
else
{
lean_object* v_leanOpts_1861_; lean_object* v_forwardedArgs_1862_; uint8_t v_component_1863_; uint8_t v_printPrefix_1864_; uint8_t v_printLibDir_1865_; uint8_t v_useStdin_1866_; uint8_t v_onlyDeps_1867_; uint8_t v_onlySrcDeps_1868_; uint8_t v_depsJson_1869_; lean_object* v_opts_1870_; uint32_t v_trustLevel_1871_; uint32_t v_numThreads_1872_; lean_object* v_rootDir_x3f_1873_; lean_object* v_setupFileName_x3f_1874_; lean_object* v_oleanFileName_x3f_1875_; lean_object* v_ileanFileName_x3f_1876_; lean_object* v_cFileName_x3f_1877_; lean_object* v_bcFileName_x3f_1878_; uint8_t v_jsonOutput_1879_; lean_object* v_errorOnKinds_1880_; uint8_t v_run_1881_; lean_object* v_incrSaveFileName_x3f_1882_; lean_object* v_incrLoadFileName_x3f_1883_; lean_object* v_incrHeaderSaveFileName_x3f_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_optArg_x3f_938_);
v_leanOpts_1861_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1862_ = lean_ctor_get(v_opts_936_, 1);
v_component_1863_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1864_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1865_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1866_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1867_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1868_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1869_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1870_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1871_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1872_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1873_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1874_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1875_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1876_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1877_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1878_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1879_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1880_ = lean_ctor_get(v_opts_936_, 9);
v_run_1881_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1882_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1883_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1884_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1886_ = v_opts_936_;
v_isShared_1887_ = v_isSharedCheck_1892_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1884_);
lean_inc(v_incrLoadFileName_x3f_1883_);
lean_inc(v_incrSaveFileName_x3f_1882_);
lean_inc(v_errorOnKinds_1880_);
lean_inc(v_bcFileName_x3f_1878_);
lean_inc(v_cFileName_x3f_1877_);
lean_inc(v_ileanFileName_x3f_1876_);
lean_inc(v_oleanFileName_x3f_1875_);
lean_inc(v_setupFileName_x3f_1874_);
lean_inc(v_rootDir_x3f_1873_);
lean_inc(v_opts_1870_);
lean_inc(v_forwardedArgs_1862_);
lean_inc(v_leanOpts_1861_);
lean_dec(v_opts_936_);
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
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_opts_1870_);
lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_rootDir_x3f_1873_);
lean_ctor_set(v_reuseFailAlloc_1891_, 4, v_setupFileName_x3f_1874_);
lean_ctor_set(v_reuseFailAlloc_1891_, 5, v_oleanFileName_x3f_1875_);
lean_ctor_set(v_reuseFailAlloc_1891_, 6, v_ileanFileName_x3f_1876_);
lean_ctor_set(v_reuseFailAlloc_1891_, 7, v_cFileName_x3f_1877_);
lean_ctor_set(v_reuseFailAlloc_1891_, 8, v_bcFileName_x3f_1878_);
lean_ctor_set(v_reuseFailAlloc_1891_, 9, v_errorOnKinds_1880_);
lean_ctor_set(v_reuseFailAlloc_1891_, 10, v_incrSaveFileName_x3f_1882_);
lean_ctor_set(v_reuseFailAlloc_1891_, 11, v_incrLoadFileName_x3f_1883_);
lean_ctor_set(v_reuseFailAlloc_1891_, 12, v_incrHeaderSaveFileName_x3f_1884_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 8, v_component_1863_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 9, v_printPrefix_1864_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 10, v_printLibDir_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 11, v_useStdin_1866_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 12, v_onlyDeps_1867_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 13, v_onlySrcDeps_1868_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 14, v_depsJson_1869_);
lean_ctor_set_uint32(v_reuseFailAlloc_1891_, sizeof(void*)*13, v_trustLevel_1871_);
lean_ctor_set_uint32(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 4, v_numThreads_1872_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 15, v_jsonOutput_1879_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13 + 17, v_run_1881_);
v___x_1889_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; 
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*13 + 16, v___x_1205_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
}
}
}
else
{
lean_object* v_leanOpts_1893_; lean_object* v_forwardedArgs_1894_; uint8_t v_component_1895_; uint8_t v_printPrefix_1896_; uint8_t v_printLibDir_1897_; uint8_t v_useStdin_1898_; uint8_t v_onlyDeps_1899_; uint8_t v_onlySrcDeps_1900_; uint8_t v_depsJson_1901_; lean_object* v_opts_1902_; uint32_t v_trustLevel_1903_; uint32_t v_numThreads_1904_; lean_object* v_rootDir_x3f_1905_; lean_object* v_setupFileName_x3f_1906_; lean_object* v_oleanFileName_x3f_1907_; lean_object* v_ileanFileName_x3f_1908_; lean_object* v_cFileName_x3f_1909_; lean_object* v_bcFileName_x3f_1910_; lean_object* v_errorOnKinds_1911_; uint8_t v_printStats_1912_; uint8_t v_run_1913_; lean_object* v_incrSaveFileName_x3f_1914_; lean_object* v_incrLoadFileName_x3f_1915_; lean_object* v_incrHeaderSaveFileName_x3f_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_optArg_x3f_938_);
v_leanOpts_1893_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1894_ = lean_ctor_get(v_opts_936_, 1);
v_component_1895_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1896_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1897_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1898_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1899_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_1900_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1901_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1902_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1903_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1904_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1905_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1906_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1907_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1908_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1909_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1910_ = lean_ctor_get(v_opts_936_, 8);
v_errorOnKinds_1911_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1912_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1913_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1914_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1915_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1916_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1918_ = v_opts_936_;
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1916_);
lean_inc(v_incrLoadFileName_x3f_1915_);
lean_inc(v_incrSaveFileName_x3f_1914_);
lean_inc(v_errorOnKinds_1911_);
lean_inc(v_bcFileName_x3f_1910_);
lean_inc(v_cFileName_x3f_1909_);
lean_inc(v_ileanFileName_x3f_1908_);
lean_inc(v_oleanFileName_x3f_1907_);
lean_inc(v_setupFileName_x3f_1906_);
lean_inc(v_rootDir_x3f_1905_);
lean_inc(v_opts_1902_);
lean_inc(v_forwardedArgs_1894_);
lean_inc(v_leanOpts_1893_);
lean_dec(v_opts_936_);
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
lean_ctor_set(v_reuseFailAlloc_1923_, 9, v_errorOnKinds_1911_);
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
lean_ctor_set_uint8(v_reuseFailAlloc_1923_, sizeof(void*)*13 + 16, v_printStats_1912_);
lean_ctor_set_uint8(v_reuseFailAlloc_1923_, sizeof(void*)*13 + 17, v_run_1913_);
v___x_1921_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; 
lean_ctor_set_uint8(v___x_1921_, sizeof(void*)*13 + 15, v___x_1203_);
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
return v___x_1922_;
}
}
}
}
else
{
lean_object* v_leanOpts_1925_; lean_object* v_forwardedArgs_1926_; uint8_t v_component_1927_; uint8_t v_printPrefix_1928_; uint8_t v_printLibDir_1929_; uint8_t v_useStdin_1930_; uint8_t v_onlySrcDeps_1931_; lean_object* v_opts_1932_; uint32_t v_trustLevel_1933_; uint32_t v_numThreads_1934_; lean_object* v_rootDir_x3f_1935_; lean_object* v_setupFileName_x3f_1936_; lean_object* v_oleanFileName_x3f_1937_; lean_object* v_ileanFileName_x3f_1938_; lean_object* v_cFileName_x3f_1939_; lean_object* v_bcFileName_x3f_1940_; uint8_t v_jsonOutput_1941_; lean_object* v_errorOnKinds_1942_; uint8_t v_printStats_1943_; uint8_t v_run_1944_; lean_object* v_incrSaveFileName_x3f_1945_; lean_object* v_incrLoadFileName_x3f_1946_; lean_object* v_incrHeaderSaveFileName_x3f_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v_optArg_x3f_938_);
v_leanOpts_1925_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1926_ = lean_ctor_get(v_opts_936_, 1);
v_component_1927_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1928_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1929_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1930_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1931_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_opts_1932_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1933_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1934_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1935_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1936_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1937_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1938_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1939_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1940_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1941_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1942_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1943_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1944_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1945_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1946_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1947_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1949_ = v_opts_936_;
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_1947_);
lean_inc(v_incrLoadFileName_x3f_1946_);
lean_inc(v_incrSaveFileName_x3f_1945_);
lean_inc(v_errorOnKinds_1942_);
lean_inc(v_bcFileName_x3f_1940_);
lean_inc(v_cFileName_x3f_1939_);
lean_inc(v_ileanFileName_x3f_1938_);
lean_inc(v_oleanFileName_x3f_1937_);
lean_inc(v_setupFileName_x3f_1936_);
lean_inc(v_rootDir_x3f_1935_);
lean_inc(v_opts_1932_);
lean_inc(v_forwardedArgs_1926_);
lean_inc(v_leanOpts_1925_);
lean_dec(v_opts_936_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_leanOpts_1925_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_forwardedArgs_1926_);
lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_opts_1932_);
lean_ctor_set(v_reuseFailAlloc_1954_, 3, v_rootDir_x3f_1935_);
lean_ctor_set(v_reuseFailAlloc_1954_, 4, v_setupFileName_x3f_1936_);
lean_ctor_set(v_reuseFailAlloc_1954_, 5, v_oleanFileName_x3f_1937_);
lean_ctor_set(v_reuseFailAlloc_1954_, 6, v_ileanFileName_x3f_1938_);
lean_ctor_set(v_reuseFailAlloc_1954_, 7, v_cFileName_x3f_1939_);
lean_ctor_set(v_reuseFailAlloc_1954_, 8, v_bcFileName_x3f_1940_);
lean_ctor_set(v_reuseFailAlloc_1954_, 9, v_errorOnKinds_1942_);
lean_ctor_set(v_reuseFailAlloc_1954_, 10, v_incrSaveFileName_x3f_1945_);
lean_ctor_set(v_reuseFailAlloc_1954_, 11, v_incrLoadFileName_x3f_1946_);
lean_ctor_set(v_reuseFailAlloc_1954_, 12, v_incrHeaderSaveFileName_x3f_1947_);
lean_ctor_set_uint8(v_reuseFailAlloc_1954_, sizeof(void*)*13 + 8, v_component_1927_);
lean_ctor_set_uint8(v_reuseFailAlloc_1954_, sizeof(void*)*13 + 9, v_printPrefix_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_1954_, sizeof(void*)*13 + 10, v_printLibDir_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_1954_, sizeof(void*)*13 + 11, v_useStdin_1930_);
lean_ctor_set_uint8(v_reuseFailAlloc_1954_, sizeof(void*)*13 + 13, v_onlySrcDeps_1931_);
lean_ctor_set_uint32(v_reuseFailAlloc_1954_, sizeof(void*)*13, v_trustLevel_1933_);
lean_ctor_set_uint32(v_reuseFailAlloc_1954_, sizeof(void*)*13 + 4, v_numThreads_1934_);
lean_ctor_set_uint8(v_reuseFailAlloc_1954_, sizeof(void*)*13 + 15, v_jsonOutput_1941_);
lean_ctor_set_uint8(v_reuseFailAlloc_1954_, sizeof(void*)*13 + 16, v_printStats_1943_);
lean_ctor_set_uint8(v_reuseFailAlloc_1954_, sizeof(void*)*13 + 17, v_run_1944_);
v___x_1952_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1953_; 
lean_ctor_set_uint8(v___x_1952_, sizeof(void*)*13 + 12, v___x_1201_);
lean_ctor_set_uint8(v___x_1952_, sizeof(void*)*13 + 14, v___x_1201_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
}
}
}
else
{
lean_object* v_leanOpts_1956_; lean_object* v_forwardedArgs_1957_; uint8_t v_component_1958_; uint8_t v_printPrefix_1959_; uint8_t v_printLibDir_1960_; uint8_t v_useStdin_1961_; uint8_t v_onlyDeps_1962_; uint8_t v_depsJson_1963_; lean_object* v_opts_1964_; uint32_t v_trustLevel_1965_; uint32_t v_numThreads_1966_; lean_object* v_rootDir_x3f_1967_; lean_object* v_setupFileName_x3f_1968_; lean_object* v_oleanFileName_x3f_1969_; lean_object* v_ileanFileName_x3f_1970_; lean_object* v_cFileName_x3f_1971_; lean_object* v_bcFileName_x3f_1972_; uint8_t v_jsonOutput_1973_; lean_object* v_errorOnKinds_1974_; uint8_t v_printStats_1975_; uint8_t v_run_1976_; lean_object* v_incrSaveFileName_x3f_1977_; lean_object* v_incrLoadFileName_x3f_1978_; lean_object* v_incrHeaderSaveFileName_x3f_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_optArg_x3f_938_);
v_leanOpts_1956_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1957_ = lean_ctor_get(v_opts_936_, 1);
v_component_1958_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1959_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1960_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1961_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_1962_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_depsJson_1963_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1964_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1965_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1966_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1967_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_1968_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_1969_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_1970_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_1971_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_1972_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_1973_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_1974_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_1975_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_1976_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_1977_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_1978_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_1979_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1981_ = v_opts_936_;
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
lean_inc(v_forwardedArgs_1957_);
lean_inc(v_leanOpts_1956_);
lean_dec(v_opts_936_);
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
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_leanOpts_1956_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_forwardedArgs_1957_);
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
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 8, v_component_1958_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 9, v_printPrefix_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 10, v_printLibDir_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 11, v_useStdin_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 12, v_onlyDeps_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1986_, sizeof(void*)*13 + 14, v_depsJson_1963_);
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
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*13 + 13, v___x_1199_);
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
return v___x_1985_;
}
}
}
}
else
{
lean_object* v_leanOpts_1988_; lean_object* v_forwardedArgs_1989_; uint8_t v_component_1990_; uint8_t v_printPrefix_1991_; uint8_t v_printLibDir_1992_; uint8_t v_useStdin_1993_; uint8_t v_onlySrcDeps_1994_; uint8_t v_depsJson_1995_; lean_object* v_opts_1996_; uint32_t v_trustLevel_1997_; uint32_t v_numThreads_1998_; lean_object* v_rootDir_x3f_1999_; lean_object* v_setupFileName_x3f_2000_; lean_object* v_oleanFileName_x3f_2001_; lean_object* v_ileanFileName_x3f_2002_; lean_object* v_cFileName_x3f_2003_; lean_object* v_bcFileName_x3f_2004_; uint8_t v_jsonOutput_2005_; lean_object* v_errorOnKinds_2006_; uint8_t v_printStats_2007_; uint8_t v_run_2008_; lean_object* v_incrSaveFileName_x3f_2009_; lean_object* v_incrLoadFileName_x3f_2010_; lean_object* v_incrHeaderSaveFileName_x3f_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2019_; 
lean_dec(v_optArg_x3f_938_);
v_leanOpts_1988_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_1989_ = lean_ctor_get(v_opts_936_, 1);
v_component_1990_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_1991_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_1992_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_1993_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlySrcDeps_1994_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_1995_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_1996_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_1997_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_1998_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_1999_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_2000_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_2001_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_2002_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_2003_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_2004_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_2005_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2006_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2007_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_2008_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2009_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2010_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2011_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2013_ = v_opts_936_;
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
lean_dec(v_opts_936_);
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
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*13 + 13, v_onlySrcDeps_1994_);
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
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*13 + 12, v___x_1197_);
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_leanOpts_2020_; lean_object* v_forwardedArgs_2021_; uint8_t v_component_2022_; uint8_t v_printPrefix_2023_; uint8_t v_printLibDir_2024_; uint8_t v_useStdin_2025_; uint8_t v_onlyDeps_2026_; uint8_t v_onlySrcDeps_2027_; uint8_t v_depsJson_2028_; lean_object* v_opts_2029_; uint32_t v_trustLevel_2030_; uint32_t v_numThreads_2031_; lean_object* v_rootDir_x3f_2032_; lean_object* v_setupFileName_x3f_2033_; lean_object* v_oleanFileName_x3f_2034_; lean_object* v_ileanFileName_x3f_2035_; lean_object* v_cFileName_x3f_2036_; lean_object* v_bcFileName_x3f_2037_; uint8_t v_jsonOutput_2038_; lean_object* v_errorOnKinds_2039_; uint8_t v_printStats_2040_; uint8_t v_run_2041_; lean_object* v_incrSaveFileName_x3f_2042_; lean_object* v_incrLoadFileName_x3f_2043_; lean_object* v_incrHeaderSaveFileName_x3f_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_optArg_x3f_938_);
v_leanOpts_2020_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_2021_ = lean_ctor_get(v_opts_936_, 1);
v_component_2022_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_2023_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_2024_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_2025_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_2026_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2027_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_2028_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_2029_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_2030_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_2031_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2032_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_2033_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_2034_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_2035_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_2036_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_2037_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_2038_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2039_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2040_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_2041_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2042_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2043_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2044_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2046_ = v_opts_936_;
v_isShared_2047_ = v_isSharedCheck_2054_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2044_);
lean_inc(v_incrLoadFileName_x3f_2043_);
lean_inc(v_incrSaveFileName_x3f_2042_);
lean_inc(v_errorOnKinds_2039_);
lean_inc(v_bcFileName_x3f_2037_);
lean_inc(v_cFileName_x3f_2036_);
lean_inc(v_ileanFileName_x3f_2035_);
lean_inc(v_oleanFileName_x3f_2034_);
lean_inc(v_setupFileName_x3f_2033_);
lean_inc(v_rootDir_x3f_2032_);
lean_inc(v_opts_2029_);
lean_inc(v_forwardedArgs_2021_);
lean_inc(v_leanOpts_2020_);
lean_dec(v_opts_936_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2054_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2048_ = l___private_Lean_Shell_0__Lean_verbose;
v___x_2049_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2020_, v___x_2048_, v___x_1193_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2049_);
v___x_2051_ = v___x_2046_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_forwardedArgs_2021_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_opts_2029_);
lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_rootDir_x3f_2032_);
lean_ctor_set(v_reuseFailAlloc_2053_, 4, v_setupFileName_x3f_2033_);
lean_ctor_set(v_reuseFailAlloc_2053_, 5, v_oleanFileName_x3f_2034_);
lean_ctor_set(v_reuseFailAlloc_2053_, 6, v_ileanFileName_x3f_2035_);
lean_ctor_set(v_reuseFailAlloc_2053_, 7, v_cFileName_x3f_2036_);
lean_ctor_set(v_reuseFailAlloc_2053_, 8, v_bcFileName_x3f_2037_);
lean_ctor_set(v_reuseFailAlloc_2053_, 9, v_errorOnKinds_2039_);
lean_ctor_set(v_reuseFailAlloc_2053_, 10, v_incrSaveFileName_x3f_2042_);
lean_ctor_set(v_reuseFailAlloc_2053_, 11, v_incrLoadFileName_x3f_2043_);
lean_ctor_set(v_reuseFailAlloc_2053_, 12, v_incrHeaderSaveFileName_x3f_2044_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*13 + 8, v_component_2022_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*13 + 9, v_printPrefix_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*13 + 10, v_printLibDir_2024_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*13 + 11, v_useStdin_2025_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*13 + 12, v_onlyDeps_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*13 + 13, v_onlySrcDeps_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*13 + 14, v_depsJson_2028_);
lean_ctor_set_uint32(v_reuseFailAlloc_2053_, sizeof(void*)*13, v_trustLevel_2030_);
lean_ctor_set_uint32(v_reuseFailAlloc_2053_, sizeof(void*)*13 + 4, v_numThreads_2031_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*13 + 15, v_jsonOutput_2038_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*13 + 16, v_printStats_2040_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*13 + 17, v_run_2041_);
v___x_2051_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
return v___x_2052_;
}
}
}
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
v___x_2056_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2055_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2110_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2110_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2110_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = lean_string_utf8_byte_size(v_a_2057_);
lean_inc(v_a_2057_);
v___x_2063_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2063_, 0, v_a_2057_);
lean_ctor_set(v___x_2063_, 1, v___x_2061_);
lean_ctor_set(v___x_2063_, 2, v___x_2062_);
v___x_2064_ = l_String_Slice_toNat_x3f(v___x_2063_);
lean_dec_ref_known(v___x_2063_, 3);
if (lean_obj_tag(v___x_2064_) == 1)
{
lean_object* v_val_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v_val_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_val_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v___x_2066_ = lean_cstr_to_nat("4294967296");
v___x_2067_ = lean_nat_dec_lt(v_val_2065_, v___x_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec(v_val_2065_);
lean_del_object(v___x_2059_);
lean_dec(v_a_2057_);
lean_dec_ref(v_opts_936_);
v___x_2068_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
v___x_2069_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2068_);
lean_dec_ref(v___x_2069_);
goto v___jp_1000_;
}
else
{
lean_object* v_leanOpts_2070_; lean_object* v_forwardedArgs_2071_; uint8_t v_component_2072_; uint8_t v_printPrefix_2073_; uint8_t v_printLibDir_2074_; uint8_t v_useStdin_2075_; uint8_t v_onlyDeps_2076_; uint8_t v_onlySrcDeps_2077_; uint8_t v_depsJson_2078_; lean_object* v_opts_2079_; uint32_t v_numThreads_2080_; lean_object* v_rootDir_x3f_2081_; lean_object* v_setupFileName_x3f_2082_; lean_object* v_oleanFileName_x3f_2083_; lean_object* v_ileanFileName_x3f_2084_; lean_object* v_cFileName_x3f_2085_; lean_object* v_bcFileName_x3f_2086_; uint8_t v_jsonOutput_2087_; lean_object* v_errorOnKinds_2088_; uint8_t v_printStats_2089_; uint8_t v_run_2090_; lean_object* v_incrSaveFileName_x3f_2091_; lean_object* v_incrLoadFileName_x3f_2092_; lean_object* v_incrHeaderSaveFileName_x3f_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2107_; 
v_leanOpts_2070_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_2071_ = lean_ctor_get(v_opts_936_, 1);
v_component_2072_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_2073_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_2074_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_2075_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_2076_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2077_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_2078_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_2079_ = lean_ctor_get(v_opts_936_, 2);
v_numThreads_2080_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2081_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_2082_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_2083_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_2084_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_2085_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_2086_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_2087_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2088_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2089_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_2090_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2091_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2092_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2093_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2095_ = v_opts_936_;
v_isShared_2096_ = v_isSharedCheck_2107_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2093_);
lean_inc(v_incrLoadFileName_x3f_2092_);
lean_inc(v_incrSaveFileName_x3f_2091_);
lean_inc(v_errorOnKinds_2088_);
lean_inc(v_bcFileName_x3f_2086_);
lean_inc(v_cFileName_x3f_2085_);
lean_inc(v_ileanFileName_x3f_2084_);
lean_inc(v_oleanFileName_x3f_2083_);
lean_inc(v_setupFileName_x3f_2082_);
lean_inc(v_rootDir_x3f_2081_);
lean_inc(v_opts_2079_);
lean_inc(v_forwardedArgs_2071_);
lean_inc(v_leanOpts_2070_);
lean_dec(v_opts_936_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2107_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
uint32_t v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2097_ = lean_uint32_of_nat(v_val_2065_);
lean_dec(v_val_2065_);
v___x_2098_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
v___x_2099_ = lean_string_append(v___x_2098_, v_a_2057_);
lean_dec(v_a_2057_);
v___x_2100_ = lean_array_push(v_forwardedArgs_2071_, v___x_2099_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 1, v___x_2100_);
v___x_2102_ = v___x_2095_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_leanOpts_2070_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2106_, 2, v_opts_2079_);
lean_ctor_set(v_reuseFailAlloc_2106_, 3, v_rootDir_x3f_2081_);
lean_ctor_set(v_reuseFailAlloc_2106_, 4, v_setupFileName_x3f_2082_);
lean_ctor_set(v_reuseFailAlloc_2106_, 5, v_oleanFileName_x3f_2083_);
lean_ctor_set(v_reuseFailAlloc_2106_, 6, v_ileanFileName_x3f_2084_);
lean_ctor_set(v_reuseFailAlloc_2106_, 7, v_cFileName_x3f_2085_);
lean_ctor_set(v_reuseFailAlloc_2106_, 8, v_bcFileName_x3f_2086_);
lean_ctor_set(v_reuseFailAlloc_2106_, 9, v_errorOnKinds_2088_);
lean_ctor_set(v_reuseFailAlloc_2106_, 10, v_incrSaveFileName_x3f_2091_);
lean_ctor_set(v_reuseFailAlloc_2106_, 11, v_incrLoadFileName_x3f_2092_);
lean_ctor_set(v_reuseFailAlloc_2106_, 12, v_incrHeaderSaveFileName_x3f_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*13 + 8, v_component_2072_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*13 + 9, v_printPrefix_2073_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*13 + 10, v_printLibDir_2074_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*13 + 11, v_useStdin_2075_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*13 + 12, v_onlyDeps_2076_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*13 + 13, v_onlySrcDeps_2077_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*13 + 14, v_depsJson_2078_);
lean_ctor_set_uint32(v_reuseFailAlloc_2106_, sizeof(void*)*13 + 4, v_numThreads_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*13 + 15, v_jsonOutput_2087_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*13 + 16, v_printStats_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*13 + 17, v_run_2090_);
v___x_2102_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2104_; 
lean_ctor_set_uint32(v___x_2102_, sizeof(void*)*13, v___x_2097_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2102_);
v___x_2104_ = v___x_2059_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_dec(v___x_2064_);
lean_del_object(v___x_2059_);
lean_dec(v_a_2057_);
lean_dec_ref(v_opts_936_);
v___x_2108_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
v___x_2109_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2108_);
lean_dec_ref(v___x_2109_);
goto v___jp_997_;
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec_ref(v_opts_936_);
v_a_2111_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2056_, 1);
v___x_2115_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2116_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2115_);
lean_dec_ref(v___x_2116_);
goto v___jp_2112_;
v___jp_2112_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_io_error_to_string(v_a_2111_);
v___x_2114_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2113_);
lean_dec_ref(v___x_2114_);
goto v___jp_1006_;
}
}
}
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
v___x_2118_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2117_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2170_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2170_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2170_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2123_ = lean_unsigned_to_nat(0u);
v___x_2124_ = lean_string_utf8_byte_size(v_a_2119_);
lean_inc(v_a_2119_);
v___x_2125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2125_, 0, v_a_2119_);
lean_ctor_set(v___x_2125_, 1, v___x_2123_);
lean_ctor_set(v___x_2125_, 2, v___x_2124_);
v___x_2126_ = l_String_Slice_toNat_x3f(v___x_2125_);
lean_dec_ref_known(v___x_2125_, 3);
if (lean_obj_tag(v___x_2126_) == 1)
{
lean_object* v_val_2127_; lean_object* v_leanOpts_2128_; lean_object* v_forwardedArgs_2129_; uint8_t v_component_2130_; uint8_t v_printPrefix_2131_; uint8_t v_printLibDir_2132_; uint8_t v_useStdin_2133_; uint8_t v_onlyDeps_2134_; uint8_t v_onlySrcDeps_2135_; uint8_t v_depsJson_2136_; lean_object* v_opts_2137_; uint32_t v_trustLevel_2138_; uint32_t v_numThreads_2139_; lean_object* v_rootDir_x3f_2140_; lean_object* v_setupFileName_x3f_2141_; lean_object* v_oleanFileName_x3f_2142_; lean_object* v_ileanFileName_x3f_2143_; lean_object* v_cFileName_x3f_2144_; lean_object* v_bcFileName_x3f_2145_; uint8_t v_jsonOutput_2146_; lean_object* v_errorOnKinds_2147_; uint8_t v_printStats_2148_; uint8_t v_run_2149_; lean_object* v_incrSaveFileName_x3f_2150_; lean_object* v_incrLoadFileName_x3f_2151_; lean_object* v_incrHeaderSaveFileName_x3f_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2167_; 
v_val_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_val_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v_leanOpts_2128_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_2129_ = lean_ctor_get(v_opts_936_, 1);
v_component_2130_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_2131_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_2132_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_2133_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_2134_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2135_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_2136_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_2137_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_2138_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_2139_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2140_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_2141_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_2142_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_2143_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_2144_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_2145_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_2146_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2147_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2148_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_2149_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2150_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2151_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2152_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2154_ = v_opts_936_;
v_isShared_2155_ = v_isSharedCheck_2167_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2152_);
lean_inc(v_incrLoadFileName_x3f_2151_);
lean_inc(v_incrSaveFileName_x3f_2150_);
lean_inc(v_errorOnKinds_2147_);
lean_inc(v_bcFileName_x3f_2145_);
lean_inc(v_cFileName_x3f_2144_);
lean_inc(v_ileanFileName_x3f_2143_);
lean_inc(v_oleanFileName_x3f_2142_);
lean_inc(v_setupFileName_x3f_2141_);
lean_inc(v_rootDir_x3f_2140_);
lean_inc(v_opts_2137_);
lean_inc(v_forwardedArgs_2129_);
lean_inc(v_leanOpts_2128_);
lean_dec(v_opts_936_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2167_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2156_ = l___private_Lean_Shell_0__Lean_timeout;
v___x_2157_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2128_, v___x_2156_, v_val_2127_);
v___x_2158_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
v___x_2159_ = lean_string_append(v___x_2158_, v_a_2119_);
lean_dec(v_a_2119_);
v___x_2160_ = lean_array_push(v_forwardedArgs_2129_, v___x_2159_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v___x_2160_);
lean_ctor_set(v___x_2154_, 0, v___x_2157_);
v___x_2162_ = v___x_2154_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2166_, 2, v_opts_2137_);
lean_ctor_set(v_reuseFailAlloc_2166_, 3, v_rootDir_x3f_2140_);
lean_ctor_set(v_reuseFailAlloc_2166_, 4, v_setupFileName_x3f_2141_);
lean_ctor_set(v_reuseFailAlloc_2166_, 5, v_oleanFileName_x3f_2142_);
lean_ctor_set(v_reuseFailAlloc_2166_, 6, v_ileanFileName_x3f_2143_);
lean_ctor_set(v_reuseFailAlloc_2166_, 7, v_cFileName_x3f_2144_);
lean_ctor_set(v_reuseFailAlloc_2166_, 8, v_bcFileName_x3f_2145_);
lean_ctor_set(v_reuseFailAlloc_2166_, 9, v_errorOnKinds_2147_);
lean_ctor_set(v_reuseFailAlloc_2166_, 10, v_incrSaveFileName_x3f_2150_);
lean_ctor_set(v_reuseFailAlloc_2166_, 11, v_incrLoadFileName_x3f_2151_);
lean_ctor_set(v_reuseFailAlloc_2166_, 12, v_incrHeaderSaveFileName_x3f_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2166_, sizeof(void*)*13 + 8, v_component_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2166_, sizeof(void*)*13 + 9, v_printPrefix_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2166_, sizeof(void*)*13 + 10, v_printLibDir_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2166_, sizeof(void*)*13 + 11, v_useStdin_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2166_, sizeof(void*)*13 + 12, v_onlyDeps_2134_);
lean_ctor_set_uint8(v_reuseFailAlloc_2166_, sizeof(void*)*13 + 13, v_onlySrcDeps_2135_);
lean_ctor_set_uint8(v_reuseFailAlloc_2166_, sizeof(void*)*13 + 14, v_depsJson_2136_);
lean_ctor_set_uint32(v_reuseFailAlloc_2166_, sizeof(void*)*13, v_trustLevel_2138_);
lean_ctor_set_uint32(v_reuseFailAlloc_2166_, sizeof(void*)*13 + 4, v_numThreads_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2166_, sizeof(void*)*13 + 15, v_jsonOutput_2146_);
lean_ctor_set_uint8(v_reuseFailAlloc_2166_, sizeof(void*)*13 + 16, v_printStats_2148_);
lean_ctor_set_uint8(v_reuseFailAlloc_2166_, sizeof(void*)*13 + 17, v_run_2149_);
v___x_2162_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2164_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2162_);
v___x_2164_ = v___x_2121_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_dec(v___x_2126_);
lean_del_object(v___x_2121_);
lean_dec(v_a_2119_);
lean_dec_ref(v_opts_936_);
v___x_2168_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
v___x_2169_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2168_);
lean_dec_ref(v___x_2169_);
goto v___jp_1113_;
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec_ref(v_opts_936_);
v_a_2171_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2118_, 1);
v___x_2175_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2176_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2175_);
lean_dec_ref(v___x_2176_);
goto v___jp_2172_;
v___jp_2172_:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_io_error_to_string(v_a_2171_);
v___x_2174_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2173_);
lean_dec_ref(v___x_2174_);
goto v___jp_1119_;
}
}
}
}
else
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
v___x_2178_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2177_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2230_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2230_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2230_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2183_ = lean_unsigned_to_nat(0u);
v___x_2184_ = lean_string_utf8_byte_size(v_a_2179_);
lean_inc(v_a_2179_);
v___x_2185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2185_, 0, v_a_2179_);
lean_ctor_set(v___x_2185_, 1, v___x_2183_);
lean_ctor_set(v___x_2185_, 2, v___x_2184_);
v___x_2186_ = l_String_Slice_toNat_x3f(v___x_2185_);
lean_dec_ref_known(v___x_2185_, 3);
if (lean_obj_tag(v___x_2186_) == 1)
{
lean_object* v_val_2187_; lean_object* v_leanOpts_2188_; lean_object* v_forwardedArgs_2189_; uint8_t v_component_2190_; uint8_t v_printPrefix_2191_; uint8_t v_printLibDir_2192_; uint8_t v_useStdin_2193_; uint8_t v_onlyDeps_2194_; uint8_t v_onlySrcDeps_2195_; uint8_t v_depsJson_2196_; lean_object* v_opts_2197_; uint32_t v_trustLevel_2198_; uint32_t v_numThreads_2199_; lean_object* v_rootDir_x3f_2200_; lean_object* v_setupFileName_x3f_2201_; lean_object* v_oleanFileName_x3f_2202_; lean_object* v_ileanFileName_x3f_2203_; lean_object* v_cFileName_x3f_2204_; lean_object* v_bcFileName_x3f_2205_; uint8_t v_jsonOutput_2206_; lean_object* v_errorOnKinds_2207_; uint8_t v_printStats_2208_; uint8_t v_run_2209_; lean_object* v_incrSaveFileName_x3f_2210_; lean_object* v_incrLoadFileName_x3f_2211_; lean_object* v_incrHeaderSaveFileName_x3f_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2227_; 
v_val_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_val_2187_);
lean_dec_ref_known(v___x_2186_, 1);
v_leanOpts_2188_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_2189_ = lean_ctor_get(v_opts_936_, 1);
v_component_2190_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_2191_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_2192_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_2193_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_2194_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2195_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_2196_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_2197_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_2198_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_2199_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2200_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_2201_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_2202_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_2203_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_2204_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_2205_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_2206_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2207_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2208_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_2209_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2210_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2211_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2212_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2214_ = v_opts_936_;
v_isShared_2215_ = v_isSharedCheck_2227_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2212_);
lean_inc(v_incrLoadFileName_x3f_2211_);
lean_inc(v_incrSaveFileName_x3f_2210_);
lean_inc(v_errorOnKinds_2207_);
lean_inc(v_bcFileName_x3f_2205_);
lean_inc(v_cFileName_x3f_2204_);
lean_inc(v_ileanFileName_x3f_2203_);
lean_inc(v_oleanFileName_x3f_2202_);
lean_inc(v_setupFileName_x3f_2201_);
lean_inc(v_rootDir_x3f_2200_);
lean_inc(v_opts_2197_);
lean_inc(v_forwardedArgs_2189_);
lean_inc(v_leanOpts_2188_);
lean_dec(v_opts_936_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2227_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2216_ = l___private_Lean_Shell_0__Lean_maxMemory;
v___x_2217_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(v_leanOpts_2188_, v___x_2216_, v_val_2187_);
v___x_2218_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
v___x_2219_ = lean_string_append(v___x_2218_, v_a_2179_);
lean_dec(v_a_2179_);
v___x_2220_ = lean_array_push(v_forwardedArgs_2189_, v___x_2219_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___x_2220_);
lean_ctor_set(v___x_2214_, 0, v___x_2217_);
v___x_2222_ = v___x_2214_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_opts_2197_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_rootDir_x3f_2200_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_setupFileName_x3f_2201_);
lean_ctor_set(v_reuseFailAlloc_2226_, 5, v_oleanFileName_x3f_2202_);
lean_ctor_set(v_reuseFailAlloc_2226_, 6, v_ileanFileName_x3f_2203_);
lean_ctor_set(v_reuseFailAlloc_2226_, 7, v_cFileName_x3f_2204_);
lean_ctor_set(v_reuseFailAlloc_2226_, 8, v_bcFileName_x3f_2205_);
lean_ctor_set(v_reuseFailAlloc_2226_, 9, v_errorOnKinds_2207_);
lean_ctor_set(v_reuseFailAlloc_2226_, 10, v_incrSaveFileName_x3f_2210_);
lean_ctor_set(v_reuseFailAlloc_2226_, 11, v_incrLoadFileName_x3f_2211_);
lean_ctor_set(v_reuseFailAlloc_2226_, 12, v_incrHeaderSaveFileName_x3f_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*13 + 8, v_component_2190_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*13 + 9, v_printPrefix_2191_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*13 + 10, v_printLibDir_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*13 + 11, v_useStdin_2193_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*13 + 12, v_onlyDeps_2194_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*13 + 13, v_onlySrcDeps_2195_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*13 + 14, v_depsJson_2196_);
lean_ctor_set_uint32(v_reuseFailAlloc_2226_, sizeof(void*)*13, v_trustLevel_2198_);
lean_ctor_set_uint32(v_reuseFailAlloc_2226_, sizeof(void*)*13 + 4, v_numThreads_2199_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*13 + 15, v_jsonOutput_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*13 + 16, v_printStats_2208_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*13 + 17, v_run_2209_);
v___x_2222_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2224_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2222_);
v___x_2224_ = v___x_2181_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec(v___x_2186_);
lean_del_object(v___x_2181_);
lean_dec(v_a_2179_);
lean_dec_ref(v_opts_936_);
v___x_2228_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
v___x_2229_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2228_);
lean_dec_ref(v___x_2229_);
goto v___jp_988_;
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_dec_ref(v_opts_936_);
v_a_2231_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2235_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2236_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2235_);
lean_dec_ref(v___x_2236_);
goto v___jp_2232_;
v___jp_2232_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_io_error_to_string(v_a_2231_);
v___x_2234_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2233_);
lean_dec_ref(v___x_2234_);
goto v___jp_994_;
}
}
}
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
v___x_2238_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2237_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2282_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2282_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2282_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v_leanOpts_2243_; lean_object* v_forwardedArgs_2244_; uint8_t v_component_2245_; uint8_t v_printPrefix_2246_; uint8_t v_printLibDir_2247_; uint8_t v_useStdin_2248_; uint8_t v_onlyDeps_2249_; uint8_t v_onlySrcDeps_2250_; uint8_t v_depsJson_2251_; lean_object* v_opts_2252_; uint32_t v_trustLevel_2253_; uint32_t v_numThreads_2254_; lean_object* v_setupFileName_x3f_2255_; lean_object* v_oleanFileName_x3f_2256_; lean_object* v_ileanFileName_x3f_2257_; lean_object* v_cFileName_x3f_2258_; lean_object* v_bcFileName_x3f_2259_; uint8_t v_jsonOutput_2260_; lean_object* v_errorOnKinds_2261_; uint8_t v_printStats_2262_; uint8_t v_run_2263_; lean_object* v_incrSaveFileName_x3f_2264_; lean_object* v_incrLoadFileName_x3f_2265_; lean_object* v_incrHeaderSaveFileName_x3f_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2280_; 
v_leanOpts_2243_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_2244_ = lean_ctor_get(v_opts_936_, 1);
v_component_2245_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_2246_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_2247_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_2248_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_2249_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2250_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_2251_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_2252_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_2253_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_2254_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_setupFileName_x3f_2255_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_2256_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_2257_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_2258_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_2259_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_2260_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2261_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2262_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_2263_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2264_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2265_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2266_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2280_ == 0)
{
lean_object* v_unused_2281_; 
v_unused_2281_ = lean_ctor_get(v_opts_936_, 3);
lean_dec(v_unused_2281_);
v___x_2268_ = v_opts_936_;
v_isShared_2269_ = v_isSharedCheck_2280_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2266_);
lean_inc(v_incrLoadFileName_x3f_2265_);
lean_inc(v_incrSaveFileName_x3f_2264_);
lean_inc(v_errorOnKinds_2261_);
lean_inc(v_bcFileName_x3f_2259_);
lean_inc(v_cFileName_x3f_2258_);
lean_inc(v_ileanFileName_x3f_2257_);
lean_inc(v_oleanFileName_x3f_2256_);
lean_inc(v_setupFileName_x3f_2255_);
lean_inc(v_opts_2252_);
lean_inc(v_forwardedArgs_2244_);
lean_inc(v_leanOpts_2243_);
lean_dec(v_opts_936_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2280_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2275_; 
v___x_2270_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
v___x_2271_ = lean_string_append(v___x_2270_, v_a_2239_);
v___x_2272_ = lean_array_push(v_forwardedArgs_2244_, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2273_, 0, v_a_2239_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 3, v___x_2273_);
lean_ctor_set(v___x_2268_, 1, v___x_2272_);
v___x_2275_ = v___x_2268_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_leanOpts_2243_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_opts_2252_);
lean_ctor_set(v_reuseFailAlloc_2279_, 3, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2279_, 4, v_setupFileName_x3f_2255_);
lean_ctor_set(v_reuseFailAlloc_2279_, 5, v_oleanFileName_x3f_2256_);
lean_ctor_set(v_reuseFailAlloc_2279_, 6, v_ileanFileName_x3f_2257_);
lean_ctor_set(v_reuseFailAlloc_2279_, 7, v_cFileName_x3f_2258_);
lean_ctor_set(v_reuseFailAlloc_2279_, 8, v_bcFileName_x3f_2259_);
lean_ctor_set(v_reuseFailAlloc_2279_, 9, v_errorOnKinds_2261_);
lean_ctor_set(v_reuseFailAlloc_2279_, 10, v_incrSaveFileName_x3f_2264_);
lean_ctor_set(v_reuseFailAlloc_2279_, 11, v_incrLoadFileName_x3f_2265_);
lean_ctor_set(v_reuseFailAlloc_2279_, 12, v_incrHeaderSaveFileName_x3f_2266_);
lean_ctor_set_uint8(v_reuseFailAlloc_2279_, sizeof(void*)*13 + 8, v_component_2245_);
lean_ctor_set_uint8(v_reuseFailAlloc_2279_, sizeof(void*)*13 + 9, v_printPrefix_2246_);
lean_ctor_set_uint8(v_reuseFailAlloc_2279_, sizeof(void*)*13 + 10, v_printLibDir_2247_);
lean_ctor_set_uint8(v_reuseFailAlloc_2279_, sizeof(void*)*13 + 11, v_useStdin_2248_);
lean_ctor_set_uint8(v_reuseFailAlloc_2279_, sizeof(void*)*13 + 12, v_onlyDeps_2249_);
lean_ctor_set_uint8(v_reuseFailAlloc_2279_, sizeof(void*)*13 + 13, v_onlySrcDeps_2250_);
lean_ctor_set_uint8(v_reuseFailAlloc_2279_, sizeof(void*)*13 + 14, v_depsJson_2251_);
lean_ctor_set_uint32(v_reuseFailAlloc_2279_, sizeof(void*)*13, v_trustLevel_2253_);
lean_ctor_set_uint32(v_reuseFailAlloc_2279_, sizeof(void*)*13 + 4, v_numThreads_2254_);
lean_ctor_set_uint8(v_reuseFailAlloc_2279_, sizeof(void*)*13 + 15, v_jsonOutput_2260_);
lean_ctor_set_uint8(v_reuseFailAlloc_2279_, sizeof(void*)*13 + 16, v_printStats_2262_);
lean_ctor_set_uint8(v_reuseFailAlloc_2279_, sizeof(void*)*13 + 17, v_run_2263_);
v___x_2275_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
lean_object* v___x_2277_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2275_);
v___x_2277_ = v___x_2241_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
lean_dec_ref(v_opts_936_);
v_a_2283_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2238_, 1);
v___x_2287_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2288_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2287_);
lean_dec_ref(v___x_2288_);
goto v___jp_2284_;
v___jp_2284_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_io_error_to_string(v_a_2283_);
v___x_2286_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2285_);
lean_dec_ref(v___x_2286_);
goto v___jp_1125_;
}
}
}
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25));
v___x_2290_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2289_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2331_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2293_ = v___x_2290_;
v_isShared_2294_ = v_isSharedCheck_2331_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2331_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v_leanOpts_2295_; lean_object* v_forwardedArgs_2296_; uint8_t v_component_2297_; uint8_t v_printPrefix_2298_; uint8_t v_printLibDir_2299_; uint8_t v_useStdin_2300_; uint8_t v_onlyDeps_2301_; uint8_t v_onlySrcDeps_2302_; uint8_t v_depsJson_2303_; lean_object* v_opts_2304_; uint32_t v_trustLevel_2305_; uint32_t v_numThreads_2306_; lean_object* v_rootDir_x3f_2307_; lean_object* v_setupFileName_x3f_2308_; lean_object* v_oleanFileName_x3f_2309_; lean_object* v_cFileName_x3f_2310_; lean_object* v_bcFileName_x3f_2311_; uint8_t v_jsonOutput_2312_; lean_object* v_errorOnKinds_2313_; uint8_t v_printStats_2314_; uint8_t v_run_2315_; lean_object* v_incrSaveFileName_x3f_2316_; lean_object* v_incrLoadFileName_x3f_2317_; lean_object* v_incrHeaderSaveFileName_x3f_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2329_; 
v_leanOpts_2295_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_2296_ = lean_ctor_get(v_opts_936_, 1);
v_component_2297_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_2298_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_2299_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_2300_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_2301_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2302_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_2303_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_2304_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_2305_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_2306_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2307_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_2308_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_2309_ = lean_ctor_get(v_opts_936_, 5);
v_cFileName_x3f_2310_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_2311_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_2312_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2313_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2314_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_2315_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2316_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2317_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2318_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v_opts_936_, 6);
lean_dec(v_unused_2330_);
v___x_2320_ = v_opts_936_;
v_isShared_2321_ = v_isSharedCheck_2329_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2318_);
lean_inc(v_incrLoadFileName_x3f_2317_);
lean_inc(v_incrSaveFileName_x3f_2316_);
lean_inc(v_errorOnKinds_2313_);
lean_inc(v_bcFileName_x3f_2311_);
lean_inc(v_cFileName_x3f_2310_);
lean_inc(v_oleanFileName_x3f_2309_);
lean_inc(v_setupFileName_x3f_2308_);
lean_inc(v_rootDir_x3f_2307_);
lean_inc(v_opts_2304_);
lean_inc(v_forwardedArgs_2296_);
lean_inc(v_leanOpts_2295_);
lean_dec(v_opts_936_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2329_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2324_; 
v___x_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2322_, 0, v_a_2291_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 6, v___x_2322_);
v___x_2324_ = v___x_2320_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_leanOpts_2295_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_forwardedArgs_2296_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_opts_2304_);
lean_ctor_set(v_reuseFailAlloc_2328_, 3, v_rootDir_x3f_2307_);
lean_ctor_set(v_reuseFailAlloc_2328_, 4, v_setupFileName_x3f_2308_);
lean_ctor_set(v_reuseFailAlloc_2328_, 5, v_oleanFileName_x3f_2309_);
lean_ctor_set(v_reuseFailAlloc_2328_, 6, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2328_, 7, v_cFileName_x3f_2310_);
lean_ctor_set(v_reuseFailAlloc_2328_, 8, v_bcFileName_x3f_2311_);
lean_ctor_set(v_reuseFailAlloc_2328_, 9, v_errorOnKinds_2313_);
lean_ctor_set(v_reuseFailAlloc_2328_, 10, v_incrSaveFileName_x3f_2316_);
lean_ctor_set(v_reuseFailAlloc_2328_, 11, v_incrLoadFileName_x3f_2317_);
lean_ctor_set(v_reuseFailAlloc_2328_, 12, v_incrHeaderSaveFileName_x3f_2318_);
lean_ctor_set_uint8(v_reuseFailAlloc_2328_, sizeof(void*)*13 + 8, v_component_2297_);
lean_ctor_set_uint8(v_reuseFailAlloc_2328_, sizeof(void*)*13 + 9, v_printPrefix_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2328_, sizeof(void*)*13 + 10, v_printLibDir_2299_);
lean_ctor_set_uint8(v_reuseFailAlloc_2328_, sizeof(void*)*13 + 11, v_useStdin_2300_);
lean_ctor_set_uint8(v_reuseFailAlloc_2328_, sizeof(void*)*13 + 12, v_onlyDeps_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2328_, sizeof(void*)*13 + 13, v_onlySrcDeps_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2328_, sizeof(void*)*13 + 14, v_depsJson_2303_);
lean_ctor_set_uint32(v_reuseFailAlloc_2328_, sizeof(void*)*13, v_trustLevel_2305_);
lean_ctor_set_uint32(v_reuseFailAlloc_2328_, sizeof(void*)*13 + 4, v_numThreads_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2328_, sizeof(void*)*13 + 15, v_jsonOutput_2312_);
lean_ctor_set_uint8(v_reuseFailAlloc_2328_, sizeof(void*)*13 + 16, v_printStats_2314_);
lean_ctor_set_uint8(v_reuseFailAlloc_2328_, sizeof(void*)*13 + 17, v_run_2315_);
v___x_2324_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2326_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2324_);
v___x_2326_ = v___x_2293_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec_ref(v_opts_936_);
v_a_2332_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2336_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2337_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2336_);
lean_dec_ref(v___x_2337_);
goto v___jp_2333_;
v___jp_2333_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_io_error_to_string(v_a_2332_);
v___x_2335_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2334_);
lean_dec_ref(v___x_2335_);
goto v___jp_985_;
}
}
}
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
v___x_2339_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2338_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2380_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2380_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2380_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v_leanOpts_2344_; lean_object* v_forwardedArgs_2345_; uint8_t v_component_2346_; uint8_t v_printPrefix_2347_; uint8_t v_printLibDir_2348_; uint8_t v_useStdin_2349_; uint8_t v_onlyDeps_2350_; uint8_t v_onlySrcDeps_2351_; uint8_t v_depsJson_2352_; lean_object* v_opts_2353_; uint32_t v_trustLevel_2354_; uint32_t v_numThreads_2355_; lean_object* v_rootDir_x3f_2356_; lean_object* v_setupFileName_x3f_2357_; lean_object* v_ileanFileName_x3f_2358_; lean_object* v_cFileName_x3f_2359_; lean_object* v_bcFileName_x3f_2360_; uint8_t v_jsonOutput_2361_; lean_object* v_errorOnKinds_2362_; uint8_t v_printStats_2363_; uint8_t v_run_2364_; lean_object* v_incrSaveFileName_x3f_2365_; lean_object* v_incrLoadFileName_x3f_2366_; lean_object* v_incrHeaderSaveFileName_x3f_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2378_; 
v_leanOpts_2344_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_2345_ = lean_ctor_get(v_opts_936_, 1);
v_component_2346_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_2347_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_2348_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_2349_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_2350_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2351_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_2352_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_2353_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_2354_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_2355_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2356_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_2357_ = lean_ctor_get(v_opts_936_, 4);
v_ileanFileName_x3f_2358_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_2359_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_2360_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_2361_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2362_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2363_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_2364_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2365_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2366_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2367_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; 
v_unused_2379_ = lean_ctor_get(v_opts_936_, 5);
lean_dec(v_unused_2379_);
v___x_2369_ = v_opts_936_;
v_isShared_2370_ = v_isSharedCheck_2378_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2367_);
lean_inc(v_incrLoadFileName_x3f_2366_);
lean_inc(v_incrSaveFileName_x3f_2365_);
lean_inc(v_errorOnKinds_2362_);
lean_inc(v_bcFileName_x3f_2360_);
lean_inc(v_cFileName_x3f_2359_);
lean_inc(v_ileanFileName_x3f_2358_);
lean_inc(v_setupFileName_x3f_2357_);
lean_inc(v_rootDir_x3f_2356_);
lean_inc(v_opts_2353_);
lean_inc(v_forwardedArgs_2345_);
lean_inc(v_leanOpts_2344_);
lean_dec(v_opts_936_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2378_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2371_, 0, v_a_2340_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 5, v___x_2371_);
v___x_2373_ = v___x_2369_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_leanOpts_2344_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_forwardedArgs_2345_);
lean_ctor_set(v_reuseFailAlloc_2377_, 2, v_opts_2353_);
lean_ctor_set(v_reuseFailAlloc_2377_, 3, v_rootDir_x3f_2356_);
lean_ctor_set(v_reuseFailAlloc_2377_, 4, v_setupFileName_x3f_2357_);
lean_ctor_set(v_reuseFailAlloc_2377_, 5, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2377_, 6, v_ileanFileName_x3f_2358_);
lean_ctor_set(v_reuseFailAlloc_2377_, 7, v_cFileName_x3f_2359_);
lean_ctor_set(v_reuseFailAlloc_2377_, 8, v_bcFileName_x3f_2360_);
lean_ctor_set(v_reuseFailAlloc_2377_, 9, v_errorOnKinds_2362_);
lean_ctor_set(v_reuseFailAlloc_2377_, 10, v_incrSaveFileName_x3f_2365_);
lean_ctor_set(v_reuseFailAlloc_2377_, 11, v_incrLoadFileName_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2377_, 12, v_incrHeaderSaveFileName_x3f_2367_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 8, v_component_2346_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 9, v_printPrefix_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 10, v_printLibDir_2348_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 11, v_useStdin_2349_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 12, v_onlyDeps_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 13, v_onlySrcDeps_2351_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 14, v_depsJson_2352_);
lean_ctor_set_uint32(v_reuseFailAlloc_2377_, sizeof(void*)*13, v_trustLevel_2354_);
lean_ctor_set_uint32(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 4, v_numThreads_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 15, v_jsonOutput_2361_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 16, v_printStats_2363_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 17, v_run_2364_);
v___x_2373_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2375_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2373_);
v___x_2375_ = v___x_2342_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec_ref(v_opts_936_);
v_a_2381_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2385_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2386_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2385_);
lean_dec_ref(v___x_2386_);
goto v___jp_2382_;
v___jp_2382_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = lean_io_error_to_string(v_a_2381_);
v___x_2384_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2383_);
lean_dec_ref(v___x_2384_);
goto v___jp_1131_;
}
}
}
}
else
{
lean_object* v_leanOpts_2387_; lean_object* v_forwardedArgs_2388_; uint8_t v_component_2389_; uint8_t v_printPrefix_2390_; uint8_t v_printLibDir_2391_; uint8_t v_useStdin_2392_; uint8_t v_onlyDeps_2393_; uint8_t v_onlySrcDeps_2394_; uint8_t v_depsJson_2395_; lean_object* v_opts_2396_; uint32_t v_trustLevel_2397_; uint32_t v_numThreads_2398_; lean_object* v_rootDir_x3f_2399_; lean_object* v_setupFileName_x3f_2400_; lean_object* v_oleanFileName_x3f_2401_; lean_object* v_ileanFileName_x3f_2402_; lean_object* v_cFileName_x3f_2403_; lean_object* v_bcFileName_x3f_2404_; uint8_t v_jsonOutput_2405_; lean_object* v_errorOnKinds_2406_; uint8_t v_printStats_2407_; lean_object* v_incrSaveFileName_x3f_2408_; lean_object* v_incrLoadFileName_x3f_2409_; lean_object* v_incrHeaderSaveFileName_x3f_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2420_; 
lean_dec(v_optArg_x3f_938_);
v_leanOpts_2387_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_2388_ = lean_ctor_get(v_opts_936_, 1);
v_component_2389_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_2390_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_2391_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_2392_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_2393_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2394_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_2395_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_2396_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_2397_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_2398_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2399_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_2400_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_2401_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_2402_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_2403_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_2404_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_2405_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2406_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2407_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_incrSaveFileName_x3f_2408_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2409_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2410_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2412_ = v_opts_936_;
v_isShared_2413_ = v_isSharedCheck_2420_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2410_);
lean_inc(v_incrLoadFileName_x3f_2409_);
lean_inc(v_incrSaveFileName_x3f_2408_);
lean_inc(v_errorOnKinds_2406_);
lean_inc(v_bcFileName_x3f_2404_);
lean_inc(v_cFileName_x3f_2403_);
lean_inc(v_ileanFileName_x3f_2402_);
lean_inc(v_oleanFileName_x3f_2401_);
lean_inc(v_setupFileName_x3f_2400_);
lean_inc(v_rootDir_x3f_2399_);
lean_inc(v_opts_2396_);
lean_inc(v_forwardedArgs_2388_);
lean_inc(v_leanOpts_2387_);
lean_dec(v_opts_936_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2420_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2414_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2415_ = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(v_leanOpts_2387_, v___x_2414_, v___x_1179_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2415_);
v___x_2417_ = v___x_2412_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_forwardedArgs_2388_);
lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_opts_2396_);
lean_ctor_set(v_reuseFailAlloc_2419_, 3, v_rootDir_x3f_2399_);
lean_ctor_set(v_reuseFailAlloc_2419_, 4, v_setupFileName_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2419_, 5, v_oleanFileName_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2419_, 6, v_ileanFileName_x3f_2402_);
lean_ctor_set(v_reuseFailAlloc_2419_, 7, v_cFileName_x3f_2403_);
lean_ctor_set(v_reuseFailAlloc_2419_, 8, v_bcFileName_x3f_2404_);
lean_ctor_set(v_reuseFailAlloc_2419_, 9, v_errorOnKinds_2406_);
lean_ctor_set(v_reuseFailAlloc_2419_, 10, v_incrSaveFileName_x3f_2408_);
lean_ctor_set(v_reuseFailAlloc_2419_, 11, v_incrLoadFileName_x3f_2409_);
lean_ctor_set(v_reuseFailAlloc_2419_, 12, v_incrHeaderSaveFileName_x3f_2410_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*13 + 8, v_component_2389_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*13 + 9, v_printPrefix_2390_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*13 + 10, v_printLibDir_2391_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*13 + 11, v_useStdin_2392_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*13 + 12, v_onlyDeps_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*13 + 13, v_onlySrcDeps_2394_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*13 + 14, v_depsJson_2395_);
lean_ctor_set_uint32(v_reuseFailAlloc_2419_, sizeof(void*)*13, v_trustLevel_2397_);
lean_ctor_set_uint32(v_reuseFailAlloc_2419_, sizeof(void*)*13 + 4, v_numThreads_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*13 + 15, v_jsonOutput_2405_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*13 + 16, v_printStats_2407_);
v___x_2417_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2418_; 
lean_ctor_set_uint8(v___x_2417_, sizeof(void*)*13 + 17, v___x_1181_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
return v___x_2418_;
}
}
}
}
else
{
lean_object* v_leanOpts_2421_; lean_object* v_forwardedArgs_2422_; uint8_t v_component_2423_; uint8_t v_printPrefix_2424_; uint8_t v_printLibDir_2425_; uint8_t v_onlyDeps_2426_; uint8_t v_onlySrcDeps_2427_; uint8_t v_depsJson_2428_; lean_object* v_opts_2429_; uint32_t v_trustLevel_2430_; uint32_t v_numThreads_2431_; lean_object* v_rootDir_x3f_2432_; lean_object* v_setupFileName_x3f_2433_; lean_object* v_oleanFileName_x3f_2434_; lean_object* v_ileanFileName_x3f_2435_; lean_object* v_cFileName_x3f_2436_; lean_object* v_bcFileName_x3f_2437_; uint8_t v_jsonOutput_2438_; lean_object* v_errorOnKinds_2439_; uint8_t v_printStats_2440_; uint8_t v_run_2441_; lean_object* v_incrSaveFileName_x3f_2442_; lean_object* v_incrLoadFileName_x3f_2443_; lean_object* v_incrHeaderSaveFileName_x3f_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2452_; 
lean_dec(v_optArg_x3f_938_);
v_leanOpts_2421_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_2422_ = lean_ctor_get(v_opts_936_, 1);
v_component_2423_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_2424_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_2425_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_onlyDeps_2426_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2427_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_2428_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_2429_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_2430_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_2431_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2432_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_2433_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_2434_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_2435_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_2436_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_2437_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_2438_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2439_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2440_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_2441_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2442_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2443_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2444_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2446_ = v_opts_936_;
v_isShared_2447_ = v_isSharedCheck_2452_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2444_);
lean_inc(v_incrLoadFileName_x3f_2443_);
lean_inc(v_incrSaveFileName_x3f_2442_);
lean_inc(v_errorOnKinds_2439_);
lean_inc(v_bcFileName_x3f_2437_);
lean_inc(v_cFileName_x3f_2436_);
lean_inc(v_ileanFileName_x3f_2435_);
lean_inc(v_oleanFileName_x3f_2434_);
lean_inc(v_setupFileName_x3f_2433_);
lean_inc(v_rootDir_x3f_2432_);
lean_inc(v_opts_2429_);
lean_inc(v_forwardedArgs_2422_);
lean_inc(v_leanOpts_2421_);
lean_dec(v_opts_936_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2452_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_leanOpts_2421_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_forwardedArgs_2422_);
lean_ctor_set(v_reuseFailAlloc_2451_, 2, v_opts_2429_);
lean_ctor_set(v_reuseFailAlloc_2451_, 3, v_rootDir_x3f_2432_);
lean_ctor_set(v_reuseFailAlloc_2451_, 4, v_setupFileName_x3f_2433_);
lean_ctor_set(v_reuseFailAlloc_2451_, 5, v_oleanFileName_x3f_2434_);
lean_ctor_set(v_reuseFailAlloc_2451_, 6, v_ileanFileName_x3f_2435_);
lean_ctor_set(v_reuseFailAlloc_2451_, 7, v_cFileName_x3f_2436_);
lean_ctor_set(v_reuseFailAlloc_2451_, 8, v_bcFileName_x3f_2437_);
lean_ctor_set(v_reuseFailAlloc_2451_, 9, v_errorOnKinds_2439_);
lean_ctor_set(v_reuseFailAlloc_2451_, 10, v_incrSaveFileName_x3f_2442_);
lean_ctor_set(v_reuseFailAlloc_2451_, 11, v_incrLoadFileName_x3f_2443_);
lean_ctor_set(v_reuseFailAlloc_2451_, 12, v_incrHeaderSaveFileName_x3f_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 8, v_component_2423_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 9, v_printPrefix_2424_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 10, v_printLibDir_2425_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 12, v_onlyDeps_2426_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 13, v_onlySrcDeps_2427_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 14, v_depsJson_2428_);
lean_ctor_set_uint32(v_reuseFailAlloc_2451_, sizeof(void*)*13, v_trustLevel_2430_);
lean_ctor_set_uint32(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 4, v_numThreads_2431_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 15, v_jsonOutput_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 16, v_printStats_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2451_, sizeof(void*)*13 + 17, v_run_2441_);
v___x_2449_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; 
lean_ctor_set_uint8(v___x_2449_, sizeof(void*)*13 + 11, v___x_1179_);
v___x_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
return v___x_2450_;
}
}
}
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
v___x_2454_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2453_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2516_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2516_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2516_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2459_ = lean_unsigned_to_nat(0u);
v___x_2460_ = lean_string_utf8_byte_size(v_a_2455_);
lean_inc(v_a_2455_);
v___x_2461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2461_, 0, v_a_2455_);
lean_ctor_set(v___x_2461_, 1, v___x_2459_);
lean_ctor_set(v___x_2461_, 2, v___x_2460_);
v___x_2462_ = l_String_Slice_toNat_x3f(v___x_2461_);
lean_dec_ref_known(v___x_2461_, 3);
if (lean_obj_tag(v___x_2462_) == 1)
{
lean_object* v_val_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; 
v_val_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_val_2463_);
lean_dec_ref_known(v___x_2462_, 1);
v___x_2464_ = lean_unsigned_to_nat(4u);
v___x_2465_ = lean_unsigned_to_nat(2u);
v___x_2466_ = lean_nat_shiftr(v_val_2463_, v___x_2465_);
lean_dec(v_val_2463_);
v___x_2467_ = lean_nat_mul(v___x_2466_, v___x_2464_);
lean_dec(v___x_2466_);
v___x_2468_ = lean_unsigned_to_nat(1024u);
v___x_2469_ = lean_nat_mul(v___x_2467_, v___x_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28);
v___x_2471_ = lean_nat_dec_lt(v___x_2469_, v___x_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_dec(v___x_2469_);
lean_del_object(v___x_2457_);
lean_dec(v_a_2455_);
lean_dec_ref(v_opts_936_);
v___x_2472_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
v___x_2473_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2472_);
lean_dec_ref(v___x_2473_);
goto v___jp_973_;
}
else
{
size_t v___x_2474_; lean_object* v___x_2475_; lean_object* v_leanOpts_2476_; lean_object* v_forwardedArgs_2477_; uint8_t v_component_2478_; uint8_t v_printPrefix_2479_; uint8_t v_printLibDir_2480_; uint8_t v_useStdin_2481_; uint8_t v_onlyDeps_2482_; uint8_t v_onlySrcDeps_2483_; uint8_t v_depsJson_2484_; lean_object* v_opts_2485_; uint32_t v_trustLevel_2486_; uint32_t v_numThreads_2487_; lean_object* v_rootDir_x3f_2488_; lean_object* v_setupFileName_x3f_2489_; lean_object* v_oleanFileName_x3f_2490_; lean_object* v_ileanFileName_x3f_2491_; lean_object* v_cFileName_x3f_2492_; lean_object* v_bcFileName_x3f_2493_; uint8_t v_jsonOutput_2494_; lean_object* v_errorOnKinds_2495_; uint8_t v_printStats_2496_; uint8_t v_run_2497_; lean_object* v_incrSaveFileName_x3f_2498_; lean_object* v_incrLoadFileName_x3f_2499_; lean_object* v_incrHeaderSaveFileName_x3f_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2513_; 
v___x_2474_ = lean_usize_of_nat(v___x_2469_);
lean_dec(v___x_2469_);
v___x_2475_ = lean_internal_set_thread_stack_size(v___x_2474_);
v_leanOpts_2476_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_2477_ = lean_ctor_get(v_opts_936_, 1);
v_component_2478_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_2479_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_2480_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_2481_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_2482_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2483_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_2484_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_2485_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_2486_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_2487_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2488_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_2489_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_2490_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_2491_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_2492_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_2493_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_2494_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2495_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2496_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_2497_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2498_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2499_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2500_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2502_ = v_opts_936_;
v_isShared_2503_ = v_isSharedCheck_2513_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2500_);
lean_inc(v_incrLoadFileName_x3f_2499_);
lean_inc(v_incrSaveFileName_x3f_2498_);
lean_inc(v_errorOnKinds_2495_);
lean_inc(v_bcFileName_x3f_2493_);
lean_inc(v_cFileName_x3f_2492_);
lean_inc(v_ileanFileName_x3f_2491_);
lean_inc(v_oleanFileName_x3f_2490_);
lean_inc(v_setupFileName_x3f_2489_);
lean_inc(v_rootDir_x3f_2488_);
lean_inc(v_opts_2485_);
lean_inc(v_forwardedArgs_2477_);
lean_inc(v_leanOpts_2476_);
lean_dec(v_opts_936_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2513_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2504_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
v___x_2505_ = lean_string_append(v___x_2504_, v_a_2455_);
lean_dec(v_a_2455_);
v___x_2506_ = lean_array_push(v_forwardedArgs_2477_, v___x_2505_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 1, v___x_2506_);
v___x_2508_ = v___x_2502_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_leanOpts_2476_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_opts_2485_);
lean_ctor_set(v_reuseFailAlloc_2512_, 3, v_rootDir_x3f_2488_);
lean_ctor_set(v_reuseFailAlloc_2512_, 4, v_setupFileName_x3f_2489_);
lean_ctor_set(v_reuseFailAlloc_2512_, 5, v_oleanFileName_x3f_2490_);
lean_ctor_set(v_reuseFailAlloc_2512_, 6, v_ileanFileName_x3f_2491_);
lean_ctor_set(v_reuseFailAlloc_2512_, 7, v_cFileName_x3f_2492_);
lean_ctor_set(v_reuseFailAlloc_2512_, 8, v_bcFileName_x3f_2493_);
lean_ctor_set(v_reuseFailAlloc_2512_, 9, v_errorOnKinds_2495_);
lean_ctor_set(v_reuseFailAlloc_2512_, 10, v_incrSaveFileName_x3f_2498_);
lean_ctor_set(v_reuseFailAlloc_2512_, 11, v_incrLoadFileName_x3f_2499_);
lean_ctor_set(v_reuseFailAlloc_2512_, 12, v_incrHeaderSaveFileName_x3f_2500_);
lean_ctor_set_uint8(v_reuseFailAlloc_2512_, sizeof(void*)*13 + 8, v_component_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2512_, sizeof(void*)*13 + 9, v_printPrefix_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2512_, sizeof(void*)*13 + 10, v_printLibDir_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2512_, sizeof(void*)*13 + 11, v_useStdin_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2512_, sizeof(void*)*13 + 12, v_onlyDeps_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2512_, sizeof(void*)*13 + 13, v_onlySrcDeps_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2512_, sizeof(void*)*13 + 14, v_depsJson_2484_);
lean_ctor_set_uint32(v_reuseFailAlloc_2512_, sizeof(void*)*13, v_trustLevel_2486_);
lean_ctor_set_uint32(v_reuseFailAlloc_2512_, sizeof(void*)*13 + 4, v_numThreads_2487_);
lean_ctor_set_uint8(v_reuseFailAlloc_2512_, sizeof(void*)*13 + 15, v_jsonOutput_2494_);
lean_ctor_set_uint8(v_reuseFailAlloc_2512_, sizeof(void*)*13 + 16, v_printStats_2496_);
lean_ctor_set_uint8(v_reuseFailAlloc_2512_, sizeof(void*)*13 + 17, v_run_2497_);
v___x_2508_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2510_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2508_);
v___x_2510_ = v___x_2457_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec(v___x_2462_);
lean_del_object(v___x_2457_);
lean_dec(v_a_2455_);
lean_dec_ref(v_opts_936_);
v___x_2514_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
v___x_2515_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2514_);
lean_dec_ref(v___x_2515_);
goto v___jp_970_;
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_dec_ref(v_opts_936_);
v_a_2517_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2454_, 1);
v___x_2521_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2522_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2521_);
lean_dec_ref(v___x_2522_);
goto v___jp_2518_;
v___jp_2518_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = lean_io_error_to_string(v_a_2517_);
v___x_2520_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2519_);
lean_dec_ref(v___x_2520_);
goto v___jp_979_;
}
}
}
}
else
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
v___x_2524_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2523_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2565_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2565_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2565_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v_leanOpts_2529_; lean_object* v_forwardedArgs_2530_; uint8_t v_component_2531_; uint8_t v_printPrefix_2532_; uint8_t v_printLibDir_2533_; uint8_t v_useStdin_2534_; uint8_t v_onlyDeps_2535_; uint8_t v_onlySrcDeps_2536_; uint8_t v_depsJson_2537_; lean_object* v_opts_2538_; uint32_t v_trustLevel_2539_; uint32_t v_numThreads_2540_; lean_object* v_rootDir_x3f_2541_; lean_object* v_setupFileName_x3f_2542_; lean_object* v_oleanFileName_x3f_2543_; lean_object* v_ileanFileName_x3f_2544_; lean_object* v_cFileName_x3f_2545_; uint8_t v_jsonOutput_2546_; lean_object* v_errorOnKinds_2547_; uint8_t v_printStats_2548_; uint8_t v_run_2549_; lean_object* v_incrSaveFileName_x3f_2550_; lean_object* v_incrLoadFileName_x3f_2551_; lean_object* v_incrHeaderSaveFileName_x3f_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2563_; 
v_leanOpts_2529_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_2530_ = lean_ctor_get(v_opts_936_, 1);
v_component_2531_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_2532_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_2533_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_2534_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_2535_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2536_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_2537_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_2538_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_2539_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_2540_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2541_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_2542_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_2543_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_2544_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_2545_ = lean_ctor_get(v_opts_936_, 7);
v_jsonOutput_2546_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2547_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2548_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_2549_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2550_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2551_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2552_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; 
v_unused_2564_ = lean_ctor_get(v_opts_936_, 8);
lean_dec(v_unused_2564_);
v___x_2554_ = v_opts_936_;
v_isShared_2555_ = v_isSharedCheck_2563_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2552_);
lean_inc(v_incrLoadFileName_x3f_2551_);
lean_inc(v_incrSaveFileName_x3f_2550_);
lean_inc(v_errorOnKinds_2547_);
lean_inc(v_cFileName_x3f_2545_);
lean_inc(v_ileanFileName_x3f_2544_);
lean_inc(v_oleanFileName_x3f_2543_);
lean_inc(v_setupFileName_x3f_2542_);
lean_inc(v_rootDir_x3f_2541_);
lean_inc(v_opts_2538_);
lean_inc(v_forwardedArgs_2530_);
lean_inc(v_leanOpts_2529_);
lean_dec(v_opts_936_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2563_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_a_2525_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 8, v___x_2556_);
v___x_2558_ = v___x_2554_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_leanOpts_2529_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_forwardedArgs_2530_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_opts_2538_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_rootDir_x3f_2541_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_setupFileName_x3f_2542_);
lean_ctor_set(v_reuseFailAlloc_2562_, 5, v_oleanFileName_x3f_2543_);
lean_ctor_set(v_reuseFailAlloc_2562_, 6, v_ileanFileName_x3f_2544_);
lean_ctor_set(v_reuseFailAlloc_2562_, 7, v_cFileName_x3f_2545_);
lean_ctor_set(v_reuseFailAlloc_2562_, 8, v___x_2556_);
lean_ctor_set(v_reuseFailAlloc_2562_, 9, v_errorOnKinds_2547_);
lean_ctor_set(v_reuseFailAlloc_2562_, 10, v_incrSaveFileName_x3f_2550_);
lean_ctor_set(v_reuseFailAlloc_2562_, 11, v_incrLoadFileName_x3f_2551_);
lean_ctor_set(v_reuseFailAlloc_2562_, 12, v_incrHeaderSaveFileName_x3f_2552_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*13 + 8, v_component_2531_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*13 + 9, v_printPrefix_2532_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*13 + 10, v_printLibDir_2533_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*13 + 11, v_useStdin_2534_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*13 + 12, v_onlyDeps_2535_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*13 + 13, v_onlySrcDeps_2536_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*13 + 14, v_depsJson_2537_);
lean_ctor_set_uint32(v_reuseFailAlloc_2562_, sizeof(void*)*13, v_trustLevel_2539_);
lean_ctor_set_uint32(v_reuseFailAlloc_2562_, sizeof(void*)*13 + 4, v_numThreads_2540_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*13 + 15, v_jsonOutput_2546_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*13 + 16, v_printStats_2548_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*13 + 17, v_run_2549_);
v___x_2558_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2560_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2558_);
v___x_2560_ = v___x_2527_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
lean_dec_ref(v_opts_936_);
v_a_2566_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2524_, 1);
v___x_2570_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2571_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2570_);
lean_dec_ref(v___x_2571_);
goto v___jp_2567_;
v___jp_2567_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2568_ = lean_io_error_to_string(v_a_2566_);
v___x_2569_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2568_);
lean_dec_ref(v___x_2569_);
goto v___jp_1137_;
}
}
}
}
else
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
v___x_2573_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2572_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2614_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2614_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2614_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v_leanOpts_2578_; lean_object* v_forwardedArgs_2579_; uint8_t v_component_2580_; uint8_t v_printPrefix_2581_; uint8_t v_printLibDir_2582_; uint8_t v_useStdin_2583_; uint8_t v_onlyDeps_2584_; uint8_t v_onlySrcDeps_2585_; uint8_t v_depsJson_2586_; lean_object* v_opts_2587_; uint32_t v_trustLevel_2588_; uint32_t v_numThreads_2589_; lean_object* v_rootDir_x3f_2590_; lean_object* v_setupFileName_x3f_2591_; lean_object* v_oleanFileName_x3f_2592_; lean_object* v_ileanFileName_x3f_2593_; lean_object* v_bcFileName_x3f_2594_; uint8_t v_jsonOutput_2595_; lean_object* v_errorOnKinds_2596_; uint8_t v_printStats_2597_; uint8_t v_run_2598_; lean_object* v_incrSaveFileName_x3f_2599_; lean_object* v_incrLoadFileName_x3f_2600_; lean_object* v_incrHeaderSaveFileName_x3f_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2612_; 
v_leanOpts_2578_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_2579_ = lean_ctor_get(v_opts_936_, 1);
v_component_2580_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_2581_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_2582_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_2583_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_2584_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2585_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_2586_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_2587_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_2588_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_numThreads_2589_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13 + 4);
v_rootDir_x3f_2590_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_2591_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_2592_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_2593_ = lean_ctor_get(v_opts_936_, 6);
v_bcFileName_x3f_2594_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_2595_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2596_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2597_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_2598_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2599_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2600_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2601_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2612_ == 0)
{
lean_object* v_unused_2613_; 
v_unused_2613_ = lean_ctor_get(v_opts_936_, 7);
lean_dec(v_unused_2613_);
v___x_2603_ = v_opts_936_;
v_isShared_2604_ = v_isSharedCheck_2612_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2601_);
lean_inc(v_incrLoadFileName_x3f_2600_);
lean_inc(v_incrSaveFileName_x3f_2599_);
lean_inc(v_errorOnKinds_2596_);
lean_inc(v_bcFileName_x3f_2594_);
lean_inc(v_ileanFileName_x3f_2593_);
lean_inc(v_oleanFileName_x3f_2592_);
lean_inc(v_setupFileName_x3f_2591_);
lean_inc(v_rootDir_x3f_2590_);
lean_inc(v_opts_2587_);
lean_inc(v_forwardedArgs_2579_);
lean_inc(v_leanOpts_2578_);
lean_dec(v_opts_936_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2612_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2605_, 0, v_a_2574_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 7, v___x_2605_);
v___x_2607_ = v___x_2603_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_leanOpts_2578_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_forwardedArgs_2579_);
lean_ctor_set(v_reuseFailAlloc_2611_, 2, v_opts_2587_);
lean_ctor_set(v_reuseFailAlloc_2611_, 3, v_rootDir_x3f_2590_);
lean_ctor_set(v_reuseFailAlloc_2611_, 4, v_setupFileName_x3f_2591_);
lean_ctor_set(v_reuseFailAlloc_2611_, 5, v_oleanFileName_x3f_2592_);
lean_ctor_set(v_reuseFailAlloc_2611_, 6, v_ileanFileName_x3f_2593_);
lean_ctor_set(v_reuseFailAlloc_2611_, 7, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2611_, 8, v_bcFileName_x3f_2594_);
lean_ctor_set(v_reuseFailAlloc_2611_, 9, v_errorOnKinds_2596_);
lean_ctor_set(v_reuseFailAlloc_2611_, 10, v_incrSaveFileName_x3f_2599_);
lean_ctor_set(v_reuseFailAlloc_2611_, 11, v_incrLoadFileName_x3f_2600_);
lean_ctor_set(v_reuseFailAlloc_2611_, 12, v_incrHeaderSaveFileName_x3f_2601_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*13 + 8, v_component_2580_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*13 + 9, v_printPrefix_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*13 + 10, v_printLibDir_2582_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*13 + 11, v_useStdin_2583_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*13 + 12, v_onlyDeps_2584_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*13 + 13, v_onlySrcDeps_2585_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*13 + 14, v_depsJson_2586_);
lean_ctor_set_uint32(v_reuseFailAlloc_2611_, sizeof(void*)*13, v_trustLevel_2588_);
lean_ctor_set_uint32(v_reuseFailAlloc_2611_, sizeof(void*)*13 + 4, v_numThreads_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*13 + 15, v_jsonOutput_2595_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*13 + 16, v_printStats_2597_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*13 + 17, v_run_2598_);
v___x_2607_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2609_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2607_);
v___x_2609_ = v___x_2576_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_dec_ref(v_opts_936_);
v_a_2615_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2573_, 1);
v___x_2619_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2620_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2619_);
lean_dec_ref(v___x_2620_);
goto v___jp_2616_;
v___jp_2616_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = lean_io_error_to_string(v_a_2615_);
v___x_2618_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2617_);
lean_dec_ref(v___x_2618_);
goto v___jp_967_;
}
}
}
}
else
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
lean_dec(v_optArg_x3f_938_);
lean_dec_ref(v_opts_936_);
v___x_2621_ = l___private_Lean_Shell_0__Lean_featuresString;
v___x_2622_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2621_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2630_; 
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; 
v_unused_2631_ = lean_ctor_get(v___x_2622_, 0);
lean_dec(v_unused_2631_);
v___x_2624_ = v___x_2622_;
v_isShared_2625_ = v_isSharedCheck_2630_;
goto v_resetjp_2623_;
}
else
{
lean_dec(v___x_2622_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2630_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2626_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 1);
lean_ctor_set(v___x_2624_, 0, v___x_2626_);
v___x_2628_ = v___x_2624_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v_a_2632_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2622_, 1);
v___x_2636_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2637_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2636_);
lean_dec_ref(v___x_2637_);
goto v___jp_2633_;
v___jp_2633_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_io_error_to_string(v_a_2632_);
v___x_2635_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2634_);
lean_dec_ref(v___x_2635_);
goto v___jp_1143_;
}
}
}
}
else
{
lean_object* v___x_2638_; 
lean_dec(v_optArg_x3f_938_);
lean_dec_ref(v_opts_936_);
v___x_2638_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1167_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2646_; 
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2646_ == 0)
{
lean_object* v_unused_2647_; 
v_unused_2647_ = lean_ctor_get(v___x_2638_, 0);
lean_dec(v_unused_2647_);
v___x_2640_ = v___x_2638_;
v_isShared_2641_ = v_isSharedCheck_2646_;
goto v_resetjp_2639_;
}
else
{
lean_dec(v___x_2638_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2646_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2642_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2641_ == 0)
{
lean_ctor_set_tag(v___x_2640_, 1);
lean_ctor_set(v___x_2640_, 0, v___x_2642_);
v___x_2644_ = v___x_2640_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_a_2648_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2638_, 1);
v___x_2652_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2653_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2652_);
lean_dec_ref(v___x_2653_);
goto v___jp_2649_;
v___jp_2649_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_io_error_to_string(v_a_2648_);
v___x_2651_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2650_);
lean_dec_ref(v___x_2651_);
goto v___jp_961_;
}
}
}
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_dec(v_optArg_x3f_938_);
lean_dec_ref(v_opts_936_);
v___x_2654_ = l_Lean_githash;
v___x_2655_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2654_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2663_; 
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2663_ == 0)
{
lean_object* v_unused_2664_; 
v_unused_2664_ = lean_ctor_get(v___x_2655_, 0);
lean_dec(v_unused_2664_);
v___x_2657_ = v___x_2655_;
v_isShared_2658_ = v_isSharedCheck_2663_;
goto v_resetjp_2656_;
}
else
{
lean_dec(v___x_2655_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2663_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2659_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2658_ == 0)
{
lean_ctor_set_tag(v___x_2657_, 1);
lean_ctor_set(v___x_2657_, 0, v___x_2659_);
v___x_2661_ = v___x_2657_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v_a_2665_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2655_, 1);
v___x_2669_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2670_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2669_);
lean_dec_ref(v___x_2670_);
goto v___jp_2666_;
v___jp_2666_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = lean_io_error_to_string(v_a_2665_);
v___x_2668_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2667_);
lean_dec_ref(v___x_2668_);
goto v___jp_1149_;
}
}
}
}
else
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_dec(v_optArg_x3f_938_);
lean_dec_ref(v_opts_936_);
v___x_2671_ = l___private_Lean_Shell_0__Lean_shortVersionString;
v___x_2672_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2671_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2680_; 
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2680_ == 0)
{
lean_object* v_unused_2681_; 
v_unused_2681_ = lean_ctor_get(v___x_2672_, 0);
lean_dec(v_unused_2681_);
v___x_2674_ = v___x_2672_;
v_isShared_2675_ = v_isSharedCheck_2680_;
goto v_resetjp_2673_;
}
else
{
lean_dec(v___x_2672_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2680_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2676_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2675_ == 0)
{
lean_ctor_set_tag(v___x_2674_, 1);
lean_ctor_set(v___x_2674_, 0, v___x_2676_);
v___x_2678_ = v___x_2674_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v_a_2682_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2686_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2687_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2686_);
lean_dec_ref(v___x_2687_);
goto v___jp_2683_;
v___jp_2683_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = lean_io_error_to_string(v_a_2682_);
v___x_2685_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2684_);
lean_dec_ref(v___x_2685_);
goto v___jp_955_;
}
}
}
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
lean_dec(v_optArg_x3f_938_);
lean_dec_ref(v_opts_936_);
v___x_2688_ = l___private_Lean_Shell_0__Lean_versionHeader;
v___x_2689_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(v___x_2688_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2697_; 
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2697_ == 0)
{
lean_object* v_unused_2698_; 
v_unused_2698_ = lean_ctor_get(v___x_2689_, 0);
lean_dec(v_unused_2698_);
v___x_2691_ = v___x_2689_;
v_isShared_2692_ = v_isSharedCheck_2697_;
goto v_resetjp_2690_;
}
else
{
lean_dec(v___x_2689_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2697_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; lean_object* v___x_2695_; 
v___x_2693_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_2692_ == 0)
{
lean_ctor_set_tag(v___x_2691_, 1);
lean_ctor_set(v___x_2691_, 0, v___x_2693_);
v___x_2695_ = v___x_2691_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_a_2699_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2689_, 1);
v___x_2703_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2704_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2703_);
lean_dec_ref(v___x_2704_);
goto v___jp_2700_;
v___jp_2700_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_io_error_to_string(v_a_2699_);
v___x_2702_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2701_);
lean_dec_ref(v___x_2702_);
goto v___jp_1155_;
}
}
}
}
else
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
v___x_2706_ = l___private_Lean_Shell_0__Lean_checkOptArg(v___x_2705_, v_optArg_x3f_938_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2760_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2709_ = v___x_2706_;
v_isShared_2710_ = v_isSharedCheck_2760_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2706_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2760_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2711_ = lean_unsigned_to_nat(0u);
v___x_2712_ = lean_string_utf8_byte_size(v_a_2707_);
lean_inc(v_a_2707_);
v___x_2713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2713_, 0, v_a_2707_);
lean_ctor_set(v___x_2713_, 1, v___x_2711_);
lean_ctor_set(v___x_2713_, 2, v___x_2712_);
v___x_2714_ = l_String_Slice_toNat_x3f(v___x_2713_);
lean_dec_ref_known(v___x_2713_, 3);
if (lean_obj_tag(v___x_2714_) == 1)
{
lean_object* v_val_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; 
v_val_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_val_2715_);
lean_dec_ref_known(v___x_2714_, 1);
v___x_2716_ = lean_cstr_to_nat("4294967296");
v___x_2717_ = lean_nat_dec_lt(v_val_2715_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
lean_dec(v_val_2715_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_dec_ref(v_opts_936_);
v___x_2718_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__35));
v___x_2719_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2718_);
lean_dec_ref(v___x_2719_);
goto v___jp_943_;
}
else
{
lean_object* v_leanOpts_2720_; lean_object* v_forwardedArgs_2721_; uint8_t v_component_2722_; uint8_t v_printPrefix_2723_; uint8_t v_printLibDir_2724_; uint8_t v_useStdin_2725_; uint8_t v_onlyDeps_2726_; uint8_t v_onlySrcDeps_2727_; uint8_t v_depsJson_2728_; lean_object* v_opts_2729_; uint32_t v_trustLevel_2730_; lean_object* v_rootDir_x3f_2731_; lean_object* v_setupFileName_x3f_2732_; lean_object* v_oleanFileName_x3f_2733_; lean_object* v_ileanFileName_x3f_2734_; lean_object* v_cFileName_x3f_2735_; lean_object* v_bcFileName_x3f_2736_; uint8_t v_jsonOutput_2737_; lean_object* v_errorOnKinds_2738_; uint8_t v_printStats_2739_; uint8_t v_run_2740_; lean_object* v_incrSaveFileName_x3f_2741_; lean_object* v_incrLoadFileName_x3f_2742_; lean_object* v_incrHeaderSaveFileName_x3f_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2757_; 
v_leanOpts_2720_ = lean_ctor_get(v_opts_936_, 0);
v_forwardedArgs_2721_ = lean_ctor_get(v_opts_936_, 1);
v_component_2722_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 8);
v_printPrefix_2723_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 9);
v_printLibDir_2724_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 10);
v_useStdin_2725_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 11);
v_onlyDeps_2726_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 12);
v_onlySrcDeps_2727_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 13);
v_depsJson_2728_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 14);
v_opts_2729_ = lean_ctor_get(v_opts_936_, 2);
v_trustLevel_2730_ = lean_ctor_get_uint32(v_opts_936_, sizeof(void*)*13);
v_rootDir_x3f_2731_ = lean_ctor_get(v_opts_936_, 3);
v_setupFileName_x3f_2732_ = lean_ctor_get(v_opts_936_, 4);
v_oleanFileName_x3f_2733_ = lean_ctor_get(v_opts_936_, 5);
v_ileanFileName_x3f_2734_ = lean_ctor_get(v_opts_936_, 6);
v_cFileName_x3f_2735_ = lean_ctor_get(v_opts_936_, 7);
v_bcFileName_x3f_2736_ = lean_ctor_get(v_opts_936_, 8);
v_jsonOutput_2737_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 15);
v_errorOnKinds_2738_ = lean_ctor_get(v_opts_936_, 9);
v_printStats_2739_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 16);
v_run_2740_ = lean_ctor_get_uint8(v_opts_936_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_2741_ = lean_ctor_get(v_opts_936_, 10);
v_incrLoadFileName_x3f_2742_ = lean_ctor_get(v_opts_936_, 11);
v_incrHeaderSaveFileName_x3f_2743_ = lean_ctor_get(v_opts_936_, 12);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_opts_936_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2745_ = v_opts_936_;
v_isShared_2746_ = v_isSharedCheck_2757_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_incrHeaderSaveFileName_x3f_2743_);
lean_inc(v_incrLoadFileName_x3f_2742_);
lean_inc(v_incrSaveFileName_x3f_2741_);
lean_inc(v_errorOnKinds_2738_);
lean_inc(v_bcFileName_x3f_2736_);
lean_inc(v_cFileName_x3f_2735_);
lean_inc(v_ileanFileName_x3f_2734_);
lean_inc(v_oleanFileName_x3f_2733_);
lean_inc(v_setupFileName_x3f_2732_);
lean_inc(v_rootDir_x3f_2731_);
lean_inc(v_opts_2729_);
lean_inc(v_forwardedArgs_2721_);
lean_inc(v_leanOpts_2720_);
lean_dec(v_opts_936_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2757_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
uint32_t v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2747_ = lean_uint32_of_nat(v_val_2715_);
lean_dec(v_val_2715_);
v___x_2748_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__36));
v___x_2749_ = lean_string_append(v___x_2748_, v_a_2707_);
lean_dec(v_a_2707_);
v___x_2750_ = lean_array_push(v_forwardedArgs_2721_, v___x_2749_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 1, v___x_2750_);
v___x_2752_ = v___x_2745_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 13, 18);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_leanOpts_2720_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2756_, 2, v_opts_2729_);
lean_ctor_set(v_reuseFailAlloc_2756_, 3, v_rootDir_x3f_2731_);
lean_ctor_set(v_reuseFailAlloc_2756_, 4, v_setupFileName_x3f_2732_);
lean_ctor_set(v_reuseFailAlloc_2756_, 5, v_oleanFileName_x3f_2733_);
lean_ctor_set(v_reuseFailAlloc_2756_, 6, v_ileanFileName_x3f_2734_);
lean_ctor_set(v_reuseFailAlloc_2756_, 7, v_cFileName_x3f_2735_);
lean_ctor_set(v_reuseFailAlloc_2756_, 8, v_bcFileName_x3f_2736_);
lean_ctor_set(v_reuseFailAlloc_2756_, 9, v_errorOnKinds_2738_);
lean_ctor_set(v_reuseFailAlloc_2756_, 10, v_incrSaveFileName_x3f_2741_);
lean_ctor_set(v_reuseFailAlloc_2756_, 11, v_incrLoadFileName_x3f_2742_);
lean_ctor_set(v_reuseFailAlloc_2756_, 12, v_incrHeaderSaveFileName_x3f_2743_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, sizeof(void*)*13 + 8, v_component_2722_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, sizeof(void*)*13 + 9, v_printPrefix_2723_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, sizeof(void*)*13 + 10, v_printLibDir_2724_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, sizeof(void*)*13 + 11, v_useStdin_2725_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, sizeof(void*)*13 + 12, v_onlyDeps_2726_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, sizeof(void*)*13 + 13, v_onlySrcDeps_2727_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, sizeof(void*)*13 + 14, v_depsJson_2728_);
lean_ctor_set_uint32(v_reuseFailAlloc_2756_, sizeof(void*)*13, v_trustLevel_2730_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, sizeof(void*)*13 + 15, v_jsonOutput_2737_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, sizeof(void*)*13 + 16, v_printStats_2739_);
lean_ctor_set_uint8(v_reuseFailAlloc_2756_, sizeof(void*)*13 + 17, v_run_2740_);
v___x_2752_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2754_; 
lean_ctor_set_uint32(v___x_2752_, sizeof(void*)*13 + 4, v___x_2747_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v___x_2752_);
v___x_2754_ = v___x_2709_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_dec(v___x_2714_);
lean_del_object(v___x_2709_);
lean_dec(v_a_2707_);
lean_dec_ref(v_opts_936_);
v___x_2758_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__37));
v___x_2759_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2758_);
lean_dec_ref(v___x_2759_);
goto v___jp_940_;
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_dec_ref(v_opts_936_);
v_a_2761_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2706_, 1);
v___x_2765_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_2766_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2765_);
lean_dec_ref(v___x_2766_);
goto v___jp_2762_;
v___jp_2762_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = lean_io_error_to_string(v_a_2761_);
v___x_2764_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_2763_);
lean_dec_ref(v___x_2764_);
goto v___jp_949_;
}
}
}
}
else
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
lean_dec(v_optArg_x3f_938_);
v___x_2767_ = lean_internal_set_exit_on_panic(v___x_1159_);
v___x_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2768_, 0, v_opts_936_);
return v___x_2768_;
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
v___x_956_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_957_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_956_);
lean_dec_ref(v___x_957_);
goto v___jp_952_;
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
v___x_974_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
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
v___x_986_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_987_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_986_);
lean_dec_ref(v___x_987_);
goto v___jp_982_;
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
v___x_1013_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1014_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1013_);
lean_dec_ref(v___x_1014_);
goto v___jp_1009_;
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
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_io_error_to_string(v___y_1046_);
v___x_1048_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1047_);
lean_dec_ref(v___x_1048_);
goto v___jp_1042_;
}
v___jp_1049_:
{
uint8_t v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = 1;
v___x_1051_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_1050_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1059_; 
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v___x_1051_, 0);
lean_dec(v_unused_1060_);
v___x_1053_ = v___x_1051_;
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
else
{
lean_dec(v___x_1051_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 1);
lean_ctor_set(v___x_1053_, 0, v___x_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_a_1061_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1062_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
v___x_1063_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1062_);
lean_dec_ref(v___x_1063_);
v___y_1046_ = v_a_1061_;
goto v___jp_1045_;
}
}
v___jp_1064_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
v___x_1066_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1065_);
lean_dec_ref(v___x_1066_);
goto v___jp_1049_;
}
v___jp_1067_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
v___jp_1070_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1072_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1071_);
lean_dec_ref(v___x_1072_);
goto v___jp_1067_;
}
v___jp_1073_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
v___jp_1076_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1078_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1077_);
lean_dec_ref(v___x_1078_);
goto v___jp_1073_;
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
goto v___jp_1094_;
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
v___x_1117_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
v___jp_1119_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
v___x_1121_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_1120_);
lean_dec_ref(v___x_1121_);
goto v___jp_1116_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* v_opts_2769_, lean_object* v_opt_2770_, lean_object* v_optArg_x3f_2771_, lean_object* v_a_2772_){
_start:
{
uint32_t v_opt_boxed_2773_; lean_object* v_res_2774_; 
v_opt_boxed_2773_ = lean_unbox_uint32(v_opt_2770_);
lean_dec(v_opt_2770_);
v_res_2774_ = lean_shell_options_process(v_opts_2769_, v_opt_boxed_2773_, v_optArg_x3f_2771_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(lean_object* v_name_2776_, lean_object* v_f_2777_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_uv_os_getpid();
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2815_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2815_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2815_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; uint64_t v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v_a_2791_; uint8_t v___x_2805_; lean_object* v___x_2806_; 
v___x_2784_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___closed__0));
v___x_2785_ = lean_unbox_uint64(v_a_2780_);
lean_dec(v_a_2780_);
v___x_2786_ = lean_uint64_to_nat(v___x_2785_);
v___x_2787_ = l_Nat_reprFast(v___x_2786_);
v___x_2788_ = lean_string_append(v___x_2784_, v___x_2787_);
lean_dec_ref(v___x_2787_);
lean_inc_ref(v_name_2776_);
v___x_2789_ = l_System_FilePath_addExtension(v_name_2776_, v___x_2788_);
lean_dec_ref(v___x_2788_);
v___x_2805_ = 1;
v___x_2806_ = lean_io_prim_handle_mk(v___x_2789_, v___x_2805_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2808_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc_n(v_a_2807_, 2);
lean_dec_ref_known(v___x_2806_, 1);
v___x_2808_ = lean_apply_2(v_f_2777_, v_a_2807_, lean_box(0));
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v___x_2809_; 
lean_dec_ref_known(v___x_2808_, 1);
v___x_2809_ = lean_io_prim_handle_flush(v_a_2807_);
lean_dec(v_a_2807_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2810_; 
lean_dec_ref_known(v___x_2809_, 1);
v___x_2810_ = lean_io_rename(v___x_2789_, v_name_2776_);
lean_dec_ref(v_name_2776_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_dec_ref(v___x_2789_);
lean_del_object(v___x_2782_);
return v___x_2810_;
}
else
{
lean_object* v_a_2811_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v_a_2791_ = v_a_2811_;
goto v___jp_2790_;
}
}
else
{
lean_object* v_a_2812_; 
lean_dec_ref(v_name_2776_);
v_a_2812_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2809_, 1);
v_a_2791_ = v_a_2812_;
goto v___jp_2790_;
}
}
else
{
lean_object* v_a_2813_; 
lean_dec(v_a_2807_);
lean_dec_ref(v_name_2776_);
v_a_2813_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2808_, 1);
v_a_2791_ = v_a_2813_;
goto v___jp_2790_;
}
}
else
{
lean_object* v_a_2814_; 
lean_dec_ref(v_f_2777_);
lean_dec_ref(v_name_2776_);
v_a_2814_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2806_, 1);
v_a_2791_ = v_a_2814_;
goto v___jp_2790_;
}
v___jp_2790_:
{
uint8_t v___x_2792_; 
v___x_2792_ = l_System_FilePath_pathExists(v___x_2789_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2794_; 
lean_dec_ref(v___x_2789_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 1);
lean_ctor_set(v___x_2782_, 0, v_a_2791_);
v___x_2794_ = v___x_2782_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2791_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
else
{
lean_object* v___x_2796_; 
lean_del_object(v___x_2782_);
v___x_2796_ = lean_io_remove_file(v___x_2789_);
lean_dec_ref(v___x_2789_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2803_ == 0)
{
lean_object* v_unused_2804_; 
v_unused_2804_ = lean_ctor_get(v___x_2796_, 0);
lean_dec(v_unused_2804_);
v___x_2798_ = v___x_2796_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_dec(v___x_2796_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set_tag(v___x_2798_, 1);
lean_ctor_set(v___x_2798_, 0, v_a_2791_);
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2791_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
lean_dec(v_a_2791_);
return v___x_2796_;
}
}
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec_ref(v_f_2777_);
lean_dec_ref(v_name_2776_);
v_a_2816_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2779_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2779_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically___boxed(lean_object* v_name_2824_, lean_object* v_f_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(v_name_2824_, v_f_2825_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* v_opts_2828_, lean_object* v_opt_2829_){
_start:
{
lean_object* v_name_2830_; lean_object* v_defValue_2831_; lean_object* v_map_2832_; lean_object* v___x_2833_; 
v_name_2830_ = lean_ctor_get(v_opt_2829_, 0);
v_defValue_2831_ = lean_ctor_get(v_opt_2829_, 1);
v_map_2832_ = lean_ctor_get(v_opts_2828_, 0);
v___x_2833_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2832_, v_name_2830_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_inc(v_defValue_2831_);
return v_defValue_2831_;
}
else
{
lean_object* v_val_2834_; 
v_val_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_val_2834_);
lean_dec_ref_known(v___x_2833_, 1);
if (lean_obj_tag(v_val_2834_) == 3)
{
lean_object* v_v_2835_; 
v_v_2835_ = lean_ctor_get(v_val_2834_, 0);
lean_inc(v_v_2835_);
lean_dec_ref_known(v_val_2834_, 1);
return v_v_2835_;
}
else
{
lean_dec(v_val_2834_);
lean_inc(v_defValue_2831_);
return v_defValue_2831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* v_opts_2836_, lean_object* v_opt_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v_opts_2836_, v_opt_2837_);
lean_dec_ref(v_opt_2837_);
lean_dec_ref(v_opts_2836_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* v_s_2840_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2841_ = lean_string_utf8_byte_size(v_s_2840_);
v___x_2842_ = lean_unsigned_to_nat(5u);
v___x_2843_ = lean_nat_dec_le(v___x_2842_, v___x_2841_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; 
lean_dec_ref(v_s_2840_);
v___x_2844_ = lean_box(0);
return v___x_2844_;
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; 
v___x_2845_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
v___x_2846_ = lean_unsigned_to_nat(0u);
v___x_2847_ = lean_string_memcmp(v_s_2840_, v___x_2845_, v___x_2846_, v___x_2846_, v___x_2842_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; 
lean_dec_ref(v_s_2840_);
v___x_2848_ = lean_box(0);
return v___x_2848_;
}
else
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
lean_inc_ref(v_s_2840_);
v___x_2849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2849_, 0, v_s_2840_);
lean_ctor_set(v___x_2849_, 1, v___x_2846_);
lean_ctor_set(v___x_2849_, 2, v___x_2841_);
v___x_2850_ = l_String_Slice_pos_x21(v___x_2849_, v___x_2842_);
lean_dec_ref_known(v___x_2849_, 3);
v___x_2851_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2851_, 0, v_s_2840_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
lean_ctor_set(v___x_2851_, 2, v___x_2841_);
v___x_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
return v___x_2852_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* v_s_2853_, lean_object* v_pat_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v_s_2853_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* v_s_2856_, lean_object* v_pat_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(v_s_2856_, v_pat_2857_);
lean_dec_ref(v_pat_2857_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* v_x_2859_, lean_object* v_x_2860_, lean_object* v_v_2861_){
_start:
{
lean_inc_ref(v_v_2861_);
return v_v_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* v_x_2862_, lean_object* v_x_2863_, lean_object* v_v_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l___private_Lean_Shell_0__Lean_shellMain___lam__0(v_x_2862_, v_x_2863_, v_v_2864_);
lean_dec_ref(v_v_2864_);
lean_dec_ref(v_x_2863_);
lean_dec(v_x_2862_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object* v___x_2869_, lean_object* v_mainModuleName_2870_, lean_object* v_out_2871_, uint8_t v___x_2872_, lean_object* v___x_2873_, lean_object* v_fileName_2874_, lean_object* v___x_2875_, lean_object* v___x_2876_, lean_object* v___x_2877_, lean_object* v___x_2878_, lean_object* v___x_2879_, lean_object* v___x_2880_, lean_object* v___x_2881_, lean_object* v___x_2882_, uint8_t v_run_2883_, lean_object* v___x_2884_, uint8_t v_printLibDir_2885_){
_start:
{
lean_object* v_a_2888_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___y_2894_; uint16_t v___y_2895_; lean_object* v_fileName_2896_; lean_object* v_fileMap_2897_; lean_object* v_currNamespace_2898_; lean_object* v_openDecls_2899_; lean_object* v_initHeartbeats_2900_; lean_object* v_maxHeartbeats_2901_; lean_object* v_quotContext_2902_; lean_object* v_currMacroScope_2903_; lean_object* v_cancelTk_x3f_2904_; lean_object* v_inheritedTraceOptions_2905_; lean_object* v_currRecDepth_2906_; lean_object* v_ref_2907_; uint8_t v_suppressElabErrors_2908_; uint8_t v_isRecordingDeps_2909_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___y_2944_; uint8_t v___y_2945_; uint16_t v___y_2946_; uint16_t v___x_2967_; lean_object* v___x_2968_; lean_object* v_env_2969_; uint8_t v___x_2970_; uint16_t v___x_2971_; uint16_t v___x_2972_; uint16_t v___x_2973_; uint8_t v___x_2974_; 
v___x_2891_ = lean_io_get_num_heartbeats();
v___x_2892_ = lean_st_mk_ref(v___x_2869_);
v___x_2941_ = l_Lean_inheritedTraceOptions;
v___x_2942_ = lean_st_ref_get(v___x_2941_);
v___x_2967_ = l_Lean_OptionFlags_ofOptions(v___x_2884_);
v___x_2968_ = lean_st_ref_get(v___x_2892_);
v_env_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc_ref(v_env_2969_);
lean_dec(v___x_2968_);
v___x_2970_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2969_);
lean_dec_ref(v_env_2969_);
v___x_2971_ = 512;
v___x_2972_ = lean_uint16_land(v___x_2967_, v___x_2971_);
v___x_2973_ = 0;
v___x_2974_ = lean_uint16_dec_eq(v___x_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
if (v___x_2970_ == 0)
{
v___y_2944_ = v___x_2884_;
v___y_2945_ = v___x_2872_;
v___y_2946_ = v___x_2967_;
goto v___jp_2943_;
}
else
{
lean_dec_ref(v___x_2873_);
lean_inc(v___x_2876_);
v___y_2894_ = v___x_2884_;
v___y_2895_ = v___x_2967_;
v_fileName_2896_ = v_fileName_2874_;
v_fileMap_2897_ = v___x_2875_;
v_currNamespace_2898_ = v___x_2876_;
v_openDecls_2899_ = v___x_2877_;
v_initHeartbeats_2900_ = v___x_2891_;
v_maxHeartbeats_2901_ = v___x_2878_;
v_quotContext_2902_ = v___x_2876_;
v_currMacroScope_2903_ = v___x_2879_;
v_cancelTk_x3f_2904_ = v___x_2880_;
v_inheritedTraceOptions_2905_ = v___x_2942_;
v_currRecDepth_2906_ = v___x_2881_;
v_ref_2907_ = v___x_2882_;
v_suppressElabErrors_2908_ = v_run_2883_;
v_isRecordingDeps_2909_ = v_run_2883_;
goto v___jp_2893_;
}
}
else
{
if (v___x_2970_ == 0)
{
lean_dec_ref(v___x_2873_);
lean_inc(v___x_2876_);
v___y_2894_ = v___x_2884_;
v___y_2895_ = v___x_2967_;
v_fileName_2896_ = v_fileName_2874_;
v_fileMap_2897_ = v___x_2875_;
v_currNamespace_2898_ = v___x_2876_;
v_openDecls_2899_ = v___x_2877_;
v_initHeartbeats_2900_ = v___x_2891_;
v_maxHeartbeats_2901_ = v___x_2878_;
v_quotContext_2902_ = v___x_2876_;
v_currMacroScope_2903_ = v___x_2879_;
v_cancelTk_x3f_2904_ = v___x_2880_;
v_inheritedTraceOptions_2905_ = v___x_2942_;
v_currRecDepth_2906_ = v___x_2881_;
v_ref_2907_ = v___x_2882_;
v_suppressElabErrors_2908_ = v_run_2883_;
v_isRecordingDeps_2909_ = v_run_2883_;
goto v___jp_2893_;
}
else
{
v___y_2944_ = v___x_2884_;
v___y_2945_ = v_printLibDir_2885_;
v___y_2946_ = v___x_2967_;
goto v___jp_2943_;
}
}
v___jp_2887_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_mk_io_user_error(v_a_2888_);
v___x_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
return v___x_2890_;
}
v___jp_2893_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2910_ = l_Lean_maxRecDepth;
v___x_2911_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___y_2894_, v___x_2910_);
v___x_2912_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2912_, 0, v_fileName_2896_);
lean_ctor_set(v___x_2912_, 1, v_fileMap_2897_);
lean_ctor_set(v___x_2912_, 2, v___y_2894_);
lean_ctor_set(v___x_2912_, 3, v___x_2911_);
lean_ctor_set(v___x_2912_, 4, v_currNamespace_2898_);
lean_ctor_set(v___x_2912_, 5, v_openDecls_2899_);
lean_ctor_set(v___x_2912_, 6, v_initHeartbeats_2900_);
lean_ctor_set(v___x_2912_, 7, v_maxHeartbeats_2901_);
lean_ctor_set(v___x_2912_, 8, v_quotContext_2902_);
lean_ctor_set(v___x_2912_, 9, v_currMacroScope_2903_);
lean_ctor_set(v___x_2912_, 10, v_cancelTk_x3f_2904_);
lean_ctor_set(v___x_2912_, 11, v_inheritedTraceOptions_2905_);
v___x_2913_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
lean_ctor_set(v___x_2913_, 1, v_currRecDepth_2906_);
lean_ctor_set(v___x_2913_, 2, v_ref_2907_);
lean_ctor_set_uint16(v___x_2913_, sizeof(void*)*3, v___y_2895_);
lean_ctor_set_uint8(v___x_2913_, sizeof(void*)*3 + 2, v_suppressElabErrors_2908_);
lean_ctor_set_uint8(v___x_2913_, sizeof(void*)*3 + 3, v_isRecordingDeps_2909_);
v___x_2914_ = l_Lean_Compiler_LCNF_emitC(v_mainModuleName_2870_, v___x_2913_, v___x_2892_);
lean_dec_ref_known(v___x_2913_, 3);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
v___x_2916_ = lean_st_ref_get(v___x_2892_);
lean_dec(v___x_2892_);
lean_dec(v___x_2916_);
v___x_2917_ = lean_string_to_utf8(v_a_2915_);
lean_dec(v_a_2915_);
v___x_2918_ = lean_io_prim_handle_write(v_out_2871_, v___x_2917_);
lean_dec_ref(v___x_2917_);
return v___x_2918_;
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2940_; 
lean_dec(v___x_2892_);
v_a_2919_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2921_ = v___x_2914_;
v_isShared_2922_ = v_isSharedCheck_2940_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2914_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2940_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
if (lean_obj_tag(v_a_2919_) == 0)
{
lean_object* v_msg_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2927_; 
v_msg_2923_ = lean_ctor_get(v_a_2919_, 1);
lean_inc_ref(v_msg_2923_);
lean_dec_ref_known(v_a_2919_, 2);
v___x_2924_ = l_Lean_MessageData_toString(v_msg_2923_);
v___x_2925_ = lean_mk_io_user_error(v___x_2924_);
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 0, v___x_2925_);
v___x_2927_ = v___x_2921_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2925_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
else
{
lean_object* v_id_2929_; lean_object* v___x_2930_; 
lean_del_object(v___x_2921_);
v_id_2929_ = lean_ctor_get(v_a_2919_, 0);
lean_inc(v_id_2929_);
lean_dec_ref_known(v_a_2919_, 2);
v___x_2930_ = l_Lean_InternalExceptionId_getName(v_id_2929_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_dec(v_id_2929_);
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2930_, 1);
v___x_2932_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__0));
v___x_2933_ = l_Lean_Name_toString(v_a_2931_, v___x_2872_);
v___x_2934_ = lean_string_append(v___x_2932_, v___x_2933_);
lean_dec_ref(v___x_2933_);
v_a_2888_ = v___x_2934_;
goto v___jp_2887_;
}
else
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
lean_dec_ref_known(v___x_2930_, 1);
v___x_2935_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__1));
v___x_2936_ = l_Nat_reprFast(v_id_2929_);
v___x_2937_ = lean_string_append(v___x_2935_, v___x_2936_);
lean_dec_ref(v___x_2936_);
v___x_2938_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___closed__2));
v___x_2939_ = lean_string_append(v___x_2937_, v___x_2938_);
v_a_2888_ = v___x_2939_;
goto v___jp_2887_;
}
}
}
}
}
v___jp_2943_:
{
lean_object* v___x_2947_; lean_object* v_env_2948_; lean_object* v_nextMacroScope_2949_; lean_object* v_ngen_2950_; lean_object* v_auxDeclNGen_2951_; lean_object* v_traceState_2952_; lean_object* v_recordedDeps_2953_; lean_object* v_messages_2954_; lean_object* v_infoState_2955_; lean_object* v_snapshotTasks_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2965_; 
v___x_2947_ = lean_st_ref_take(v___x_2892_);
v_env_2948_ = lean_ctor_get(v___x_2947_, 0);
v_nextMacroScope_2949_ = lean_ctor_get(v___x_2947_, 1);
v_ngen_2950_ = lean_ctor_get(v___x_2947_, 2);
v_auxDeclNGen_2951_ = lean_ctor_get(v___x_2947_, 3);
v_traceState_2952_ = lean_ctor_get(v___x_2947_, 4);
v_recordedDeps_2953_ = lean_ctor_get(v___x_2947_, 6);
v_messages_2954_ = lean_ctor_get(v___x_2947_, 7);
v_infoState_2955_ = lean_ctor_get(v___x_2947_, 8);
v_snapshotTasks_2956_ = lean_ctor_get(v___x_2947_, 9);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2965_ == 0)
{
lean_object* v_unused_2966_; 
v_unused_2966_ = lean_ctor_get(v___x_2947_, 5);
lean_dec(v_unused_2966_);
v___x_2958_ = v___x_2947_;
v_isShared_2959_ = v_isSharedCheck_2965_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_snapshotTasks_2956_);
lean_inc(v_infoState_2955_);
lean_inc(v_messages_2954_);
lean_inc(v_recordedDeps_2953_);
lean_inc(v_traceState_2952_);
lean_inc(v_auxDeclNGen_2951_);
lean_inc(v_ngen_2950_);
lean_inc(v_nextMacroScope_2949_);
lean_inc(v_env_2948_);
lean_dec(v___x_2947_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2965_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2960_ = l_Lean_Kernel_enableDiag(v_env_2948_, v___y_2945_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 5, v___x_2873_);
lean_ctor_set(v___x_2958_, 0, v___x_2960_);
v___x_2962_ = v___x_2958_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_nextMacroScope_2949_);
lean_ctor_set(v_reuseFailAlloc_2964_, 2, v_ngen_2950_);
lean_ctor_set(v_reuseFailAlloc_2964_, 3, v_auxDeclNGen_2951_);
lean_ctor_set(v_reuseFailAlloc_2964_, 4, v_traceState_2952_);
lean_ctor_set(v_reuseFailAlloc_2964_, 5, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2964_, 6, v_recordedDeps_2953_);
lean_ctor_set(v_reuseFailAlloc_2964_, 7, v_messages_2954_);
lean_ctor_set(v_reuseFailAlloc_2964_, 8, v_infoState_2955_);
lean_ctor_set(v_reuseFailAlloc_2964_, 9, v_snapshotTasks_2956_);
v___x_2962_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_st_ref_put(v___x_2892_, v___x_2962_);
lean_inc(v___x_2876_);
v___y_2894_ = v___y_2944_;
v___y_2895_ = v___y_2946_;
v_fileName_2896_ = v_fileName_2874_;
v_fileMap_2897_ = v___x_2875_;
v_currNamespace_2898_ = v___x_2876_;
v_openDecls_2899_ = v___x_2877_;
v_initHeartbeats_2900_ = v___x_2891_;
v_maxHeartbeats_2901_ = v___x_2878_;
v_quotContext_2902_ = v___x_2876_;
v_currMacroScope_2903_ = v___x_2879_;
v_cancelTk_x3f_2904_ = v___x_2880_;
v_inheritedTraceOptions_2905_ = v___x_2942_;
v_currRecDepth_2906_ = v___x_2881_;
v_ref_2907_ = v___x_2882_;
v_suppressElabErrors_2908_ = v_run_2883_;
v_isRecordingDeps_2909_ = v_run_2883_;
goto v___jp_2893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object** _args){
lean_object* v___x_2975_ = _args[0];
lean_object* v_mainModuleName_2976_ = _args[1];
lean_object* v_out_2977_ = _args[2];
lean_object* v___x_2978_ = _args[3];
lean_object* v___x_2979_ = _args[4];
lean_object* v_fileName_2980_ = _args[5];
lean_object* v___x_2981_ = _args[6];
lean_object* v___x_2982_ = _args[7];
lean_object* v___x_2983_ = _args[8];
lean_object* v___x_2984_ = _args[9];
lean_object* v___x_2985_ = _args[10];
lean_object* v___x_2986_ = _args[11];
lean_object* v___x_2987_ = _args[12];
lean_object* v___x_2988_ = _args[13];
lean_object* v_run_2989_ = _args[14];
lean_object* v___x_2990_ = _args[15];
lean_object* v_printLibDir_2991_ = _args[16];
lean_object* v___y_2992_ = _args[17];
_start:
{
uint8_t v___x_12772__boxed_2993_; uint8_t v_run_boxed_2994_; uint8_t v_printLibDir_boxed_2995_; lean_object* v_res_2996_; 
v___x_12772__boxed_2993_ = lean_unbox(v___x_2978_);
v_run_boxed_2994_ = lean_unbox(v_run_2989_);
v_printLibDir_boxed_2995_ = lean_unbox(v_printLibDir_2991_);
v_res_2996_ = l___private_Lean_Shell_0__Lean_shellMain___lam__1(v___x_2975_, v_mainModuleName_2976_, v_out_2977_, v___x_12772__boxed_2993_, v___x_2979_, v_fileName_2980_, v___x_2981_, v___x_2982_, v___x_2983_, v___x_2984_, v___x_2985_, v___x_2986_, v___x_2987_, v___x_2988_, v_run_boxed_2994_, v___x_2990_, v_printLibDir_boxed_2995_);
lean_dec(v_out_2977_);
return v_res_2996_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = l_Lean_Options_empty;
v___x_2999_ = l_Lean_Core_getMaxHeartbeats(v___x_2998_);
return v___x_2999_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3000_ = lean_unsigned_to_nat(1u);
v___x_3001_ = l_Lean_firstFrontendMacroScope;
v___x_3002_ = lean_nat_add(v___x_3001_, v___x_3000_);
return v___x_3002_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_unsigned_to_nat(32u);
v___x_3014_ = lean_mk_empty_array_with_capacity(v___x_3013_);
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
return v___x_3015_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8(void){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_3016_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9(void){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__8);
v___x_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
return v___x_3018_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9);
v___x_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2(lean_object* v___x_3021_, uint8_t v___x_3022_, lean_object* v_val_3023_, lean_object* v_mainModuleName_3024_, lean_object* v_fileName_3025_, uint8_t v_run_3026_, uint8_t v_printLibDir_3027_, lean_object* v___x_3028_, lean_object* v_out_3029_){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; uint64_t v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; size_t v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___f_3061_; lean_object* v___x_3062_; 
v___x_3031_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__0));
v___x_3032_ = l_Lean_instInhabitedFileMap_default;
v___x_3033_ = l_Lean_Options_empty;
v___x_3034_ = lean_box(0);
v___x_3035_ = lean_box(0);
v___x_3036_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__1);
v___x_3037_ = l_Lean_firstFrontendMacroScope;
v___x_3038_ = lean_box(0);
v___x_3039_ = lean_box(0);
v___x_3040_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__2);
v___x_3041_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__5));
v___x_3042_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__6));
v___x_3043_ = 0ULL;
v___x_3044_ = lean_unsigned_to_nat(32u);
v___x_3045_ = lean_mk_empty_array_with_capacity(v___x_3044_);
v___x_3046_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__7);
v___x_3047_ = ((size_t)5ULL);
lean_inc_n(v___x_3021_, 5);
v___x_3048_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3048_, 0, v___x_3046_);
lean_ctor_set(v___x_3048_, 1, v___x_3045_);
lean_ctor_set(v___x_3048_, 2, v___x_3021_);
lean_ctor_set(v___x_3048_, 3, v___x_3021_);
lean_ctor_set_usize(v___x_3048_, 4, v___x_3047_);
lean_inc_ref_n(v___x_3048_, 3);
v___x_3049_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
lean_ctor_set_uint64(v___x_3049_, sizeof(void*)*1, v___x_3043_);
v___x_3050_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__9);
v___x_3051_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10, &l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10_once, _init_l___private_Lean_Shell_0__Lean_shellMain___lam__2___closed__10);
v___x_3052_ = lean_mk_empty_array_with_capacity(v___x_3021_);
lean_inc_ref_n(v___x_3052_, 2);
v___x_3053_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v___x_3033_);
lean_ctor_set(v___x_3053_, 2, v___x_3052_);
lean_ctor_set(v___x_3053_, 3, v___x_3021_);
lean_ctor_set(v___x_3053_, 4, v___x_3021_);
lean_ctor_set(v___x_3053_, 5, v___x_3021_);
v___x_3054_ = l_Lean_NameSet_empty;
v___x_3055_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3048_);
lean_ctor_set(v___x_3055_, 1, v___x_3048_);
lean_ctor_set(v___x_3055_, 2, v___x_3054_);
v___x_3056_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3056_, 0, v___x_3050_);
lean_ctor_set(v___x_3056_, 1, v___x_3050_);
lean_ctor_set(v___x_3056_, 2, v___x_3048_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*3, v___x_3022_);
v___x_3057_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3057_, 0, v_val_3023_);
lean_ctor_set(v___x_3057_, 1, v___x_3040_);
lean_ctor_set(v___x_3057_, 2, v___x_3041_);
lean_ctor_set(v___x_3057_, 3, v___x_3042_);
lean_ctor_set(v___x_3057_, 4, v___x_3049_);
lean_ctor_set(v___x_3057_, 5, v___x_3051_);
lean_ctor_set(v___x_3057_, 6, v___x_3053_);
lean_ctor_set(v___x_3057_, 7, v___x_3055_);
lean_ctor_set(v___x_3057_, 8, v___x_3056_);
lean_ctor_set(v___x_3057_, 9, v___x_3052_);
v___x_3058_ = lean_box(v___x_3022_);
v___x_3059_ = lean_box(v_run_3026_);
v___x_3060_ = lean_box(v_printLibDir_3027_);
v___f_3061_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 18, 17);
lean_closure_set(v___f_3061_, 0, v___x_3057_);
lean_closure_set(v___f_3061_, 1, v_mainModuleName_3024_);
lean_closure_set(v___f_3061_, 2, v_out_3029_);
lean_closure_set(v___f_3061_, 3, v___x_3058_);
lean_closure_set(v___f_3061_, 4, v___x_3051_);
lean_closure_set(v___f_3061_, 5, v_fileName_3025_);
lean_closure_set(v___f_3061_, 6, v___x_3032_);
lean_closure_set(v___f_3061_, 7, v___x_3034_);
lean_closure_set(v___f_3061_, 8, v___x_3035_);
lean_closure_set(v___f_3061_, 9, v___x_3036_);
lean_closure_set(v___f_3061_, 10, v___x_3037_);
lean_closure_set(v___f_3061_, 11, v___x_3038_);
lean_closure_set(v___f_3061_, 12, v___x_3021_);
lean_closure_set(v___f_3061_, 13, v___x_3039_);
lean_closure_set(v___f_3061_, 14, v___x_3059_);
lean_closure_set(v___f_3061_, 15, v___x_3033_);
lean_closure_set(v___f_3061_, 16, v___x_3060_);
v___x_3062_ = l_Lean_profileitIOUnsafe___redArg(v___x_3031_, v___x_3028_, v___f_3061_, v___x_3034_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__2___boxed(lean_object* v___x_3063_, lean_object* v___x_3064_, lean_object* v_val_3065_, lean_object* v_mainModuleName_3066_, lean_object* v_fileName_3067_, lean_object* v_run_3068_, lean_object* v_printLibDir_3069_, lean_object* v___x_3070_, lean_object* v_out_3071_, lean_object* v___y_3072_){
_start:
{
uint8_t v___x_12995__boxed_3073_; uint8_t v_run_boxed_3074_; uint8_t v_printLibDir_boxed_3075_; lean_object* v_res_3076_; 
v___x_12995__boxed_3073_ = lean_unbox(v___x_3064_);
v_run_boxed_3074_ = lean_unbox(v_run_3068_);
v_printLibDir_boxed_3075_ = lean_unbox(v_printLibDir_3069_);
v_res_3076_ = l___private_Lean_Shell_0__Lean_shellMain___lam__2(v___x_3063_, v___x_12995__boxed_3073_, v_val_3065_, v_mainModuleName_3066_, v_fileName_3067_, v_run_boxed_3074_, v_printLibDir_boxed_3075_, v___x_3070_, v_out_3071_);
lean_dec_ref(v___x_3070_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* v_val_3077_, lean_object* v_a_3078_, lean_object* v_b_3079_){
_start:
{
lean_object* v_str_3080_; lean_object* v_startInclusive_3081_; lean_object* v_endExclusive_3082_; lean_object* v___x_3083_; uint8_t v_decide_3084_; 
v_str_3080_ = lean_ctor_get(v_val_3077_, 0);
v_startInclusive_3081_ = lean_ctor_get(v_val_3077_, 1);
v_endExclusive_3082_ = lean_ctor_get(v_val_3077_, 2);
v___x_3083_ = lean_nat_sub(v_endExclusive_3082_, v_startInclusive_3081_);
v_decide_3084_ = lean_nat_dec_eq(v_a_3078_, v___x_3083_);
lean_dec(v___x_3083_);
if (v_decide_3084_ == 0)
{
lean_object* v___x_3085_; uint32_t v___x_3086_; uint32_t v___x_3087_; uint8_t v___x_3088_; 
v___x_3085_ = lean_nat_add(v_startInclusive_3081_, v_a_3078_);
v___x_3086_ = lean_string_utf8_get_fast(v_str_3080_, v___x_3085_);
v___x_3087_ = 10;
v___x_3088_ = lean_uint32_dec_eq(v___x_3086_, v___x_3087_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_dec(v_a_3078_);
v___x_3089_ = lean_box(0);
v___x_3090_ = lean_string_utf8_next_fast(v_str_3080_, v___x_3085_);
lean_dec(v___x_3085_);
v___x_3091_ = lean_nat_sub(v___x_3090_, v_startInclusive_3081_);
v_a_3078_ = v___x_3091_;
v_b_3079_ = v___x_3089_;
goto _start;
}
else
{
lean_object* v___x_3093_; 
lean_dec(v___x_3085_);
v___x_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3093_, 0, v_a_3078_);
return v___x_3093_;
}
}
else
{
lean_dec(v_a_3078_);
lean_inc(v_b_3079_);
return v_b_3079_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* v_val_3094_, lean_object* v_a_3095_, lean_object* v_b_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3094_, v_a_3095_, v_b_3096_);
lean_dec(v_b_3096_);
lean_dec_ref(v_val_3094_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* v_s_3098_){
_start:
{
uint32_t v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = 10;
v___x_3101_ = lean_string_push(v_s_3098_, v___x_3100_);
v___x_3102_ = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(v___x_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* v_s_3103_, lean_object* v_a_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v_s_3103_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* v_s_3106_){
_start:
{
uint32_t v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = 10;
v___x_3109_ = lean_string_push(v_s_3106_, v___x_3108_);
v___x_3110_ = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(v___x_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* v_s_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_s_3111_);
return v_res_3113_;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1(void){
_start:
{
lean_object* v___x_3115_; uint8_t v___x_3116_; 
v___x_3115_ = lean_box(0);
v___x_3116_ = lean_internal_has_address_sanitizer(v___x_3115_);
return v___x_3116_;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = lean_box(0);
v___x_3118_ = lean_internal_get_option_overrides(v___x_3117_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* v_args_3133_, lean_object* v_opts_3134_){
_start:
{
lean_object* v_fns_3137_; uint8_t v_printPrefix_3162_; 
v_printPrefix_3162_ = lean_ctor_get_uint8(v_opts_3134_, sizeof(void*)*13 + 9);
if (v_printPrefix_3162_ == 0)
{
uint8_t v_printLibDir_3163_; 
v_printLibDir_3163_ = lean_ctor_get_uint8(v_opts_3134_, sizeof(void*)*13 + 10);
if (v_printLibDir_3163_ == 0)
{
lean_object* v_leanOpts_3164_; lean_object* v_forwardedArgs_3165_; uint8_t v_component_3166_; uint8_t v_useStdin_3167_; uint8_t v_onlyDeps_3168_; uint8_t v_onlySrcDeps_3169_; uint8_t v_depsJson_3170_; uint32_t v_trustLevel_3171_; lean_object* v_rootDir_x3f_3172_; lean_object* v_setupFileName_x3f_3173_; lean_object* v_oleanFileName_x3f_3174_; lean_object* v_ileanFileName_x3f_3175_; lean_object* v_cFileName_x3f_3176_; lean_object* v_bcFileName_x3f_3177_; uint8_t v_jsonOutput_3178_; lean_object* v_errorOnKinds_3179_; uint8_t v_printStats_3180_; uint8_t v_run_3181_; lean_object* v_incrSaveFileName_x3f_3182_; lean_object* v_incrLoadFileName_x3f_3183_; lean_object* v_incrHeaderSaveFileName_x3f_3184_; lean_object* v___f_3185_; lean_object* v___y_3187_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; uint8_t v___x_3229_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v_mainModuleName_3265_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v_contents_3325_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v_str_3354_; lean_object* v_startInclusive_3355_; lean_object* v_endExclusive_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v_fileName_3457_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3495_; lean_object* v___y_3496_; uint8_t v___y_3497_; uint8_t v___y_3500_; lean_object* v_fst_3501_; lean_object* v_snd_3502_; uint8_t v___y_3504_; lean_object* v___x_3534_; lean_object* v_maxMemory_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
v_leanOpts_3164_ = lean_ctor_get(v_opts_3134_, 0);
lean_inc_ref(v_leanOpts_3164_);
v_forwardedArgs_3165_ = lean_ctor_get(v_opts_3134_, 1);
lean_inc_ref(v_forwardedArgs_3165_);
v_component_3166_ = lean_ctor_get_uint8(v_opts_3134_, sizeof(void*)*13 + 8);
v_useStdin_3167_ = lean_ctor_get_uint8(v_opts_3134_, sizeof(void*)*13 + 11);
v_onlyDeps_3168_ = lean_ctor_get_uint8(v_opts_3134_, sizeof(void*)*13 + 12);
v_onlySrcDeps_3169_ = lean_ctor_get_uint8(v_opts_3134_, sizeof(void*)*13 + 13);
v_depsJson_3170_ = lean_ctor_get_uint8(v_opts_3134_, sizeof(void*)*13 + 14);
v_trustLevel_3171_ = lean_ctor_get_uint32(v_opts_3134_, sizeof(void*)*13);
v_rootDir_x3f_3172_ = lean_ctor_get(v_opts_3134_, 3);
lean_inc(v_rootDir_x3f_3172_);
v_setupFileName_x3f_3173_ = lean_ctor_get(v_opts_3134_, 4);
lean_inc(v_setupFileName_x3f_3173_);
v_oleanFileName_x3f_3174_ = lean_ctor_get(v_opts_3134_, 5);
lean_inc(v_oleanFileName_x3f_3174_);
v_ileanFileName_x3f_3175_ = lean_ctor_get(v_opts_3134_, 6);
lean_inc(v_ileanFileName_x3f_3175_);
v_cFileName_x3f_3176_ = lean_ctor_get(v_opts_3134_, 7);
lean_inc(v_cFileName_x3f_3176_);
v_bcFileName_x3f_3177_ = lean_ctor_get(v_opts_3134_, 8);
lean_inc(v_bcFileName_x3f_3177_);
v_jsonOutput_3178_ = lean_ctor_get_uint8(v_opts_3134_, sizeof(void*)*13 + 15);
v_errorOnKinds_3179_ = lean_ctor_get(v_opts_3134_, 9);
lean_inc_ref(v_errorOnKinds_3179_);
v_printStats_3180_ = lean_ctor_get_uint8(v_opts_3134_, sizeof(void*)*13 + 16);
v_run_3181_ = lean_ctor_get_uint8(v_opts_3134_, sizeof(void*)*13 + 17);
v_incrSaveFileName_x3f_3182_ = lean_ctor_get(v_opts_3134_, 10);
lean_inc(v_incrSaveFileName_x3f_3182_);
v_incrLoadFileName_x3f_3183_ = lean_ctor_get(v_opts_3134_, 11);
lean_inc(v_incrLoadFileName_x3f_3183_);
v_incrHeaderSaveFileName_x3f_3184_ = lean_ctor_get(v_opts_3134_, 12);
lean_inc(v_incrHeaderSaveFileName_x3f_3184_);
lean_dec_ref(v_opts_3134_);
v___f_3185_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__0));
v___x_3201_ = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__2, &l___private_Lean_Shell_0__Lean_shellMain___closed__2_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2);
v___x_3202_ = l_Lean_Options_mergeBy(v___f_3185_, v_leanOpts_3164_, v___x_3201_);
v___x_3229_ = 1;
v___x_3534_ = l___private_Lean_Shell_0__Lean_maxMemory;
v_maxMemory_3535_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3202_, v___x_3534_);
v___x_3536_ = lean_unsigned_to_nat(0u);
v___x_3537_ = lean_nat_dec_eq(v_maxMemory_3535_, v___x_3536_);
if (v___x_3537_ == 0)
{
size_t v___x_3538_; size_t v___x_3539_; size_t v___x_3540_; size_t v___x_3541_; lean_object* v___x_3542_; 
v___x_3538_ = lean_usize_of_nat(v_maxMemory_3535_);
lean_dec(v_maxMemory_3535_);
v___x_3539_ = ((size_t)10ULL);
v___x_3540_ = lean_usize_shift_left(v___x_3538_, v___x_3539_);
v___x_3541_ = lean_usize_shift_left(v___x_3540_, v___x_3539_);
v___x_3542_ = lean_internal_set_max_memory(v___x_3541_);
goto v___jp_3525_;
}
else
{
lean_dec(v_maxMemory_3535_);
goto v___jp_3525_;
}
v___jp_3186_:
{
lean_object* v___x_3188_; uint8_t v___x_3189_; 
v___x_3188_ = lean_display_cumulative_profiling_times();
v___x_3189_ = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__1, &l___private_Lean_Shell_0__Lean_shellMain___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1);
if (v___x_3189_ == 0)
{
if (lean_obj_tag(v___y_3187_) == 0)
{
if (v___x_3189_ == 0)
{
uint8_t v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = 1;
v___x_3191_ = lean_io_exit(v___x_3190_);
return v___x_3191_;
}
else
{
goto v___jp_3156_;
}
}
else
{
lean_dec_ref_known(v___y_3187_, 1);
goto v___jp_3156_;
}
}
else
{
if (lean_obj_tag(v___y_3187_) == 0)
{
goto v___jp_3159_;
}
else
{
lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3199_; 
v_isSharedCheck_3199_ = !lean_is_exclusive(v___y_3187_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; 
v_unused_3200_ = lean_ctor_get(v___y_3187_, 0);
lean_dec(v_unused_3200_);
v___x_3193_ = v___y_3187_;
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
else
{
lean_dec(v___y_3187_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
if (v___x_3189_ == 0)
{
lean_del_object(v___x_3193_);
goto v___jp_3159_;
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3197_; 
v___x_3195_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3194_ == 0)
{
lean_ctor_set_tag(v___x_3193_, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3195_);
v___x_3197_ = v___x_3193_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
}
}
v___jp_3203_:
{
if (lean_obj_tag(v_bcFileName_x3f_3177_) == 1)
{
lean_object* v_val_3207_; lean_object* v___x_3208_; 
v_val_3207_ = lean_ctor_get(v_bcFileName_x3f_3177_, 0);
lean_inc(v_val_3207_);
lean_dec_ref_known(v_bcFileName_x3f_3177_, 1);
v___x_3208_ = lean_init_llvm();
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
lean_dec_ref_known(v___x_3208_, 1);
v___x_3209_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__3));
v___x_3210_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(v___x_3210_, 0, v___y_3206_);
lean_closure_set(v___x_3210_, 1, v___y_3205_);
lean_closure_set(v___x_3210_, 2, v_val_3207_);
v___x_3211_ = lean_box(0);
v___x_3212_ = l_Lean_profileitIOUnsafe___redArg(v___x_3209_, v___x_3202_, v___x_3210_, v___x_3211_);
lean_dec_ref(v___x_3202_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_dec_ref_known(v___x_3212_, 1);
v___y_3187_ = v___y_3204_;
goto v___jp_3186_;
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec(v___y_3204_);
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3212_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3212_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v_val_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___x_3202_);
v_a_3221_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3208_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3208_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
else
{
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___x_3202_);
lean_dec(v_bcFileName_x3f_3177_);
v___y_3187_ = v___y_3204_;
goto v___jp_3186_;
}
}
v___jp_3230_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__4));
v___x_3232_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3231_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v___x_3233_; 
lean_dec_ref_known(v___x_3232_, 1);
v___x_3233_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3229_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3241_; 
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3241_ == 0)
{
lean_object* v_unused_3242_; 
v_unused_3242_ = lean_ctor_get(v___x_3233_, 0);
lean_dec(v_unused_3242_);
v___x_3235_ = v___x_3233_;
v_isShared_3236_ = v_isSharedCheck_3241_;
goto v_resetjp_3234_;
}
else
{
lean_dec(v___x_3233_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3241_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
v___x_3237_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___x_3237_);
v___x_3239_ = v___x_3235_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
v_a_3243_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3233_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3233_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
v_a_3251_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3232_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3232_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
v___jp_3259_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3266_ = lean_unsigned_to_nat(0u);
v___x_3267_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__5));
lean_inc(v_mainModuleName_3265_);
lean_inc_ref(v___x_3202_);
v___x_3268_ = l_Lean_Elab_runFrontend(v___y_3262_, v___x_3202_, v___y_3261_, v_mainModuleName_3265_, v_trustLevel_3171_, v_oleanFileName_x3f_3174_, v_ileanFileName_x3f_3175_, v_jsonOutput_3178_, v_errorOnKinds_3179_, v___x_3267_, v_printStats_3180_, v___y_3263_, v_incrSaveFileName_x3f_3182_, v_incrLoadFileName_x3f_3183_, v_incrHeaderSaveFileName_x3f_3184_);
lean_dec_ref(v_errorOnKinds_3179_);
lean_dec(v_ileanFileName_x3f_3175_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3295_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3295_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3295_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
if (lean_obj_tag(v_a_3269_) == 1)
{
if (v_run_3181_ == 0)
{
lean_del_object(v___x_3271_);
lean_dec(v___y_3264_);
if (lean_obj_tag(v_cFileName_x3f_3176_) == 1)
{
lean_object* v_val_3273_; lean_object* v_val_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___f_3278_; lean_object* v___x_3279_; 
v_val_3273_ = lean_ctor_get(v_a_3269_, 0);
lean_inc_n(v_val_3273_, 2);
v_val_3274_ = lean_ctor_get(v_cFileName_x3f_3176_, 0);
lean_inc(v_val_3274_);
lean_dec_ref_known(v_cFileName_x3f_3176_, 1);
v___x_3275_ = lean_box(v___x_3229_);
v___x_3276_ = lean_box(v_run_3181_);
v___x_3277_ = lean_box(v_printLibDir_3163_);
lean_inc_ref(v___x_3202_);
lean_inc(v_mainModuleName_3265_);
v___f_3278_ = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__2___boxed), 10, 8);
lean_closure_set(v___f_3278_, 0, v___x_3266_);
lean_closure_set(v___f_3278_, 1, v___x_3275_);
lean_closure_set(v___f_3278_, 2, v_val_3273_);
lean_closure_set(v___f_3278_, 3, v_mainModuleName_3265_);
lean_closure_set(v___f_3278_, 4, v___y_3260_);
lean_closure_set(v___f_3278_, 5, v___x_3276_);
lean_closure_set(v___f_3278_, 6, v___x_3277_);
lean_closure_set(v___f_3278_, 7, v___x_3202_);
v___x_3279_ = l___private_Lean_Shell_0__Lean_shellMain_writeFileAtomically(v_val_3274_, v___f_3278_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_dec_ref_known(v___x_3279_, 1);
v___y_3204_ = v_a_3269_;
v___y_3205_ = v_mainModuleName_3265_;
v___y_3206_ = v_val_3273_;
goto v___jp_3203_;
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec(v_val_3273_);
lean_dec_ref_known(v_a_3269_, 1);
lean_dec(v_mainModuleName_3265_);
lean_dec_ref(v___x_3202_);
lean_dec(v_bcFileName_x3f_3177_);
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3279_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
else
{
lean_object* v_val_3288_; 
lean_dec_ref(v___y_3260_);
lean_dec(v_cFileName_x3f_3176_);
v_val_3288_ = lean_ctor_get(v_a_3269_, 0);
lean_inc(v_val_3288_);
v___y_3204_ = v_a_3269_;
v___y_3205_ = v_mainModuleName_3265_;
v___y_3206_ = v_val_3288_;
goto v___jp_3203_;
}
}
else
{
lean_object* v_val_3289_; uint32_t v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3293_; 
lean_dec(v_mainModuleName_3265_);
lean_dec_ref(v___y_3260_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
v_val_3289_ = lean_ctor_get(v_a_3269_, 0);
lean_inc(v_val_3289_);
lean_dec_ref_known(v_a_3269_, 1);
v___x_3290_ = lean_eval_main(v_val_3289_, v___x_3202_, v___y_3264_);
lean_dec(v___y_3264_);
lean_dec_ref(v___x_3202_);
lean_dec(v_val_3289_);
v___x_3291_ = lean_box_uint32(v___x_3290_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v___x_3291_);
v___x_3293_ = v___x_3271_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
else
{
lean_del_object(v___x_3271_);
lean_dec(v_mainModuleName_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3260_);
lean_dec_ref(v___x_3202_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
v___y_3187_ = v_a_3269_;
goto v___jp_3186_;
}
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec(v_mainModuleName_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3260_);
lean_dec_ref(v___x_3202_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
v_a_3296_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3268_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3268_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
v___jp_3304_:
{
if (lean_obj_tag(v___y_3310_) == 0)
{
lean_object* v_a_3311_; 
v_a_3311_ = lean_ctor_get(v___y_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___y_3310_, 1);
v___y_3260_ = v___y_3305_;
v___y_3261_ = v___y_3306_;
v___y_3262_ = v___y_3307_;
v___y_3263_ = v___y_3308_;
v___y_3264_ = v___y_3309_;
v_mainModuleName_3265_ = v_a_3311_;
goto v___jp_3259_;
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
lean_dec(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec_ref(v___x_3202_);
lean_dec(v_incrHeaderSaveFileName_x3f_3184_);
lean_dec(v_incrLoadFileName_x3f_3183_);
lean_dec(v_incrSaveFileName_x3f_3182_);
lean_dec_ref(v_errorOnKinds_3179_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
lean_dec(v_ileanFileName_x3f_3175_);
lean_dec(v_oleanFileName_x3f_3174_);
v_a_3312_ = lean_ctor_get(v___y_3310_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___y_3310_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___y_3310_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___y_3310_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
v___jp_3320_:
{
if (lean_obj_tag(v_setupFileName_x3f_3173_) == 0)
{
lean_object* v___x_3326_; 
v___x_3326_ = lean_box(0);
if (lean_obj_tag(v___y_3323_) == 1)
{
lean_object* v_val_3327_; lean_object* v___x_3328_; 
v_val_3327_ = lean_ctor_get(v___y_3323_, 0);
lean_inc(v_val_3327_);
lean_dec_ref_known(v___y_3323_, 1);
v___x_3328_ = l_Lean_moduleNameOfFileName(v_val_3327_, v_rootDir_x3f_3172_);
if (lean_obj_tag(v___x_3328_) == 0)
{
v___y_3305_ = v___y_3321_;
v___y_3306_ = v___y_3322_;
v___y_3307_ = v_contents_3325_;
v___y_3308_ = v___x_3326_;
v___y_3309_ = v___y_3324_;
v___y_3310_ = v___x_3328_;
goto v___jp_3304_;
}
else
{
if (lean_obj_tag(v_oleanFileName_x3f_3174_) == 0)
{
if (lean_obj_tag(v_cFileName_x3f_3176_) == 0)
{
lean_object* v___x_3329_; 
lean_dec_ref_known(v___x_3328_, 1);
v___x_3329_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__7));
v___y_3260_ = v___y_3321_;
v___y_3261_ = v___y_3322_;
v___y_3262_ = v_contents_3325_;
v___y_3263_ = v___x_3326_;
v___y_3264_ = v___y_3324_;
v_mainModuleName_3265_ = v___x_3329_;
goto v___jp_3259_;
}
else
{
v___y_3305_ = v___y_3321_;
v___y_3306_ = v___y_3322_;
v___y_3307_ = v_contents_3325_;
v___y_3308_ = v___x_3326_;
v___y_3309_ = v___y_3324_;
v___y_3310_ = v___x_3328_;
goto v___jp_3304_;
}
}
else
{
v___y_3305_ = v___y_3321_;
v___y_3306_ = v___y_3322_;
v___y_3307_ = v_contents_3325_;
v___y_3308_ = v___x_3326_;
v___y_3309_ = v___y_3324_;
v___y_3310_ = v___x_3328_;
goto v___jp_3304_;
}
}
}
else
{
lean_object* v___x_3330_; 
lean_dec(v___y_3323_);
lean_dec(v_rootDir_x3f_3172_);
v___x_3330_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__7));
v___y_3260_ = v___y_3321_;
v___y_3261_ = v___y_3322_;
v___y_3262_ = v_contents_3325_;
v___y_3263_ = v___x_3326_;
v___y_3264_ = v___y_3324_;
v_mainModuleName_3265_ = v___x_3330_;
goto v___jp_3259_;
}
}
else
{
lean_object* v_val_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3349_; 
lean_dec(v___y_3323_);
lean_dec(v_rootDir_x3f_3172_);
v_val_3331_ = lean_ctor_get(v_setupFileName_x3f_3173_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v_setupFileName_x3f_3173_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3333_ = v_setupFileName_x3f_3173_;
v_isShared_3334_ = v_isSharedCheck_3349_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_val_3331_);
lean_dec(v_setupFileName_x3f_3173_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3349_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_ModuleSetup_load(v_val_3331_);
lean_dec(v_val_3331_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v_name_3337_; lean_object* v___x_3339_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
v_name_3337_ = lean_ctor_get(v_a_3336_, 0);
lean_inc(v_name_3337_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v_a_3336_);
v___x_3339_ = v___x_3333_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3336_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
v___y_3260_ = v___y_3321_;
v___y_3261_ = v___y_3322_;
v___y_3262_ = v_contents_3325_;
v___y_3263_ = v___x_3339_;
v___y_3264_ = v___y_3324_;
v_mainModuleName_3265_ = v_name_3337_;
goto v___jp_3259_;
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_del_object(v___x_3333_);
lean_dec_ref(v_contents_3325_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec_ref(v___x_3202_);
lean_dec(v_incrHeaderSaveFileName_x3f_3184_);
lean_dec(v_incrLoadFileName_x3f_3183_);
lean_dec(v_incrSaveFileName_x3f_3182_);
lean_dec_ref(v_errorOnKinds_3179_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
lean_dec(v_ileanFileName_x3f_3175_);
lean_dec(v_oleanFileName_x3f_3174_);
v_a_3341_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3335_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3335_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
}
v___jp_3350_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v___x_3359_ = lean_nat_add(v_startInclusive_3355_, v___y_3358_);
lean_dec(v___y_3358_);
lean_inc(v___x_3359_);
lean_inc_ref(v_str_3354_);
v___x_3360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3360_, 0, v_str_3354_);
lean_ctor_set(v___x_3360_, 1, v_startInclusive_3355_);
lean_ctor_set(v___x_3360_, 2, v___x_3359_);
v___x_3361_ = l_String_Slice_trimAscii(v___x_3360_);
v___x_3362_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__9));
v___x_3363_ = l_String_Slice_beq(v___x_3361_, v___x_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
lean_dec(v___x_3359_);
lean_dec(v___y_3357_);
lean_dec(v_endExclusive_3356_);
lean_dec_ref(v_str_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec_ref(v___x_3202_);
lean_dec(v_incrHeaderSaveFileName_x3f_3184_);
lean_dec(v_incrLoadFileName_x3f_3183_);
lean_dec(v_incrSaveFileName_x3f_3182_);
lean_dec_ref(v_errorOnKinds_3179_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
lean_dec(v_ileanFileName_x3f_3175_);
lean_dec(v_oleanFileName_x3f_3174_);
lean_dec(v_setupFileName_x3f_3173_);
lean_dec(v_rootDir_x3f_3172_);
v___x_3364_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__10));
v___x_3365_ = l_String_Slice_toString(v___x_3361_);
lean_dec_ref(v___x_3361_);
v___x_3366_ = lean_string_append(v___x_3364_, v___x_3365_);
lean_dec_ref(v___x_3365_);
v___x_3367_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
v___x_3368_ = lean_string_append(v___x_3366_, v___x_3367_);
v___x_3369_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3368_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3377_; 
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3377_ == 0)
{
lean_object* v_unused_3378_; 
v_unused_3378_ = lean_ctor_get(v___x_3369_, 0);
lean_dec(v_unused_3378_);
v___x_3371_ = v___x_3369_;
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
else
{
lean_dec(v___x_3369_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3373_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3373_);
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
v_a_3379_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3369_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3369_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v___x_3387_; 
lean_dec_ref(v___x_3361_);
v___x_3387_ = lean_string_utf8_extract_fast(v_str_3354_, v___x_3359_, v_endExclusive_3356_);
lean_dec(v_endExclusive_3356_);
lean_dec(v___x_3359_);
lean_dec_ref(v_str_3354_);
v___y_3321_ = v___y_3351_;
v___y_3322_ = v___y_3352_;
v___y_3323_ = v___y_3353_;
v___y_3324_ = v___y_3357_;
v_contents_3325_ = v___x_3387_;
goto v___jp_3320_;
}
}
v___jp_3388_:
{
if (lean_obj_tag(v___y_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___x_3394_; 
v_a_3393_ = lean_ctor_get(v___y_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___y_3392_, 1);
v___x_3394_ = lean_decode_lossy_utf8(v_a_3393_);
lean_dec(v_a_3393_);
if (v_onlyDeps_3168_ == 0)
{
if (v_onlySrcDeps_3169_ == 0)
{
lean_object* v___x_3395_; 
lean_inc_ref(v___x_3394_);
v___x_3395_ = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(v___x_3394_);
if (lean_obj_tag(v___x_3395_) == 1)
{
lean_object* v_val_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
lean_dec_ref(v___x_3394_);
v_val_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_val_3396_);
lean_dec_ref_known(v___x_3395_, 1);
v___x_3397_ = lean_unsigned_to_nat(0u);
v___x_3398_ = lean_box(0);
v___x_3399_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3396_, v___x_3397_, v___x_3398_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_str_3400_; lean_object* v_startInclusive_3401_; lean_object* v_endExclusive_3402_; lean_object* v___x_3403_; 
v_str_3400_ = lean_ctor_get(v_val_3396_, 0);
lean_inc_ref(v_str_3400_);
v_startInclusive_3401_ = lean_ctor_get(v_val_3396_, 1);
lean_inc(v_startInclusive_3401_);
v_endExclusive_3402_ = lean_ctor_get(v_val_3396_, 2);
lean_inc(v_endExclusive_3402_);
lean_dec(v_val_3396_);
v___x_3403_ = lean_nat_sub(v_endExclusive_3402_, v_startInclusive_3401_);
lean_inc_ref(v___y_3389_);
v___y_3351_ = v___y_3389_;
v___y_3352_ = v___y_3389_;
v___y_3353_ = v___y_3390_;
v_str_3354_ = v_str_3400_;
v_startInclusive_3355_ = v_startInclusive_3401_;
v_endExclusive_3356_ = v_endExclusive_3402_;
v___y_3357_ = v___y_3391_;
v___y_3358_ = v___x_3403_;
goto v___jp_3350_;
}
else
{
lean_object* v_val_3404_; lean_object* v_str_3405_; lean_object* v_startInclusive_3406_; lean_object* v_endExclusive_3407_; 
v_val_3404_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_val_3404_);
lean_dec_ref_known(v___x_3399_, 1);
v_str_3405_ = lean_ctor_get(v_val_3396_, 0);
lean_inc_ref(v_str_3405_);
v_startInclusive_3406_ = lean_ctor_get(v_val_3396_, 1);
lean_inc(v_startInclusive_3406_);
v_endExclusive_3407_ = lean_ctor_get(v_val_3396_, 2);
lean_inc(v_endExclusive_3407_);
lean_dec(v_val_3396_);
lean_inc_ref(v___y_3389_);
v___y_3351_ = v___y_3389_;
v___y_3352_ = v___y_3389_;
v___y_3353_ = v___y_3390_;
v_str_3354_ = v_str_3405_;
v_startInclusive_3355_ = v_startInclusive_3406_;
v_endExclusive_3356_ = v_endExclusive_3407_;
v___y_3357_ = v___y_3391_;
v___y_3358_ = v_val_3404_;
goto v___jp_3350_;
}
}
else
{
lean_dec(v___x_3395_);
lean_inc_ref(v___y_3389_);
v___y_3321_ = v___y_3389_;
v___y_3322_ = v___y_3389_;
v___y_3323_ = v___y_3390_;
v___y_3324_ = v___y_3391_;
v_contents_3325_ = v___x_3394_;
goto v___jp_3320_;
}
}
else
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
lean_dec(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___x_3202_);
lean_dec(v_incrHeaderSaveFileName_x3f_3184_);
lean_dec(v_incrLoadFileName_x3f_3183_);
lean_dec(v_incrSaveFileName_x3f_3182_);
lean_dec_ref(v_errorOnKinds_3179_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
lean_dec(v_ileanFileName_x3f_3175_);
lean_dec(v_oleanFileName_x3f_3174_);
lean_dec(v_setupFileName_x3f_3173_);
lean_dec(v_rootDir_x3f_3172_);
v___x_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3408_, 0, v___y_3389_);
v___x_3409_ = l_Lean_Elab_printImportSrcs(v___x_3394_, v___x_3408_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3417_; 
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; 
v_unused_3418_ = lean_ctor_get(v___x_3409_, 0);
lean_dec(v_unused_3418_);
v___x_3411_ = v___x_3409_;
v_isShared_3412_ = v_isSharedCheck_3417_;
goto v_resetjp_3410_;
}
else
{
lean_dec(v___x_3409_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3417_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3413_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3413_);
v___x_3415_ = v___x_3411_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
v_a_3419_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3409_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3409_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
lean_dec(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___x_3202_);
lean_dec(v_incrHeaderSaveFileName_x3f_3184_);
lean_dec(v_incrLoadFileName_x3f_3183_);
lean_dec(v_incrSaveFileName_x3f_3182_);
lean_dec_ref(v_errorOnKinds_3179_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
lean_dec(v_ileanFileName_x3f_3175_);
lean_dec(v_oleanFileName_x3f_3174_);
lean_dec(v_setupFileName_x3f_3173_);
lean_dec(v_rootDir_x3f_3172_);
v___x_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3427_, 0, v___y_3389_);
v___x_3428_ = l_Lean_Elab_printImports(v___x_3394_, v___x_3427_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3436_; 
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3436_ == 0)
{
lean_object* v_unused_3437_; 
v_unused_3437_ = lean_ctor_get(v___x_3428_, 0);
lean_dec(v_unused_3437_);
v___x_3430_ = v___x_3428_;
v_isShared_3431_ = v_isSharedCheck_3436_;
goto v_resetjp_3429_;
}
else
{
lean_dec(v___x_3428_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3436_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; lean_object* v___x_3434_; 
v___x_3432_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3432_);
v___x_3434_ = v___x_3430_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3432_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
v_a_3438_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3428_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3428_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec_ref(v___x_3202_);
lean_dec(v_incrHeaderSaveFileName_x3f_3184_);
lean_dec(v_incrLoadFileName_x3f_3183_);
lean_dec(v_incrSaveFileName_x3f_3182_);
lean_dec_ref(v_errorOnKinds_3179_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
lean_dec(v_ileanFileName_x3f_3175_);
lean_dec(v_oleanFileName_x3f_3174_);
lean_dec(v_setupFileName_x3f_3173_);
lean_dec(v_rootDir_x3f_3172_);
v_a_3446_ = lean_ctor_get(v___y_3392_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___y_3392_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___y_3392_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___y_3392_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
v___jp_3454_:
{
if (v_useStdin_3167_ == 0)
{
lean_object* v___x_3458_; 
v___x_3458_ = l_IO_FS_readBinFile(v_fileName_3457_);
v___y_3389_ = v_fileName_3457_;
v___y_3390_ = v___y_3455_;
v___y_3391_ = v___y_3456_;
v___y_3392_ = v___x_3458_;
goto v___jp_3388_;
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = lean_get_stdin();
v___x_3460_ = l_IO_FS_Stream_readBinToEnd(v___x_3459_);
v___y_3389_ = v_fileName_3457_;
v___y_3390_ = v___y_3455_;
v___y_3391_ = v___y_3456_;
v___y_3392_ = v___x_3460_;
goto v___jp_3388_;
}
}
v___jp_3461_:
{
if (lean_obj_tag(v___y_3462_) == 1)
{
lean_object* v_val_3464_; 
v_val_3464_ = lean_ctor_get(v___y_3462_, 0);
lean_inc(v_val_3464_);
v___y_3455_ = v___y_3462_;
v___y_3456_ = v___y_3463_;
v_fileName_3457_ = v_val_3464_;
goto v___jp_3454_;
}
else
{
if (v_useStdin_3167_ == 0)
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
lean_dec(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___x_3202_);
lean_dec(v_incrHeaderSaveFileName_x3f_3184_);
lean_dec(v_incrLoadFileName_x3f_3183_);
lean_dec(v_incrSaveFileName_x3f_3182_);
lean_dec_ref(v_errorOnKinds_3179_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
lean_dec(v_ileanFileName_x3f_3175_);
lean_dec(v_oleanFileName_x3f_3174_);
lean_dec(v_setupFileName_x3f_3173_);
lean_dec(v_rootDir_x3f_3172_);
v___x_3465_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__4));
v___x_3466_ = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(v___x_3465_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v___x_3467_; 
lean_dec_ref_known(v___x_3466_, 1);
v___x_3467_ = l___private_Lean_Shell_0__Lean_displayHelp(v___x_3229_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3475_; 
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v___x_3467_, 0);
lean_dec(v_unused_3476_);
v___x_3469_ = v___x_3467_;
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
else
{
lean_dec(v___x_3467_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
v_a_3477_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3467_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3467_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
v_a_3485_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3466_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3466_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
lean_object* v___x_3493_; 
v___x_3493_ = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__11));
v___y_3455_ = v___y_3462_;
v___y_3456_ = v___y_3463_;
v_fileName_3457_ = v___x_3493_;
goto v___jp_3454_;
}
}
}
v___jp_3494_:
{
uint8_t v___x_3498_; 
v___x_3498_ = l_List_isEmpty___redArg(v___y_3496_);
if (v___x_3498_ == 0)
{
lean_dec(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___x_3202_);
lean_dec(v_incrHeaderSaveFileName_x3f_3184_);
lean_dec(v_incrLoadFileName_x3f_3183_);
lean_dec(v_incrSaveFileName_x3f_3182_);
lean_dec_ref(v_errorOnKinds_3179_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
lean_dec(v_ileanFileName_x3f_3175_);
lean_dec(v_oleanFileName_x3f_3174_);
lean_dec(v_setupFileName_x3f_3173_);
lean_dec(v_rootDir_x3f_3172_);
goto v___jp_3230_;
}
else
{
if (v___y_3497_ == 0)
{
v___y_3462_ = v___y_3495_;
v___y_3463_ = v___y_3496_;
goto v___jp_3461_;
}
else
{
lean_dec(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___x_3202_);
lean_dec(v_incrHeaderSaveFileName_x3f_3184_);
lean_dec(v_incrLoadFileName_x3f_3183_);
lean_dec(v_incrSaveFileName_x3f_3182_);
lean_dec_ref(v_errorOnKinds_3179_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
lean_dec(v_ileanFileName_x3f_3175_);
lean_dec(v_oleanFileName_x3f_3174_);
lean_dec(v_setupFileName_x3f_3173_);
lean_dec(v_rootDir_x3f_3172_);
goto v___jp_3230_;
}
}
}
v___jp_3499_:
{
if (v_run_3181_ == 0)
{
v___y_3495_ = v_fst_3501_;
v___y_3496_ = v_snd_3502_;
v___y_3497_ = v___y_3500_;
goto v___jp_3494_;
}
else
{
if (v___y_3500_ == 0)
{
v___y_3462_ = v_fst_3501_;
v___y_3463_ = v_snd_3502_;
goto v___jp_3461_;
}
else
{
v___y_3495_ = v_fst_3501_;
v___y_3496_ = v_snd_3502_;
v___y_3497_ = v___y_3500_;
goto v___jp_3494_;
}
}
}
v___jp_3503_:
{
if (lean_obj_tag(v_args_3133_) == 0)
{
lean_object* v___x_3505_; 
v___x_3505_ = lean_box(0);
v___y_3500_ = v___y_3504_;
v_fst_3501_ = v___x_3505_;
v_snd_3502_ = v_args_3133_;
goto v___jp_3499_;
}
else
{
lean_object* v_head_3506_; lean_object* v_tail_3507_; lean_object* v___x_3508_; 
v_head_3506_ = lean_ctor_get(v_args_3133_, 0);
lean_inc(v_head_3506_);
v_tail_3507_ = lean_ctor_get(v_args_3133_, 1);
lean_inc(v_tail_3507_);
lean_dec_ref_known(v_args_3133_, 2);
v___x_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3508_, 0, v_head_3506_);
v___y_3500_ = v___y_3504_;
v_fst_3501_ = v___x_3508_;
v_snd_3502_ = v_tail_3507_;
goto v___jp_3499_;
}
}
v___jp_3509_:
{
switch(v_component_3166_)
{
case 0:
{
lean_dec_ref(v_forwardedArgs_3165_);
if (v_onlyDeps_3168_ == 0)
{
v___y_3504_ = v_printLibDir_3163_;
goto v___jp_3503_;
}
else
{
if (v_depsJson_3170_ == 0)
{
v___y_3504_ = v_depsJson_3170_;
goto v___jp_3503_;
}
else
{
lean_dec_ref(v___x_3202_);
lean_dec(v_incrHeaderSaveFileName_x3f_3184_);
lean_dec(v_incrLoadFileName_x3f_3183_);
lean_dec(v_incrSaveFileName_x3f_3182_);
lean_dec_ref(v_errorOnKinds_3179_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
lean_dec(v_ileanFileName_x3f_3175_);
lean_dec(v_oleanFileName_x3f_3174_);
lean_dec(v_setupFileName_x3f_3173_);
lean_dec(v_rootDir_x3f_3172_);
if (v_useStdin_3167_ == 0)
{
lean_object* v___x_3510_; 
v___x_3510_ = lean_array_mk(v_args_3133_);
v_fns_3137_ = v___x_3510_;
goto v___jp_3136_;
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_dec(v_args_3133_);
v___x_3511_ = lean_get_stdin();
v___x_3512_ = l_IO_FS_Stream_lines(v___x_3511_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
v_fns_3137_ = v_a_3513_;
goto v___jp_3136_;
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
v_a_3514_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3512_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3512_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
lean_dec_ref(v___x_3202_);
lean_dec(v_incrHeaderSaveFileName_x3f_3184_);
lean_dec(v_incrLoadFileName_x3f_3183_);
lean_dec(v_incrSaveFileName_x3f_3182_);
lean_dec_ref(v_errorOnKinds_3179_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
lean_dec(v_ileanFileName_x3f_3175_);
lean_dec(v_oleanFileName_x3f_3174_);
lean_dec(v_setupFileName_x3f_3173_);
lean_dec(v_rootDir_x3f_3172_);
lean_dec(v_args_3133_);
v___x_3522_ = lean_array_to_list(v_forwardedArgs_3165_);
v___x_3523_ = l_Lean_Server_Watchdog_watchdogMain(v___x_3522_);
return v___x_3523_;
}
default: 
{
lean_object* v___x_3524_; 
lean_dec(v_incrHeaderSaveFileName_x3f_3184_);
lean_dec(v_incrLoadFileName_x3f_3183_);
lean_dec(v_incrSaveFileName_x3f_3182_);
lean_dec_ref(v_errorOnKinds_3179_);
lean_dec(v_bcFileName_x3f_3177_);
lean_dec(v_cFileName_x3f_3176_);
lean_dec(v_ileanFileName_x3f_3175_);
lean_dec(v_oleanFileName_x3f_3174_);
lean_dec(v_setupFileName_x3f_3173_);
lean_dec(v_rootDir_x3f_3172_);
lean_dec_ref(v_forwardedArgs_3165_);
lean_dec(v_args_3133_);
v___x_3524_ = l_Lean_Server_FileWorker_workerMain(v___x_3202_);
return v___x_3524_;
}
}
}
v___jp_3525_:
{
lean_object* v___x_3526_; lean_object* v_timeout_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; 
v___x_3526_ = l___private_Lean_Shell_0__Lean_timeout;
v_timeout_3527_ = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(v___x_3202_, v___x_3526_);
v___x_3528_ = lean_unsigned_to_nat(0u);
v___x_3529_ = lean_nat_dec_eq(v_timeout_3527_, v___x_3528_);
if (v___x_3529_ == 0)
{
size_t v___x_3530_; size_t v___x_3531_; size_t v___x_3532_; lean_object* v___x_3533_; 
v___x_3530_ = lean_usize_of_nat(v_timeout_3527_);
lean_dec(v_timeout_3527_);
v___x_3531_ = ((size_t)1000ULL);
v___x_3532_ = lean_usize_mul(v___x_3530_, v___x_3531_);
v___x_3533_ = lean_internal_set_max_heartbeat(v___x_3532_);
goto v___jp_3509_;
}
else
{
lean_dec(v_timeout_3527_);
goto v___jp_3509_;
}
}
}
else
{
lean_object* v___x_3543_; 
lean_dec_ref(v_opts_3134_);
lean_dec(v_args_3133_);
v___x_3543_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
v___x_3545_ = l_Lean_getLibDir(v_a_3544_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3547_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3545_, 1);
v___x_3547_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3546_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3555_; 
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3555_ == 0)
{
lean_object* v_unused_3556_; 
v_unused_3556_ = lean_ctor_get(v___x_3547_, 0);
lean_dec(v_unused_3556_);
v___x_3549_ = v___x_3547_;
v_isShared_3550_ = v_isSharedCheck_3555_;
goto v_resetjp_3548_;
}
else
{
lean_dec(v___x_3547_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3555_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3551_; lean_object* v___x_3553_; 
v___x_3551_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3551_);
v___x_3553_ = v___x_3549_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
v_a_3557_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3547_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3547_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
else
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
v_a_3565_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3545_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3545_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
v_a_3573_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3543_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3543_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
}
else
{
lean_object* v___x_3581_; 
lean_dec_ref(v_opts_3134_);
lean_dec(v_args_3133_);
v___x_3581_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3583_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3581_, 1);
v___x_3583_ = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(v_a_3582_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3591_; 
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3591_ == 0)
{
lean_object* v_unused_3592_; 
v_unused_3592_ = lean_ctor_get(v___x_3583_, 0);
lean_dec(v_unused_3592_);
v___x_3585_ = v___x_3583_;
v_isShared_3586_ = v_isSharedCheck_3591_;
goto v_resetjp_3584_;
}
else
{
lean_dec(v___x_3583_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3591_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3587_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 0, v___x_3587_);
v___x_3589_ = v___x_3585_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
v_a_3593_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___x_3583_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3583_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
v_a_3601_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3581_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3581_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
v___jp_3136_:
{
lean_object* v___x_3138_; 
v___x_3138_ = l_Lean_printImportsJson(v_fns_3137_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3146_; 
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3146_ == 0)
{
lean_object* v_unused_3147_; 
v_unused_3147_ = lean_ctor_get(v___x_3138_, 0);
lean_dec(v_unused_3147_);
v___x_3140_ = v___x_3138_;
v_isShared_3141_ = v_isSharedCheck_3146_;
goto v_resetjp_3139_;
}
else
{
lean_dec(v___x_3138_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3146_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3142_ = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v___x_3142_);
v___x_3144_ = v___x_3140_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
v_a_3148_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3138_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3138_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
v___jp_3156_:
{
uint8_t v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = 0;
v___x_3158_ = lean_io_exit(v___x_3157_);
return v___x_3158_;
}
v___jp_3159_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
return v___x_3161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* v_args_3609_, lean_object* v_opts_3610_, lean_object* v_a_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = lean_shell_main(v_args_3609_, v_opts_3610_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* v_val_3613_, lean_object* v_inst_3614_, lean_object* v_R_3615_, lean_object* v_a_3616_, lean_object* v_b_3617_, lean_object* v_c_3618_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(v_val_3613_, v_a_3616_, v_b_3617_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* v_val_3620_, lean_object* v_inst_3621_, lean_object* v_R_3622_, lean_object* v_a_3623_, lean_object* v_b_3624_, lean_object* v_c_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(v_val_3620_, v_inst_3621_, v_R_3622_, v_a_3623_, v_b_3624_, v_c_3625_);
lean_dec(v_b_3624_);
lean_dec_ref(v_val_3620_);
return v_res_3626_;
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
