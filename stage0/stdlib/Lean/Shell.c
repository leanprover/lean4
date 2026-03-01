// Lean compiler output
// Module: Lean.Shell
// Imports: import Lean.Elab.Frontend import Lean.Elab.ParseImportsFast import Lean.Server.Watchdog import Lean.Server.FileWorker import Lean.Compiler.IR.EmitC import Init.System.Platform
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
lean_object* lean_decode_lossy_utf8(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_decodeLossyUTF8___boxed(lean_object*);
uint32_t lean_run_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_init_llvm();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object*);
lean_object* lean_emit_llvm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_display_cumulative_profiling_times();
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayCumulativeProfilingTimes___boxed(lean_object*);
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
extern lean_object* l_Lean_version_specialDesc;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__1;
static const lean_string_object l___private_Lean_Shell_0__Lean_shortVersionString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__2 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shortVersionString___closed__2_value;
extern lean_object* l_Lean_versionStringCore;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__3;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__4;
static const lean_string_object l___private_Lean_Shell_0__Lean_shortVersionString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "-pre"};
static const lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shortVersionString___closed__5_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__6;
extern uint8_t l_Lean_version_isRelease;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shortVersionString;
static const lean_string_object l___private_Lean_Shell_0__Lean_versionHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean (version "};
static const lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_versionHeader___closed__0_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_versionHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_versionHeader___closed__1_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_versionHeader___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__2;
static const lean_string_object l___private_Lean_Shell_0__Lean_versionHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__3 = (const lean_object*)&l___private_Lean_Shell_0__Lean_versionHeader___closed__3_value;
extern lean_object* l_Lean_githash;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_versionHeader___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__4;
static const lean_string_object l___private_Lean_Shell_0__Lean_versionHeader___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", commit "};
static const lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_versionHeader___closed__5_value;
extern lean_object* l_System_Platform_target;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_versionHeader___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__6;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_versionHeader___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__7;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_versionHeader___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_versionHeader;
uint8_t lean_internal_has_llvm_backend(lean_object*);
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
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
lean_object* lean_get_stdout();
lean_object* lean_get_stderr();
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
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "max_memory"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__0_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 81, 94, 214, 186, 212, 139, 105)}};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
uint32_t lean_uint32_add(uint32_t, uint32_t);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1_value;
extern lean_object* l_Lean_Options_empty;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2;
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object*);
LEAN_EXPORT uint8_t lean_shell_options_get_run(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getRun___boxed(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_profiler;
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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_setConfigOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "invalid -D parameter, argument must contain '='"};
static const lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_setConfigOption___closed__0_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_setConfigOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Lean_Shell_0__Lean_setConfigOption___closed__0_value)}};
static const lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_setConfigOption___closed__1_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* l_String_Slice_toName(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0_value;
lean_object* l_IO_eprint___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
lean_object* lean_io_error_to_string(lean_object*);
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
lean_object* lean_string_push(lean_object*, uint32_t);
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
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
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
lean_object* l_String_toName(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_load_dynlib(lean_object*);
lean_object* lean_load_plugin(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "#lang"};
static const lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Shell_0__Lean_shellMain___closed__0;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "LLVM code generation"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__1 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__1_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "C code generation"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__2 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__2_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "failed to create '"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__3 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__3_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_stdin"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__4 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__4_value;
static const lean_ctor_object l___private_Lean_Shell_0__Lean_shellMain___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__4_value),LEAN_SCALAR_PTR_LITERAL(37, 142, 62, 167, 41, 238, 22, 79)}};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__5 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__5_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lean4"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__6 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__6_value;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__7;
static lean_once_cell_t l___private_Lean_Shell_0__Lean_shellMain___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__8;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown language '"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__9 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__9_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Expected exactly one file name"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__10 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__10_value;
static const lean_string_object l___private_Lean_Shell_0__Lean_shellMain___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<stdin>"};
static const lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__11 = (const lean_object*)&l___private_Lean_Shell_0__Lean_shellMain___closed__11_value;
lean_object* lean_io_exit(uint8_t);
lean_object* l_Lean_printImportsJson(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* l_Lean_IR_emitC(lean_object*, lean_object*);
lean_object* l_Lean_moduleNameOfFileName(lean_object*, lean_object*);
lean_object* l_Lean_ModuleSetup_load(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
uint8_t l_String_Slice_beq(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
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
LEAN_EXPORT lean_object* lean_shell_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_decodeLossyUTF8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_decode_lossy_utf8(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_run_main(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_init_llvm();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_emit_llvm(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayCumulativeProfilingTimes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_display_cumulative_profiling_times();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_internal_has_address_sanitizer(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isMultiThread___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_internal_is_multi_thread(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isDebug___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_internal_is_debug(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBuildType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_internal_get_build_type(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxMemory___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_internal_get_default_max_memory(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxMemory___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_internal_set_max_memory(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultMaxHeartbeat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_internal_get_default_max_heartbeat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setMaxHeartbeat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_internal_set_max_heartbeat(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultVerbose___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_internal_get_default_verbose(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setExitOnPanic___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = lean_internal_set_exit_on_panic(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_setThreadStackSize___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_internal_set_thread_stack_size(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_enableDebug___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_internal_enable_debug(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
x_2 = l_Lean_version_specialDesc;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__2));
x_2 = l_Lean_versionStringCore;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_version_specialDesc;
x_2 = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__3, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__3_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__5));
x_2 = l_Lean_versionStringCore;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString(void) {
_start:
{
uint8_t x_1; 
x_1 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__1, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__1_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1);
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__4, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__4_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = l_Lean_version_isRelease;
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_obj_once(&l___private_Lean_Shell_0__Lean_shortVersionString___closed__6, &l___private_Lean_Shell_0__Lean_shortVersionString___closed__6_once, _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_versionStringCore;
return x_5;
}
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_get_build_type(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
x_2 = l_Lean_githash;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
x_2 = l_System_Platform_target;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__1));
x_2 = l___private_Lean_Shell_0__Lean_shortVersionString;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_Platform_target;
x_2 = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__7, &l___private_Lean_Shell_0__Lean_versionHeader___closed__7_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader(void) {
_start:
{
lean_object* x_1; lean_object* x_11; lean_object* x_18; uint8_t x_19; 
x_18 = l___private_Lean_Shell_0__Lean_shortVersionString;
x_19 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__6, &l___private_Lean_Shell_0__Lean_versionHeader___closed__6_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__8, &l___private_Lean_Shell_0__Lean_versionHeader___closed__8_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8);
x_11 = x_20;
goto block_17;
}
else
{
x_11 = x_18;
goto block_17;
}
block_10:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__0));
x_3 = lean_string_append(x_2, x_1);
lean_dec_ref(x_1);
x_4 = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__1));
x_5 = lean_string_append(x_3, x_4);
x_6 = lean_obj_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__2, &l___private_Lean_Shell_0__Lean_versionHeader___closed__2_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2);
x_7 = lean_string_append(x_5, x_6);
x_8 = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__3));
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
block_17:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_githash;
x_13 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_versionHeader___closed__4, &l___private_Lean_Shell_0__Lean_versionHeader___closed__4_once, _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = ((lean_object*)(l___private_Lean_Shell_0__Lean_versionHeader___closed__5));
x_15 = lean_string_append(x_11, x_14);
x_16 = lean_string_append(x_15, x_12);
x_1 = x_16;
goto block_10;
}
else
{
x_1 = x_11;
goto block_10;
}
}
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_featuresString___closed__0(void) {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_has_llvm_backend(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_featuresString(void) {
_start:
{
uint8_t x_1; 
x_1 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_featuresString___closed__0, &l___private_Lean_Shell_0__Lean_featuresString___closed__0_once, _init_l___private_Lean_Shell_0__Lean_featuresString___closed__0);
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l___private_Lean_Shell_0__Lean_featuresString___closed__1));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = ((lean_object*)(l___private_Lean_Shell_0__Lean_featuresString___closed__2));
return x_3;
}
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12(void) {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_is_debug(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36(void) {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_is_multi_thread(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp(uint8_t x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_36; lean_object* x_37; 
if (x_1 == 0)
{
lean_object* x_94; 
x_94 = lean_get_stdout();
x_36 = x_94;
x_37 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_95; 
x_95 = lean_get_stderr();
x_36 = x_95;
x_37 = lean_box(0);
goto block_93;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__0));
x_6 = l_IO_FS_Stream_putStrLn(x_3, x_5);
return x_6;
}
block_35:
{
lean_object* x_10; lean_object* x_11; 
x_10 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__1));
lean_inc_ref(x_8);
x_11 = l_IO_FS_Stream_putStrLn(x_8, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_11);
x_12 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__2));
lean_inc_ref(x_8);
x_13 = l_IO_FS_Stream_putStrLn(x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_13);
x_14 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__3));
lean_inc_ref(x_8);
x_15 = l_IO_FS_Stream_putStrLn(x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_15);
x_16 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__4));
lean_inc_ref(x_8);
x_17 = l_IO_FS_Stream_putStrLn(x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_17);
x_18 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__5));
lean_inc_ref(x_8);
x_19 = l_IO_FS_Stream_putStrLn(x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_19);
x_20 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__6));
lean_inc_ref(x_8);
x_21 = l_IO_FS_Stream_putStrLn(x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_21);
x_22 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__7));
lean_inc_ref(x_8);
x_23 = l_IO_FS_Stream_putStrLn(x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_23);
x_24 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__8));
lean_inc_ref(x_8);
x_25 = l_IO_FS_Stream_putStrLn(x_8, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_25);
x_26 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__9));
lean_inc_ref(x_8);
x_27 = l_IO_FS_Stream_putStrLn(x_8, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_27);
x_28 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__10));
lean_inc_ref(x_8);
x_29 = l_IO_FS_Stream_putStrLn(x_8, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_29);
x_30 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__11));
lean_inc_ref(x_8);
x_31 = l_IO_FS_Stream_putStrLn(x_8, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec_ref(x_31);
x_32 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__12, &l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12);
if (x_32 == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto block_7;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__13));
lean_inc_ref(x_8);
x_34 = l_IO_FS_Stream_putStrLn(x_8, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_dec_ref(x_34);
x_3 = x_8;
x_4 = lean_box(0);
goto block_7;
}
else
{
lean_dec_ref(x_8);
return x_34;
}
}
}
else
{
lean_dec_ref(x_8);
return x_31;
}
}
else
{
lean_dec_ref(x_8);
return x_29;
}
}
else
{
lean_dec_ref(x_8);
return x_27;
}
}
else
{
lean_dec_ref(x_8);
return x_25;
}
}
else
{
lean_dec_ref(x_8);
return x_23;
}
}
else
{
lean_dec_ref(x_8);
return x_21;
}
}
else
{
lean_dec_ref(x_8);
return x_19;
}
}
else
{
lean_dec_ref(x_8);
return x_17;
}
}
else
{
lean_dec_ref(x_8);
return x_15;
}
}
else
{
lean_dec_ref(x_8);
return x_13;
}
}
else
{
lean_dec_ref(x_8);
return x_11;
}
}
block_93:
{
lean_object* x_38; lean_object* x_39; 
x_38 = l___private_Lean_Shell_0__Lean_versionHeader;
lean_inc_ref(x_36);
x_39 = l_IO_FS_Stream_putStrLn(x_36, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_39);
x_40 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__14));
lean_inc_ref(x_36);
x_41 = l_IO_FS_Stream_putStrLn(x_36, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_41);
x_42 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__15));
lean_inc_ref(x_36);
x_43 = l_IO_FS_Stream_putStrLn(x_36, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_43);
x_44 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__16));
lean_inc_ref(x_36);
x_45 = l_IO_FS_Stream_putStrLn(x_36, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_45);
x_46 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__17));
lean_inc_ref(x_36);
x_47 = l_IO_FS_Stream_putStrLn(x_36, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_47);
x_48 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__18));
lean_inc_ref(x_36);
x_49 = l_IO_FS_Stream_putStrLn(x_36, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_49);
x_50 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__19));
lean_inc_ref(x_36);
x_51 = l_IO_FS_Stream_putStrLn(x_36, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_51);
x_52 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__20));
lean_inc_ref(x_36);
x_53 = l_IO_FS_Stream_putStrLn(x_36, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_53);
x_54 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__21));
lean_inc_ref(x_36);
x_55 = l_IO_FS_Stream_putStrLn(x_36, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_55);
x_56 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__22));
lean_inc_ref(x_36);
x_57 = l_IO_FS_Stream_putStrLn(x_36, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_57);
x_58 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__23));
lean_inc_ref(x_36);
x_59 = l_IO_FS_Stream_putStrLn(x_36, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_59);
x_60 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__24));
lean_inc_ref(x_36);
x_61 = l_IO_FS_Stream_putStrLn(x_36, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_61);
x_62 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__25));
lean_inc_ref(x_36);
x_63 = l_IO_FS_Stream_putStrLn(x_36, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_63);
x_64 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__26));
lean_inc_ref(x_36);
x_65 = l_IO_FS_Stream_putStrLn(x_36, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_65);
x_66 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__27));
lean_inc_ref(x_36);
x_67 = l_IO_FS_Stream_putStrLn(x_36, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_67);
x_68 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__28));
lean_inc_ref(x_36);
x_69 = l_IO_FS_Stream_putStrLn(x_36, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_69);
x_70 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__29));
lean_inc_ref(x_36);
x_71 = l_IO_FS_Stream_putStrLn(x_36, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_71);
x_72 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__30));
lean_inc_ref(x_36);
x_73 = l_IO_FS_Stream_putStrLn(x_36, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_73);
x_74 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__31));
lean_inc_ref(x_36);
x_75 = l_IO_FS_Stream_putStrLn(x_36, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_75);
x_76 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__32));
lean_inc_ref(x_36);
x_77 = l_IO_FS_Stream_putStrLn(x_36, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_77);
x_78 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__33));
lean_inc_ref(x_36);
x_79 = l_IO_FS_Stream_putStrLn(x_36, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_79);
x_80 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__34));
lean_inc_ref(x_36);
x_81 = l_IO_FS_Stream_putStrLn(x_36, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_81);
x_82 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__35));
lean_inc_ref(x_36);
x_83 = l_IO_FS_Stream_putStrLn(x_36, x_82);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
lean_dec_ref(x_83);
x_84 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__36, &l___private_Lean_Shell_0__Lean_displayHelp___closed__36_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36);
if (x_84 == 0)
{
x_8 = x_36;
x_9 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__37));
lean_inc_ref(x_36);
x_86 = l_IO_FS_Stream_putStrLn(x_36, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_86);
x_87 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__38));
lean_inc_ref(x_36);
x_88 = l_IO_FS_Stream_putStrLn(x_36, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_88);
x_89 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__39));
lean_inc_ref(x_36);
x_90 = l_IO_FS_Stream_putStrLn(x_36, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_90);
x_91 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__40));
lean_inc_ref(x_36);
x_92 = l_IO_FS_Stream_putStrLn(x_36, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_dec_ref(x_92);
x_8 = x_36;
x_9 = lean_box(0);
goto block_35;
}
else
{
lean_dec_ref(x_36);
return x_92;
}
}
else
{
lean_dec_ref(x_36);
return x_90;
}
}
else
{
lean_dec_ref(x_36);
return x_88;
}
}
else
{
lean_dec_ref(x_36);
return x_86;
}
}
}
else
{
lean_dec_ref(x_36);
return x_83;
}
}
else
{
lean_dec_ref(x_36);
return x_81;
}
}
else
{
lean_dec_ref(x_36);
return x_79;
}
}
else
{
lean_dec_ref(x_36);
return x_77;
}
}
else
{
lean_dec_ref(x_36);
return x_75;
}
}
else
{
lean_dec_ref(x_36);
return x_73;
}
}
else
{
lean_dec_ref(x_36);
return x_71;
}
}
else
{
lean_dec_ref(x_36);
return x_69;
}
}
else
{
lean_dec_ref(x_36);
return x_67;
}
}
else
{
lean_dec_ref(x_36);
return x_65;
}
}
else
{
lean_dec_ref(x_36);
return x_63;
}
}
else
{
lean_dec_ref(x_36);
return x_61;
}
}
else
{
lean_dec_ref(x_36);
return x_59;
}
}
else
{
lean_dec_ref(x_36);
return x_57;
}
}
else
{
lean_dec_ref(x_36);
return x_55;
}
}
else
{
lean_dec_ref(x_36);
return x_53;
}
}
else
{
lean_dec_ref(x_36);
return x_51;
}
}
else
{
lean_dec_ref(x_36);
return x_49;
}
}
else
{
lean_dec_ref(x_36);
return x_47;
}
}
else
{
lean_dec_ref(x_36);
return x_45;
}
}
else
{
lean_dec_ref(x_36);
return x_43;
}
}
else
{
lean_dec_ref(x_36);
return x_41;
}
}
else
{
lean_dec_ref(x_36);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l___private_Lean_Shell_0__Lean_displayHelp(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_ShellComponent_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Lean_Shell_0__Lean_ShellComponent_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l___private_Lean_Shell_0__Lean_ShellComponent_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lean_Shell_0__Lean_ShellComponent_frontend_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lean_Shell_0__Lean_ShellComponent_watchdog_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lean_Shell_0__Lean_ShellComponent_worker_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_32; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
x_7 = x_2;
x_8 = x_32;
goto block_31;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_5);
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_6);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
x_12 = x_11;
x_13 = x_21;
goto block_20;
}
else
{
lean_dec(x_11);
x_12 = lean_box(0);
x_13 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_14; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_5);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_del_object(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_23 = lean_ctor_get(x_11, 0);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
x_24 = x_11;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_get_default_max_memory(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
x_2 = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
x_3 = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_);
x_4 = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__13_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_));
x_5 = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_get_default_max_heartbeat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
x_2 = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
x_3 = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_);
x_4 = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_));
x_5 = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_33; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
x_7 = x_2;
x_8 = x_33;
goto block_32;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_ctor(1, 0, 1);
x_10 = lean_unbox(x_5);
lean_ctor_set_uint8(x_9, 0, x_10);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_6);
lean_inc(x_1);
x_12 = lean_register_option(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
x_13 = x_12;
x_14 = x_22;
goto block_21;
}
else
{
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_15; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 0, x_1);
x_15 = x_7;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_5);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_del_object(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_24 = lean_ctor_get(x_12, 0);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
x_25 = x_12;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(x_1, x_2, x_3);
return x_5;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_get_default_verbose(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0));
x_2 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__2_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__1_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
x_3 = lean_obj_once(&l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_, &l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__once, _init_l___private_Lean_Shell_0__Lean_initFn___closed__3_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_);
x_4 = ((lean_object*)(l___private_Lean_Shell_0__Lean_initFn___closed__4_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_));
x_5 = l_Lean_Option_register___at___00__private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getDefaultOptions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_internal_get_default_options(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBelieverTrustLevel___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_internal_get_believer_trust_level(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_get_believer_trust_level(x_1);
return x_2;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1(void) {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 1;
x_2 = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__0);
x_3 = lean_uint32_add(x_2, x_1);
return x_3;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel(void) {
_start:
{
uint32_t x_1; 
x_1 = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1, &l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1_once, _init_l___private_Lean_Shell_0__Lean_defaultTrustLevel___closed__1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getHardwareCurrency___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_internal_get_hardware_concurrency(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_get_hardware_concurrency(x_1);
return x_2;
}
}
static uint32_t _init_l___private_Lean_Shell_0__Lean_defaultNumThreads(void) {
_start:
{
uint8_t x_1; 
x_1 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__36, &l___private_Lean_Shell_0__Lean_displayHelp___closed__36_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36);
if (x_1 == 0)
{
uint32_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint32_t x_3; 
x_3 = lean_uint32_once(&l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0, &l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0_once, _init_l___private_Lean_Shell_0__Lean_defaultNumThreads___closed__0);
return x_3;
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_get_default_options(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2(void) {
_start:
{
lean_object* x_1; uint32_t x_2; uint32_t x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Shell_0__Lean_defaultNumThreads;
x_3 = l___private_Lean_Shell_0__Lean_defaultTrustLevel;
x_4 = l_Lean_Options_empty;
x_5 = 0;
x_6 = 0;
x_7 = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1));
x_8 = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__0);
x_9 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_1);
lean_ctor_set(x_9, 4, x_1);
lean_ctor_set(x_9, 5, x_1);
lean_ctor_set(x_9, 6, x_1);
lean_ctor_set(x_9, 7, x_1);
lean_ctor_set(x_9, 8, x_1);
lean_ctor_set(x_9, 9, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*10 + 8, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*10 + 9, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*10 + 10, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*10 + 11, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*10 + 12, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*10 + 13, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*10 + 14, x_5);
lean_ctor_set_uint32(x_9, sizeof(void*)*10, x_3);
lean_ctor_set_uint32(x_9, sizeof(void*)*10 + 4, x_2);
lean_ctor_set_uint8(x_9, sizeof(void*)*10 + 15, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*10 + 16, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*10 + 17, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* lean_shell_options_mk(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2, &l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2_once, _init_l___private_Lean_Shell_0__Lean_mkShellOptions___closed__2);
return x_2;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_run(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getRun___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_shell_options_get_run(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_shell_options_get_profiler(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_profiler;
x_4 = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_ShellOptions_getProfiler_spec__0(x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getProfiler___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_shell_options_get_profiler(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t lean_shell_options_get_num_threads(lean_object* x_1) {
_start:
{
uint32_t x_2; 
x_2 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_getNumThreads___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_shell_options_get_num_threads(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
x_5 = x_2;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 0);
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_12 = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__0));
x_13 = lean_string_append(x_12, x_1);
x_14 = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_checkOptArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_19; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_6 = x_1;
x_7 = x_19;
goto block_18;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
lean_inc(x_2);
x_9 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_8, x_4);
if (x_5 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
x_11 = l_Lean_Name_isPrefixOf(x_10, x_2);
lean_dec(x_2);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_12 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_9);
x_12 = x_14;
goto block_13;
}
block_13:
{
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_15 = x_6;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_5);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; 
lean_dec(x_4);
x_9 = 61;
x_10 = lean_string_utf8_get_fast(x_2, x_3);
x_11 = lean_uint32_dec_eq(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_3);
return x_15;
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_string_utf8_byte_size(x_2);
lean_inc_ref(x_2);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_box(0);
x_40 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(x_38, x_2, x_36, x_39);
lean_dec_ref(x_38);
if (lean_obj_tag(x_40) == 0)
{
x_4 = x_37;
goto block_35;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_4 = x_41;
goto block_35;
}
block_35:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_getOptionDecls();
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_24; 
x_8 = lean_ctor_get(x_7, 0);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
x_9 = x_7;
x_10 = x_24;
goto block_23;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
lean_inc_ref(x_2);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_4);
x_13 = lean_string_utf8_next_fast(x_2, x_4);
lean_dec(x_4);
x_14 = l_String_Slice_toName(x_12);
lean_dec_ref(x_12);
x_15 = lean_string_utf8_extract(x_2, x_13, x_5);
lean_dec_ref(x_2);
x_16 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_8, x_14);
lean_dec(x_8);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; 
lean_del_object(x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Language_Lean_setOption(x_1, x_17, x_14, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
x_19 = l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0(x_1, x_14, x_15);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_19);
x_20 = x_9;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_25 = lean_ctor_get(x_7, 0);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
x_26 = x_7;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l___private_Lean_Shell_0__Lean_setConfigOption___closed__1));
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_setConfigOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Shell_0__Lean_setConfigOption(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___redArg(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_4 = l_IO_eprint___redArg(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_12; 
x_5 = lean_ctor_get(x_4, 0);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
x_6 = x_4;
x_7 = x_12;
goto block_11;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_8; 
if (x_7 == 0)
{
x_8 = x_6;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_4, 0);
lean_dec(x_21);
x_13 = x_4;
x_14 = x_20;
goto block_19;
}
else
{
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_7; lean_object* x_12; 
x_12 = lean_apply_1(x_1, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
x_14 = x_12;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec_ref(x_12);
x_27 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_28 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_29 = l_IO_eprint___redArg(x_28, x_27);
lean_dec_ref(x_29);
x_22 = lean_box(0);
goto block_26;
block_26:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_io_error_to_string(x_21);
x_24 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_25 = l_IO_eprint___redArg(x_24, x_23);
lean_dec_ref(x_25);
x_7 = lean_box(0);
goto block_11;
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_9 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_10 = l_IO_eprint___redArg(x_9, x_8);
lean_dec_ref(x_10);
x_3 = lean_box(0);
goto block_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_13; 
x_13 = lean_apply_1(x_2, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
x_15 = x_13;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec_ref(x_13);
x_28 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_29 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_30 = l_IO_eprint___redArg(x_29, x_28);
lean_dec_ref(x_30);
x_23 = lean_box(0);
goto block_27;
block_27:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_io_error_to_string(x_22);
x_25 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_26 = l_IO_eprint___redArg(x_25, x_24);
lean_dec_ref(x_26);
x_8 = lean_box(0);
goto block_12;
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_10 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_11 = l_IO_eprint___redArg(x_10, x_9);
lean_dec_ref(x_11);
x_4 = lean_box(0);
goto block_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0));
x_8 = lean_string_append(x_7, x_1);
x_9 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
x_10 = lean_string_append(x_8, x_9);
x_11 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_12 = l_IO_eprint___redArg(x_11, x_10);
lean_dec_ref(x_12);
x_3 = lean_box(0);
goto block_6;
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0));
x_8 = lean_string_append(x_7, x_1);
x_9 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1));
x_10 = lean_string_append(x_8, x_9);
x_11 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_12 = l_IO_eprint___redArg(x_11, x_10);
lean_dec_ref(x_12);
x_3 = lean_box(0);
goto block_6;
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stderr();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stdout();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_19; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_6 = x_1;
x_7 = x_19;
goto block_18;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_8, 0, x_3);
lean_inc(x_2);
x_9 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_8, x_4);
if (x_5 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
x_11 = l_Lean_Name_isPrefixOf(x_10, x_2);
lean_dec(x_2);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_12 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_9);
x_12 = x_14;
goto block_13;
}
block_13:
{
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_15 = x_6;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_5);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1_spec__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_19; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_6 = x_1;
x_7 = x_19;
goto block_18;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_3);
lean_inc(x_2);
x_9 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_8, x_4);
if (x_5 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Shell_0__Lean_setConfigOption_spec__0___closed__1));
x_11 = l_Lean_Name_isPrefixOf(x_10, x_2);
lean_dec(x_2);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_12 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_9);
x_12 = x_14;
goto block_13;
}
block_13:
{
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_15 = x_6;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_5);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2_spec__3(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_Platform_numBits;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_pow(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_shell_options_process(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_9; lean_object* x_13; lean_object* x_17; lean_object* x_21; lean_object* x_25; lean_object* x_29; lean_object* x_33; lean_object* x_37; lean_object* x_41; lean_object* x_45; lean_object* x_49; lean_object* x_53; lean_object* x_57; lean_object* x_61; lean_object* x_65; lean_object* x_69; lean_object* x_73; lean_object* x_77; lean_object* x_81; lean_object* x_85; lean_object* x_89; lean_object* x_93; lean_object* x_97; lean_object* x_101; lean_object* x_105; lean_object* x_109; lean_object* x_113; lean_object* x_117; lean_object* x_121; lean_object* x_125; lean_object* x_129; lean_object* x_133; lean_object* x_137; lean_object* x_138; lean_object* x_142; lean_object* x_158; lean_object* x_162; lean_object* x_166; lean_object* x_170; lean_object* x_174; lean_object* x_178; lean_object* x_182; lean_object* x_186; lean_object* x_190; lean_object* x_194; lean_object* x_198; lean_object* x_202; lean_object* x_206; lean_object* x_210; lean_object* x_214; lean_object* x_218; lean_object* x_222; lean_object* x_226; lean_object* x_230; lean_object* x_234; lean_object* x_238; lean_object* x_242; lean_object* x_246; lean_object* x_250; lean_object* x_254; lean_object* x_258; uint32_t x_262; uint8_t x_263; 
x_262 = 101;
x_263 = lean_uint32_dec_eq(x_2, x_262);
if (x_263 == 0)
{
uint32_t x_264; uint8_t x_265; 
x_264 = 106;
x_265 = lean_uint32_dec_eq(x_2, x_264);
if (x_265 == 0)
{
uint32_t x_266; uint8_t x_267; 
x_266 = 118;
x_267 = lean_uint32_dec_eq(x_2, x_266);
if (x_267 == 0)
{
uint32_t x_268; uint8_t x_269; 
x_268 = 86;
x_269 = lean_uint32_dec_eq(x_2, x_268);
if (x_269 == 0)
{
uint32_t x_270; uint8_t x_271; 
x_270 = 103;
x_271 = lean_uint32_dec_eq(x_2, x_270);
if (x_271 == 0)
{
uint32_t x_272; uint8_t x_273; 
x_272 = 104;
x_273 = lean_uint32_dec_eq(x_2, x_272);
if (x_273 == 0)
{
uint32_t x_274; uint8_t x_275; 
x_274 = 102;
x_275 = lean_uint32_dec_eq(x_2, x_274);
if (x_275 == 0)
{
uint32_t x_276; uint8_t x_277; 
x_276 = 99;
x_277 = lean_uint32_dec_eq(x_2, x_276);
if (x_277 == 0)
{
uint32_t x_278; uint8_t x_279; 
x_278 = 98;
x_279 = lean_uint32_dec_eq(x_2, x_278);
if (x_279 == 0)
{
uint32_t x_280; uint8_t x_281; 
x_280 = 115;
x_281 = lean_uint32_dec_eq(x_2, x_280);
if (x_281 == 0)
{
uint32_t x_282; uint8_t x_283; 
x_282 = 73;
x_283 = lean_uint32_dec_eq(x_2, x_282);
if (x_283 == 0)
{
uint32_t x_284; uint8_t x_285; 
x_284 = 114;
x_285 = lean_uint32_dec_eq(x_2, x_284);
if (x_285 == 0)
{
uint32_t x_286; uint8_t x_287; 
x_286 = 111;
x_287 = lean_uint32_dec_eq(x_2, x_286);
if (x_287 == 0)
{
uint32_t x_288; uint8_t x_289; 
x_288 = 105;
x_289 = lean_uint32_dec_eq(x_2, x_288);
if (x_289 == 0)
{
uint32_t x_290; uint8_t x_291; 
x_290 = 82;
x_291 = lean_uint32_dec_eq(x_2, x_290);
if (x_291 == 0)
{
uint32_t x_292; uint8_t x_293; 
x_292 = 77;
x_293 = lean_uint32_dec_eq(x_2, x_292);
if (x_293 == 0)
{
uint32_t x_294; uint8_t x_295; 
x_294 = 84;
x_295 = lean_uint32_dec_eq(x_2, x_294);
if (x_295 == 0)
{
uint32_t x_296; uint8_t x_297; 
x_296 = 116;
x_297 = lean_uint32_dec_eq(x_2, x_296);
if (x_297 == 0)
{
uint32_t x_298; uint8_t x_299; 
x_298 = 113;
x_299 = lean_uint32_dec_eq(x_2, x_298);
if (x_299 == 0)
{
uint32_t x_300; uint8_t x_301; 
x_300 = 100;
x_301 = lean_uint32_dec_eq(x_2, x_300);
if (x_301 == 0)
{
uint32_t x_302; uint8_t x_303; 
x_302 = 79;
x_303 = lean_uint32_dec_eq(x_2, x_302);
if (x_303 == 0)
{
uint32_t x_304; uint8_t x_305; 
x_304 = 78;
x_305 = lean_uint32_dec_eq(x_2, x_304);
if (x_305 == 0)
{
uint32_t x_306; uint8_t x_307; 
x_306 = 74;
x_307 = lean_uint32_dec_eq(x_2, x_306);
if (x_307 == 0)
{
uint32_t x_308; uint8_t x_309; 
x_308 = 97;
x_309 = lean_uint32_dec_eq(x_2, x_308);
if (x_309 == 0)
{
uint32_t x_310; uint8_t x_311; 
x_310 = 120;
x_311 = lean_uint32_dec_eq(x_2, x_310);
if (x_311 == 0)
{
uint32_t x_312; uint8_t x_313; 
x_312 = 76;
x_313 = lean_uint32_dec_eq(x_2, x_312);
if (x_313 == 0)
{
uint32_t x_314; uint8_t x_315; 
x_314 = 68;
x_315 = lean_uint32_dec_eq(x_2, x_314);
if (x_315 == 0)
{
uint32_t x_316; uint8_t x_317; 
x_316 = 83;
x_317 = lean_uint32_dec_eq(x_2, x_316);
if (x_317 == 0)
{
uint32_t x_318; uint8_t x_319; 
x_318 = 87;
x_319 = lean_uint32_dec_eq(x_2, x_318);
if (x_319 == 0)
{
uint32_t x_320; uint8_t x_321; 
x_320 = 80;
x_321 = lean_uint32_dec_eq(x_2, x_320);
if (x_321 == 0)
{
uint32_t x_322; uint8_t x_323; 
x_322 = 66;
x_323 = lean_uint32_dec_eq(x_2, x_322);
if (x_323 == 0)
{
uint32_t x_324; uint8_t x_325; 
x_324 = 112;
x_325 = lean_uint32_dec_eq(x_2, x_324);
if (x_325 == 0)
{
uint32_t x_326; uint8_t x_327; 
x_326 = 108;
x_327 = lean_uint32_dec_eq(x_2, x_326);
if (x_327 == 0)
{
uint32_t x_328; uint8_t x_329; 
x_328 = 117;
x_329 = lean_uint32_dec_eq(x_2, x_328);
if (x_329 == 0)
{
uint32_t x_330; uint8_t x_331; 
x_330 = 69;
x_331 = lean_uint32_dec_eq(x_2, x_330);
if (x_331 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
x_158 = lean_box(0);
goto block_161;
}
else
{
lean_object* x_332; lean_object* x_333; 
x_332 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
x_333 = l___private_Lean_Shell_0__Lean_checkOptArg(x_332, x_3);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; uint8_t x_336; uint8_t x_372; 
x_334 = lean_ctor_get(x_333, 0);
x_372 = !lean_is_exclusive(x_333);
if (x_372 == 0)
{
x_335 = x_333;
x_336 = x_372;
goto block_371;
}
else
{
lean_inc(x_334);
lean_dec(x_333);
x_335 = lean_box(0);
x_336 = x_372;
goto block_371;
}
block_371:
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; uint8_t x_340; uint8_t x_341; uint8_t x_342; uint8_t x_343; uint8_t x_344; uint8_t x_345; lean_object* x_346; uint32_t x_347; uint32_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; uint8_t x_357; uint8_t x_358; lean_object* x_359; uint8_t x_360; uint8_t x_370; 
x_337 = lean_ctor_get(x_1, 0);
x_338 = lean_ctor_get(x_1, 1);
x_339 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_340 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_341 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_342 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_343 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_344 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_345 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_346 = lean_ctor_get(x_1, 2);
x_347 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_348 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_349 = lean_ctor_get(x_1, 3);
x_350 = lean_ctor_get(x_1, 4);
x_351 = lean_ctor_get(x_1, 5);
x_352 = lean_ctor_get(x_1, 6);
x_353 = lean_ctor_get(x_1, 7);
x_354 = lean_ctor_get(x_1, 8);
x_355 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_356 = lean_ctor_get(x_1, 9);
x_357 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_358 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_370 = !lean_is_exclusive(x_1);
if (x_370 == 0)
{
x_359 = x_1;
x_360 = x_370;
goto block_369;
}
else
{
lean_inc(x_356);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_346);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_1);
x_359 = lean_box(0);
x_360 = x_370;
goto block_369;
}
block_369:
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = l_String_toName(x_334);
x_362 = lean_array_push(x_356, x_361);
if (x_360 == 0)
{
lean_ctor_set(x_359, 9, x_362);
x_363 = x_359;
goto block_367;
}
else
{
lean_object* x_368; 
x_368 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_368, 0, x_337);
lean_ctor_set(x_368, 1, x_338);
lean_ctor_set(x_368, 2, x_346);
lean_ctor_set(x_368, 3, x_349);
lean_ctor_set(x_368, 4, x_350);
lean_ctor_set(x_368, 5, x_351);
lean_ctor_set(x_368, 6, x_352);
lean_ctor_set(x_368, 7, x_353);
lean_ctor_set(x_368, 8, x_354);
lean_ctor_set(x_368, 9, x_362);
lean_ctor_set_uint8(x_368, sizeof(void*)*10 + 8, x_339);
lean_ctor_set_uint8(x_368, sizeof(void*)*10 + 9, x_340);
lean_ctor_set_uint8(x_368, sizeof(void*)*10 + 10, x_341);
lean_ctor_set_uint8(x_368, sizeof(void*)*10 + 11, x_342);
lean_ctor_set_uint8(x_368, sizeof(void*)*10 + 12, x_343);
lean_ctor_set_uint8(x_368, sizeof(void*)*10 + 13, x_344);
lean_ctor_set_uint8(x_368, sizeof(void*)*10 + 14, x_345);
lean_ctor_set_uint32(x_368, sizeof(void*)*10, x_347);
lean_ctor_set_uint32(x_368, sizeof(void*)*10 + 4, x_348);
lean_ctor_set_uint8(x_368, sizeof(void*)*10 + 15, x_355);
lean_ctor_set_uint8(x_368, sizeof(void*)*10 + 16, x_357);
lean_ctor_set_uint8(x_368, sizeof(void*)*10 + 17, x_358);
x_363 = x_368;
goto block_367;
}
block_367:
{
lean_object* x_364; 
if (x_336 == 0)
{
lean_ctor_set(x_335, 0, x_363);
x_364 = x_335;
goto block_365;
}
else
{
lean_object* x_366; 
x_366 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_366, 0, x_363);
x_364 = x_366;
goto block_365;
}
block_365:
{
return x_364;
}
}
}
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_378; lean_object* x_379; 
lean_dec_ref(x_1);
x_373 = lean_ctor_get(x_333, 0);
lean_inc(x_373);
lean_dec_ref(x_333);
x_378 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_379 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_378);
lean_dec_ref(x_379);
x_374 = lean_box(0);
goto block_377;
block_377:
{
lean_object* x_375; lean_object* x_376; 
x_375 = lean_io_error_to_string(x_373);
x_376 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_375);
lean_dec_ref(x_376);
x_166 = lean_box(0);
goto block_169;
}
}
}
}
else
{
lean_object* x_380; lean_object* x_381; 
x_380 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
x_381 = l___private_Lean_Shell_0__Lean_checkOptArg(x_380, x_3);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; uint8_t x_384; uint8_t x_419; 
x_382 = lean_ctor_get(x_381, 0);
x_419 = !lean_is_exclusive(x_381);
if (x_419 == 0)
{
x_383 = x_381;
x_384 = x_419;
goto block_418;
}
else
{
lean_inc(x_382);
lean_dec(x_381);
x_383 = lean_box(0);
x_384 = x_419;
goto block_418;
}
block_418:
{
lean_object* x_385; lean_object* x_386; uint8_t x_387; uint8_t x_388; uint8_t x_389; uint8_t x_390; uint8_t x_391; uint8_t x_392; uint8_t x_393; lean_object* x_394; uint32_t x_395; uint32_t x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; uint8_t x_404; uint8_t x_405; lean_object* x_406; uint8_t x_407; uint8_t x_416; 
x_385 = lean_ctor_get(x_1, 0);
x_386 = lean_ctor_get(x_1, 1);
x_387 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_388 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_389 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_390 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_391 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_392 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_393 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_394 = lean_ctor_get(x_1, 2);
x_395 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_396 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_397 = lean_ctor_get(x_1, 3);
x_398 = lean_ctor_get(x_1, 5);
x_399 = lean_ctor_get(x_1, 6);
x_400 = lean_ctor_get(x_1, 7);
x_401 = lean_ctor_get(x_1, 8);
x_402 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_403 = lean_ctor_get(x_1, 9);
x_404 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_405 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_416 = !lean_is_exclusive(x_1);
if (x_416 == 0)
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_1, 4);
lean_dec(x_417);
x_406 = x_1;
x_407 = x_416;
goto block_415;
}
else
{
lean_inc(x_403);
lean_inc(x_401);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_397);
lean_inc(x_394);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_1);
x_406 = lean_box(0);
x_407 = x_416;
goto block_415;
}
block_415:
{
lean_object* x_408; lean_object* x_409; 
x_408 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_408, 0, x_382);
if (x_407 == 0)
{
lean_ctor_set(x_406, 4, x_408);
x_409 = x_406;
goto block_413;
}
else
{
lean_object* x_414; 
x_414 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_414, 0, x_385);
lean_ctor_set(x_414, 1, x_386);
lean_ctor_set(x_414, 2, x_394);
lean_ctor_set(x_414, 3, x_397);
lean_ctor_set(x_414, 4, x_408);
lean_ctor_set(x_414, 5, x_398);
lean_ctor_set(x_414, 6, x_399);
lean_ctor_set(x_414, 7, x_400);
lean_ctor_set(x_414, 8, x_401);
lean_ctor_set(x_414, 9, x_403);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 8, x_387);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 9, x_388);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 10, x_389);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 11, x_390);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 12, x_391);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 13, x_392);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 14, x_393);
lean_ctor_set_uint32(x_414, sizeof(void*)*10, x_395);
lean_ctor_set_uint32(x_414, sizeof(void*)*10 + 4, x_396);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 15, x_402);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 16, x_404);
lean_ctor_set_uint8(x_414, sizeof(void*)*10 + 17, x_405);
x_409 = x_414;
goto block_413;
}
block_413:
{
lean_object* x_410; 
if (x_384 == 0)
{
lean_ctor_set(x_383, 0, x_409);
x_410 = x_383;
goto block_411;
}
else
{
lean_object* x_412; 
x_412 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_412, 0, x_409);
x_410 = x_412;
goto block_411;
}
block_411:
{
return x_410;
}
}
}
}
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_425; lean_object* x_426; 
lean_dec_ref(x_1);
x_420 = lean_ctor_get(x_381, 0);
lean_inc(x_420);
lean_dec_ref(x_381);
x_425 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_426 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_425);
lean_dec_ref(x_426);
x_421 = lean_box(0);
goto block_424;
block_424:
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_io_error_to_string(x_420);
x_423 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_422);
lean_dec_ref(x_423);
x_125 = lean_box(0);
goto block_128;
}
}
}
}
else
{
lean_object* x_427; lean_object* x_428; 
x_427 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
x_428 = l___private_Lean_Shell_0__Lean_checkOptArg(x_427, x_3);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
lean_dec_ref(x_428);
lean_inc(x_429);
x_430 = lean_load_dynlib(x_429);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; uint8_t x_432; uint8_t x_469; 
x_469 = !lean_is_exclusive(x_430);
if (x_469 == 0)
{
lean_object* x_470; 
x_470 = lean_ctor_get(x_430, 0);
lean_dec(x_470);
x_431 = x_430;
x_432 = x_469;
goto block_468;
}
else
{
lean_dec(x_430);
x_431 = lean_box(0);
x_432 = x_469;
goto block_468;
}
block_468:
{
lean_object* x_433; lean_object* x_434; uint8_t x_435; uint8_t x_436; uint8_t x_437; uint8_t x_438; uint8_t x_439; uint8_t x_440; uint8_t x_441; lean_object* x_442; uint32_t x_443; uint32_t x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; uint8_t x_453; uint8_t x_454; lean_object* x_455; uint8_t x_456; uint8_t x_467; 
x_433 = lean_ctor_get(x_1, 0);
x_434 = lean_ctor_get(x_1, 1);
x_435 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_436 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_437 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_438 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_439 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_440 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_441 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_442 = lean_ctor_get(x_1, 2);
x_443 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_444 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_445 = lean_ctor_get(x_1, 3);
x_446 = lean_ctor_get(x_1, 4);
x_447 = lean_ctor_get(x_1, 5);
x_448 = lean_ctor_get(x_1, 6);
x_449 = lean_ctor_get(x_1, 7);
x_450 = lean_ctor_get(x_1, 8);
x_451 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_452 = lean_ctor_get(x_1, 9);
x_453 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_454 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_467 = !lean_is_exclusive(x_1);
if (x_467 == 0)
{
x_455 = x_1;
x_456 = x_467;
goto block_466;
}
else
{
lean_inc(x_452);
lean_inc(x_450);
lean_inc(x_449);
lean_inc(x_448);
lean_inc(x_447);
lean_inc(x_446);
lean_inc(x_445);
lean_inc(x_442);
lean_inc(x_434);
lean_inc(x_433);
lean_dec(x_1);
x_455 = lean_box(0);
x_456 = x_467;
goto block_466;
}
block_466:
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
x_458 = lean_string_append(x_457, x_429);
lean_dec(x_429);
x_459 = lean_array_push(x_434, x_458);
if (x_456 == 0)
{
lean_ctor_set(x_455, 1, x_459);
x_460 = x_455;
goto block_464;
}
else
{
lean_object* x_465; 
x_465 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_465, 0, x_433);
lean_ctor_set(x_465, 1, x_459);
lean_ctor_set(x_465, 2, x_442);
lean_ctor_set(x_465, 3, x_445);
lean_ctor_set(x_465, 4, x_446);
lean_ctor_set(x_465, 5, x_447);
lean_ctor_set(x_465, 6, x_448);
lean_ctor_set(x_465, 7, x_449);
lean_ctor_set(x_465, 8, x_450);
lean_ctor_set(x_465, 9, x_452);
lean_ctor_set_uint8(x_465, sizeof(void*)*10 + 8, x_435);
lean_ctor_set_uint8(x_465, sizeof(void*)*10 + 9, x_436);
lean_ctor_set_uint8(x_465, sizeof(void*)*10 + 10, x_437);
lean_ctor_set_uint8(x_465, sizeof(void*)*10 + 11, x_438);
lean_ctor_set_uint8(x_465, sizeof(void*)*10 + 12, x_439);
lean_ctor_set_uint8(x_465, sizeof(void*)*10 + 13, x_440);
lean_ctor_set_uint8(x_465, sizeof(void*)*10 + 14, x_441);
lean_ctor_set_uint32(x_465, sizeof(void*)*10, x_443);
lean_ctor_set_uint32(x_465, sizeof(void*)*10 + 4, x_444);
lean_ctor_set_uint8(x_465, sizeof(void*)*10 + 15, x_451);
lean_ctor_set_uint8(x_465, sizeof(void*)*10 + 16, x_453);
lean_ctor_set_uint8(x_465, sizeof(void*)*10 + 17, x_454);
x_460 = x_465;
goto block_464;
}
block_464:
{
lean_object* x_461; 
if (x_432 == 0)
{
lean_ctor_set(x_431, 0, x_460);
x_461 = x_431;
goto block_462;
}
else
{
lean_object* x_463; 
x_463 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_463, 0, x_460);
x_461 = x_463;
goto block_462;
}
block_462:
{
return x_461;
}
}
}
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_476; lean_object* x_477; 
lean_dec(x_429);
lean_dec_ref(x_1);
x_471 = lean_ctor_get(x_430, 0);
lean_inc(x_471);
lean_dec_ref(x_430);
x_476 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_477 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_476);
lean_dec_ref(x_477);
x_472 = lean_box(0);
goto block_475;
block_475:
{
lean_object* x_473; lean_object* x_474; 
x_473 = lean_io_error_to_string(x_471);
x_474 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_473);
lean_dec_ref(x_474);
x_174 = lean_box(0);
goto block_177;
}
}
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_483; lean_object* x_484; 
lean_dec_ref(x_1);
x_478 = lean_ctor_get(x_428, 0);
lean_inc(x_478);
lean_dec_ref(x_428);
x_483 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_484 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_483);
lean_dec_ref(x_484);
x_479 = lean_box(0);
goto block_482;
block_482:
{
lean_object* x_480; lean_object* x_481; 
x_480 = lean_io_error_to_string(x_478);
x_481 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_480);
lean_dec_ref(x_481);
x_117 = lean_box(0);
goto block_120;
}
}
}
}
else
{
lean_object* x_485; lean_object* x_486; 
x_485 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
x_486 = l___private_Lean_Shell_0__Lean_checkOptArg(x_485, x_3);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
lean_dec_ref(x_486);
lean_inc(x_487);
x_488 = lean_load_plugin(x_487);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; uint8_t x_490; uint8_t x_527; 
x_527 = !lean_is_exclusive(x_488);
if (x_527 == 0)
{
lean_object* x_528; 
x_528 = lean_ctor_get(x_488, 0);
lean_dec(x_528);
x_489 = x_488;
x_490 = x_527;
goto block_526;
}
else
{
lean_dec(x_488);
x_489 = lean_box(0);
x_490 = x_527;
goto block_526;
}
block_526:
{
lean_object* x_491; lean_object* x_492; uint8_t x_493; uint8_t x_494; uint8_t x_495; uint8_t x_496; uint8_t x_497; uint8_t x_498; uint8_t x_499; lean_object* x_500; uint32_t x_501; uint32_t x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; uint8_t x_511; uint8_t x_512; lean_object* x_513; uint8_t x_514; uint8_t x_525; 
x_491 = lean_ctor_get(x_1, 0);
x_492 = lean_ctor_get(x_1, 1);
x_493 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_494 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_495 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_496 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_497 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_498 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_499 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_500 = lean_ctor_get(x_1, 2);
x_501 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_502 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_503 = lean_ctor_get(x_1, 3);
x_504 = lean_ctor_get(x_1, 4);
x_505 = lean_ctor_get(x_1, 5);
x_506 = lean_ctor_get(x_1, 6);
x_507 = lean_ctor_get(x_1, 7);
x_508 = lean_ctor_get(x_1, 8);
x_509 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_510 = lean_ctor_get(x_1, 9);
x_511 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_512 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_525 = !lean_is_exclusive(x_1);
if (x_525 == 0)
{
x_513 = x_1;
x_514 = x_525;
goto block_524;
}
else
{
lean_inc(x_510);
lean_inc(x_508);
lean_inc(x_507);
lean_inc(x_506);
lean_inc(x_505);
lean_inc(x_504);
lean_inc(x_503);
lean_inc(x_500);
lean_inc(x_492);
lean_inc(x_491);
lean_dec(x_1);
x_513 = lean_box(0);
x_514 = x_525;
goto block_524;
}
block_524:
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_515 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
x_516 = lean_string_append(x_515, x_487);
lean_dec(x_487);
x_517 = lean_array_push(x_492, x_516);
if (x_514 == 0)
{
lean_ctor_set(x_513, 1, x_517);
x_518 = x_513;
goto block_522;
}
else
{
lean_object* x_523; 
x_523 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_523, 0, x_491);
lean_ctor_set(x_523, 1, x_517);
lean_ctor_set(x_523, 2, x_500);
lean_ctor_set(x_523, 3, x_503);
lean_ctor_set(x_523, 4, x_504);
lean_ctor_set(x_523, 5, x_505);
lean_ctor_set(x_523, 6, x_506);
lean_ctor_set(x_523, 7, x_507);
lean_ctor_set(x_523, 8, x_508);
lean_ctor_set(x_523, 9, x_510);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 8, x_493);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 9, x_494);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 10, x_495);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 11, x_496);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 12, x_497);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 13, x_498);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 14, x_499);
lean_ctor_set_uint32(x_523, sizeof(void*)*10, x_501);
lean_ctor_set_uint32(x_523, sizeof(void*)*10 + 4, x_502);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 15, x_509);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 16, x_511);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 17, x_512);
x_518 = x_523;
goto block_522;
}
block_522:
{
lean_object* x_519; 
if (x_490 == 0)
{
lean_ctor_set(x_489, 0, x_518);
x_519 = x_489;
goto block_520;
}
else
{
lean_object* x_521; 
x_521 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_521, 0, x_518);
x_519 = x_521;
goto block_520;
}
block_520:
{
return x_519;
}
}
}
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_534; lean_object* x_535; 
lean_dec(x_487);
lean_dec_ref(x_1);
x_529 = lean_ctor_get(x_488, 0);
lean_inc(x_529);
lean_dec_ref(x_488);
x_534 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_535 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_534);
lean_dec_ref(x_535);
x_530 = lean_box(0);
goto block_533;
block_533:
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_io_error_to_string(x_529);
x_532 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_531);
lean_dec_ref(x_532);
x_182 = lean_box(0);
goto block_185;
}
}
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_541; lean_object* x_542; 
lean_dec_ref(x_1);
x_536 = lean_ctor_get(x_486, 0);
lean_inc(x_536);
lean_dec_ref(x_486);
x_541 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_542 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_541);
lean_dec_ref(x_542);
x_537 = lean_box(0);
goto block_540;
block_540:
{
lean_object* x_538; lean_object* x_539; 
x_538 = lean_io_error_to_string(x_536);
x_539 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_538);
lean_dec_ref(x_539);
x_109 = lean_box(0);
goto block_112;
}
}
}
}
else
{
uint8_t x_543; 
x_543 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__12, &l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12);
if (x_543 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
x_158 = lean_box(0);
goto block_161;
}
else
{
lean_object* x_544; lean_object* x_545; 
x_544 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
x_545 = l___private_Lean_Shell_0__Lean_checkOptArg(x_544, x_3);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; uint8_t x_548; uint8_t x_554; 
x_546 = lean_ctor_get(x_545, 0);
x_554 = !lean_is_exclusive(x_545);
if (x_554 == 0)
{
x_547 = x_545;
x_548 = x_554;
goto block_553;
}
else
{
lean_inc(x_546);
lean_dec(x_545);
x_547 = lean_box(0);
x_548 = x_554;
goto block_553;
}
block_553:
{
lean_object* x_549; lean_object* x_550; 
x_549 = lean_internal_enable_debug(x_546);
lean_dec(x_546);
if (x_548 == 0)
{
lean_ctor_set(x_547, 0, x_1);
x_550 = x_547;
goto block_551;
}
else
{
lean_object* x_552; 
x_552 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_552, 0, x_1);
x_550 = x_552;
goto block_551;
}
block_551:
{
return x_550;
}
}
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_560; lean_object* x_561; 
lean_dec_ref(x_1);
x_555 = lean_ctor_get(x_545, 0);
lean_inc(x_555);
lean_dec_ref(x_545);
x_560 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_561 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_560);
lean_dec_ref(x_561);
x_556 = lean_box(0);
goto block_559;
block_559:
{
lean_object* x_557; lean_object* x_558; 
x_557 = lean_io_error_to_string(x_555);
x_558 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_557);
lean_dec_ref(x_558);
x_190 = lean_box(0);
goto block_193;
}
}
}
}
}
else
{
lean_object* x_562; lean_object* x_563; uint8_t x_564; uint8_t x_565; uint8_t x_566; uint8_t x_567; uint8_t x_568; uint8_t x_569; uint8_t x_570; lean_object* x_571; uint32_t x_572; uint32_t x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; uint8_t x_580; lean_object* x_581; uint8_t x_582; uint8_t x_583; lean_object* x_584; uint8_t x_585; uint8_t x_593; 
lean_dec(x_3);
x_562 = lean_ctor_get(x_1, 0);
x_563 = lean_ctor_get(x_1, 1);
x_564 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_565 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_566 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_567 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_568 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_569 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_570 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_571 = lean_ctor_get(x_1, 2);
x_572 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_573 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_574 = lean_ctor_get(x_1, 3);
x_575 = lean_ctor_get(x_1, 4);
x_576 = lean_ctor_get(x_1, 5);
x_577 = lean_ctor_get(x_1, 6);
x_578 = lean_ctor_get(x_1, 7);
x_579 = lean_ctor_get(x_1, 8);
x_580 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_581 = lean_ctor_get(x_1, 9);
x_582 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_583 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_593 = !lean_is_exclusive(x_1);
if (x_593 == 0)
{
x_584 = x_1;
x_585 = x_593;
goto block_592;
}
else
{
lean_inc(x_581);
lean_inc(x_579);
lean_inc(x_578);
lean_inc(x_577);
lean_inc(x_576);
lean_inc(x_575);
lean_inc(x_574);
lean_inc(x_571);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_1);
x_584 = lean_box(0);
x_585 = x_593;
goto block_592;
}
block_592:
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_586 = l_Lean_profiler;
x_587 = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(x_562, x_586, x_321);
if (x_585 == 0)
{
lean_ctor_set(x_584, 0, x_587);
x_588 = x_584;
goto block_590;
}
else
{
lean_object* x_591; 
x_591 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_591, 0, x_587);
lean_ctor_set(x_591, 1, x_563);
lean_ctor_set(x_591, 2, x_571);
lean_ctor_set(x_591, 3, x_574);
lean_ctor_set(x_591, 4, x_575);
lean_ctor_set(x_591, 5, x_576);
lean_ctor_set(x_591, 6, x_577);
lean_ctor_set(x_591, 7, x_578);
lean_ctor_set(x_591, 8, x_579);
lean_ctor_set(x_591, 9, x_581);
lean_ctor_set_uint8(x_591, sizeof(void*)*10 + 8, x_564);
lean_ctor_set_uint8(x_591, sizeof(void*)*10 + 9, x_565);
lean_ctor_set_uint8(x_591, sizeof(void*)*10 + 10, x_566);
lean_ctor_set_uint8(x_591, sizeof(void*)*10 + 11, x_567);
lean_ctor_set_uint8(x_591, sizeof(void*)*10 + 12, x_568);
lean_ctor_set_uint8(x_591, sizeof(void*)*10 + 13, x_569);
lean_ctor_set_uint8(x_591, sizeof(void*)*10 + 14, x_570);
lean_ctor_set_uint32(x_591, sizeof(void*)*10, x_572);
lean_ctor_set_uint32(x_591, sizeof(void*)*10 + 4, x_573);
lean_ctor_set_uint8(x_591, sizeof(void*)*10 + 15, x_580);
lean_ctor_set_uint8(x_591, sizeof(void*)*10 + 16, x_582);
lean_ctor_set_uint8(x_591, sizeof(void*)*10 + 17, x_583);
x_588 = x_591;
goto block_590;
}
block_590:
{
lean_object* x_589; 
x_589 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_589, 0, x_588);
return x_589;
}
}
}
}
else
{
lean_object* x_594; lean_object* x_595; uint8_t x_596; uint8_t x_597; uint8_t x_598; uint8_t x_599; uint8_t x_600; uint8_t x_601; lean_object* x_602; uint32_t x_603; uint32_t x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; uint8_t x_611; lean_object* x_612; uint8_t x_613; uint8_t x_614; lean_object* x_615; uint8_t x_616; uint8_t x_623; 
lean_dec(x_3);
x_594 = lean_ctor_get(x_1, 0);
x_595 = lean_ctor_get(x_1, 1);
x_596 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_597 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_598 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_599 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_600 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_601 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_602 = lean_ctor_get(x_1, 2);
x_603 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_604 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_605 = lean_ctor_get(x_1, 3);
x_606 = lean_ctor_get(x_1, 4);
x_607 = lean_ctor_get(x_1, 5);
x_608 = lean_ctor_get(x_1, 6);
x_609 = lean_ctor_get(x_1, 7);
x_610 = lean_ctor_get(x_1, 8);
x_611 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_612 = lean_ctor_get(x_1, 9);
x_613 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_614 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_623 = !lean_is_exclusive(x_1);
if (x_623 == 0)
{
x_615 = x_1;
x_616 = x_623;
goto block_622;
}
else
{
lean_inc(x_612);
lean_inc(x_610);
lean_inc(x_609);
lean_inc(x_608);
lean_inc(x_607);
lean_inc(x_606);
lean_inc(x_605);
lean_inc(x_602);
lean_inc(x_595);
lean_inc(x_594);
lean_dec(x_1);
x_615 = lean_box(0);
x_616 = x_623;
goto block_622;
}
block_622:
{
uint8_t x_617; lean_object* x_618; 
x_617 = 2;
if (x_616 == 0)
{
x_618 = x_615;
goto block_620;
}
else
{
lean_object* x_621; 
x_621 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_621, 0, x_594);
lean_ctor_set(x_621, 1, x_595);
lean_ctor_set(x_621, 2, x_602);
lean_ctor_set(x_621, 3, x_605);
lean_ctor_set(x_621, 4, x_606);
lean_ctor_set(x_621, 5, x_607);
lean_ctor_set(x_621, 6, x_608);
lean_ctor_set(x_621, 7, x_609);
lean_ctor_set(x_621, 8, x_610);
lean_ctor_set(x_621, 9, x_612);
lean_ctor_set_uint8(x_621, sizeof(void*)*10 + 9, x_596);
lean_ctor_set_uint8(x_621, sizeof(void*)*10 + 10, x_597);
lean_ctor_set_uint8(x_621, sizeof(void*)*10 + 11, x_598);
lean_ctor_set_uint8(x_621, sizeof(void*)*10 + 12, x_599);
lean_ctor_set_uint8(x_621, sizeof(void*)*10 + 13, x_600);
lean_ctor_set_uint8(x_621, sizeof(void*)*10 + 14, x_601);
lean_ctor_set_uint32(x_621, sizeof(void*)*10, x_603);
lean_ctor_set_uint32(x_621, sizeof(void*)*10 + 4, x_604);
lean_ctor_set_uint8(x_621, sizeof(void*)*10 + 15, x_611);
lean_ctor_set_uint8(x_621, sizeof(void*)*10 + 16, x_613);
lean_ctor_set_uint8(x_621, sizeof(void*)*10 + 17, x_614);
x_618 = x_621;
goto block_620;
}
block_620:
{
lean_object* x_619; 
lean_ctor_set_uint8(x_618, sizeof(void*)*10 + 8, x_617);
x_619 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_619, 0, x_618);
return x_619;
}
}
}
}
else
{
lean_object* x_624; lean_object* x_625; uint8_t x_626; uint8_t x_627; uint8_t x_628; uint8_t x_629; uint8_t x_630; uint8_t x_631; lean_object* x_632; uint32_t x_633; uint32_t x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; uint8_t x_641; lean_object* x_642; uint8_t x_643; uint8_t x_644; lean_object* x_645; uint8_t x_646; uint8_t x_653; 
lean_dec(x_3);
x_624 = lean_ctor_get(x_1, 0);
x_625 = lean_ctor_get(x_1, 1);
x_626 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_627 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_628 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_629 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_630 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_631 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_632 = lean_ctor_get(x_1, 2);
x_633 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_634 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_635 = lean_ctor_get(x_1, 3);
x_636 = lean_ctor_get(x_1, 4);
x_637 = lean_ctor_get(x_1, 5);
x_638 = lean_ctor_get(x_1, 6);
x_639 = lean_ctor_get(x_1, 7);
x_640 = lean_ctor_get(x_1, 8);
x_641 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_642 = lean_ctor_get(x_1, 9);
x_643 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_644 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_653 = !lean_is_exclusive(x_1);
if (x_653 == 0)
{
x_645 = x_1;
x_646 = x_653;
goto block_652;
}
else
{
lean_inc(x_642);
lean_inc(x_640);
lean_inc(x_639);
lean_inc(x_638);
lean_inc(x_637);
lean_inc(x_636);
lean_inc(x_635);
lean_inc(x_632);
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_1);
x_645 = lean_box(0);
x_646 = x_653;
goto block_652;
}
block_652:
{
uint8_t x_647; lean_object* x_648; 
x_647 = 1;
if (x_646 == 0)
{
x_648 = x_645;
goto block_650;
}
else
{
lean_object* x_651; 
x_651 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_651, 0, x_624);
lean_ctor_set(x_651, 1, x_625);
lean_ctor_set(x_651, 2, x_632);
lean_ctor_set(x_651, 3, x_635);
lean_ctor_set(x_651, 4, x_636);
lean_ctor_set(x_651, 5, x_637);
lean_ctor_set(x_651, 6, x_638);
lean_ctor_set(x_651, 7, x_639);
lean_ctor_set(x_651, 8, x_640);
lean_ctor_set(x_651, 9, x_642);
lean_ctor_set_uint8(x_651, sizeof(void*)*10 + 9, x_626);
lean_ctor_set_uint8(x_651, sizeof(void*)*10 + 10, x_627);
lean_ctor_set_uint8(x_651, sizeof(void*)*10 + 11, x_628);
lean_ctor_set_uint8(x_651, sizeof(void*)*10 + 12, x_629);
lean_ctor_set_uint8(x_651, sizeof(void*)*10 + 13, x_630);
lean_ctor_set_uint8(x_651, sizeof(void*)*10 + 14, x_631);
lean_ctor_set_uint32(x_651, sizeof(void*)*10, x_633);
lean_ctor_set_uint32(x_651, sizeof(void*)*10 + 4, x_634);
lean_ctor_set_uint8(x_651, sizeof(void*)*10 + 15, x_641);
lean_ctor_set_uint8(x_651, sizeof(void*)*10 + 16, x_643);
lean_ctor_set_uint8(x_651, sizeof(void*)*10 + 17, x_644);
x_648 = x_651;
goto block_650;
}
block_650:
{
lean_object* x_649; 
lean_ctor_set_uint8(x_648, sizeof(void*)*10 + 8, x_647);
x_649 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_649, 0, x_648);
return x_649;
}
}
}
}
else
{
lean_object* x_654; lean_object* x_655; 
x_654 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
x_655 = l___private_Lean_Shell_0__Lean_checkOptArg(x_654, x_3);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; uint8_t x_659; uint8_t x_660; uint8_t x_661; uint8_t x_662; uint8_t x_663; uint8_t x_664; uint8_t x_665; lean_object* x_666; uint32_t x_667; uint32_t x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; uint8_t x_675; lean_object* x_676; uint8_t x_677; uint8_t x_678; lean_object* x_679; uint8_t x_680; uint8_t x_704; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
lean_dec_ref(x_655);
x_657 = lean_ctor_get(x_1, 0);
x_658 = lean_ctor_get(x_1, 1);
x_659 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_660 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_661 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_662 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_663 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_664 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_665 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_666 = lean_ctor_get(x_1, 2);
x_667 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_668 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_669 = lean_ctor_get(x_1, 3);
x_670 = lean_ctor_get(x_1, 4);
x_671 = lean_ctor_get(x_1, 5);
x_672 = lean_ctor_get(x_1, 6);
x_673 = lean_ctor_get(x_1, 7);
x_674 = lean_ctor_get(x_1, 8);
x_675 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_676 = lean_ctor_get(x_1, 9);
x_677 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_678 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_704 = !lean_is_exclusive(x_1);
if (x_704 == 0)
{
x_679 = x_1;
x_680 = x_704;
goto block_703;
}
else
{
lean_inc(x_676);
lean_inc(x_674);
lean_inc(x_673);
lean_inc(x_672);
lean_inc(x_671);
lean_inc(x_670);
lean_inc(x_669);
lean_inc(x_666);
lean_inc(x_658);
lean_inc(x_657);
lean_dec(x_1);
x_679 = lean_box(0);
x_680 = x_704;
goto block_703;
}
block_703:
{
lean_object* x_681; 
lean_inc(x_656);
x_681 = l___private_Lean_Shell_0__Lean_setConfigOption(x_657, x_656);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; uint8_t x_684; uint8_t x_695; 
x_682 = lean_ctor_get(x_681, 0);
x_695 = !lean_is_exclusive(x_681);
if (x_695 == 0)
{
x_683 = x_681;
x_684 = x_695;
goto block_694;
}
else
{
lean_inc(x_682);
lean_dec(x_681);
x_683 = lean_box(0);
x_684 = x_695;
goto block_694;
}
block_694:
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_685 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
x_686 = lean_string_append(x_685, x_656);
lean_dec(x_656);
x_687 = lean_array_push(x_658, x_686);
if (x_680 == 0)
{
lean_ctor_set(x_679, 1, x_687);
lean_ctor_set(x_679, 0, x_682);
x_688 = x_679;
goto block_692;
}
else
{
lean_object* x_693; 
x_693 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_693, 0, x_682);
lean_ctor_set(x_693, 1, x_687);
lean_ctor_set(x_693, 2, x_666);
lean_ctor_set(x_693, 3, x_669);
lean_ctor_set(x_693, 4, x_670);
lean_ctor_set(x_693, 5, x_671);
lean_ctor_set(x_693, 6, x_672);
lean_ctor_set(x_693, 7, x_673);
lean_ctor_set(x_693, 8, x_674);
lean_ctor_set(x_693, 9, x_676);
lean_ctor_set_uint8(x_693, sizeof(void*)*10 + 8, x_659);
lean_ctor_set_uint8(x_693, sizeof(void*)*10 + 9, x_660);
lean_ctor_set_uint8(x_693, sizeof(void*)*10 + 10, x_661);
lean_ctor_set_uint8(x_693, sizeof(void*)*10 + 11, x_662);
lean_ctor_set_uint8(x_693, sizeof(void*)*10 + 12, x_663);
lean_ctor_set_uint8(x_693, sizeof(void*)*10 + 13, x_664);
lean_ctor_set_uint8(x_693, sizeof(void*)*10 + 14, x_665);
lean_ctor_set_uint32(x_693, sizeof(void*)*10, x_667);
lean_ctor_set_uint32(x_693, sizeof(void*)*10 + 4, x_668);
lean_ctor_set_uint8(x_693, sizeof(void*)*10 + 15, x_675);
lean_ctor_set_uint8(x_693, sizeof(void*)*10 + 16, x_677);
lean_ctor_set_uint8(x_693, sizeof(void*)*10 + 17, x_678);
x_688 = x_693;
goto block_692;
}
block_692:
{
lean_object* x_689; 
if (x_684 == 0)
{
lean_ctor_set(x_683, 0, x_688);
x_689 = x_683;
goto block_690;
}
else
{
lean_object* x_691; 
x_691 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_691, 0, x_688);
x_689 = x_691;
goto block_690;
}
block_690:
{
return x_689;
}
}
}
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_701; lean_object* x_702; 
lean_del_object(x_679);
lean_dec_ref(x_676);
lean_dec(x_674);
lean_dec(x_673);
lean_dec(x_672);
lean_dec(x_671);
lean_dec(x_670);
lean_dec(x_669);
lean_dec_ref(x_666);
lean_dec_ref(x_658);
lean_dec(x_656);
x_696 = lean_ctor_get(x_681, 0);
lean_inc(x_696);
lean_dec_ref(x_681);
x_701 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_702 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_701);
lean_dec_ref(x_702);
x_697 = lean_box(0);
goto block_700;
block_700:
{
lean_object* x_698; lean_object* x_699; 
x_698 = lean_io_error_to_string(x_696);
x_699 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_698);
lean_dec_ref(x_699);
x_101 = lean_box(0);
goto block_104;
}
}
}
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_710; lean_object* x_711; 
lean_dec_ref(x_1);
x_705 = lean_ctor_get(x_655, 0);
lean_inc(x_705);
lean_dec_ref(x_655);
x_710 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_711 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_710);
lean_dec_ref(x_711);
x_706 = lean_box(0);
goto block_709;
block_709:
{
lean_object* x_707; lean_object* x_708; 
x_707 = lean_io_error_to_string(x_705);
x_708 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_707);
lean_dec_ref(x_708);
x_198 = lean_box(0);
goto block_201;
}
}
}
}
else
{
lean_object* x_712; lean_object* x_713; uint8_t x_714; uint8_t x_715; uint8_t x_716; uint8_t x_717; uint8_t x_718; uint8_t x_719; lean_object* x_720; uint32_t x_721; uint32_t x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; uint8_t x_729; lean_object* x_730; uint8_t x_731; uint8_t x_732; lean_object* x_733; uint8_t x_734; uint8_t x_740; 
lean_dec(x_3);
x_712 = lean_ctor_get(x_1, 0);
x_713 = lean_ctor_get(x_1, 1);
x_714 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_715 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_716 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_717 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_718 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_719 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_720 = lean_ctor_get(x_1, 2);
x_721 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_722 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_723 = lean_ctor_get(x_1, 3);
x_724 = lean_ctor_get(x_1, 4);
x_725 = lean_ctor_get(x_1, 5);
x_726 = lean_ctor_get(x_1, 6);
x_727 = lean_ctor_get(x_1, 7);
x_728 = lean_ctor_get(x_1, 8);
x_729 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_730 = lean_ctor_get(x_1, 9);
x_731 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_732 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_740 = !lean_is_exclusive(x_1);
if (x_740 == 0)
{
x_733 = x_1;
x_734 = x_740;
goto block_739;
}
else
{
lean_inc(x_730);
lean_inc(x_728);
lean_inc(x_727);
lean_inc(x_726);
lean_inc(x_725);
lean_inc(x_724);
lean_inc(x_723);
lean_inc(x_720);
lean_inc(x_713);
lean_inc(x_712);
lean_dec(x_1);
x_733 = lean_box(0);
x_734 = x_740;
goto block_739;
}
block_739:
{
lean_object* x_735; 
if (x_734 == 0)
{
x_735 = x_733;
goto block_737;
}
else
{
lean_object* x_738; 
x_738 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_738, 0, x_712);
lean_ctor_set(x_738, 1, x_713);
lean_ctor_set(x_738, 2, x_720);
lean_ctor_set(x_738, 3, x_723);
lean_ctor_set(x_738, 4, x_724);
lean_ctor_set(x_738, 5, x_725);
lean_ctor_set(x_738, 6, x_726);
lean_ctor_set(x_738, 7, x_727);
lean_ctor_set(x_738, 8, x_728);
lean_ctor_set(x_738, 9, x_730);
lean_ctor_set_uint8(x_738, sizeof(void*)*10 + 8, x_714);
lean_ctor_set_uint8(x_738, sizeof(void*)*10 + 9, x_715);
lean_ctor_set_uint8(x_738, sizeof(void*)*10 + 11, x_716);
lean_ctor_set_uint8(x_738, sizeof(void*)*10 + 12, x_717);
lean_ctor_set_uint8(x_738, sizeof(void*)*10 + 13, x_718);
lean_ctor_set_uint8(x_738, sizeof(void*)*10 + 14, x_719);
lean_ctor_set_uint32(x_738, sizeof(void*)*10, x_721);
lean_ctor_set_uint32(x_738, sizeof(void*)*10 + 4, x_722);
lean_ctor_set_uint8(x_738, sizeof(void*)*10 + 15, x_729);
lean_ctor_set_uint8(x_738, sizeof(void*)*10 + 16, x_731);
lean_ctor_set_uint8(x_738, sizeof(void*)*10 + 17, x_732);
x_735 = x_738;
goto block_737;
}
block_737:
{
lean_object* x_736; 
lean_ctor_set_uint8(x_735, sizeof(void*)*10 + 10, x_313);
x_736 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_736, 0, x_735);
return x_736;
}
}
}
}
else
{
lean_object* x_741; lean_object* x_742; uint8_t x_743; uint8_t x_744; uint8_t x_745; uint8_t x_746; uint8_t x_747; uint8_t x_748; lean_object* x_749; uint32_t x_750; uint32_t x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; uint8_t x_758; lean_object* x_759; uint8_t x_760; uint8_t x_761; lean_object* x_762; uint8_t x_763; uint8_t x_769; 
lean_dec(x_3);
x_741 = lean_ctor_get(x_1, 0);
x_742 = lean_ctor_get(x_1, 1);
x_743 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_744 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_745 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_746 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_747 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_748 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_749 = lean_ctor_get(x_1, 2);
x_750 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_751 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_752 = lean_ctor_get(x_1, 3);
x_753 = lean_ctor_get(x_1, 4);
x_754 = lean_ctor_get(x_1, 5);
x_755 = lean_ctor_get(x_1, 6);
x_756 = lean_ctor_get(x_1, 7);
x_757 = lean_ctor_get(x_1, 8);
x_758 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_759 = lean_ctor_get(x_1, 9);
x_760 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_761 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_769 = !lean_is_exclusive(x_1);
if (x_769 == 0)
{
x_762 = x_1;
x_763 = x_769;
goto block_768;
}
else
{
lean_inc(x_759);
lean_inc(x_757);
lean_inc(x_756);
lean_inc(x_755);
lean_inc(x_754);
lean_inc(x_753);
lean_inc(x_752);
lean_inc(x_749);
lean_inc(x_742);
lean_inc(x_741);
lean_dec(x_1);
x_762 = lean_box(0);
x_763 = x_769;
goto block_768;
}
block_768:
{
lean_object* x_764; 
if (x_763 == 0)
{
x_764 = x_762;
goto block_766;
}
else
{
lean_object* x_767; 
x_767 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_767, 0, x_741);
lean_ctor_set(x_767, 1, x_742);
lean_ctor_set(x_767, 2, x_749);
lean_ctor_set(x_767, 3, x_752);
lean_ctor_set(x_767, 4, x_753);
lean_ctor_set(x_767, 5, x_754);
lean_ctor_set(x_767, 6, x_755);
lean_ctor_set(x_767, 7, x_756);
lean_ctor_set(x_767, 8, x_757);
lean_ctor_set(x_767, 9, x_759);
lean_ctor_set_uint8(x_767, sizeof(void*)*10 + 8, x_743);
lean_ctor_set_uint8(x_767, sizeof(void*)*10 + 10, x_744);
lean_ctor_set_uint8(x_767, sizeof(void*)*10 + 11, x_745);
lean_ctor_set_uint8(x_767, sizeof(void*)*10 + 12, x_746);
lean_ctor_set_uint8(x_767, sizeof(void*)*10 + 13, x_747);
lean_ctor_set_uint8(x_767, sizeof(void*)*10 + 14, x_748);
lean_ctor_set_uint32(x_767, sizeof(void*)*10, x_750);
lean_ctor_set_uint32(x_767, sizeof(void*)*10 + 4, x_751);
lean_ctor_set_uint8(x_767, sizeof(void*)*10 + 15, x_758);
lean_ctor_set_uint8(x_767, sizeof(void*)*10 + 16, x_760);
lean_ctor_set_uint8(x_767, sizeof(void*)*10 + 17, x_761);
x_764 = x_767;
goto block_766;
}
block_766:
{
lean_object* x_765; 
lean_ctor_set_uint8(x_764, sizeof(void*)*10 + 9, x_311);
x_765 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_765, 0, x_764);
return x_765;
}
}
}
}
else
{
lean_object* x_770; lean_object* x_771; uint8_t x_772; uint8_t x_773; uint8_t x_774; uint8_t x_775; uint8_t x_776; uint8_t x_777; uint8_t x_778; lean_object* x_779; uint32_t x_780; uint32_t x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; uint8_t x_788; lean_object* x_789; uint8_t x_790; lean_object* x_791; uint8_t x_792; uint8_t x_798; 
lean_dec(x_3);
x_770 = lean_ctor_get(x_1, 0);
x_771 = lean_ctor_get(x_1, 1);
x_772 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_773 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_774 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_775 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_776 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_777 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_778 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_779 = lean_ctor_get(x_1, 2);
x_780 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_781 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_782 = lean_ctor_get(x_1, 3);
x_783 = lean_ctor_get(x_1, 4);
x_784 = lean_ctor_get(x_1, 5);
x_785 = lean_ctor_get(x_1, 6);
x_786 = lean_ctor_get(x_1, 7);
x_787 = lean_ctor_get(x_1, 8);
x_788 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_789 = lean_ctor_get(x_1, 9);
x_790 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_798 = !lean_is_exclusive(x_1);
if (x_798 == 0)
{
x_791 = x_1;
x_792 = x_798;
goto block_797;
}
else
{
lean_inc(x_789);
lean_inc(x_787);
lean_inc(x_786);
lean_inc(x_785);
lean_inc(x_784);
lean_inc(x_783);
lean_inc(x_782);
lean_inc(x_779);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_1);
x_791 = lean_box(0);
x_792 = x_798;
goto block_797;
}
block_797:
{
lean_object* x_793; 
if (x_792 == 0)
{
x_793 = x_791;
goto block_795;
}
else
{
lean_object* x_796; 
x_796 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_796, 0, x_770);
lean_ctor_set(x_796, 1, x_771);
lean_ctor_set(x_796, 2, x_779);
lean_ctor_set(x_796, 3, x_782);
lean_ctor_set(x_796, 4, x_783);
lean_ctor_set(x_796, 5, x_784);
lean_ctor_set(x_796, 6, x_785);
lean_ctor_set(x_796, 7, x_786);
lean_ctor_set(x_796, 8, x_787);
lean_ctor_set(x_796, 9, x_789);
lean_ctor_set_uint8(x_796, sizeof(void*)*10 + 8, x_772);
lean_ctor_set_uint8(x_796, sizeof(void*)*10 + 9, x_773);
lean_ctor_set_uint8(x_796, sizeof(void*)*10 + 10, x_774);
lean_ctor_set_uint8(x_796, sizeof(void*)*10 + 11, x_775);
lean_ctor_set_uint8(x_796, sizeof(void*)*10 + 12, x_776);
lean_ctor_set_uint8(x_796, sizeof(void*)*10 + 13, x_777);
lean_ctor_set_uint8(x_796, sizeof(void*)*10 + 14, x_778);
lean_ctor_set_uint32(x_796, sizeof(void*)*10, x_780);
lean_ctor_set_uint32(x_796, sizeof(void*)*10 + 4, x_781);
lean_ctor_set_uint8(x_796, sizeof(void*)*10 + 15, x_788);
lean_ctor_set_uint8(x_796, sizeof(void*)*10 + 17, x_790);
x_793 = x_796;
goto block_795;
}
block_795:
{
lean_object* x_794; 
lean_ctor_set_uint8(x_793, sizeof(void*)*10 + 16, x_309);
x_794 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_794, 0, x_793);
return x_794;
}
}
}
}
else
{
lean_object* x_799; lean_object* x_800; uint8_t x_801; uint8_t x_802; uint8_t x_803; uint8_t x_804; uint8_t x_805; uint8_t x_806; uint8_t x_807; lean_object* x_808; uint32_t x_809; uint32_t x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; uint8_t x_818; uint8_t x_819; lean_object* x_820; uint8_t x_821; uint8_t x_827; 
lean_dec(x_3);
x_799 = lean_ctor_get(x_1, 0);
x_800 = lean_ctor_get(x_1, 1);
x_801 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_802 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_803 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_804 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_805 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_806 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_807 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_808 = lean_ctor_get(x_1, 2);
x_809 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_810 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_811 = lean_ctor_get(x_1, 3);
x_812 = lean_ctor_get(x_1, 4);
x_813 = lean_ctor_get(x_1, 5);
x_814 = lean_ctor_get(x_1, 6);
x_815 = lean_ctor_get(x_1, 7);
x_816 = lean_ctor_get(x_1, 8);
x_817 = lean_ctor_get(x_1, 9);
x_818 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_819 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_827 = !lean_is_exclusive(x_1);
if (x_827 == 0)
{
x_820 = x_1;
x_821 = x_827;
goto block_826;
}
else
{
lean_inc(x_817);
lean_inc(x_816);
lean_inc(x_815);
lean_inc(x_814);
lean_inc(x_813);
lean_inc(x_812);
lean_inc(x_811);
lean_inc(x_808);
lean_inc(x_800);
lean_inc(x_799);
lean_dec(x_1);
x_820 = lean_box(0);
x_821 = x_827;
goto block_826;
}
block_826:
{
lean_object* x_822; 
if (x_821 == 0)
{
x_822 = x_820;
goto block_824;
}
else
{
lean_object* x_825; 
x_825 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_825, 0, x_799);
lean_ctor_set(x_825, 1, x_800);
lean_ctor_set(x_825, 2, x_808);
lean_ctor_set(x_825, 3, x_811);
lean_ctor_set(x_825, 4, x_812);
lean_ctor_set(x_825, 5, x_813);
lean_ctor_set(x_825, 6, x_814);
lean_ctor_set(x_825, 7, x_815);
lean_ctor_set(x_825, 8, x_816);
lean_ctor_set(x_825, 9, x_817);
lean_ctor_set_uint8(x_825, sizeof(void*)*10 + 8, x_801);
lean_ctor_set_uint8(x_825, sizeof(void*)*10 + 9, x_802);
lean_ctor_set_uint8(x_825, sizeof(void*)*10 + 10, x_803);
lean_ctor_set_uint8(x_825, sizeof(void*)*10 + 11, x_804);
lean_ctor_set_uint8(x_825, sizeof(void*)*10 + 12, x_805);
lean_ctor_set_uint8(x_825, sizeof(void*)*10 + 13, x_806);
lean_ctor_set_uint8(x_825, sizeof(void*)*10 + 14, x_807);
lean_ctor_set_uint32(x_825, sizeof(void*)*10, x_809);
lean_ctor_set_uint32(x_825, sizeof(void*)*10 + 4, x_810);
lean_ctor_set_uint8(x_825, sizeof(void*)*10 + 16, x_818);
lean_ctor_set_uint8(x_825, sizeof(void*)*10 + 17, x_819);
x_822 = x_825;
goto block_824;
}
block_824:
{
lean_object* x_823; 
lean_ctor_set_uint8(x_822, sizeof(void*)*10 + 15, x_307);
x_823 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_823, 0, x_822);
return x_823;
}
}
}
}
else
{
lean_object* x_828; lean_object* x_829; uint8_t x_830; uint8_t x_831; uint8_t x_832; uint8_t x_833; uint8_t x_834; lean_object* x_835; uint32_t x_836; uint32_t x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; uint8_t x_844; lean_object* x_845; uint8_t x_846; uint8_t x_847; lean_object* x_848; uint8_t x_849; uint8_t x_855; 
lean_dec(x_3);
x_828 = lean_ctor_get(x_1, 0);
x_829 = lean_ctor_get(x_1, 1);
x_830 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_831 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_832 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_833 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_834 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_835 = lean_ctor_get(x_1, 2);
x_836 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_837 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_838 = lean_ctor_get(x_1, 3);
x_839 = lean_ctor_get(x_1, 4);
x_840 = lean_ctor_get(x_1, 5);
x_841 = lean_ctor_get(x_1, 6);
x_842 = lean_ctor_get(x_1, 7);
x_843 = lean_ctor_get(x_1, 8);
x_844 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_845 = lean_ctor_get(x_1, 9);
x_846 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_847 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_855 = !lean_is_exclusive(x_1);
if (x_855 == 0)
{
x_848 = x_1;
x_849 = x_855;
goto block_854;
}
else
{
lean_inc(x_845);
lean_inc(x_843);
lean_inc(x_842);
lean_inc(x_841);
lean_inc(x_840);
lean_inc(x_839);
lean_inc(x_838);
lean_inc(x_835);
lean_inc(x_829);
lean_inc(x_828);
lean_dec(x_1);
x_848 = lean_box(0);
x_849 = x_855;
goto block_854;
}
block_854:
{
lean_object* x_850; 
if (x_849 == 0)
{
x_850 = x_848;
goto block_852;
}
else
{
lean_object* x_853; 
x_853 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_853, 0, x_828);
lean_ctor_set(x_853, 1, x_829);
lean_ctor_set(x_853, 2, x_835);
lean_ctor_set(x_853, 3, x_838);
lean_ctor_set(x_853, 4, x_839);
lean_ctor_set(x_853, 5, x_840);
lean_ctor_set(x_853, 6, x_841);
lean_ctor_set(x_853, 7, x_842);
lean_ctor_set(x_853, 8, x_843);
lean_ctor_set(x_853, 9, x_845);
lean_ctor_set_uint8(x_853, sizeof(void*)*10 + 8, x_830);
lean_ctor_set_uint8(x_853, sizeof(void*)*10 + 9, x_831);
lean_ctor_set_uint8(x_853, sizeof(void*)*10 + 10, x_832);
lean_ctor_set_uint8(x_853, sizeof(void*)*10 + 11, x_833);
lean_ctor_set_uint8(x_853, sizeof(void*)*10 + 13, x_834);
lean_ctor_set_uint32(x_853, sizeof(void*)*10, x_836);
lean_ctor_set_uint32(x_853, sizeof(void*)*10 + 4, x_837);
lean_ctor_set_uint8(x_853, sizeof(void*)*10 + 15, x_844);
lean_ctor_set_uint8(x_853, sizeof(void*)*10 + 16, x_846);
lean_ctor_set_uint8(x_853, sizeof(void*)*10 + 17, x_847);
x_850 = x_853;
goto block_852;
}
block_852:
{
lean_object* x_851; 
lean_ctor_set_uint8(x_850, sizeof(void*)*10 + 12, x_305);
lean_ctor_set_uint8(x_850, sizeof(void*)*10 + 14, x_305);
x_851 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_851, 0, x_850);
return x_851;
}
}
}
}
else
{
lean_object* x_856; lean_object* x_857; uint8_t x_858; uint8_t x_859; uint8_t x_860; uint8_t x_861; uint8_t x_862; uint8_t x_863; lean_object* x_864; uint32_t x_865; uint32_t x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; uint8_t x_873; lean_object* x_874; uint8_t x_875; uint8_t x_876; lean_object* x_877; uint8_t x_878; uint8_t x_884; 
lean_dec(x_3);
x_856 = lean_ctor_get(x_1, 0);
x_857 = lean_ctor_get(x_1, 1);
x_858 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_859 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_860 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_861 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_862 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_863 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_864 = lean_ctor_get(x_1, 2);
x_865 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_866 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_867 = lean_ctor_get(x_1, 3);
x_868 = lean_ctor_get(x_1, 4);
x_869 = lean_ctor_get(x_1, 5);
x_870 = lean_ctor_get(x_1, 6);
x_871 = lean_ctor_get(x_1, 7);
x_872 = lean_ctor_get(x_1, 8);
x_873 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_874 = lean_ctor_get(x_1, 9);
x_875 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_876 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_884 = !lean_is_exclusive(x_1);
if (x_884 == 0)
{
x_877 = x_1;
x_878 = x_884;
goto block_883;
}
else
{
lean_inc(x_874);
lean_inc(x_872);
lean_inc(x_871);
lean_inc(x_870);
lean_inc(x_869);
lean_inc(x_868);
lean_inc(x_867);
lean_inc(x_864);
lean_inc(x_857);
lean_inc(x_856);
lean_dec(x_1);
x_877 = lean_box(0);
x_878 = x_884;
goto block_883;
}
block_883:
{
lean_object* x_879; 
if (x_878 == 0)
{
x_879 = x_877;
goto block_881;
}
else
{
lean_object* x_882; 
x_882 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_882, 0, x_856);
lean_ctor_set(x_882, 1, x_857);
lean_ctor_set(x_882, 2, x_864);
lean_ctor_set(x_882, 3, x_867);
lean_ctor_set(x_882, 4, x_868);
lean_ctor_set(x_882, 5, x_869);
lean_ctor_set(x_882, 6, x_870);
lean_ctor_set(x_882, 7, x_871);
lean_ctor_set(x_882, 8, x_872);
lean_ctor_set(x_882, 9, x_874);
lean_ctor_set_uint8(x_882, sizeof(void*)*10 + 8, x_858);
lean_ctor_set_uint8(x_882, sizeof(void*)*10 + 9, x_859);
lean_ctor_set_uint8(x_882, sizeof(void*)*10 + 10, x_860);
lean_ctor_set_uint8(x_882, sizeof(void*)*10 + 11, x_861);
lean_ctor_set_uint8(x_882, sizeof(void*)*10 + 12, x_862);
lean_ctor_set_uint8(x_882, sizeof(void*)*10 + 14, x_863);
lean_ctor_set_uint32(x_882, sizeof(void*)*10, x_865);
lean_ctor_set_uint32(x_882, sizeof(void*)*10 + 4, x_866);
lean_ctor_set_uint8(x_882, sizeof(void*)*10 + 15, x_873);
lean_ctor_set_uint8(x_882, sizeof(void*)*10 + 16, x_875);
lean_ctor_set_uint8(x_882, sizeof(void*)*10 + 17, x_876);
x_879 = x_882;
goto block_881;
}
block_881:
{
lean_object* x_880; 
lean_ctor_set_uint8(x_879, sizeof(void*)*10 + 13, x_303);
x_880 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_880, 0, x_879);
return x_880;
}
}
}
}
else
{
lean_object* x_885; lean_object* x_886; uint8_t x_887; uint8_t x_888; uint8_t x_889; uint8_t x_890; uint8_t x_891; uint8_t x_892; lean_object* x_893; uint32_t x_894; uint32_t x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; uint8_t x_902; lean_object* x_903; uint8_t x_904; uint8_t x_905; lean_object* x_906; uint8_t x_907; uint8_t x_913; 
lean_dec(x_3);
x_885 = lean_ctor_get(x_1, 0);
x_886 = lean_ctor_get(x_1, 1);
x_887 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_888 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_889 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_890 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_891 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_892 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_893 = lean_ctor_get(x_1, 2);
x_894 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_895 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_896 = lean_ctor_get(x_1, 3);
x_897 = lean_ctor_get(x_1, 4);
x_898 = lean_ctor_get(x_1, 5);
x_899 = lean_ctor_get(x_1, 6);
x_900 = lean_ctor_get(x_1, 7);
x_901 = lean_ctor_get(x_1, 8);
x_902 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_903 = lean_ctor_get(x_1, 9);
x_904 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_905 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_913 = !lean_is_exclusive(x_1);
if (x_913 == 0)
{
x_906 = x_1;
x_907 = x_913;
goto block_912;
}
else
{
lean_inc(x_903);
lean_inc(x_901);
lean_inc(x_900);
lean_inc(x_899);
lean_inc(x_898);
lean_inc(x_897);
lean_inc(x_896);
lean_inc(x_893);
lean_inc(x_886);
lean_inc(x_885);
lean_dec(x_1);
x_906 = lean_box(0);
x_907 = x_913;
goto block_912;
}
block_912:
{
lean_object* x_908; 
if (x_907 == 0)
{
x_908 = x_906;
goto block_910;
}
else
{
lean_object* x_911; 
x_911 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_911, 0, x_885);
lean_ctor_set(x_911, 1, x_886);
lean_ctor_set(x_911, 2, x_893);
lean_ctor_set(x_911, 3, x_896);
lean_ctor_set(x_911, 4, x_897);
lean_ctor_set(x_911, 5, x_898);
lean_ctor_set(x_911, 6, x_899);
lean_ctor_set(x_911, 7, x_900);
lean_ctor_set(x_911, 8, x_901);
lean_ctor_set(x_911, 9, x_903);
lean_ctor_set_uint8(x_911, sizeof(void*)*10 + 8, x_887);
lean_ctor_set_uint8(x_911, sizeof(void*)*10 + 9, x_888);
lean_ctor_set_uint8(x_911, sizeof(void*)*10 + 10, x_889);
lean_ctor_set_uint8(x_911, sizeof(void*)*10 + 11, x_890);
lean_ctor_set_uint8(x_911, sizeof(void*)*10 + 13, x_891);
lean_ctor_set_uint8(x_911, sizeof(void*)*10 + 14, x_892);
lean_ctor_set_uint32(x_911, sizeof(void*)*10, x_894);
lean_ctor_set_uint32(x_911, sizeof(void*)*10 + 4, x_895);
lean_ctor_set_uint8(x_911, sizeof(void*)*10 + 15, x_902);
lean_ctor_set_uint8(x_911, sizeof(void*)*10 + 16, x_904);
lean_ctor_set_uint8(x_911, sizeof(void*)*10 + 17, x_905);
x_908 = x_911;
goto block_910;
}
block_910:
{
lean_object* x_909; 
lean_ctor_set_uint8(x_908, sizeof(void*)*10 + 12, x_301);
x_909 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_909, 0, x_908);
return x_909;
}
}
}
}
else
{
lean_object* x_914; lean_object* x_915; uint8_t x_916; uint8_t x_917; uint8_t x_918; uint8_t x_919; uint8_t x_920; uint8_t x_921; uint8_t x_922; lean_object* x_923; uint32_t x_924; uint32_t x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; uint8_t x_932; lean_object* x_933; uint8_t x_934; uint8_t x_935; lean_object* x_936; uint8_t x_937; uint8_t x_945; 
lean_dec(x_3);
x_914 = lean_ctor_get(x_1, 0);
x_915 = lean_ctor_get(x_1, 1);
x_916 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_917 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_918 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_919 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_920 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_921 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_922 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_923 = lean_ctor_get(x_1, 2);
x_924 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_925 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_926 = lean_ctor_get(x_1, 3);
x_927 = lean_ctor_get(x_1, 4);
x_928 = lean_ctor_get(x_1, 5);
x_929 = lean_ctor_get(x_1, 6);
x_930 = lean_ctor_get(x_1, 7);
x_931 = lean_ctor_get(x_1, 8);
x_932 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_933 = lean_ctor_get(x_1, 9);
x_934 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_935 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_945 = !lean_is_exclusive(x_1);
if (x_945 == 0)
{
x_936 = x_1;
x_937 = x_945;
goto block_944;
}
else
{
lean_inc(x_933);
lean_inc(x_931);
lean_inc(x_930);
lean_inc(x_929);
lean_inc(x_928);
lean_inc(x_927);
lean_inc(x_926);
lean_inc(x_923);
lean_inc(x_915);
lean_inc(x_914);
lean_dec(x_1);
x_936 = lean_box(0);
x_937 = x_945;
goto block_944;
}
block_944:
{
lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_938 = l___private_Lean_Shell_0__Lean_verbose;
x_939 = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(x_914, x_938, x_297);
if (x_937 == 0)
{
lean_ctor_set(x_936, 0, x_939);
x_940 = x_936;
goto block_942;
}
else
{
lean_object* x_943; 
x_943 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_943, 0, x_939);
lean_ctor_set(x_943, 1, x_915);
lean_ctor_set(x_943, 2, x_923);
lean_ctor_set(x_943, 3, x_926);
lean_ctor_set(x_943, 4, x_927);
lean_ctor_set(x_943, 5, x_928);
lean_ctor_set(x_943, 6, x_929);
lean_ctor_set(x_943, 7, x_930);
lean_ctor_set(x_943, 8, x_931);
lean_ctor_set(x_943, 9, x_933);
lean_ctor_set_uint8(x_943, sizeof(void*)*10 + 8, x_916);
lean_ctor_set_uint8(x_943, sizeof(void*)*10 + 9, x_917);
lean_ctor_set_uint8(x_943, sizeof(void*)*10 + 10, x_918);
lean_ctor_set_uint8(x_943, sizeof(void*)*10 + 11, x_919);
lean_ctor_set_uint8(x_943, sizeof(void*)*10 + 12, x_920);
lean_ctor_set_uint8(x_943, sizeof(void*)*10 + 13, x_921);
lean_ctor_set_uint8(x_943, sizeof(void*)*10 + 14, x_922);
lean_ctor_set_uint32(x_943, sizeof(void*)*10, x_924);
lean_ctor_set_uint32(x_943, sizeof(void*)*10 + 4, x_925);
lean_ctor_set_uint8(x_943, sizeof(void*)*10 + 15, x_932);
lean_ctor_set_uint8(x_943, sizeof(void*)*10 + 16, x_934);
lean_ctor_set_uint8(x_943, sizeof(void*)*10 + 17, x_935);
x_940 = x_943;
goto block_942;
}
block_942:
{
lean_object* x_941; 
x_941 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_941, 0, x_940);
return x_941;
}
}
}
}
else
{
lean_object* x_946; lean_object* x_947; 
x_946 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
x_947 = l___private_Lean_Shell_0__Lean_checkOptArg(x_946, x_3);
if (lean_obj_tag(x_947) == 0)
{
lean_object* x_948; lean_object* x_949; uint8_t x_950; uint8_t x_998; 
x_948 = lean_ctor_get(x_947, 0);
x_998 = !lean_is_exclusive(x_947);
if (x_998 == 0)
{
x_949 = x_947;
x_950 = x_998;
goto block_997;
}
else
{
lean_inc(x_948);
lean_dec(x_947);
x_949 = lean_box(0);
x_950 = x_998;
goto block_997;
}
block_997:
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
x_951 = lean_unsigned_to_nat(0u);
x_952 = lean_string_utf8_byte_size(x_948);
lean_inc(x_948);
x_953 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_953, 0, x_948);
lean_ctor_set(x_953, 1, x_951);
lean_ctor_set(x_953, 2, x_952);
x_954 = l_String_Slice_toNat_x3f(x_953);
lean_dec_ref(x_953);
if (lean_obj_tag(x_954) == 1)
{
lean_object* x_955; lean_object* x_956; uint8_t x_957; 
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
lean_dec_ref(x_954);
x_956 = lean_cstr_to_nat("4294967296");
x_957 = lean_nat_dec_lt(x_955, x_956);
if (x_957 == 0)
{
lean_object* x_958; lean_object* x_959; 
lean_dec(x_955);
lean_del_object(x_949);
lean_dec(x_948);
lean_dec_ref(x_1);
x_958 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
x_959 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_958);
lean_dec_ref(x_959);
x_93 = lean_box(0);
goto block_96;
}
else
{
lean_object* x_960; lean_object* x_961; uint8_t x_962; uint8_t x_963; uint8_t x_964; uint8_t x_965; uint8_t x_966; uint8_t x_967; uint8_t x_968; lean_object* x_969; uint32_t x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; uint8_t x_977; lean_object* x_978; uint8_t x_979; uint8_t x_980; lean_object* x_981; uint8_t x_982; uint8_t x_994; 
x_960 = lean_ctor_get(x_1, 0);
x_961 = lean_ctor_get(x_1, 1);
x_962 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_963 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_964 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_965 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_966 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_967 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_968 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_969 = lean_ctor_get(x_1, 2);
x_970 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_971 = lean_ctor_get(x_1, 3);
x_972 = lean_ctor_get(x_1, 4);
x_973 = lean_ctor_get(x_1, 5);
x_974 = lean_ctor_get(x_1, 6);
x_975 = lean_ctor_get(x_1, 7);
x_976 = lean_ctor_get(x_1, 8);
x_977 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_978 = lean_ctor_get(x_1, 9);
x_979 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_980 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_994 = !lean_is_exclusive(x_1);
if (x_994 == 0)
{
x_981 = x_1;
x_982 = x_994;
goto block_993;
}
else
{
lean_inc(x_978);
lean_inc(x_976);
lean_inc(x_975);
lean_inc(x_974);
lean_inc(x_973);
lean_inc(x_972);
lean_inc(x_971);
lean_inc(x_969);
lean_inc(x_961);
lean_inc(x_960);
lean_dec(x_1);
x_981 = lean_box(0);
x_982 = x_994;
goto block_993;
}
block_993:
{
uint32_t x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_983 = lean_uint32_of_nat(x_955);
lean_dec(x_955);
x_984 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
x_985 = lean_string_append(x_984, x_948);
lean_dec(x_948);
x_986 = lean_array_push(x_961, x_985);
if (x_982 == 0)
{
lean_ctor_set(x_981, 1, x_986);
x_987 = x_981;
goto block_991;
}
else
{
lean_object* x_992; 
x_992 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_992, 0, x_960);
lean_ctor_set(x_992, 1, x_986);
lean_ctor_set(x_992, 2, x_969);
lean_ctor_set(x_992, 3, x_971);
lean_ctor_set(x_992, 4, x_972);
lean_ctor_set(x_992, 5, x_973);
lean_ctor_set(x_992, 6, x_974);
lean_ctor_set(x_992, 7, x_975);
lean_ctor_set(x_992, 8, x_976);
lean_ctor_set(x_992, 9, x_978);
lean_ctor_set_uint8(x_992, sizeof(void*)*10 + 8, x_962);
lean_ctor_set_uint8(x_992, sizeof(void*)*10 + 9, x_963);
lean_ctor_set_uint8(x_992, sizeof(void*)*10 + 10, x_964);
lean_ctor_set_uint8(x_992, sizeof(void*)*10 + 11, x_965);
lean_ctor_set_uint8(x_992, sizeof(void*)*10 + 12, x_966);
lean_ctor_set_uint8(x_992, sizeof(void*)*10 + 13, x_967);
lean_ctor_set_uint8(x_992, sizeof(void*)*10 + 14, x_968);
lean_ctor_set_uint32(x_992, sizeof(void*)*10 + 4, x_970);
lean_ctor_set_uint8(x_992, sizeof(void*)*10 + 15, x_977);
lean_ctor_set_uint8(x_992, sizeof(void*)*10 + 16, x_979);
lean_ctor_set_uint8(x_992, sizeof(void*)*10 + 17, x_980);
x_987 = x_992;
goto block_991;
}
block_991:
{
lean_object* x_988; 
lean_ctor_set_uint32(x_987, sizeof(void*)*10, x_983);
if (x_950 == 0)
{
lean_ctor_set(x_949, 0, x_987);
x_988 = x_949;
goto block_989;
}
else
{
lean_object* x_990; 
x_990 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_990, 0, x_987);
x_988 = x_990;
goto block_989;
}
block_989:
{
return x_988;
}
}
}
}
}
else
{
lean_object* x_995; lean_object* x_996; 
lean_dec(x_954);
lean_del_object(x_949);
lean_dec(x_948);
lean_dec_ref(x_1);
x_995 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
x_996 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_995);
lean_dec_ref(x_996);
x_89 = lean_box(0);
goto block_92;
}
}
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1004; lean_object* x_1005; 
lean_dec_ref(x_1);
x_999 = lean_ctor_get(x_947, 0);
lean_inc(x_999);
lean_dec_ref(x_947);
x_1004 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1005 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1004);
lean_dec_ref(x_1005);
x_1000 = lean_box(0);
goto block_1003;
block_1003:
{
lean_object* x_1001; lean_object* x_1002; 
x_1001 = lean_io_error_to_string(x_999);
x_1002 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1001);
lean_dec_ref(x_1002);
x_85 = lean_box(0);
goto block_88;
}
}
}
}
else
{
lean_object* x_1006; lean_object* x_1007; 
x_1006 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
x_1007 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1006, x_3);
if (lean_obj_tag(x_1007) == 0)
{
lean_object* x_1008; lean_object* x_1009; uint8_t x_1010; uint8_t x_1056; 
x_1008 = lean_ctor_get(x_1007, 0);
x_1056 = !lean_is_exclusive(x_1007);
if (x_1056 == 0)
{
x_1009 = x_1007;
x_1010 = x_1056;
goto block_1055;
}
else
{
lean_inc(x_1008);
lean_dec(x_1007);
x_1009 = lean_box(0);
x_1010 = x_1056;
goto block_1055;
}
block_1055:
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
x_1011 = lean_unsigned_to_nat(0u);
x_1012 = lean_string_utf8_byte_size(x_1008);
lean_inc(x_1008);
x_1013 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1013, 0, x_1008);
lean_ctor_set(x_1013, 1, x_1011);
lean_ctor_set(x_1013, 2, x_1012);
x_1014 = l_String_Slice_toNat_x3f(x_1013);
lean_dec_ref(x_1013);
if (lean_obj_tag(x_1014) == 1)
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; uint8_t x_1018; uint8_t x_1019; uint8_t x_1020; uint8_t x_1021; uint8_t x_1022; uint8_t x_1023; uint8_t x_1024; lean_object* x_1025; uint32_t x_1026; uint32_t x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; uint8_t x_1034; lean_object* x_1035; uint8_t x_1036; uint8_t x_1037; lean_object* x_1038; uint8_t x_1039; uint8_t x_1052; 
x_1015 = lean_ctor_get(x_1014, 0);
lean_inc(x_1015);
lean_dec_ref(x_1014);
x_1016 = lean_ctor_get(x_1, 0);
x_1017 = lean_ctor_get(x_1, 1);
x_1018 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1019 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1020 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1021 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1022 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1023 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1024 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1025 = lean_ctor_get(x_1, 2);
x_1026 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1027 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1028 = lean_ctor_get(x_1, 3);
x_1029 = lean_ctor_get(x_1, 4);
x_1030 = lean_ctor_get(x_1, 5);
x_1031 = lean_ctor_get(x_1, 6);
x_1032 = lean_ctor_get(x_1, 7);
x_1033 = lean_ctor_get(x_1, 8);
x_1034 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1035 = lean_ctor_get(x_1, 9);
x_1036 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1037 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1052 = !lean_is_exclusive(x_1);
if (x_1052 == 0)
{
x_1038 = x_1;
x_1039 = x_1052;
goto block_1051;
}
else
{
lean_inc(x_1035);
lean_inc(x_1033);
lean_inc(x_1032);
lean_inc(x_1031);
lean_inc(x_1030);
lean_inc(x_1029);
lean_inc(x_1028);
lean_inc(x_1025);
lean_inc(x_1017);
lean_inc(x_1016);
lean_dec(x_1);
x_1038 = lean_box(0);
x_1039 = x_1052;
goto block_1051;
}
block_1051:
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
x_1040 = l___private_Lean_Shell_0__Lean_timeout;
x_1041 = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(x_1016, x_1040, x_1015);
x_1042 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
x_1043 = lean_string_append(x_1042, x_1008);
lean_dec(x_1008);
x_1044 = lean_array_push(x_1017, x_1043);
if (x_1039 == 0)
{
lean_ctor_set(x_1038, 1, x_1044);
lean_ctor_set(x_1038, 0, x_1041);
x_1045 = x_1038;
goto block_1049;
}
else
{
lean_object* x_1050; 
x_1050 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1050, 0, x_1041);
lean_ctor_set(x_1050, 1, x_1044);
lean_ctor_set(x_1050, 2, x_1025);
lean_ctor_set(x_1050, 3, x_1028);
lean_ctor_set(x_1050, 4, x_1029);
lean_ctor_set(x_1050, 5, x_1030);
lean_ctor_set(x_1050, 6, x_1031);
lean_ctor_set(x_1050, 7, x_1032);
lean_ctor_set(x_1050, 8, x_1033);
lean_ctor_set(x_1050, 9, x_1035);
lean_ctor_set_uint8(x_1050, sizeof(void*)*10 + 8, x_1018);
lean_ctor_set_uint8(x_1050, sizeof(void*)*10 + 9, x_1019);
lean_ctor_set_uint8(x_1050, sizeof(void*)*10 + 10, x_1020);
lean_ctor_set_uint8(x_1050, sizeof(void*)*10 + 11, x_1021);
lean_ctor_set_uint8(x_1050, sizeof(void*)*10 + 12, x_1022);
lean_ctor_set_uint8(x_1050, sizeof(void*)*10 + 13, x_1023);
lean_ctor_set_uint8(x_1050, sizeof(void*)*10 + 14, x_1024);
lean_ctor_set_uint32(x_1050, sizeof(void*)*10, x_1026);
lean_ctor_set_uint32(x_1050, sizeof(void*)*10 + 4, x_1027);
lean_ctor_set_uint8(x_1050, sizeof(void*)*10 + 15, x_1034);
lean_ctor_set_uint8(x_1050, sizeof(void*)*10 + 16, x_1036);
lean_ctor_set_uint8(x_1050, sizeof(void*)*10 + 17, x_1037);
x_1045 = x_1050;
goto block_1049;
}
block_1049:
{
lean_object* x_1046; 
if (x_1010 == 0)
{
lean_ctor_set(x_1009, 0, x_1045);
x_1046 = x_1009;
goto block_1047;
}
else
{
lean_object* x_1048; 
x_1048 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1048, 0, x_1045);
x_1046 = x_1048;
goto block_1047;
}
block_1047:
{
return x_1046;
}
}
}
}
else
{
lean_object* x_1053; lean_object* x_1054; 
lean_dec(x_1014);
lean_del_object(x_1009);
lean_dec(x_1008);
lean_dec_ref(x_1);
x_1053 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
x_1054 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1053);
lean_dec_ref(x_1054);
x_202 = lean_box(0);
goto block_205;
}
}
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1062; lean_object* x_1063; 
lean_dec_ref(x_1);
x_1057 = lean_ctor_get(x_1007, 0);
lean_inc(x_1057);
lean_dec_ref(x_1007);
x_1062 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1063 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1062);
lean_dec_ref(x_1063);
x_1058 = lean_box(0);
goto block_1061;
block_1061:
{
lean_object* x_1059; lean_object* x_1060; 
x_1059 = lean_io_error_to_string(x_1057);
x_1060 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1059);
lean_dec_ref(x_1060);
x_210 = lean_box(0);
goto block_213;
}
}
}
}
else
{
lean_object* x_1064; lean_object* x_1065; 
x_1064 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
x_1065 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1064, x_3);
if (lean_obj_tag(x_1065) == 0)
{
lean_object* x_1066; lean_object* x_1067; uint8_t x_1068; uint8_t x_1114; 
x_1066 = lean_ctor_get(x_1065, 0);
x_1114 = !lean_is_exclusive(x_1065);
if (x_1114 == 0)
{
x_1067 = x_1065;
x_1068 = x_1114;
goto block_1113;
}
else
{
lean_inc(x_1066);
lean_dec(x_1065);
x_1067 = lean_box(0);
x_1068 = x_1114;
goto block_1113;
}
block_1113:
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
x_1069 = lean_unsigned_to_nat(0u);
x_1070 = lean_string_utf8_byte_size(x_1066);
lean_inc(x_1066);
x_1071 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1071, 0, x_1066);
lean_ctor_set(x_1071, 1, x_1069);
lean_ctor_set(x_1071, 2, x_1070);
x_1072 = l_String_Slice_toNat_x3f(x_1071);
lean_dec_ref(x_1071);
if (lean_obj_tag(x_1072) == 1)
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; uint8_t x_1076; uint8_t x_1077; uint8_t x_1078; uint8_t x_1079; uint8_t x_1080; uint8_t x_1081; uint8_t x_1082; lean_object* x_1083; uint32_t x_1084; uint32_t x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; uint8_t x_1092; lean_object* x_1093; uint8_t x_1094; uint8_t x_1095; lean_object* x_1096; uint8_t x_1097; uint8_t x_1110; 
x_1073 = lean_ctor_get(x_1072, 0);
lean_inc(x_1073);
lean_dec_ref(x_1072);
x_1074 = lean_ctor_get(x_1, 0);
x_1075 = lean_ctor_get(x_1, 1);
x_1076 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1077 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1078 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1079 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1080 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1081 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1082 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1083 = lean_ctor_get(x_1, 2);
x_1084 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1085 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1086 = lean_ctor_get(x_1, 3);
x_1087 = lean_ctor_get(x_1, 4);
x_1088 = lean_ctor_get(x_1, 5);
x_1089 = lean_ctor_get(x_1, 6);
x_1090 = lean_ctor_get(x_1, 7);
x_1091 = lean_ctor_get(x_1, 8);
x_1092 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1093 = lean_ctor_get(x_1, 9);
x_1094 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1095 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1110 = !lean_is_exclusive(x_1);
if (x_1110 == 0)
{
x_1096 = x_1;
x_1097 = x_1110;
goto block_1109;
}
else
{
lean_inc(x_1093);
lean_inc(x_1091);
lean_inc(x_1090);
lean_inc(x_1089);
lean_inc(x_1088);
lean_inc(x_1087);
lean_inc(x_1086);
lean_inc(x_1083);
lean_inc(x_1075);
lean_inc(x_1074);
lean_dec(x_1);
x_1096 = lean_box(0);
x_1097 = x_1110;
goto block_1109;
}
block_1109:
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
x_1098 = l___private_Lean_Shell_0__Lean_maxMemory;
x_1099 = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(x_1074, x_1098, x_1073);
x_1100 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
x_1101 = lean_string_append(x_1100, x_1066);
lean_dec(x_1066);
x_1102 = lean_array_push(x_1075, x_1101);
if (x_1097 == 0)
{
lean_ctor_set(x_1096, 1, x_1102);
lean_ctor_set(x_1096, 0, x_1099);
x_1103 = x_1096;
goto block_1107;
}
else
{
lean_object* x_1108; 
x_1108 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1108, 0, x_1099);
lean_ctor_set(x_1108, 1, x_1102);
lean_ctor_set(x_1108, 2, x_1083);
lean_ctor_set(x_1108, 3, x_1086);
lean_ctor_set(x_1108, 4, x_1087);
lean_ctor_set(x_1108, 5, x_1088);
lean_ctor_set(x_1108, 6, x_1089);
lean_ctor_set(x_1108, 7, x_1090);
lean_ctor_set(x_1108, 8, x_1091);
lean_ctor_set(x_1108, 9, x_1093);
lean_ctor_set_uint8(x_1108, sizeof(void*)*10 + 8, x_1076);
lean_ctor_set_uint8(x_1108, sizeof(void*)*10 + 9, x_1077);
lean_ctor_set_uint8(x_1108, sizeof(void*)*10 + 10, x_1078);
lean_ctor_set_uint8(x_1108, sizeof(void*)*10 + 11, x_1079);
lean_ctor_set_uint8(x_1108, sizeof(void*)*10 + 12, x_1080);
lean_ctor_set_uint8(x_1108, sizeof(void*)*10 + 13, x_1081);
lean_ctor_set_uint8(x_1108, sizeof(void*)*10 + 14, x_1082);
lean_ctor_set_uint32(x_1108, sizeof(void*)*10, x_1084);
lean_ctor_set_uint32(x_1108, sizeof(void*)*10 + 4, x_1085);
lean_ctor_set_uint8(x_1108, sizeof(void*)*10 + 15, x_1092);
lean_ctor_set_uint8(x_1108, sizeof(void*)*10 + 16, x_1094);
lean_ctor_set_uint8(x_1108, sizeof(void*)*10 + 17, x_1095);
x_1103 = x_1108;
goto block_1107;
}
block_1107:
{
lean_object* x_1104; 
if (x_1068 == 0)
{
lean_ctor_set(x_1067, 0, x_1103);
x_1104 = x_1067;
goto block_1105;
}
else
{
lean_object* x_1106; 
x_1106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1106, 0, x_1103);
x_1104 = x_1106;
goto block_1105;
}
block_1105:
{
return x_1104;
}
}
}
}
else
{
lean_object* x_1111; lean_object* x_1112; 
lean_dec(x_1072);
lean_del_object(x_1067);
lean_dec(x_1066);
lean_dec_ref(x_1);
x_1111 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
x_1112 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1111);
lean_dec_ref(x_1112);
x_77 = lean_box(0);
goto block_80;
}
}
}
else
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1120; lean_object* x_1121; 
lean_dec_ref(x_1);
x_1115 = lean_ctor_get(x_1065, 0);
lean_inc(x_1115);
lean_dec_ref(x_1065);
x_1120 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1121 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1120);
lean_dec_ref(x_1121);
x_1116 = lean_box(0);
goto block_1119;
block_1119:
{
lean_object* x_1117; lean_object* x_1118; 
x_1117 = lean_io_error_to_string(x_1115);
x_1118 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1117);
lean_dec_ref(x_1118);
x_73 = lean_box(0);
goto block_76;
}
}
}
}
else
{
lean_object* x_1122; lean_object* x_1123; 
x_1122 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
x_1123 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1122, x_3);
if (lean_obj_tag(x_1123) == 0)
{
lean_object* x_1124; lean_object* x_1125; uint8_t x_1126; uint8_t x_1164; 
x_1124 = lean_ctor_get(x_1123, 0);
x_1164 = !lean_is_exclusive(x_1123);
if (x_1164 == 0)
{
x_1125 = x_1123;
x_1126 = x_1164;
goto block_1163;
}
else
{
lean_inc(x_1124);
lean_dec(x_1123);
x_1125 = lean_box(0);
x_1126 = x_1164;
goto block_1163;
}
block_1163:
{
lean_object* x_1127; lean_object* x_1128; uint8_t x_1129; uint8_t x_1130; uint8_t x_1131; uint8_t x_1132; uint8_t x_1133; uint8_t x_1134; uint8_t x_1135; lean_object* x_1136; uint32_t x_1137; uint32_t x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; uint8_t x_1144; lean_object* x_1145; uint8_t x_1146; uint8_t x_1147; lean_object* x_1148; uint8_t x_1149; uint8_t x_1161; 
x_1127 = lean_ctor_get(x_1, 0);
x_1128 = lean_ctor_get(x_1, 1);
x_1129 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1130 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1131 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1132 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1133 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1134 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1135 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1136 = lean_ctor_get(x_1, 2);
x_1137 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1138 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1139 = lean_ctor_get(x_1, 4);
x_1140 = lean_ctor_get(x_1, 5);
x_1141 = lean_ctor_get(x_1, 6);
x_1142 = lean_ctor_get(x_1, 7);
x_1143 = lean_ctor_get(x_1, 8);
x_1144 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1145 = lean_ctor_get(x_1, 9);
x_1146 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1147 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1161 = !lean_is_exclusive(x_1);
if (x_1161 == 0)
{
lean_object* x_1162; 
x_1162 = lean_ctor_get(x_1, 3);
lean_dec(x_1162);
x_1148 = x_1;
x_1149 = x_1161;
goto block_1160;
}
else
{
lean_inc(x_1145);
lean_inc(x_1143);
lean_inc(x_1142);
lean_inc(x_1141);
lean_inc(x_1140);
lean_inc(x_1139);
lean_inc(x_1136);
lean_inc(x_1128);
lean_inc(x_1127);
lean_dec(x_1);
x_1148 = lean_box(0);
x_1149 = x_1161;
goto block_1160;
}
block_1160:
{
lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; 
x_1150 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
x_1151 = lean_string_append(x_1150, x_1124);
x_1152 = lean_array_push(x_1128, x_1151);
x_1153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1153, 0, x_1124);
if (x_1149 == 0)
{
lean_ctor_set(x_1148, 3, x_1153);
lean_ctor_set(x_1148, 1, x_1152);
x_1154 = x_1148;
goto block_1158;
}
else
{
lean_object* x_1159; 
x_1159 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1159, 0, x_1127);
lean_ctor_set(x_1159, 1, x_1152);
lean_ctor_set(x_1159, 2, x_1136);
lean_ctor_set(x_1159, 3, x_1153);
lean_ctor_set(x_1159, 4, x_1139);
lean_ctor_set(x_1159, 5, x_1140);
lean_ctor_set(x_1159, 6, x_1141);
lean_ctor_set(x_1159, 7, x_1142);
lean_ctor_set(x_1159, 8, x_1143);
lean_ctor_set(x_1159, 9, x_1145);
lean_ctor_set_uint8(x_1159, sizeof(void*)*10 + 8, x_1129);
lean_ctor_set_uint8(x_1159, sizeof(void*)*10 + 9, x_1130);
lean_ctor_set_uint8(x_1159, sizeof(void*)*10 + 10, x_1131);
lean_ctor_set_uint8(x_1159, sizeof(void*)*10 + 11, x_1132);
lean_ctor_set_uint8(x_1159, sizeof(void*)*10 + 12, x_1133);
lean_ctor_set_uint8(x_1159, sizeof(void*)*10 + 13, x_1134);
lean_ctor_set_uint8(x_1159, sizeof(void*)*10 + 14, x_1135);
lean_ctor_set_uint32(x_1159, sizeof(void*)*10, x_1137);
lean_ctor_set_uint32(x_1159, sizeof(void*)*10 + 4, x_1138);
lean_ctor_set_uint8(x_1159, sizeof(void*)*10 + 15, x_1144);
lean_ctor_set_uint8(x_1159, sizeof(void*)*10 + 16, x_1146);
lean_ctor_set_uint8(x_1159, sizeof(void*)*10 + 17, x_1147);
x_1154 = x_1159;
goto block_1158;
}
block_1158:
{
lean_object* x_1155; 
if (x_1126 == 0)
{
lean_ctor_set(x_1125, 0, x_1154);
x_1155 = x_1125;
goto block_1156;
}
else
{
lean_object* x_1157; 
x_1157 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1157, 0, x_1154);
x_1155 = x_1157;
goto block_1156;
}
block_1156:
{
return x_1155;
}
}
}
}
}
else
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1170; lean_object* x_1171; 
lean_dec_ref(x_1);
x_1165 = lean_ctor_get(x_1123, 0);
lean_inc(x_1165);
lean_dec_ref(x_1123);
x_1170 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1171 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1170);
lean_dec_ref(x_1171);
x_1166 = lean_box(0);
goto block_1169;
block_1169:
{
lean_object* x_1167; lean_object* x_1168; 
x_1167 = lean_io_error_to_string(x_1165);
x_1168 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1167);
lean_dec_ref(x_1168);
x_218 = lean_box(0);
goto block_221;
}
}
}
}
else
{
lean_object* x_1172; lean_object* x_1173; 
x_1172 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
x_1173 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1172, x_3);
if (lean_obj_tag(x_1173) == 0)
{
lean_object* x_1174; lean_object* x_1175; uint8_t x_1176; uint8_t x_1211; 
x_1174 = lean_ctor_get(x_1173, 0);
x_1211 = !lean_is_exclusive(x_1173);
if (x_1211 == 0)
{
x_1175 = x_1173;
x_1176 = x_1211;
goto block_1210;
}
else
{
lean_inc(x_1174);
lean_dec(x_1173);
x_1175 = lean_box(0);
x_1176 = x_1211;
goto block_1210;
}
block_1210:
{
lean_object* x_1177; lean_object* x_1178; uint8_t x_1179; uint8_t x_1180; uint8_t x_1181; uint8_t x_1182; uint8_t x_1183; uint8_t x_1184; uint8_t x_1185; lean_object* x_1186; uint32_t x_1187; uint32_t x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; uint8_t x_1194; lean_object* x_1195; uint8_t x_1196; uint8_t x_1197; lean_object* x_1198; uint8_t x_1199; uint8_t x_1208; 
x_1177 = lean_ctor_get(x_1, 0);
x_1178 = lean_ctor_get(x_1, 1);
x_1179 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1180 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1181 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1182 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1183 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1184 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1185 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1186 = lean_ctor_get(x_1, 2);
x_1187 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1188 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1189 = lean_ctor_get(x_1, 3);
x_1190 = lean_ctor_get(x_1, 4);
x_1191 = lean_ctor_get(x_1, 5);
x_1192 = lean_ctor_get(x_1, 7);
x_1193 = lean_ctor_get(x_1, 8);
x_1194 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1195 = lean_ctor_get(x_1, 9);
x_1196 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1197 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1208 = !lean_is_exclusive(x_1);
if (x_1208 == 0)
{
lean_object* x_1209; 
x_1209 = lean_ctor_get(x_1, 6);
lean_dec(x_1209);
x_1198 = x_1;
x_1199 = x_1208;
goto block_1207;
}
else
{
lean_inc(x_1195);
lean_inc(x_1193);
lean_inc(x_1192);
lean_inc(x_1191);
lean_inc(x_1190);
lean_inc(x_1189);
lean_inc(x_1186);
lean_inc(x_1178);
lean_inc(x_1177);
lean_dec(x_1);
x_1198 = lean_box(0);
x_1199 = x_1208;
goto block_1207;
}
block_1207:
{
lean_object* x_1200; lean_object* x_1201; 
x_1200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1200, 0, x_1174);
if (x_1199 == 0)
{
lean_ctor_set(x_1198, 6, x_1200);
x_1201 = x_1198;
goto block_1205;
}
else
{
lean_object* x_1206; 
x_1206 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1206, 0, x_1177);
lean_ctor_set(x_1206, 1, x_1178);
lean_ctor_set(x_1206, 2, x_1186);
lean_ctor_set(x_1206, 3, x_1189);
lean_ctor_set(x_1206, 4, x_1190);
lean_ctor_set(x_1206, 5, x_1191);
lean_ctor_set(x_1206, 6, x_1200);
lean_ctor_set(x_1206, 7, x_1192);
lean_ctor_set(x_1206, 8, x_1193);
lean_ctor_set(x_1206, 9, x_1195);
lean_ctor_set_uint8(x_1206, sizeof(void*)*10 + 8, x_1179);
lean_ctor_set_uint8(x_1206, sizeof(void*)*10 + 9, x_1180);
lean_ctor_set_uint8(x_1206, sizeof(void*)*10 + 10, x_1181);
lean_ctor_set_uint8(x_1206, sizeof(void*)*10 + 11, x_1182);
lean_ctor_set_uint8(x_1206, sizeof(void*)*10 + 12, x_1183);
lean_ctor_set_uint8(x_1206, sizeof(void*)*10 + 13, x_1184);
lean_ctor_set_uint8(x_1206, sizeof(void*)*10 + 14, x_1185);
lean_ctor_set_uint32(x_1206, sizeof(void*)*10, x_1187);
lean_ctor_set_uint32(x_1206, sizeof(void*)*10 + 4, x_1188);
lean_ctor_set_uint8(x_1206, sizeof(void*)*10 + 15, x_1194);
lean_ctor_set_uint8(x_1206, sizeof(void*)*10 + 16, x_1196);
lean_ctor_set_uint8(x_1206, sizeof(void*)*10 + 17, x_1197);
x_1201 = x_1206;
goto block_1205;
}
block_1205:
{
lean_object* x_1202; 
if (x_1176 == 0)
{
lean_ctor_set(x_1175, 0, x_1201);
x_1202 = x_1175;
goto block_1203;
}
else
{
lean_object* x_1204; 
x_1204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1204, 0, x_1201);
x_1202 = x_1204;
goto block_1203;
}
block_1203:
{
return x_1202;
}
}
}
}
}
else
{
lean_object* x_1212; lean_object* x_1213; lean_object* x_1217; lean_object* x_1218; 
lean_dec_ref(x_1);
x_1212 = lean_ctor_get(x_1173, 0);
lean_inc(x_1212);
lean_dec_ref(x_1173);
x_1217 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1218 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1217);
lean_dec_ref(x_1218);
x_1213 = lean_box(0);
goto block_1216;
block_1216:
{
lean_object* x_1214; lean_object* x_1215; 
x_1214 = lean_io_error_to_string(x_1212);
x_1215 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1214);
lean_dec_ref(x_1215);
x_65 = lean_box(0);
goto block_68;
}
}
}
}
else
{
lean_object* x_1219; lean_object* x_1220; 
x_1219 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
x_1220 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1219, x_3);
if (lean_obj_tag(x_1220) == 0)
{
lean_object* x_1221; lean_object* x_1222; uint8_t x_1223; uint8_t x_1258; 
x_1221 = lean_ctor_get(x_1220, 0);
x_1258 = !lean_is_exclusive(x_1220);
if (x_1258 == 0)
{
x_1222 = x_1220;
x_1223 = x_1258;
goto block_1257;
}
else
{
lean_inc(x_1221);
lean_dec(x_1220);
x_1222 = lean_box(0);
x_1223 = x_1258;
goto block_1257;
}
block_1257:
{
lean_object* x_1224; lean_object* x_1225; uint8_t x_1226; uint8_t x_1227; uint8_t x_1228; uint8_t x_1229; uint8_t x_1230; uint8_t x_1231; uint8_t x_1232; lean_object* x_1233; uint32_t x_1234; uint32_t x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; uint8_t x_1241; lean_object* x_1242; uint8_t x_1243; uint8_t x_1244; lean_object* x_1245; uint8_t x_1246; uint8_t x_1255; 
x_1224 = lean_ctor_get(x_1, 0);
x_1225 = lean_ctor_get(x_1, 1);
x_1226 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1227 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1228 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1229 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1230 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1231 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1232 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1233 = lean_ctor_get(x_1, 2);
x_1234 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1235 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1236 = lean_ctor_get(x_1, 3);
x_1237 = lean_ctor_get(x_1, 4);
x_1238 = lean_ctor_get(x_1, 6);
x_1239 = lean_ctor_get(x_1, 7);
x_1240 = lean_ctor_get(x_1, 8);
x_1241 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1242 = lean_ctor_get(x_1, 9);
x_1243 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1244 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1255 = !lean_is_exclusive(x_1);
if (x_1255 == 0)
{
lean_object* x_1256; 
x_1256 = lean_ctor_get(x_1, 5);
lean_dec(x_1256);
x_1245 = x_1;
x_1246 = x_1255;
goto block_1254;
}
else
{
lean_inc(x_1242);
lean_inc(x_1240);
lean_inc(x_1239);
lean_inc(x_1238);
lean_inc(x_1237);
lean_inc(x_1236);
lean_inc(x_1233);
lean_inc(x_1225);
lean_inc(x_1224);
lean_dec(x_1);
x_1245 = lean_box(0);
x_1246 = x_1255;
goto block_1254;
}
block_1254:
{
lean_object* x_1247; lean_object* x_1248; 
x_1247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1247, 0, x_1221);
if (x_1246 == 0)
{
lean_ctor_set(x_1245, 5, x_1247);
x_1248 = x_1245;
goto block_1252;
}
else
{
lean_object* x_1253; 
x_1253 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1253, 0, x_1224);
lean_ctor_set(x_1253, 1, x_1225);
lean_ctor_set(x_1253, 2, x_1233);
lean_ctor_set(x_1253, 3, x_1236);
lean_ctor_set(x_1253, 4, x_1237);
lean_ctor_set(x_1253, 5, x_1247);
lean_ctor_set(x_1253, 6, x_1238);
lean_ctor_set(x_1253, 7, x_1239);
lean_ctor_set(x_1253, 8, x_1240);
lean_ctor_set(x_1253, 9, x_1242);
lean_ctor_set_uint8(x_1253, sizeof(void*)*10 + 8, x_1226);
lean_ctor_set_uint8(x_1253, sizeof(void*)*10 + 9, x_1227);
lean_ctor_set_uint8(x_1253, sizeof(void*)*10 + 10, x_1228);
lean_ctor_set_uint8(x_1253, sizeof(void*)*10 + 11, x_1229);
lean_ctor_set_uint8(x_1253, sizeof(void*)*10 + 12, x_1230);
lean_ctor_set_uint8(x_1253, sizeof(void*)*10 + 13, x_1231);
lean_ctor_set_uint8(x_1253, sizeof(void*)*10 + 14, x_1232);
lean_ctor_set_uint32(x_1253, sizeof(void*)*10, x_1234);
lean_ctor_set_uint32(x_1253, sizeof(void*)*10 + 4, x_1235);
lean_ctor_set_uint8(x_1253, sizeof(void*)*10 + 15, x_1241);
lean_ctor_set_uint8(x_1253, sizeof(void*)*10 + 16, x_1243);
lean_ctor_set_uint8(x_1253, sizeof(void*)*10 + 17, x_1244);
x_1248 = x_1253;
goto block_1252;
}
block_1252:
{
lean_object* x_1249; 
if (x_1223 == 0)
{
lean_ctor_set(x_1222, 0, x_1248);
x_1249 = x_1222;
goto block_1250;
}
else
{
lean_object* x_1251; 
x_1251 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1251, 0, x_1248);
x_1249 = x_1251;
goto block_1250;
}
block_1250:
{
return x_1249;
}
}
}
}
}
else
{
lean_object* x_1259; lean_object* x_1260; lean_object* x_1264; lean_object* x_1265; 
lean_dec_ref(x_1);
x_1259 = lean_ctor_get(x_1220, 0);
lean_inc(x_1259);
lean_dec_ref(x_1220);
x_1264 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1265 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1264);
lean_dec_ref(x_1265);
x_1260 = lean_box(0);
goto block_1263;
block_1263:
{
lean_object* x_1261; lean_object* x_1262; 
x_1261 = lean_io_error_to_string(x_1259);
x_1262 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1261);
lean_dec_ref(x_1262);
x_226 = lean_box(0);
goto block_229;
}
}
}
}
else
{
lean_object* x_1266; lean_object* x_1267; uint8_t x_1268; uint8_t x_1269; uint8_t x_1270; uint8_t x_1271; uint8_t x_1272; uint8_t x_1273; uint8_t x_1274; lean_object* x_1275; uint32_t x_1276; uint32_t x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; uint8_t x_1284; lean_object* x_1285; uint8_t x_1286; lean_object* x_1287; uint8_t x_1288; uint8_t x_1294; 
lean_dec(x_3);
x_1266 = lean_ctor_get(x_1, 0);
x_1267 = lean_ctor_get(x_1, 1);
x_1268 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1269 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1270 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1271 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1272 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1273 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1274 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1275 = lean_ctor_get(x_1, 2);
x_1276 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1277 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1278 = lean_ctor_get(x_1, 3);
x_1279 = lean_ctor_get(x_1, 4);
x_1280 = lean_ctor_get(x_1, 5);
x_1281 = lean_ctor_get(x_1, 6);
x_1282 = lean_ctor_get(x_1, 7);
x_1283 = lean_ctor_get(x_1, 8);
x_1284 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1285 = lean_ctor_get(x_1, 9);
x_1286 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1294 = !lean_is_exclusive(x_1);
if (x_1294 == 0)
{
x_1287 = x_1;
x_1288 = x_1294;
goto block_1293;
}
else
{
lean_inc(x_1285);
lean_inc(x_1283);
lean_inc(x_1282);
lean_inc(x_1281);
lean_inc(x_1280);
lean_inc(x_1279);
lean_inc(x_1278);
lean_inc(x_1275);
lean_inc(x_1267);
lean_inc(x_1266);
lean_dec(x_1);
x_1287 = lean_box(0);
x_1288 = x_1294;
goto block_1293;
}
block_1293:
{
lean_object* x_1289; 
if (x_1288 == 0)
{
x_1289 = x_1287;
goto block_1291;
}
else
{
lean_object* x_1292; 
x_1292 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1292, 0, x_1266);
lean_ctor_set(x_1292, 1, x_1267);
lean_ctor_set(x_1292, 2, x_1275);
lean_ctor_set(x_1292, 3, x_1278);
lean_ctor_set(x_1292, 4, x_1279);
lean_ctor_set(x_1292, 5, x_1280);
lean_ctor_set(x_1292, 6, x_1281);
lean_ctor_set(x_1292, 7, x_1282);
lean_ctor_set(x_1292, 8, x_1283);
lean_ctor_set(x_1292, 9, x_1285);
lean_ctor_set_uint8(x_1292, sizeof(void*)*10 + 8, x_1268);
lean_ctor_set_uint8(x_1292, sizeof(void*)*10 + 9, x_1269);
lean_ctor_set_uint8(x_1292, sizeof(void*)*10 + 10, x_1270);
lean_ctor_set_uint8(x_1292, sizeof(void*)*10 + 11, x_1271);
lean_ctor_set_uint8(x_1292, sizeof(void*)*10 + 12, x_1272);
lean_ctor_set_uint8(x_1292, sizeof(void*)*10 + 13, x_1273);
lean_ctor_set_uint8(x_1292, sizeof(void*)*10 + 14, x_1274);
lean_ctor_set_uint32(x_1292, sizeof(void*)*10, x_1276);
lean_ctor_set_uint32(x_1292, sizeof(void*)*10 + 4, x_1277);
lean_ctor_set_uint8(x_1292, sizeof(void*)*10 + 15, x_1284);
lean_ctor_set_uint8(x_1292, sizeof(void*)*10 + 16, x_1286);
x_1289 = x_1292;
goto block_1291;
}
block_1291:
{
lean_object* x_1290; 
lean_ctor_set_uint8(x_1289, sizeof(void*)*10 + 17, x_285);
x_1290 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1290, 0, x_1289);
return x_1290;
}
}
}
}
else
{
lean_object* x_1295; lean_object* x_1296; uint8_t x_1297; uint8_t x_1298; uint8_t x_1299; uint8_t x_1300; uint8_t x_1301; uint8_t x_1302; lean_object* x_1303; uint32_t x_1304; uint32_t x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; uint8_t x_1312; lean_object* x_1313; uint8_t x_1314; uint8_t x_1315; lean_object* x_1316; uint8_t x_1317; uint8_t x_1323; 
lean_dec(x_3);
x_1295 = lean_ctor_get(x_1, 0);
x_1296 = lean_ctor_get(x_1, 1);
x_1297 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1298 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1299 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1300 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1301 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1302 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1303 = lean_ctor_get(x_1, 2);
x_1304 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1305 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1306 = lean_ctor_get(x_1, 3);
x_1307 = lean_ctor_get(x_1, 4);
x_1308 = lean_ctor_get(x_1, 5);
x_1309 = lean_ctor_get(x_1, 6);
x_1310 = lean_ctor_get(x_1, 7);
x_1311 = lean_ctor_get(x_1, 8);
x_1312 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1313 = lean_ctor_get(x_1, 9);
x_1314 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1315 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1323 = !lean_is_exclusive(x_1);
if (x_1323 == 0)
{
x_1316 = x_1;
x_1317 = x_1323;
goto block_1322;
}
else
{
lean_inc(x_1313);
lean_inc(x_1311);
lean_inc(x_1310);
lean_inc(x_1309);
lean_inc(x_1308);
lean_inc(x_1307);
lean_inc(x_1306);
lean_inc(x_1303);
lean_inc(x_1296);
lean_inc(x_1295);
lean_dec(x_1);
x_1316 = lean_box(0);
x_1317 = x_1323;
goto block_1322;
}
block_1322:
{
lean_object* x_1318; 
if (x_1317 == 0)
{
x_1318 = x_1316;
goto block_1320;
}
else
{
lean_object* x_1321; 
x_1321 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1321, 0, x_1295);
lean_ctor_set(x_1321, 1, x_1296);
lean_ctor_set(x_1321, 2, x_1303);
lean_ctor_set(x_1321, 3, x_1306);
lean_ctor_set(x_1321, 4, x_1307);
lean_ctor_set(x_1321, 5, x_1308);
lean_ctor_set(x_1321, 6, x_1309);
lean_ctor_set(x_1321, 7, x_1310);
lean_ctor_set(x_1321, 8, x_1311);
lean_ctor_set(x_1321, 9, x_1313);
lean_ctor_set_uint8(x_1321, sizeof(void*)*10 + 8, x_1297);
lean_ctor_set_uint8(x_1321, sizeof(void*)*10 + 9, x_1298);
lean_ctor_set_uint8(x_1321, sizeof(void*)*10 + 10, x_1299);
lean_ctor_set_uint8(x_1321, sizeof(void*)*10 + 12, x_1300);
lean_ctor_set_uint8(x_1321, sizeof(void*)*10 + 13, x_1301);
lean_ctor_set_uint8(x_1321, sizeof(void*)*10 + 14, x_1302);
lean_ctor_set_uint32(x_1321, sizeof(void*)*10, x_1304);
lean_ctor_set_uint32(x_1321, sizeof(void*)*10 + 4, x_1305);
lean_ctor_set_uint8(x_1321, sizeof(void*)*10 + 15, x_1312);
lean_ctor_set_uint8(x_1321, sizeof(void*)*10 + 16, x_1314);
lean_ctor_set_uint8(x_1321, sizeof(void*)*10 + 17, x_1315);
x_1318 = x_1321;
goto block_1320;
}
block_1320:
{
lean_object* x_1319; 
lean_ctor_set_uint8(x_1318, sizeof(void*)*10 + 11, x_283);
x_1319 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1319, 0, x_1318);
return x_1319;
}
}
}
}
else
{
lean_object* x_1324; lean_object* x_1325; 
x_1324 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
x_1325 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1324, x_3);
if (lean_obj_tag(x_1325) == 0)
{
lean_object* x_1326; lean_object* x_1327; uint8_t x_1328; uint8_t x_1384; 
x_1326 = lean_ctor_get(x_1325, 0);
x_1384 = !lean_is_exclusive(x_1325);
if (x_1384 == 0)
{
x_1327 = x_1325;
x_1328 = x_1384;
goto block_1383;
}
else
{
lean_inc(x_1326);
lean_dec(x_1325);
x_1327 = lean_box(0);
x_1328 = x_1384;
goto block_1383;
}
block_1383:
{
lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; 
x_1329 = lean_unsigned_to_nat(0u);
x_1330 = lean_string_utf8_byte_size(x_1326);
lean_inc(x_1326);
x_1331 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1331, 0, x_1326);
lean_ctor_set(x_1331, 1, x_1329);
lean_ctor_set(x_1331, 2, x_1330);
x_1332 = l_String_Slice_toNat_x3f(x_1331);
lean_dec_ref(x_1331);
if (lean_obj_tag(x_1332) == 1)
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; uint8_t x_1341; 
x_1333 = lean_ctor_get(x_1332, 0);
lean_inc(x_1333);
lean_dec_ref(x_1332);
x_1334 = lean_unsigned_to_nat(4u);
x_1335 = lean_unsigned_to_nat(2u);
x_1336 = lean_nat_shiftr(x_1333, x_1335);
lean_dec(x_1333);
x_1337 = lean_nat_mul(x_1336, x_1334);
lean_dec(x_1336);
x_1338 = lean_unsigned_to_nat(1024u);
x_1339 = lean_nat_mul(x_1337, x_1338);
lean_dec(x_1337);
x_1340 = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25);
x_1341 = lean_nat_dec_lt(x_1339, x_1340);
if (x_1341 == 0)
{
lean_object* x_1342; lean_object* x_1343; 
lean_dec(x_1339);
lean_del_object(x_1327);
lean_dec(x_1326);
lean_dec_ref(x_1);
x_1342 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
x_1343 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1342);
lean_dec_ref(x_1343);
x_57 = lean_box(0);
goto block_60;
}
else
{
size_t x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; uint8_t x_1348; uint8_t x_1349; uint8_t x_1350; uint8_t x_1351; uint8_t x_1352; uint8_t x_1353; uint8_t x_1354; lean_object* x_1355; uint32_t x_1356; uint32_t x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; uint8_t x_1364; lean_object* x_1365; uint8_t x_1366; uint8_t x_1367; lean_object* x_1368; uint8_t x_1369; uint8_t x_1380; 
x_1344 = lean_usize_of_nat(x_1339);
lean_dec(x_1339);
x_1345 = lean_internal_set_thread_stack_size(x_1344);
x_1346 = lean_ctor_get(x_1, 0);
x_1347 = lean_ctor_get(x_1, 1);
x_1348 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1349 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1350 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1351 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1352 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1353 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1354 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1355 = lean_ctor_get(x_1, 2);
x_1356 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1357 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1358 = lean_ctor_get(x_1, 3);
x_1359 = lean_ctor_get(x_1, 4);
x_1360 = lean_ctor_get(x_1, 5);
x_1361 = lean_ctor_get(x_1, 6);
x_1362 = lean_ctor_get(x_1, 7);
x_1363 = lean_ctor_get(x_1, 8);
x_1364 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1365 = lean_ctor_get(x_1, 9);
x_1366 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1367 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1380 = !lean_is_exclusive(x_1);
if (x_1380 == 0)
{
x_1368 = x_1;
x_1369 = x_1380;
goto block_1379;
}
else
{
lean_inc(x_1365);
lean_inc(x_1363);
lean_inc(x_1362);
lean_inc(x_1361);
lean_inc(x_1360);
lean_inc(x_1359);
lean_inc(x_1358);
lean_inc(x_1355);
lean_inc(x_1347);
lean_inc(x_1346);
lean_dec(x_1);
x_1368 = lean_box(0);
x_1369 = x_1380;
goto block_1379;
}
block_1379:
{
lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; 
x_1370 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
x_1371 = lean_string_append(x_1370, x_1326);
lean_dec(x_1326);
x_1372 = lean_array_push(x_1347, x_1371);
if (x_1369 == 0)
{
lean_ctor_set(x_1368, 1, x_1372);
x_1373 = x_1368;
goto block_1377;
}
else
{
lean_object* x_1378; 
x_1378 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1378, 0, x_1346);
lean_ctor_set(x_1378, 1, x_1372);
lean_ctor_set(x_1378, 2, x_1355);
lean_ctor_set(x_1378, 3, x_1358);
lean_ctor_set(x_1378, 4, x_1359);
lean_ctor_set(x_1378, 5, x_1360);
lean_ctor_set(x_1378, 6, x_1361);
lean_ctor_set(x_1378, 7, x_1362);
lean_ctor_set(x_1378, 8, x_1363);
lean_ctor_set(x_1378, 9, x_1365);
lean_ctor_set_uint8(x_1378, sizeof(void*)*10 + 8, x_1348);
lean_ctor_set_uint8(x_1378, sizeof(void*)*10 + 9, x_1349);
lean_ctor_set_uint8(x_1378, sizeof(void*)*10 + 10, x_1350);
lean_ctor_set_uint8(x_1378, sizeof(void*)*10 + 11, x_1351);
lean_ctor_set_uint8(x_1378, sizeof(void*)*10 + 12, x_1352);
lean_ctor_set_uint8(x_1378, sizeof(void*)*10 + 13, x_1353);
lean_ctor_set_uint8(x_1378, sizeof(void*)*10 + 14, x_1354);
lean_ctor_set_uint32(x_1378, sizeof(void*)*10, x_1356);
lean_ctor_set_uint32(x_1378, sizeof(void*)*10 + 4, x_1357);
lean_ctor_set_uint8(x_1378, sizeof(void*)*10 + 15, x_1364);
lean_ctor_set_uint8(x_1378, sizeof(void*)*10 + 16, x_1366);
lean_ctor_set_uint8(x_1378, sizeof(void*)*10 + 17, x_1367);
x_1373 = x_1378;
goto block_1377;
}
block_1377:
{
lean_object* x_1374; 
if (x_1328 == 0)
{
lean_ctor_set(x_1327, 0, x_1373);
x_1374 = x_1327;
goto block_1375;
}
else
{
lean_object* x_1376; 
x_1376 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1376, 0, x_1373);
x_1374 = x_1376;
goto block_1375;
}
block_1375:
{
return x_1374;
}
}
}
}
}
else
{
lean_object* x_1381; lean_object* x_1382; 
lean_dec(x_1332);
lean_del_object(x_1327);
lean_dec(x_1326);
lean_dec_ref(x_1);
x_1381 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28));
x_1382 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1381);
lean_dec_ref(x_1382);
x_53 = lean_box(0);
goto block_56;
}
}
}
else
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1390; lean_object* x_1391; 
lean_dec_ref(x_1);
x_1385 = lean_ctor_get(x_1325, 0);
lean_inc(x_1385);
lean_dec_ref(x_1325);
x_1390 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1391 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1390);
lean_dec_ref(x_1391);
x_1386 = lean_box(0);
goto block_1389;
block_1389:
{
lean_object* x_1387; lean_object* x_1388; 
x_1387 = lean_io_error_to_string(x_1385);
x_1388 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1387);
lean_dec_ref(x_1388);
x_49 = lean_box(0);
goto block_52;
}
}
}
}
else
{
lean_object* x_1392; lean_object* x_1393; 
x_1392 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
x_1393 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1392, x_3);
if (lean_obj_tag(x_1393) == 0)
{
lean_object* x_1394; lean_object* x_1395; uint8_t x_1396; uint8_t x_1431; 
x_1394 = lean_ctor_get(x_1393, 0);
x_1431 = !lean_is_exclusive(x_1393);
if (x_1431 == 0)
{
x_1395 = x_1393;
x_1396 = x_1431;
goto block_1430;
}
else
{
lean_inc(x_1394);
lean_dec(x_1393);
x_1395 = lean_box(0);
x_1396 = x_1431;
goto block_1430;
}
block_1430:
{
lean_object* x_1397; lean_object* x_1398; uint8_t x_1399; uint8_t x_1400; uint8_t x_1401; uint8_t x_1402; uint8_t x_1403; uint8_t x_1404; uint8_t x_1405; lean_object* x_1406; uint32_t x_1407; uint32_t x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; uint8_t x_1414; lean_object* x_1415; uint8_t x_1416; uint8_t x_1417; lean_object* x_1418; uint8_t x_1419; uint8_t x_1428; 
x_1397 = lean_ctor_get(x_1, 0);
x_1398 = lean_ctor_get(x_1, 1);
x_1399 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1400 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1401 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1402 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1403 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1404 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1405 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1406 = lean_ctor_get(x_1, 2);
x_1407 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1408 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1409 = lean_ctor_get(x_1, 3);
x_1410 = lean_ctor_get(x_1, 4);
x_1411 = lean_ctor_get(x_1, 5);
x_1412 = lean_ctor_get(x_1, 6);
x_1413 = lean_ctor_get(x_1, 7);
x_1414 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1415 = lean_ctor_get(x_1, 9);
x_1416 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1417 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1428 = !lean_is_exclusive(x_1);
if (x_1428 == 0)
{
lean_object* x_1429; 
x_1429 = lean_ctor_get(x_1, 8);
lean_dec(x_1429);
x_1418 = x_1;
x_1419 = x_1428;
goto block_1427;
}
else
{
lean_inc(x_1415);
lean_inc(x_1413);
lean_inc(x_1412);
lean_inc(x_1411);
lean_inc(x_1410);
lean_inc(x_1409);
lean_inc(x_1406);
lean_inc(x_1398);
lean_inc(x_1397);
lean_dec(x_1);
x_1418 = lean_box(0);
x_1419 = x_1428;
goto block_1427;
}
block_1427:
{
lean_object* x_1420; lean_object* x_1421; 
x_1420 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1420, 0, x_1394);
if (x_1419 == 0)
{
lean_ctor_set(x_1418, 8, x_1420);
x_1421 = x_1418;
goto block_1425;
}
else
{
lean_object* x_1426; 
x_1426 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1426, 0, x_1397);
lean_ctor_set(x_1426, 1, x_1398);
lean_ctor_set(x_1426, 2, x_1406);
lean_ctor_set(x_1426, 3, x_1409);
lean_ctor_set(x_1426, 4, x_1410);
lean_ctor_set(x_1426, 5, x_1411);
lean_ctor_set(x_1426, 6, x_1412);
lean_ctor_set(x_1426, 7, x_1413);
lean_ctor_set(x_1426, 8, x_1420);
lean_ctor_set(x_1426, 9, x_1415);
lean_ctor_set_uint8(x_1426, sizeof(void*)*10 + 8, x_1399);
lean_ctor_set_uint8(x_1426, sizeof(void*)*10 + 9, x_1400);
lean_ctor_set_uint8(x_1426, sizeof(void*)*10 + 10, x_1401);
lean_ctor_set_uint8(x_1426, sizeof(void*)*10 + 11, x_1402);
lean_ctor_set_uint8(x_1426, sizeof(void*)*10 + 12, x_1403);
lean_ctor_set_uint8(x_1426, sizeof(void*)*10 + 13, x_1404);
lean_ctor_set_uint8(x_1426, sizeof(void*)*10 + 14, x_1405);
lean_ctor_set_uint32(x_1426, sizeof(void*)*10, x_1407);
lean_ctor_set_uint32(x_1426, sizeof(void*)*10 + 4, x_1408);
lean_ctor_set_uint8(x_1426, sizeof(void*)*10 + 15, x_1414);
lean_ctor_set_uint8(x_1426, sizeof(void*)*10 + 16, x_1416);
lean_ctor_set_uint8(x_1426, sizeof(void*)*10 + 17, x_1417);
x_1421 = x_1426;
goto block_1425;
}
block_1425:
{
lean_object* x_1422; 
if (x_1396 == 0)
{
lean_ctor_set(x_1395, 0, x_1421);
x_1422 = x_1395;
goto block_1423;
}
else
{
lean_object* x_1424; 
x_1424 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1424, 0, x_1421);
x_1422 = x_1424;
goto block_1423;
}
block_1423:
{
return x_1422;
}
}
}
}
}
else
{
lean_object* x_1432; lean_object* x_1433; lean_object* x_1437; lean_object* x_1438; 
lean_dec_ref(x_1);
x_1432 = lean_ctor_get(x_1393, 0);
lean_inc(x_1432);
lean_dec_ref(x_1393);
x_1437 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1438 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1437);
lean_dec_ref(x_1438);
x_1433 = lean_box(0);
goto block_1436;
block_1436:
{
lean_object* x_1434; lean_object* x_1435; 
x_1434 = lean_io_error_to_string(x_1432);
x_1435 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1434);
lean_dec_ref(x_1435);
x_234 = lean_box(0);
goto block_237;
}
}
}
}
else
{
lean_object* x_1439; lean_object* x_1440; 
x_1439 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
x_1440 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1439, x_3);
if (lean_obj_tag(x_1440) == 0)
{
lean_object* x_1441; lean_object* x_1442; uint8_t x_1443; uint8_t x_1478; 
x_1441 = lean_ctor_get(x_1440, 0);
x_1478 = !lean_is_exclusive(x_1440);
if (x_1478 == 0)
{
x_1442 = x_1440;
x_1443 = x_1478;
goto block_1477;
}
else
{
lean_inc(x_1441);
lean_dec(x_1440);
x_1442 = lean_box(0);
x_1443 = x_1478;
goto block_1477;
}
block_1477:
{
lean_object* x_1444; lean_object* x_1445; uint8_t x_1446; uint8_t x_1447; uint8_t x_1448; uint8_t x_1449; uint8_t x_1450; uint8_t x_1451; uint8_t x_1452; lean_object* x_1453; uint32_t x_1454; uint32_t x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; uint8_t x_1461; lean_object* x_1462; uint8_t x_1463; uint8_t x_1464; lean_object* x_1465; uint8_t x_1466; uint8_t x_1475; 
x_1444 = lean_ctor_get(x_1, 0);
x_1445 = lean_ctor_get(x_1, 1);
x_1446 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1447 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1448 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1449 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1450 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1451 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1452 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1453 = lean_ctor_get(x_1, 2);
x_1454 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1455 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1456 = lean_ctor_get(x_1, 3);
x_1457 = lean_ctor_get(x_1, 4);
x_1458 = lean_ctor_get(x_1, 5);
x_1459 = lean_ctor_get(x_1, 6);
x_1460 = lean_ctor_get(x_1, 8);
x_1461 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1462 = lean_ctor_get(x_1, 9);
x_1463 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1464 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1475 = !lean_is_exclusive(x_1);
if (x_1475 == 0)
{
lean_object* x_1476; 
x_1476 = lean_ctor_get(x_1, 7);
lean_dec(x_1476);
x_1465 = x_1;
x_1466 = x_1475;
goto block_1474;
}
else
{
lean_inc(x_1462);
lean_inc(x_1460);
lean_inc(x_1459);
lean_inc(x_1458);
lean_inc(x_1457);
lean_inc(x_1456);
lean_inc(x_1453);
lean_inc(x_1445);
lean_inc(x_1444);
lean_dec(x_1);
x_1465 = lean_box(0);
x_1466 = x_1475;
goto block_1474;
}
block_1474:
{
lean_object* x_1467; lean_object* x_1468; 
x_1467 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1467, 0, x_1441);
if (x_1466 == 0)
{
lean_ctor_set(x_1465, 7, x_1467);
x_1468 = x_1465;
goto block_1472;
}
else
{
lean_object* x_1473; 
x_1473 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1473, 0, x_1444);
lean_ctor_set(x_1473, 1, x_1445);
lean_ctor_set(x_1473, 2, x_1453);
lean_ctor_set(x_1473, 3, x_1456);
lean_ctor_set(x_1473, 4, x_1457);
lean_ctor_set(x_1473, 5, x_1458);
lean_ctor_set(x_1473, 6, x_1459);
lean_ctor_set(x_1473, 7, x_1467);
lean_ctor_set(x_1473, 8, x_1460);
lean_ctor_set(x_1473, 9, x_1462);
lean_ctor_set_uint8(x_1473, sizeof(void*)*10 + 8, x_1446);
lean_ctor_set_uint8(x_1473, sizeof(void*)*10 + 9, x_1447);
lean_ctor_set_uint8(x_1473, sizeof(void*)*10 + 10, x_1448);
lean_ctor_set_uint8(x_1473, sizeof(void*)*10 + 11, x_1449);
lean_ctor_set_uint8(x_1473, sizeof(void*)*10 + 12, x_1450);
lean_ctor_set_uint8(x_1473, sizeof(void*)*10 + 13, x_1451);
lean_ctor_set_uint8(x_1473, sizeof(void*)*10 + 14, x_1452);
lean_ctor_set_uint32(x_1473, sizeof(void*)*10, x_1454);
lean_ctor_set_uint32(x_1473, sizeof(void*)*10 + 4, x_1455);
lean_ctor_set_uint8(x_1473, sizeof(void*)*10 + 15, x_1461);
lean_ctor_set_uint8(x_1473, sizeof(void*)*10 + 16, x_1463);
lean_ctor_set_uint8(x_1473, sizeof(void*)*10 + 17, x_1464);
x_1468 = x_1473;
goto block_1472;
}
block_1472:
{
lean_object* x_1469; 
if (x_1443 == 0)
{
lean_ctor_set(x_1442, 0, x_1468);
x_1469 = x_1442;
goto block_1470;
}
else
{
lean_object* x_1471; 
x_1471 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1471, 0, x_1468);
x_1469 = x_1471;
goto block_1470;
}
block_1470:
{
return x_1469;
}
}
}
}
}
else
{
lean_object* x_1479; lean_object* x_1480; lean_object* x_1484; lean_object* x_1485; 
lean_dec_ref(x_1);
x_1479 = lean_ctor_get(x_1440, 0);
lean_inc(x_1479);
lean_dec_ref(x_1440);
x_1484 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1485 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1484);
lean_dec_ref(x_1485);
x_1480 = lean_box(0);
goto block_1483;
block_1483:
{
lean_object* x_1481; lean_object* x_1482; 
x_1481 = lean_io_error_to_string(x_1479);
x_1482 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1481);
lean_dec_ref(x_1482);
x_41 = lean_box(0);
goto block_44;
}
}
}
}
else
{
lean_object* x_1486; lean_object* x_1487; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1486 = l___private_Lean_Shell_0__Lean_featuresString;
x_1487 = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(x_1486);
if (lean_obj_tag(x_1487) == 0)
{
lean_object* x_1488; uint8_t x_1489; uint8_t x_1495; 
x_1495 = !lean_is_exclusive(x_1487);
if (x_1495 == 0)
{
lean_object* x_1496; 
x_1496 = lean_ctor_get(x_1487, 0);
lean_dec(x_1496);
x_1488 = x_1487;
x_1489 = x_1495;
goto block_1494;
}
else
{
lean_dec(x_1487);
x_1488 = lean_box(0);
x_1489 = x_1495;
goto block_1494;
}
block_1494:
{
lean_object* x_1490; lean_object* x_1491; 
x_1490 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_1489 == 0)
{
lean_ctor_set_tag(x_1488, 1);
lean_ctor_set(x_1488, 0, x_1490);
x_1491 = x_1488;
goto block_1492;
}
else
{
lean_object* x_1493; 
x_1493 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1493, 0, x_1490);
x_1491 = x_1493;
goto block_1492;
}
block_1492:
{
return x_1491;
}
}
}
else
{
lean_object* x_1497; lean_object* x_1498; lean_object* x_1502; lean_object* x_1503; 
x_1497 = lean_ctor_get(x_1487, 0);
lean_inc(x_1497);
lean_dec_ref(x_1487);
x_1502 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1503 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1502);
lean_dec_ref(x_1503);
x_1498 = lean_box(0);
goto block_1501;
block_1501:
{
lean_object* x_1499; lean_object* x_1500; 
x_1499 = lean_io_error_to_string(x_1497);
x_1500 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1499);
lean_dec_ref(x_1500);
x_242 = lean_box(0);
goto block_245;
}
}
}
}
else
{
lean_object* x_1504; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1504 = l___private_Lean_Shell_0__Lean_displayHelp(x_271);
if (lean_obj_tag(x_1504) == 0)
{
lean_object* x_1505; uint8_t x_1506; uint8_t x_1512; 
x_1512 = !lean_is_exclusive(x_1504);
if (x_1512 == 0)
{
lean_object* x_1513; 
x_1513 = lean_ctor_get(x_1504, 0);
lean_dec(x_1513);
x_1505 = x_1504;
x_1506 = x_1512;
goto block_1511;
}
else
{
lean_dec(x_1504);
x_1505 = lean_box(0);
x_1506 = x_1512;
goto block_1511;
}
block_1511:
{
lean_object* x_1507; lean_object* x_1508; 
x_1507 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_1506 == 0)
{
lean_ctor_set_tag(x_1505, 1);
lean_ctor_set(x_1505, 0, x_1507);
x_1508 = x_1505;
goto block_1509;
}
else
{
lean_object* x_1510; 
x_1510 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1510, 0, x_1507);
x_1508 = x_1510;
goto block_1509;
}
block_1509:
{
return x_1508;
}
}
}
else
{
lean_object* x_1514; lean_object* x_1515; lean_object* x_1519; lean_object* x_1520; 
x_1514 = lean_ctor_get(x_1504, 0);
lean_inc(x_1514);
lean_dec_ref(x_1504);
x_1519 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1520 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1519);
lean_dec_ref(x_1520);
x_1515 = lean_box(0);
goto block_1518;
block_1518:
{
lean_object* x_1516; lean_object* x_1517; 
x_1516 = lean_io_error_to_string(x_1514);
x_1517 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1516);
lean_dec_ref(x_1517);
x_33 = lean_box(0);
goto block_36;
}
}
}
}
else
{
lean_object* x_1521; lean_object* x_1522; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1521 = l_Lean_githash;
x_1522 = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(x_1521);
if (lean_obj_tag(x_1522) == 0)
{
lean_object* x_1523; uint8_t x_1524; uint8_t x_1530; 
x_1530 = !lean_is_exclusive(x_1522);
if (x_1530 == 0)
{
lean_object* x_1531; 
x_1531 = lean_ctor_get(x_1522, 0);
lean_dec(x_1531);
x_1523 = x_1522;
x_1524 = x_1530;
goto block_1529;
}
else
{
lean_dec(x_1522);
x_1523 = lean_box(0);
x_1524 = x_1530;
goto block_1529;
}
block_1529:
{
lean_object* x_1525; lean_object* x_1526; 
x_1525 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_1524 == 0)
{
lean_ctor_set_tag(x_1523, 1);
lean_ctor_set(x_1523, 0, x_1525);
x_1526 = x_1523;
goto block_1527;
}
else
{
lean_object* x_1528; 
x_1528 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1528, 0, x_1525);
x_1526 = x_1528;
goto block_1527;
}
block_1527:
{
return x_1526;
}
}
}
else
{
lean_object* x_1532; lean_object* x_1533; lean_object* x_1537; lean_object* x_1538; 
x_1532 = lean_ctor_get(x_1522, 0);
lean_inc(x_1532);
lean_dec_ref(x_1522);
x_1537 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1538 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1537);
lean_dec_ref(x_1538);
x_1533 = lean_box(0);
goto block_1536;
block_1536:
{
lean_object* x_1534; lean_object* x_1535; 
x_1534 = lean_io_error_to_string(x_1532);
x_1535 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1534);
lean_dec_ref(x_1535);
x_250 = lean_box(0);
goto block_253;
}
}
}
}
else
{
lean_object* x_1539; lean_object* x_1540; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1539 = l___private_Lean_Shell_0__Lean_shortVersionString;
x_1540 = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(x_1539);
if (lean_obj_tag(x_1540) == 0)
{
lean_object* x_1541; uint8_t x_1542; uint8_t x_1548; 
x_1548 = !lean_is_exclusive(x_1540);
if (x_1548 == 0)
{
lean_object* x_1549; 
x_1549 = lean_ctor_get(x_1540, 0);
lean_dec(x_1549);
x_1541 = x_1540;
x_1542 = x_1548;
goto block_1547;
}
else
{
lean_dec(x_1540);
x_1541 = lean_box(0);
x_1542 = x_1548;
goto block_1547;
}
block_1547:
{
lean_object* x_1543; lean_object* x_1544; 
x_1543 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_1542 == 0)
{
lean_ctor_set_tag(x_1541, 1);
lean_ctor_set(x_1541, 0, x_1543);
x_1544 = x_1541;
goto block_1545;
}
else
{
lean_object* x_1546; 
x_1546 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1546, 0, x_1543);
x_1544 = x_1546;
goto block_1545;
}
block_1545:
{
return x_1544;
}
}
}
else
{
lean_object* x_1550; lean_object* x_1551; lean_object* x_1555; lean_object* x_1556; 
x_1550 = lean_ctor_get(x_1540, 0);
lean_inc(x_1550);
lean_dec_ref(x_1540);
x_1555 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1556 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1555);
lean_dec_ref(x_1556);
x_1551 = lean_box(0);
goto block_1554;
block_1554:
{
lean_object* x_1552; lean_object* x_1553; 
x_1552 = lean_io_error_to_string(x_1550);
x_1553 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1552);
lean_dec_ref(x_1553);
x_25 = lean_box(0);
goto block_28;
}
}
}
}
else
{
lean_object* x_1557; lean_object* x_1558; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1557 = l___private_Lean_Shell_0__Lean_versionHeader;
x_1558 = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(x_1557);
if (lean_obj_tag(x_1558) == 0)
{
lean_object* x_1559; uint8_t x_1560; uint8_t x_1566; 
x_1566 = !lean_is_exclusive(x_1558);
if (x_1566 == 0)
{
lean_object* x_1567; 
x_1567 = lean_ctor_get(x_1558, 0);
lean_dec(x_1567);
x_1559 = x_1558;
x_1560 = x_1566;
goto block_1565;
}
else
{
lean_dec(x_1558);
x_1559 = lean_box(0);
x_1560 = x_1566;
goto block_1565;
}
block_1565:
{
lean_object* x_1561; lean_object* x_1562; 
x_1561 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_1560 == 0)
{
lean_ctor_set_tag(x_1559, 1);
lean_ctor_set(x_1559, 0, x_1561);
x_1562 = x_1559;
goto block_1563;
}
else
{
lean_object* x_1564; 
x_1564 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1564, 0, x_1561);
x_1562 = x_1564;
goto block_1563;
}
block_1563:
{
return x_1562;
}
}
}
else
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1573; lean_object* x_1574; 
x_1568 = lean_ctor_get(x_1558, 0);
lean_inc(x_1568);
lean_dec_ref(x_1558);
x_1573 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1574 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1573);
lean_dec_ref(x_1574);
x_1569 = lean_box(0);
goto block_1572;
block_1572:
{
lean_object* x_1570; lean_object* x_1571; 
x_1570 = lean_io_error_to_string(x_1568);
x_1571 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1570);
lean_dec_ref(x_1571);
x_258 = lean_box(0);
goto block_261;
}
}
}
}
else
{
lean_object* x_1575; lean_object* x_1576; 
x_1575 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
x_1576 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1575, x_3);
if (lean_obj_tag(x_1576) == 0)
{
lean_object* x_1577; lean_object* x_1578; uint8_t x_1579; uint8_t x_1627; 
x_1577 = lean_ctor_get(x_1576, 0);
x_1627 = !lean_is_exclusive(x_1576);
if (x_1627 == 0)
{
x_1578 = x_1576;
x_1579 = x_1627;
goto block_1626;
}
else
{
lean_inc(x_1577);
lean_dec(x_1576);
x_1578 = lean_box(0);
x_1579 = x_1627;
goto block_1626;
}
block_1626:
{
lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; 
x_1580 = lean_unsigned_to_nat(0u);
x_1581 = lean_string_utf8_byte_size(x_1577);
lean_inc(x_1577);
x_1582 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1582, 0, x_1577);
lean_ctor_set(x_1582, 1, x_1580);
lean_ctor_set(x_1582, 2, x_1581);
x_1583 = l_String_Slice_toNat_x3f(x_1582);
lean_dec_ref(x_1582);
if (lean_obj_tag(x_1583) == 1)
{
lean_object* x_1584; lean_object* x_1585; uint8_t x_1586; 
x_1584 = lean_ctor_get(x_1583, 0);
lean_inc(x_1584);
lean_dec_ref(x_1583);
x_1585 = lean_cstr_to_nat("4294967296");
x_1586 = lean_nat_dec_lt(x_1584, x_1585);
if (x_1586 == 0)
{
lean_object* x_1587; lean_object* x_1588; 
lean_dec(x_1584);
lean_del_object(x_1578);
lean_dec(x_1577);
lean_dec_ref(x_1);
x_1587 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
x_1588 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1587);
lean_dec_ref(x_1588);
x_17 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_1589; lean_object* x_1590; uint8_t x_1591; uint8_t x_1592; uint8_t x_1593; uint8_t x_1594; uint8_t x_1595; uint8_t x_1596; uint8_t x_1597; lean_object* x_1598; uint32_t x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; uint8_t x_1606; lean_object* x_1607; uint8_t x_1608; uint8_t x_1609; lean_object* x_1610; uint8_t x_1611; uint8_t x_1623; 
x_1589 = lean_ctor_get(x_1, 0);
x_1590 = lean_ctor_get(x_1, 1);
x_1591 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1592 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1593 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1594 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1595 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1596 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1597 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1598 = lean_ctor_get(x_1, 2);
x_1599 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1600 = lean_ctor_get(x_1, 3);
x_1601 = lean_ctor_get(x_1, 4);
x_1602 = lean_ctor_get(x_1, 5);
x_1603 = lean_ctor_get(x_1, 6);
x_1604 = lean_ctor_get(x_1, 7);
x_1605 = lean_ctor_get(x_1, 8);
x_1606 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1607 = lean_ctor_get(x_1, 9);
x_1608 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1609 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1623 = !lean_is_exclusive(x_1);
if (x_1623 == 0)
{
x_1610 = x_1;
x_1611 = x_1623;
goto block_1622;
}
else
{
lean_inc(x_1607);
lean_inc(x_1605);
lean_inc(x_1604);
lean_inc(x_1603);
lean_inc(x_1602);
lean_inc(x_1601);
lean_inc(x_1600);
lean_inc(x_1598);
lean_inc(x_1590);
lean_inc(x_1589);
lean_dec(x_1);
x_1610 = lean_box(0);
x_1611 = x_1623;
goto block_1622;
}
block_1622:
{
uint32_t x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; 
x_1612 = lean_uint32_of_nat(x_1584);
lean_dec(x_1584);
x_1613 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
x_1614 = lean_string_append(x_1613, x_1577);
lean_dec(x_1577);
x_1615 = lean_array_push(x_1590, x_1614);
if (x_1611 == 0)
{
lean_ctor_set(x_1610, 1, x_1615);
x_1616 = x_1610;
goto block_1620;
}
else
{
lean_object* x_1621; 
x_1621 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1621, 0, x_1589);
lean_ctor_set(x_1621, 1, x_1615);
lean_ctor_set(x_1621, 2, x_1598);
lean_ctor_set(x_1621, 3, x_1600);
lean_ctor_set(x_1621, 4, x_1601);
lean_ctor_set(x_1621, 5, x_1602);
lean_ctor_set(x_1621, 6, x_1603);
lean_ctor_set(x_1621, 7, x_1604);
lean_ctor_set(x_1621, 8, x_1605);
lean_ctor_set(x_1621, 9, x_1607);
lean_ctor_set_uint8(x_1621, sizeof(void*)*10 + 8, x_1591);
lean_ctor_set_uint8(x_1621, sizeof(void*)*10 + 9, x_1592);
lean_ctor_set_uint8(x_1621, sizeof(void*)*10 + 10, x_1593);
lean_ctor_set_uint8(x_1621, sizeof(void*)*10 + 11, x_1594);
lean_ctor_set_uint8(x_1621, sizeof(void*)*10 + 12, x_1595);
lean_ctor_set_uint8(x_1621, sizeof(void*)*10 + 13, x_1596);
lean_ctor_set_uint8(x_1621, sizeof(void*)*10 + 14, x_1597);
lean_ctor_set_uint32(x_1621, sizeof(void*)*10, x_1599);
lean_ctor_set_uint8(x_1621, sizeof(void*)*10 + 15, x_1606);
lean_ctor_set_uint8(x_1621, sizeof(void*)*10 + 16, x_1608);
lean_ctor_set_uint8(x_1621, sizeof(void*)*10 + 17, x_1609);
x_1616 = x_1621;
goto block_1620;
}
block_1620:
{
lean_object* x_1617; 
lean_ctor_set_uint32(x_1616, sizeof(void*)*10 + 4, x_1612);
if (x_1579 == 0)
{
lean_ctor_set(x_1578, 0, x_1616);
x_1617 = x_1578;
goto block_1618;
}
else
{
lean_object* x_1619; 
x_1619 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1619, 0, x_1616);
x_1617 = x_1619;
goto block_1618;
}
block_1618:
{
return x_1617;
}
}
}
}
}
else
{
lean_object* x_1624; lean_object* x_1625; 
lean_dec(x_1583);
lean_del_object(x_1578);
lean_dec(x_1577);
lean_dec_ref(x_1);
x_1624 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
x_1625 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1624);
lean_dec_ref(x_1625);
x_13 = lean_box(0);
goto block_16;
}
}
}
else
{
lean_object* x_1628; lean_object* x_1629; lean_object* x_1633; lean_object* x_1634; 
lean_dec_ref(x_1);
x_1628 = lean_ctor_get(x_1576, 0);
lean_inc(x_1628);
lean_dec_ref(x_1576);
x_1633 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1634 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1633);
lean_dec_ref(x_1634);
x_1629 = lean_box(0);
goto block_1632;
block_1632:
{
lean_object* x_1630; lean_object* x_1631; 
x_1630 = lean_io_error_to_string(x_1628);
x_1631 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1630);
lean_dec_ref(x_1631);
x_9 = lean_box(0);
goto block_12;
}
}
}
}
else
{
lean_object* x_1635; lean_object* x_1636; 
lean_dec(x_3);
x_1635 = lean_internal_set_exit_on_panic(x_263);
x_1636 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1636, 0, x_1);
return x_1636;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_11 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_10);
lean_dec_ref(x_11);
x_5 = lean_box(0);
goto block_8;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_27 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_26);
lean_dec_ref(x_27);
x_21 = lean_box(0);
goto block_24;
}
block_32:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
block_36:
{
lean_object* x_34; lean_object* x_35; 
x_34 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_35 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_34);
lean_dec_ref(x_35);
x_29 = lean_box(0);
goto block_32;
}
block_40:
{
lean_object* x_38; lean_object* x_39; 
x_38 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
block_44:
{
lean_object* x_42; lean_object* x_43; 
x_42 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_43 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_42);
lean_dec_ref(x_43);
x_37 = lean_box(0);
goto block_40;
}
block_48:
{
lean_object* x_46; lean_object* x_47; 
x_46 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
block_52:
{
lean_object* x_50; lean_object* x_51; 
x_50 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_51 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_50);
lean_dec_ref(x_51);
x_45 = lean_box(0);
goto block_48;
}
block_56:
{
lean_object* x_54; lean_object* x_55; 
x_54 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
block_60:
{
lean_object* x_58; lean_object* x_59; 
x_58 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
block_64:
{
lean_object* x_62; lean_object* x_63; 
x_62 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
block_68:
{
lean_object* x_66; lean_object* x_67; 
x_66 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_67 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_66);
lean_dec_ref(x_67);
x_61 = lean_box(0);
goto block_64;
}
block_72:
{
lean_object* x_70; lean_object* x_71; 
x_70 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
block_76:
{
lean_object* x_74; lean_object* x_75; 
x_74 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_75 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_74);
lean_dec_ref(x_75);
x_69 = lean_box(0);
goto block_72;
}
block_80:
{
lean_object* x_78; lean_object* x_79; 
x_78 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
block_84:
{
lean_object* x_82; lean_object* x_83; 
x_82 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
block_88:
{
lean_object* x_86; lean_object* x_87; 
x_86 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_87 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_86);
lean_dec_ref(x_87);
x_81 = lean_box(0);
goto block_84;
}
block_92:
{
lean_object* x_90; lean_object* x_91; 
x_90 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
block_96:
{
lean_object* x_94; lean_object* x_95; 
x_94 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
block_100:
{
lean_object* x_98; lean_object* x_99; 
x_98 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
block_104:
{
lean_object* x_102; lean_object* x_103; 
x_102 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_103 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_102);
lean_dec_ref(x_103);
x_97 = lean_box(0);
goto block_100;
}
block_108:
{
lean_object* x_106; lean_object* x_107; 
x_106 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
block_112:
{
lean_object* x_110; lean_object* x_111; 
x_110 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_111 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_110);
lean_dec_ref(x_111);
x_105 = lean_box(0);
goto block_108;
}
block_116:
{
lean_object* x_114; lean_object* x_115; 
x_114 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
block_120:
{
lean_object* x_118; lean_object* x_119; 
x_118 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_119 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_118);
lean_dec_ref(x_119);
x_113 = lean_box(0);
goto block_116;
}
block_124:
{
lean_object* x_122; lean_object* x_123; 
x_122 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
block_128:
{
lean_object* x_126; lean_object* x_127; 
x_126 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_127 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_126);
lean_dec_ref(x_127);
x_121 = lean_box(0);
goto block_124;
}
block_132:
{
lean_object* x_130; lean_object* x_131; 
x_130 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
block_136:
{
lean_object* x_134; lean_object* x_135; 
x_134 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_135 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_134);
lean_dec_ref(x_135);
x_129 = lean_box(0);
goto block_132;
}
block_141:
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_io_error_to_string(x_137);
x_140 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_139);
lean_dec_ref(x_140);
x_133 = lean_box(0);
goto block_136;
}
block_157:
{
uint8_t x_143; lean_object* x_144; 
x_143 = 1;
x_144 = l___private_Lean_Shell_0__Lean_displayHelp(x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; uint8_t x_146; uint8_t x_152; 
x_152 = !lean_is_exclusive(x_144);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_144, 0);
lean_dec(x_153);
x_145 = x_144;
x_146 = x_152;
goto block_151;
}
else
{
lean_dec(x_144);
x_145 = lean_box(0);
x_146 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_147; lean_object* x_148; 
x_147 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (x_146 == 0)
{
lean_ctor_set_tag(x_145, 1);
lean_ctor_set(x_145, 0, x_147);
x_148 = x_145;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_147);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_144, 0);
lean_inc(x_154);
lean_dec_ref(x_144);
x_155 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_156 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_155);
lean_dec_ref(x_156);
x_137 = x_154;
x_138 = lean_box(0);
goto block_141;
}
}
block_161:
{
lean_object* x_159; lean_object* x_160; 
x_159 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
x_160 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_159);
lean_dec_ref(x_160);
x_142 = lean_box(0);
goto block_157;
}
block_165:
{
lean_object* x_163; lean_object* x_164; 
x_163 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
block_169:
{
lean_object* x_167; lean_object* x_168; 
x_167 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_168 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_167);
lean_dec_ref(x_168);
x_162 = lean_box(0);
goto block_165;
}
block_173:
{
lean_object* x_171; lean_object* x_172; 
x_171 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
block_177:
{
lean_object* x_175; lean_object* x_176; 
x_175 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_176 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_175);
lean_dec_ref(x_176);
x_170 = lean_box(0);
goto block_173;
}
block_181:
{
lean_object* x_179; lean_object* x_180; 
x_179 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_179);
return x_180;
}
block_185:
{
lean_object* x_183; lean_object* x_184; 
x_183 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_184 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_183);
lean_dec_ref(x_184);
x_178 = lean_box(0);
goto block_181;
}
block_189:
{
lean_object* x_187; lean_object* x_188; 
x_187 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
return x_188;
}
block_193:
{
lean_object* x_191; lean_object* x_192; 
x_191 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_192 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_191);
lean_dec_ref(x_192);
x_186 = lean_box(0);
goto block_189;
}
block_197:
{
lean_object* x_195; lean_object* x_196; 
x_195 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_195);
return x_196;
}
block_201:
{
lean_object* x_199; lean_object* x_200; 
x_199 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_200 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_199);
lean_dec_ref(x_200);
x_194 = lean_box(0);
goto block_197;
}
block_205:
{
lean_object* x_203; lean_object* x_204; 
x_203 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
return x_204;
}
block_209:
{
lean_object* x_207; lean_object* x_208; 
x_207 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
return x_208;
}
block_213:
{
lean_object* x_211; lean_object* x_212; 
x_211 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_212 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_211);
lean_dec_ref(x_212);
x_206 = lean_box(0);
goto block_209;
}
block_217:
{
lean_object* x_215; lean_object* x_216; 
x_215 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
return x_216;
}
block_221:
{
lean_object* x_219; lean_object* x_220; 
x_219 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_220 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_219);
lean_dec_ref(x_220);
x_214 = lean_box(0);
goto block_217;
}
block_225:
{
lean_object* x_223; lean_object* x_224; 
x_223 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_224 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_224, 0, x_223);
return x_224;
}
block_229:
{
lean_object* x_227; lean_object* x_228; 
x_227 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_228 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_227);
lean_dec_ref(x_228);
x_222 = lean_box(0);
goto block_225;
}
block_233:
{
lean_object* x_231; lean_object* x_232; 
x_231 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_231);
return x_232;
}
block_237:
{
lean_object* x_235; lean_object* x_236; 
x_235 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_236 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_235);
lean_dec_ref(x_236);
x_230 = lean_box(0);
goto block_233;
}
block_241:
{
lean_object* x_239; lean_object* x_240; 
x_239 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
return x_240;
}
block_245:
{
lean_object* x_243; lean_object* x_244; 
x_243 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_244 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_243);
lean_dec_ref(x_244);
x_238 = lean_box(0);
goto block_241;
}
block_249:
{
lean_object* x_247; lean_object* x_248; 
x_247 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_248, 0, x_247);
return x_248;
}
block_253:
{
lean_object* x_251; lean_object* x_252; 
x_251 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_252 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_251);
lean_dec_ref(x_252);
x_246 = lean_box(0);
goto block_249;
}
block_257:
{
lean_object* x_255; lean_object* x_256; 
x_255 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_255);
return x_256;
}
block_261:
{
lean_object* x_259; lean_object* x_260; 
x_259 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_260 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_259);
lean_dec_ref(x_260);
x_254 = lean_box(0);
goto block_257;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = lean_shell_options_process(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
x_4 = x_1;
x_5 = x_11;
goto block_10;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_io_user_error(x_3);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_6);
x_7 = x_4;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_13 = x_1;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__0));
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg___closed__1);
x_5 = lean_nat_dec_le(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_memcmp(x_1, x_2, x_7, x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_1);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_3);
x_11 = l_String_Slice_pos_x21(x_10, x_4);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00__private_Lean_Shell_0__Lean_shellMain_spec__0___redArg(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_string_to_utf8(x_5);
lean_dec(x_5);
x_7 = lean_io_prim_handle_write(x_2, x_6);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
x_8 = lean_ctor_get(x_4, 0);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
x_9 = x_4;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Shell_0__Lean_shellMain___lam__0(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
lean_dec(x_3);
x_9 = 10;
x_10 = lean_nat_add(x_5, x_2);
x_11 = lean_string_utf8_get_fast(x_4, x_10);
x_12 = lean_uint32_dec_eq(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_string_utf8_next_fast(x_4, x_10);
lean_dec(x_10);
x_15 = lean_nat_sub(x_14, x_5);
x_2 = x_15;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__5(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at___00IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3_spec__5(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__5(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0(void) {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_has_address_sanitizer(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__6));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__7, &l___private_Lean_Shell_0__Lean_shellMain___closed__7_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__7);
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__6));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_26; lean_object* x_27; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint32_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_389; lean_object* x_395; lean_object* x_412; 
x_47 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_48);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 8);
x_50 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 9);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 10);
x_52 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 11);
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 12);
x_54 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 13);
x_55 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 14);
x_56 = lean_ctor_get_uint32(x_2, sizeof(void*)*10);
x_57 = lean_ctor_get(x_2, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 5);
lean_inc(x_59);
x_60 = lean_ctor_get(x_2, 6);
lean_inc(x_60);
x_61 = lean_ctor_get(x_2, 7);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 8);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 15);
x_64 = lean_ctor_get(x_2, 9);
lean_inc_ref(x_64);
x_65 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 16);
x_66 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 17);
lean_dec_ref(x_2);
if (x_50 == 0)
{
if (x_51 == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_422 = l___private_Lean_Shell_0__Lean_maxMemory;
x_423 = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(x_47, x_422);
x_424 = lean_unsigned_to_nat(0u);
x_425 = lean_nat_dec_eq(x_423, x_424);
if (x_425 == 0)
{
size_t x_426; size_t x_427; size_t x_428; size_t x_429; lean_object* x_430; 
x_426 = lean_usize_of_nat(x_423);
lean_dec(x_423);
x_427 = 1024;
x_428 = lean_usize_mul(x_426, x_427);
x_429 = lean_usize_mul(x_428, x_427);
x_430 = lean_internal_set_max_memory(x_429);
x_412 = lean_box(0);
goto block_421;
}
else
{
lean_dec(x_423);
x_412 = lean_box(0);
goto block_421;
}
}
else
{
lean_object* x_431; 
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_1);
x_431 = l_Lean_getBuildDir();
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
lean_dec_ref(x_431);
x_433 = l_Lean_getLibDir(x_432);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
lean_dec_ref(x_433);
x_435 = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__5(x_434);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; uint8_t x_437; uint8_t x_443; 
x_443 = !lean_is_exclusive(x_435);
if (x_443 == 0)
{
lean_object* x_444; 
x_444 = lean_ctor_get(x_435, 0);
lean_dec(x_444);
x_436 = x_435;
x_437 = x_443;
goto block_442;
}
else
{
lean_dec(x_435);
x_436 = lean_box(0);
x_437 = x_443;
goto block_442;
}
block_442:
{
lean_object* x_438; lean_object* x_439; 
x_438 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_437 == 0)
{
lean_ctor_set(x_436, 0, x_438);
x_439 = x_436;
goto block_440;
}
else
{
lean_object* x_441; 
x_441 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_441, 0, x_438);
x_439 = x_441;
goto block_440;
}
block_440:
{
return x_439;
}
}
}
else
{
lean_object* x_445; lean_object* x_446; uint8_t x_447; uint8_t x_452; 
x_445 = lean_ctor_get(x_435, 0);
x_452 = !lean_is_exclusive(x_435);
if (x_452 == 0)
{
x_446 = x_435;
x_447 = x_452;
goto block_451;
}
else
{
lean_inc(x_445);
lean_dec(x_435);
x_446 = lean_box(0);
x_447 = x_452;
goto block_451;
}
block_451:
{
lean_object* x_448; 
if (x_447 == 0)
{
x_448 = x_446;
goto block_449;
}
else
{
lean_object* x_450; 
x_450 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_450, 0, x_445);
x_448 = x_450;
goto block_449;
}
block_449:
{
return x_448;
}
}
}
}
else
{
lean_object* x_453; lean_object* x_454; uint8_t x_455; uint8_t x_460; 
x_453 = lean_ctor_get(x_433, 0);
x_460 = !lean_is_exclusive(x_433);
if (x_460 == 0)
{
x_454 = x_433;
x_455 = x_460;
goto block_459;
}
else
{
lean_inc(x_453);
lean_dec(x_433);
x_454 = lean_box(0);
x_455 = x_460;
goto block_459;
}
block_459:
{
lean_object* x_456; 
if (x_455 == 0)
{
x_456 = x_454;
goto block_457;
}
else
{
lean_object* x_458; 
x_458 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_458, 0, x_453);
x_456 = x_458;
goto block_457;
}
block_457:
{
return x_456;
}
}
}
}
else
{
lean_object* x_461; lean_object* x_462; uint8_t x_463; uint8_t x_468; 
x_461 = lean_ctor_get(x_431, 0);
x_468 = !lean_is_exclusive(x_431);
if (x_468 == 0)
{
x_462 = x_431;
x_463 = x_468;
goto block_467;
}
else
{
lean_inc(x_461);
lean_dec(x_431);
x_462 = lean_box(0);
x_463 = x_468;
goto block_467;
}
block_467:
{
lean_object* x_464; 
if (x_463 == 0)
{
x_464 = x_462;
goto block_465;
}
else
{
lean_object* x_466; 
x_466 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_466, 0, x_461);
x_464 = x_466;
goto block_465;
}
block_465:
{
return x_464;
}
}
}
}
}
else
{
lean_object* x_469; 
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_1);
x_469 = l_Lean_getBuildDir();
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
lean_dec_ref(x_469);
x_471 = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__5(x_470);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; uint8_t x_473; uint8_t x_479; 
x_479 = !lean_is_exclusive(x_471);
if (x_479 == 0)
{
lean_object* x_480; 
x_480 = lean_ctor_get(x_471, 0);
lean_dec(x_480);
x_472 = x_471;
x_473 = x_479;
goto block_478;
}
else
{
lean_dec(x_471);
x_472 = lean_box(0);
x_473 = x_479;
goto block_478;
}
block_478:
{
lean_object* x_474; lean_object* x_475; 
x_474 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_473 == 0)
{
lean_ctor_set(x_472, 0, x_474);
x_475 = x_472;
goto block_476;
}
else
{
lean_object* x_477; 
x_477 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_477, 0, x_474);
x_475 = x_477;
goto block_476;
}
block_476:
{
return x_475;
}
}
}
else
{
lean_object* x_481; lean_object* x_482; uint8_t x_483; uint8_t x_488; 
x_481 = lean_ctor_get(x_471, 0);
x_488 = !lean_is_exclusive(x_471);
if (x_488 == 0)
{
x_482 = x_471;
x_483 = x_488;
goto block_487;
}
else
{
lean_inc(x_481);
lean_dec(x_471);
x_482 = lean_box(0);
x_483 = x_488;
goto block_487;
}
block_487:
{
lean_object* x_484; 
if (x_483 == 0)
{
x_484 = x_482;
goto block_485;
}
else
{
lean_object* x_486; 
x_486 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_486, 0, x_481);
x_484 = x_486;
goto block_485;
}
block_485:
{
return x_484;
}
}
}
}
else
{
lean_object* x_489; lean_object* x_490; uint8_t x_491; uint8_t x_496; 
x_489 = lean_ctor_get(x_469, 0);
x_496 = !lean_is_exclusive(x_469);
if (x_496 == 0)
{
x_490 = x_469;
x_491 = x_496;
goto block_495;
}
else
{
lean_inc(x_489);
lean_dec(x_469);
x_490 = lean_box(0);
x_491 = x_496;
goto block_495;
}
block_495:
{
lean_object* x_492; 
if (x_491 == 0)
{
x_492 = x_490;
goto block_493;
}
else
{
lean_object* x_494; 
x_494 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_494, 0, x_489);
x_492 = x_494;
goto block_493;
}
block_493:
{
return x_492;
}
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
block_25:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_display_cumulative_profiling_times();
x_11 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__0, &l___private_Lean_Shell_0__Lean_shellMain___closed__0_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0);
if (x_11 == 0)
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 1;
x_13 = lean_io_exit(x_12);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; 
lean_dec_ref(x_8);
x_14 = 0;
x_15 = lean_io_exit(x_14);
return x_15;
}
}
else
{
if (lean_obj_tag(x_8) == 0)
{
x_4 = lean_box(0);
goto block_7;
}
else
{
lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_8, 0);
lean_dec(x_24);
x_16 = x_8;
x_17 = x_23;
goto block_22;
}
else
{
lean_dec(x_8);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
if (x_11 == 0)
{
lean_del_object(x_16);
x_4 = lean_box(0);
goto block_7;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
}
block_46:
{
lean_object* x_28; 
x_28 = l_Lean_printImportsJson(x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_36; 
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_28, 0);
lean_dec(x_37);
x_29 = x_28;
x_30 = x_36;
goto block_35;
}
else
{
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_31);
x_32 = x_29;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
x_38 = lean_ctor_get(x_28, 0);
x_45 = !lean_is_exclusive(x_28);
if (x_45 == 0)
{
x_39 = x_28;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
block_93:
{
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_62, 0);
lean_inc(x_71);
lean_dec_ref(x_62);
x_72 = lean_init_llvm();
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_72);
x_73 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__1));
x_74 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(x_74, 0, x_69);
lean_closure_set(x_74, 1, x_68);
lean_closure_set(x_74, 2, x_71);
x_75 = lean_box(0);
x_76 = l_Lean_profileitIOUnsafe___redArg(x_73, x_47, x_74, x_75);
lean_dec_ref(x_47);
if (lean_obj_tag(x_76) == 0)
{
lean_dec_ref(x_76);
x_8 = x_67;
x_9 = lean_box(0);
goto block_25;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_67);
x_77 = lean_ctor_get(x_76, 0);
x_84 = !lean_is_exclusive(x_76);
if (x_84 == 0)
{
x_78 = x_76;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_92; 
lean_dec(x_71);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec_ref(x_47);
x_85 = lean_ctor_get(x_72, 0);
x_92 = !lean_is_exclusive(x_72);
if (x_92 == 0)
{
x_86 = x_72;
x_87 = x_92;
goto block_91;
}
else
{
lean_inc(x_85);
lean_dec(x_72);
x_86 = lean_box(0);
x_87 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_88; 
if (x_87 == 0)
{
x_88 = x_86;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_85);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
else
{
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec(x_62);
lean_dec_ref(x_47);
x_8 = x_67;
x_9 = lean_box(0);
goto block_25;
}
}
block_162:
{
lean_object* x_100; lean_object* x_101; 
x_100 = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1));
lean_inc(x_98);
lean_inc_ref(x_47);
x_101 = l_Lean_Elab_runFrontend(x_97, x_47, x_94, x_98, x_56, x_59, x_60, x_63, x_64, x_100, x_65, x_95);
lean_dec_ref(x_64);
lean_dec(x_60);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_153; 
x_102 = lean_ctor_get(x_101, 0);
x_153 = !lean_is_exclusive(x_101);
if (x_153 == 0)
{
x_103 = x_101;
x_104 = x_153;
goto block_152;
}
else
{
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_box(0);
x_104 = x_153;
goto block_152;
}
block_152:
{
if (lean_obj_tag(x_102) == 1)
{
if (x_66 == 0)
{
lean_del_object(x_103);
lean_dec(x_96);
if (lean_obj_tag(x_61) == 1)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_61, 0);
lean_inc(x_106);
lean_dec_ref(x_61);
x_107 = 1;
x_108 = lean_io_prim_handle_mk(x_106, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_106);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__2));
lean_inc(x_98);
lean_inc(x_105);
x_111 = l_Lean_IR_emitC(x_105, x_98);
x_112 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 3, 2);
lean_closure_set(x_112, 0, x_111);
lean_closure_set(x_112, 1, x_109);
x_113 = lean_box(0);
x_114 = l_Lean_profileitIOUnsafe___redArg(x_110, x_47, x_112, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_dec_ref(x_114);
x_67 = x_102;
x_68 = x_98;
x_69 = x_105;
x_70 = lean_box(0);
goto block_93;
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_122; 
lean_dec(x_105);
lean_dec_ref(x_102);
lean_dec(x_98);
lean_dec(x_62);
lean_dec_ref(x_47);
x_115 = lean_ctor_get(x_114, 0);
x_122 = !lean_is_exclusive(x_114);
if (x_122 == 0)
{
x_116 = x_114;
x_117 = x_122;
goto block_121;
}
else
{
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_box(0);
x_117 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_118; 
if (x_117 == 0)
{
x_118 = x_116;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_115);
x_118 = x_120;
goto block_119;
}
block_119:
{
return x_118;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_108);
lean_dec(x_105);
lean_dec_ref(x_102);
lean_dec(x_98);
lean_dec(x_62);
lean_dec_ref(x_47);
x_123 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__3));
x_124 = lean_string_append(x_123, x_106);
lean_dec(x_106);
x_125 = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
x_126 = lean_string_append(x_124, x_125);
x_127 = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; uint8_t x_129; uint8_t x_135; 
x_135 = !lean_is_exclusive(x_127);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_127, 0);
lean_dec(x_136);
x_128 = x_127;
x_129 = x_135;
goto block_134;
}
else
{
lean_dec(x_127);
x_128 = lean_box(0);
x_129 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_130; lean_object* x_131; 
x_130 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (x_129 == 0)
{
lean_ctor_set(x_128, 0, x_130);
x_131 = x_128;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_130);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_144; 
x_137 = lean_ctor_get(x_127, 0);
x_144 = !lean_is_exclusive(x_127);
if (x_144 == 0)
{
x_138 = x_127;
x_139 = x_144;
goto block_143;
}
else
{
lean_inc(x_137);
lean_dec(x_127);
x_138 = lean_box(0);
x_139 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_140; 
if (x_139 == 0)
{
x_140 = x_138;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_137);
x_140 = x_142;
goto block_141;
}
block_141:
{
return x_140;
}
}
}
}
}
else
{
lean_object* x_145; 
lean_dec(x_61);
x_145 = lean_ctor_get(x_102, 0);
lean_inc(x_145);
x_67 = x_102;
x_68 = x_98;
x_69 = x_145;
x_70 = lean_box(0);
goto block_93;
}
}
else
{
lean_object* x_146; uint32_t x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_98);
lean_dec(x_62);
lean_dec(x_61);
x_146 = lean_ctor_get(x_102, 0);
lean_inc(x_146);
lean_dec_ref(x_102);
x_147 = lean_run_main(x_146, x_47, x_96);
lean_dec(x_96);
lean_dec_ref(x_47);
lean_dec(x_146);
x_148 = lean_box_uint32(x_147);
if (x_104 == 0)
{
lean_ctor_set(x_103, 0, x_148);
x_149 = x_103;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_148);
x_149 = x_151;
goto block_150;
}
block_150:
{
return x_149;
}
}
}
else
{
lean_del_object(x_103);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_62);
lean_dec(x_61);
lean_dec_ref(x_47);
x_8 = x_102;
x_9 = lean_box(0);
goto block_25;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; uint8_t x_161; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_62);
lean_dec(x_61);
lean_dec_ref(x_47);
x_154 = lean_ctor_get(x_101, 0);
x_161 = !lean_is_exclusive(x_101);
if (x_161 == 0)
{
x_155 = x_101;
x_156 = x_161;
goto block_160;
}
else
{
lean_inc(x_154);
lean_dec(x_101);
x_155 = lean_box(0);
x_156 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_157; 
if (x_156 == 0)
{
x_157 = x_155;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_154);
x_157 = x_159;
goto block_158;
}
block_158:
{
return x_157;
}
}
}
}
block_177:
{
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
x_94 = x_163;
x_95 = x_164;
x_96 = x_166;
x_97 = x_165;
x_98 = x_168;
x_99 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_176; 
lean_dec(x_166);
lean_dec_ref(x_165);
lean_dec(x_164);
lean_dec_ref(x_163);
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_47);
x_169 = lean_ctor_get(x_167, 0);
x_176 = !lean_is_exclusive(x_167);
if (x_176 == 0)
{
x_170 = x_167;
x_171 = x_176;
goto block_175;
}
else
{
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_box(0);
x_171 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_172; 
if (x_171 == 0)
{
x_172 = x_170;
goto block_173;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_169);
x_172 = x_174;
goto block_173;
}
block_173:
{
return x_172;
}
}
}
}
block_207:
{
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_183; 
x_183 = lean_box(0);
if (lean_obj_tag(x_179) == 1)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_179, 0);
lean_inc(x_184);
lean_dec_ref(x_179);
x_185 = l_Lean_moduleNameOfFileName(x_184, x_57);
if (lean_obj_tag(x_185) == 0)
{
x_163 = x_178;
x_164 = x_183;
x_165 = x_181;
x_166 = x_180;
x_167 = x_185;
goto block_177;
}
else
{
if (lean_obj_tag(x_59) == 0)
{
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_186; 
lean_dec_ref(x_185);
x_186 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__5));
x_94 = x_178;
x_95 = x_183;
x_96 = x_180;
x_97 = x_181;
x_98 = x_186;
x_99 = lean_box(0);
goto block_162;
}
else
{
x_163 = x_178;
x_164 = x_183;
x_165 = x_181;
x_166 = x_180;
x_167 = x_185;
goto block_177;
}
}
else
{
x_163 = x_178;
x_164 = x_183;
x_165 = x_181;
x_166 = x_180;
x_167 = x_185;
goto block_177;
}
}
}
else
{
lean_object* x_187; 
lean_dec(x_179);
lean_dec(x_57);
x_187 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__5));
x_94 = x_178;
x_95 = x_183;
x_96 = x_180;
x_97 = x_181;
x_98 = x_187;
x_99 = lean_box(0);
goto block_162;
}
}
else
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_206; 
lean_dec(x_179);
lean_dec(x_57);
x_188 = lean_ctor_get(x_58, 0);
x_206 = !lean_is_exclusive(x_58);
if (x_206 == 0)
{
x_189 = x_58;
x_190 = x_206;
goto block_205;
}
else
{
lean_inc(x_188);
lean_dec(x_58);
x_189 = lean_box(0);
x_190 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_191; 
x_191 = l_Lean_ModuleSetup_load(x_188);
lean_dec(x_188);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec_ref(x_191);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (x_190 == 0)
{
lean_ctor_set(x_189, 0, x_192);
x_194 = x_189;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_192);
x_194 = x_196;
goto block_195;
}
block_195:
{
x_94 = x_178;
x_95 = x_194;
x_96 = x_180;
x_97 = x_181;
x_98 = x_193;
x_99 = lean_box(0);
goto block_162;
}
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_204; 
lean_del_object(x_189);
lean_dec_ref(x_181);
lean_dec(x_180);
lean_dec_ref(x_178);
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_47);
x_197 = lean_ctor_get(x_191, 0);
x_204 = !lean_is_exclusive(x_191);
if (x_204 == 0)
{
x_198 = x_191;
x_199 = x_204;
goto block_203;
}
else
{
lean_inc(x_197);
lean_dec(x_191);
x_198 = lean_box(0);
x_199 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_200; 
if (x_199 == 0)
{
x_200 = x_198;
goto block_201;
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_197);
x_200 = x_202;
goto block_201;
}
block_201:
{
return x_200;
}
}
}
}
}
}
block_245:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_216 = lean_nat_add(x_211, x_215);
lean_dec(x_215);
lean_inc(x_216);
lean_inc_ref(x_210);
x_217 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_217, 0, x_210);
lean_ctor_set(x_217, 1, x_211);
lean_ctor_set(x_217, 2, x_216);
x_218 = l_String_Slice_trimAscii(x_217);
lean_dec_ref(x_217);
x_219 = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__8, &l___private_Lean_Shell_0__Lean_shellMain___closed__8_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__8);
x_220 = l_String_Slice_beq(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_216);
lean_dec(x_213);
lean_dec(x_212);
lean_dec_ref(x_210);
lean_dec(x_209);
lean_dec_ref(x_208);
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_47);
x_221 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__9));
x_222 = l_String_Slice_toString(x_218);
lean_dec_ref(x_218);
x_223 = lean_string_append(x_221, x_222);
lean_dec_ref(x_222);
x_224 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
x_225 = lean_string_append(x_223, x_224);
x_226 = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(x_225);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; uint8_t x_228; uint8_t x_234; 
x_234 = !lean_is_exclusive(x_226);
if (x_234 == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_226, 0);
lean_dec(x_235);
x_227 = x_226;
x_228 = x_234;
goto block_233;
}
else
{
lean_dec(x_226);
x_227 = lean_box(0);
x_228 = x_234;
goto block_233;
}
block_233:
{
lean_object* x_229; lean_object* x_230; 
x_229 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (x_228 == 0)
{
lean_ctor_set(x_227, 0, x_229);
x_230 = x_227;
goto block_231;
}
else
{
lean_object* x_232; 
x_232 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_232, 0, x_229);
x_230 = x_232;
goto block_231;
}
block_231:
{
return x_230;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; uint8_t x_243; 
x_236 = lean_ctor_get(x_226, 0);
x_243 = !lean_is_exclusive(x_226);
if (x_243 == 0)
{
x_237 = x_226;
x_238 = x_243;
goto block_242;
}
else
{
lean_inc(x_236);
lean_dec(x_226);
x_237 = lean_box(0);
x_238 = x_243;
goto block_242;
}
block_242:
{
lean_object* x_239; 
if (x_238 == 0)
{
x_239 = x_237;
goto block_240;
}
else
{
lean_object* x_241; 
x_241 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_241, 0, x_236);
x_239 = x_241;
goto block_240;
}
block_240:
{
return x_239;
}
}
}
}
else
{
lean_object* x_244; 
lean_dec_ref(x_218);
x_244 = lean_string_utf8_extract(x_210, x_216, x_212);
lean_dec(x_212);
lean_dec(x_216);
lean_dec_ref(x_210);
x_178 = x_208;
x_179 = x_209;
x_180 = x_213;
x_181 = x_244;
x_182 = lean_box(0);
goto block_207;
}
}
block_311:
{
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
x_251 = lean_decode_lossy_utf8(x_250);
lean_dec(x_250);
if (x_53 == 0)
{
if (x_54 == 0)
{
lean_object* x_252; 
lean_inc_ref(x_251);
x_252 = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(x_251);
if (lean_obj_tag(x_252) == 1)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec_ref(x_251);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
x_254 = lean_unsigned_to_nat(0u);
x_255 = lean_box(0);
x_256 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(x_253, x_254, x_255);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_257 = lean_ctor_get(x_253, 0);
lean_inc_ref(x_257);
x_258 = lean_ctor_get(x_253, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_253, 2);
lean_inc(x_259);
lean_dec(x_253);
x_260 = lean_nat_sub(x_259, x_258);
x_208 = x_246;
x_209 = x_247;
x_210 = x_257;
x_211 = x_258;
x_212 = x_259;
x_213 = x_248;
x_214 = lean_box(0);
x_215 = x_260;
goto block_245;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_256, 0);
lean_inc(x_261);
lean_dec_ref(x_256);
x_262 = lean_ctor_get(x_253, 0);
lean_inc_ref(x_262);
x_263 = lean_ctor_get(x_253, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_253, 2);
lean_inc(x_264);
lean_dec(x_253);
x_208 = x_246;
x_209 = x_247;
x_210 = x_262;
x_211 = x_263;
x_212 = x_264;
x_213 = x_248;
x_214 = lean_box(0);
x_215 = x_261;
goto block_245;
}
}
else
{
lean_dec(x_252);
x_178 = x_246;
x_179 = x_247;
x_180 = x_248;
x_181 = x_251;
x_182 = lean_box(0);
goto block_207;
}
}
else
{
lean_object* x_265; lean_object* x_266; 
lean_dec(x_248);
lean_dec(x_247);
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_47);
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_246);
x_266 = l_Lean_Elab_printImportSrcs(x_251, x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; uint8_t x_268; uint8_t x_274; 
x_274 = !lean_is_exclusive(x_266);
if (x_274 == 0)
{
lean_object* x_275; 
x_275 = lean_ctor_get(x_266, 0);
lean_dec(x_275);
x_267 = x_266;
x_268 = x_274;
goto block_273;
}
else
{
lean_dec(x_266);
x_267 = lean_box(0);
x_268 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_269; lean_object* x_270; 
x_269 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_268 == 0)
{
lean_ctor_set(x_267, 0, x_269);
x_270 = x_267;
goto block_271;
}
else
{
lean_object* x_272; 
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_269);
x_270 = x_272;
goto block_271;
}
block_271:
{
return x_270;
}
}
}
else
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; uint8_t x_283; 
x_276 = lean_ctor_get(x_266, 0);
x_283 = !lean_is_exclusive(x_266);
if (x_283 == 0)
{
x_277 = x_266;
x_278 = x_283;
goto block_282;
}
else
{
lean_inc(x_276);
lean_dec(x_266);
x_277 = lean_box(0);
x_278 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_279; 
if (x_278 == 0)
{
x_279 = x_277;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_276);
x_279 = x_281;
goto block_280;
}
block_280:
{
return x_279;
}
}
}
}
}
else
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_248);
lean_dec(x_247);
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_47);
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_246);
x_285 = l_Lean_Elab_printImports(x_251, x_284);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; uint8_t x_287; uint8_t x_293; 
x_293 = !lean_is_exclusive(x_285);
if (x_293 == 0)
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_285, 0);
lean_dec(x_294);
x_286 = x_285;
x_287 = x_293;
goto block_292;
}
else
{
lean_dec(x_285);
x_286 = lean_box(0);
x_287 = x_293;
goto block_292;
}
block_292:
{
lean_object* x_288; lean_object* x_289; 
x_288 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_287 == 0)
{
lean_ctor_set(x_286, 0, x_288);
x_289 = x_286;
goto block_290;
}
else
{
lean_object* x_291; 
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_288);
x_289 = x_291;
goto block_290;
}
block_290:
{
return x_289;
}
}
}
else
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; uint8_t x_302; 
x_295 = lean_ctor_get(x_285, 0);
x_302 = !lean_is_exclusive(x_285);
if (x_302 == 0)
{
x_296 = x_285;
x_297 = x_302;
goto block_301;
}
else
{
lean_inc(x_295);
lean_dec(x_285);
x_296 = lean_box(0);
x_297 = x_302;
goto block_301;
}
block_301:
{
lean_object* x_298; 
if (x_297 == 0)
{
x_298 = x_296;
goto block_299;
}
else
{
lean_object* x_300; 
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_295);
x_298 = x_300;
goto block_299;
}
block_299:
{
return x_298;
}
}
}
}
}
else
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; uint8_t x_310; 
lean_dec(x_248);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_47);
x_303 = lean_ctor_get(x_249, 0);
x_310 = !lean_is_exclusive(x_249);
if (x_310 == 0)
{
x_304 = x_249;
x_305 = x_310;
goto block_309;
}
else
{
lean_inc(x_303);
lean_dec(x_249);
x_304 = lean_box(0);
x_305 = x_310;
goto block_309;
}
block_309:
{
lean_object* x_306; 
if (x_305 == 0)
{
x_306 = x_304;
goto block_307;
}
else
{
lean_object* x_308; 
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_303);
x_306 = x_308;
goto block_307;
}
block_307:
{
return x_306;
}
}
}
}
block_319:
{
if (x_52 == 0)
{
lean_object* x_316; 
x_316 = l_IO_FS_readBinFile(x_314);
x_246 = x_314;
x_247 = x_312;
x_248 = x_313;
x_249 = x_316;
goto block_311;
}
else
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_get_stdin();
x_318 = l_IO_FS_Stream_readBinToEnd(x_317);
x_246 = x_314;
x_247 = x_312;
x_248 = x_313;
x_249 = x_318;
goto block_311;
}
}
block_354:
{
if (lean_obj_tag(x_321) == 1)
{
lean_object* x_323; 
x_323 = lean_ctor_get(x_321, 0);
lean_inc(x_323);
x_312 = x_321;
x_313 = x_322;
x_314 = x_323;
x_315 = lean_box(0);
goto block_319;
}
else
{
if (x_52 == 0)
{
lean_object* x_324; lean_object* x_325; 
lean_dec(x_322);
lean_dec(x_321);
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_47);
x_324 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__10));
x_325 = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(x_324);
if (lean_obj_tag(x_325) == 0)
{
uint8_t x_326; lean_object* x_327; 
lean_dec_ref(x_325);
x_326 = 1;
x_327 = l___private_Lean_Shell_0__Lean_displayHelp(x_326);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; uint8_t x_329; uint8_t x_335; 
x_335 = !lean_is_exclusive(x_327);
if (x_335 == 0)
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_327, 0);
lean_dec(x_336);
x_328 = x_327;
x_329 = x_335;
goto block_334;
}
else
{
lean_dec(x_327);
x_328 = lean_box(0);
x_329 = x_335;
goto block_334;
}
block_334:
{
lean_object* x_330; lean_object* x_331; 
x_330 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (x_329 == 0)
{
lean_ctor_set(x_328, 0, x_330);
x_331 = x_328;
goto block_332;
}
else
{
lean_object* x_333; 
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_330);
x_331 = x_333;
goto block_332;
}
block_332:
{
return x_331;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; uint8_t x_344; 
x_337 = lean_ctor_get(x_327, 0);
x_344 = !lean_is_exclusive(x_327);
if (x_344 == 0)
{
x_338 = x_327;
x_339 = x_344;
goto block_343;
}
else
{
lean_inc(x_337);
lean_dec(x_327);
x_338 = lean_box(0);
x_339 = x_344;
goto block_343;
}
block_343:
{
lean_object* x_340; 
if (x_339 == 0)
{
x_340 = x_338;
goto block_341;
}
else
{
lean_object* x_342; 
x_342 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_342, 0, x_337);
x_340 = x_342;
goto block_341;
}
block_341:
{
return x_340;
}
}
}
}
else
{
lean_object* x_345; lean_object* x_346; uint8_t x_347; uint8_t x_352; 
x_345 = lean_ctor_get(x_325, 0);
x_352 = !lean_is_exclusive(x_325);
if (x_352 == 0)
{
x_346 = x_325;
x_347 = x_352;
goto block_351;
}
else
{
lean_inc(x_345);
lean_dec(x_325);
x_346 = lean_box(0);
x_347 = x_352;
goto block_351;
}
block_351:
{
lean_object* x_348; 
if (x_347 == 0)
{
x_348 = x_346;
goto block_349;
}
else
{
lean_object* x_350; 
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_345);
x_348 = x_350;
goto block_349;
}
block_349:
{
return x_348;
}
}
}
}
else
{
lean_object* x_353; 
x_353 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__11));
x_312 = x_321;
x_313 = x_322;
x_314 = x_353;
x_315 = lean_box(0);
goto block_319;
}
}
}
block_388:
{
if (x_66 == 0)
{
uint8_t x_358; 
x_358 = l_List_isEmpty___redArg(x_357);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; 
lean_dec(x_357);
lean_dec(x_356);
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_47);
x_359 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__10));
x_360 = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(x_359);
if (lean_obj_tag(x_360) == 0)
{
uint8_t x_361; lean_object* x_362; 
lean_dec_ref(x_360);
x_361 = 1;
x_362 = l___private_Lean_Shell_0__Lean_displayHelp(x_361);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; uint8_t x_364; uint8_t x_370; 
x_370 = !lean_is_exclusive(x_362);
if (x_370 == 0)
{
lean_object* x_371; 
x_371 = lean_ctor_get(x_362, 0);
lean_dec(x_371);
x_363 = x_362;
x_364 = x_370;
goto block_369;
}
else
{
lean_dec(x_362);
x_363 = lean_box(0);
x_364 = x_370;
goto block_369;
}
block_369:
{
lean_object* x_365; lean_object* x_366; 
x_365 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (x_364 == 0)
{
lean_ctor_set(x_363, 0, x_365);
x_366 = x_363;
goto block_367;
}
else
{
lean_object* x_368; 
x_368 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_368, 0, x_365);
x_366 = x_368;
goto block_367;
}
block_367:
{
return x_366;
}
}
}
else
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; uint8_t x_379; 
x_372 = lean_ctor_get(x_362, 0);
x_379 = !lean_is_exclusive(x_362);
if (x_379 == 0)
{
x_373 = x_362;
x_374 = x_379;
goto block_378;
}
else
{
lean_inc(x_372);
lean_dec(x_362);
x_373 = lean_box(0);
x_374 = x_379;
goto block_378;
}
block_378:
{
lean_object* x_375; 
if (x_374 == 0)
{
x_375 = x_373;
goto block_376;
}
else
{
lean_object* x_377; 
x_377 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_377, 0, x_372);
x_375 = x_377;
goto block_376;
}
block_376:
{
return x_375;
}
}
}
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint8_t x_387; 
x_380 = lean_ctor_get(x_360, 0);
x_387 = !lean_is_exclusive(x_360);
if (x_387 == 0)
{
x_381 = x_360;
x_382 = x_387;
goto block_386;
}
else
{
lean_inc(x_380);
lean_dec(x_360);
x_381 = lean_box(0);
x_382 = x_387;
goto block_386;
}
block_386:
{
lean_object* x_383; 
if (x_382 == 0)
{
x_383 = x_381;
goto block_384;
}
else
{
lean_object* x_385; 
x_385 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_385, 0, x_380);
x_383 = x_385;
goto block_384;
}
block_384:
{
return x_383;
}
}
}
}
else
{
x_320 = lean_box(0);
x_321 = x_356;
x_322 = x_357;
goto block_354;
}
}
else
{
x_320 = lean_box(0);
x_321 = x_356;
x_322 = x_357;
goto block_354;
}
}
block_394:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_390; 
x_390 = lean_box(0);
x_355 = lean_box(0);
x_356 = x_390;
x_357 = x_1;
goto block_388;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_1, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_1, 1);
lean_inc(x_392);
lean_dec_ref(x_1);
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_391);
x_355 = lean_box(0);
x_356 = x_393;
x_357 = x_392;
goto block_388;
}
}
block_411:
{
switch (x_49) {
case 0:
{
lean_dec_ref(x_48);
if (x_53 == 0)
{
x_389 = lean_box(0);
goto block_394;
}
else
{
if (x_55 == 0)
{
x_389 = lean_box(0);
goto block_394;
}
else
{
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_47);
if (x_52 == 0)
{
lean_object* x_396; 
x_396 = lean_array_mk(x_1);
x_26 = x_396;
x_27 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_397; lean_object* x_398; 
lean_dec(x_1);
x_397 = lean_get_stdin();
x_398 = l_IO_FS_Stream_lines(x_397);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
x_26 = x_399;
x_27 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_400; lean_object* x_401; uint8_t x_402; uint8_t x_407; 
x_400 = lean_ctor_get(x_398, 0);
x_407 = !lean_is_exclusive(x_398);
if (x_407 == 0)
{
x_401 = x_398;
x_402 = x_407;
goto block_406;
}
else
{
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_box(0);
x_402 = x_407;
goto block_406;
}
block_406:
{
lean_object* x_403; 
if (x_402 == 0)
{
x_403 = x_401;
goto block_404;
}
else
{
lean_object* x_405; 
x_405 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_405, 0, x_400);
x_403 = x_405;
goto block_404;
}
block_404:
{
return x_403;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_408; lean_object* x_409; 
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_47);
lean_dec(x_1);
x_408 = lean_array_to_list(x_48);
x_409 = l_Lean_Server_Watchdog_watchdogMain(x_408);
return x_409;
}
default: 
{
lean_object* x_410; 
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec_ref(x_48);
lean_dec(x_1);
x_410 = l_Lean_Server_FileWorker_workerMain(x_47);
return x_410;
}
}
}
block_421:
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; 
x_413 = l___private_Lean_Shell_0__Lean_timeout;
x_414 = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(x_47, x_413);
x_415 = lean_unsigned_to_nat(0u);
x_416 = lean_nat_dec_eq(x_414, x_415);
if (x_416 == 0)
{
size_t x_417; size_t x_418; size_t x_419; lean_object* x_420; 
x_417 = lean_usize_of_nat(x_414);
lean_dec(x_414);
x_418 = 1000;
x_419 = lean_usize_mul(x_417, x_418);
x_420 = lean_internal_set_max_heartbeat(x_419);
x_395 = lean_box(0);
goto block_411;
}
else
{
lean_dec(x_414);
x_395 = lean_box(0);
goto block_411;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_shell_main(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(x_1, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
lean_object* runtime_initialize_Lean_Elab_Frontend(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ParseImportsFast(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Watchdog(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_FileWorker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_EmitC(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Shell(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Frontend(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ParseImportsFast(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Watchdog(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_EmitC(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Shell_0__Lean_shortVersionString = _init_l___private_Lean_Shell_0__Lean_shortVersionString();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString);
l___private_Lean_Shell_0__Lean_versionHeader = _init_l___private_Lean_Shell_0__Lean_versionHeader();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader);
l___private_Lean_Shell_0__Lean_featuresString = _init_l___private_Lean_Shell_0__Lean_featuresString();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_featuresString);
res = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_3125322801____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Shell_0__Lean_maxMemory = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Shell_0__Lean_maxMemory);
lean_dec_ref(res);
res = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1197438456____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Shell_0__Lean_timeout = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Shell_0__Lean_timeout);
lean_dec_ref(res);
res = l___private_Lean_Shell_0__Lean_initFn_00___x40_Lean_Shell_1212703299____hygCtx___hyg_2_()
;
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
lean_object* initialize_Lean_Compiler_IR_EmitC(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Shell(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Frontend(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ParseImportsFast(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Watchdog(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitC(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Shell(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Shell(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Shell(builtin);
}
#ifdef __cplusplus
}
#endif
