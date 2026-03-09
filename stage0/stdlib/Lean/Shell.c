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
lean_object* x_3; lean_object* x_7; lean_object* x_34; 
if (x_1 == 0)
{
lean_object* x_91; 
x_91 = lean_get_stdout();
x_34 = x_91;
goto block_90;
}
else
{
lean_object* x_92; 
x_92 = lean_get_stderr();
x_34 = x_92;
goto block_90;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__0));
x_5 = l_IO_FS_Stream_putStrLn(x_3, x_4);
return x_5;
}
block_33:
{
lean_object* x_8; lean_object* x_9; 
x_8 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__1));
lean_inc_ref(x_7);
x_9 = l_IO_FS_Stream_putStrLn(x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_9);
x_10 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__2));
lean_inc_ref(x_7);
x_11 = l_IO_FS_Stream_putStrLn(x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_11);
x_12 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__3));
lean_inc_ref(x_7);
x_13 = l_IO_FS_Stream_putStrLn(x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_13);
x_14 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__4));
lean_inc_ref(x_7);
x_15 = l_IO_FS_Stream_putStrLn(x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_15);
x_16 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__5));
lean_inc_ref(x_7);
x_17 = l_IO_FS_Stream_putStrLn(x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_17);
x_18 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__6));
lean_inc_ref(x_7);
x_19 = l_IO_FS_Stream_putStrLn(x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_19);
x_20 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__7));
lean_inc_ref(x_7);
x_21 = l_IO_FS_Stream_putStrLn(x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_21);
x_22 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__8));
lean_inc_ref(x_7);
x_23 = l_IO_FS_Stream_putStrLn(x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_23);
x_24 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__9));
lean_inc_ref(x_7);
x_25 = l_IO_FS_Stream_putStrLn(x_7, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_25);
x_26 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__10));
lean_inc_ref(x_7);
x_27 = l_IO_FS_Stream_putStrLn(x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_27);
x_28 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__11));
lean_inc_ref(x_7);
x_29 = l_IO_FS_Stream_putStrLn(x_7, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec_ref(x_29);
x_30 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__12, &l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12);
if (x_30 == 0)
{
x_3 = x_7;
goto block_6;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__13));
lean_inc_ref(x_7);
x_32 = l_IO_FS_Stream_putStrLn(x_7, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_dec_ref(x_32);
x_3 = x_7;
goto block_6;
}
else
{
lean_dec_ref(x_7);
return x_32;
}
}
}
else
{
lean_dec_ref(x_7);
return x_29;
}
}
else
{
lean_dec_ref(x_7);
return x_27;
}
}
else
{
lean_dec_ref(x_7);
return x_25;
}
}
else
{
lean_dec_ref(x_7);
return x_23;
}
}
else
{
lean_dec_ref(x_7);
return x_21;
}
}
else
{
lean_dec_ref(x_7);
return x_19;
}
}
else
{
lean_dec_ref(x_7);
return x_17;
}
}
else
{
lean_dec_ref(x_7);
return x_15;
}
}
else
{
lean_dec_ref(x_7);
return x_13;
}
}
else
{
lean_dec_ref(x_7);
return x_11;
}
}
else
{
lean_dec_ref(x_7);
return x_9;
}
}
block_90:
{
lean_object* x_35; lean_object* x_36; 
x_35 = l___private_Lean_Shell_0__Lean_versionHeader;
lean_inc_ref(x_34);
x_36 = l_IO_FS_Stream_putStrLn(x_34, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_36);
x_37 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__14));
lean_inc_ref(x_34);
x_38 = l_IO_FS_Stream_putStrLn(x_34, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_38);
x_39 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__15));
lean_inc_ref(x_34);
x_40 = l_IO_FS_Stream_putStrLn(x_34, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_40);
x_41 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__16));
lean_inc_ref(x_34);
x_42 = l_IO_FS_Stream_putStrLn(x_34, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_42);
x_43 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__17));
lean_inc_ref(x_34);
x_44 = l_IO_FS_Stream_putStrLn(x_34, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_44);
x_45 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__18));
lean_inc_ref(x_34);
x_46 = l_IO_FS_Stream_putStrLn(x_34, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_46);
x_47 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__19));
lean_inc_ref(x_34);
x_48 = l_IO_FS_Stream_putStrLn(x_34, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_48);
x_49 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__20));
lean_inc_ref(x_34);
x_50 = l_IO_FS_Stream_putStrLn(x_34, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_50);
x_51 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__21));
lean_inc_ref(x_34);
x_52 = l_IO_FS_Stream_putStrLn(x_34, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_52);
x_53 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__22));
lean_inc_ref(x_34);
x_54 = l_IO_FS_Stream_putStrLn(x_34, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_54);
x_55 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__23));
lean_inc_ref(x_34);
x_56 = l_IO_FS_Stream_putStrLn(x_34, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_56);
x_57 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__24));
lean_inc_ref(x_34);
x_58 = l_IO_FS_Stream_putStrLn(x_34, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_58);
x_59 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__25));
lean_inc_ref(x_34);
x_60 = l_IO_FS_Stream_putStrLn(x_34, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_60);
x_61 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__26));
lean_inc_ref(x_34);
x_62 = l_IO_FS_Stream_putStrLn(x_34, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_62);
x_63 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__27));
lean_inc_ref(x_34);
x_64 = l_IO_FS_Stream_putStrLn(x_34, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_64);
x_65 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__28));
lean_inc_ref(x_34);
x_66 = l_IO_FS_Stream_putStrLn(x_34, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_66);
x_67 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__29));
lean_inc_ref(x_34);
x_68 = l_IO_FS_Stream_putStrLn(x_34, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_68);
x_69 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__30));
lean_inc_ref(x_34);
x_70 = l_IO_FS_Stream_putStrLn(x_34, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_70);
x_71 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__31));
lean_inc_ref(x_34);
x_72 = l_IO_FS_Stream_putStrLn(x_34, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_72);
x_73 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__32));
lean_inc_ref(x_34);
x_74 = l_IO_FS_Stream_putStrLn(x_34, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_74);
x_75 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__33));
lean_inc_ref(x_34);
x_76 = l_IO_FS_Stream_putStrLn(x_34, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_76);
x_77 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__34));
lean_inc_ref(x_34);
x_78 = l_IO_FS_Stream_putStrLn(x_34, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_78);
x_79 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__35));
lean_inc_ref(x_34);
x_80 = l_IO_FS_Stream_putStrLn(x_34, x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
lean_dec_ref(x_80);
x_81 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__36, &l___private_Lean_Shell_0__Lean_displayHelp___closed__36_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36);
if (x_81 == 0)
{
x_7 = x_34;
goto block_33;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__37));
lean_inc_ref(x_34);
x_83 = l_IO_FS_Stream_putStrLn(x_34, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec_ref(x_83);
x_84 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__38));
lean_inc_ref(x_34);
x_85 = l_IO_FS_Stream_putStrLn(x_34, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_85);
x_86 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__39));
lean_inc_ref(x_34);
x_87 = l_IO_FS_Stream_putStrLn(x_34, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_87);
x_88 = ((lean_object*)(l___private_Lean_Shell_0__Lean_displayHelp___closed__40));
lean_inc_ref(x_34);
x_89 = l_IO_FS_Stream_putStrLn(x_34, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_dec_ref(x_89);
x_7 = x_34;
goto block_33;
}
else
{
lean_dec_ref(x_34);
return x_89;
}
}
else
{
lean_dec_ref(x_34);
return x_87;
}
}
else
{
lean_dec_ref(x_34);
return x_85;
}
}
else
{
lean_dec_ref(x_34);
return x_83;
}
}
}
else
{
lean_dec_ref(x_34);
return x_80;
}
}
else
{
lean_dec_ref(x_34);
return x_78;
}
}
else
{
lean_dec_ref(x_34);
return x_76;
}
}
else
{
lean_dec_ref(x_34);
return x_74;
}
}
else
{
lean_dec_ref(x_34);
return x_72;
}
}
else
{
lean_dec_ref(x_34);
return x_70;
}
}
else
{
lean_dec_ref(x_34);
return x_68;
}
}
else
{
lean_dec_ref(x_34);
return x_66;
}
}
else
{
lean_dec_ref(x_34);
return x_64;
}
}
else
{
lean_dec_ref(x_34);
return x_62;
}
}
else
{
lean_dec_ref(x_34);
return x_60;
}
}
else
{
lean_dec_ref(x_34);
return x_58;
}
}
else
{
lean_dec_ref(x_34);
return x_56;
}
}
else
{
lean_dec_ref(x_34);
return x_54;
}
}
else
{
lean_dec_ref(x_34);
return x_52;
}
}
else
{
lean_dec_ref(x_34);
return x_50;
}
}
else
{
lean_dec_ref(x_34);
return x_48;
}
}
else
{
lean_dec_ref(x_34);
return x_46;
}
}
else
{
lean_dec_ref(x_34);
return x_44;
}
}
else
{
lean_dec_ref(x_34);
return x_42;
}
}
else
{
lean_dec_ref(x_34);
return x_40;
}
}
else
{
lean_dec_ref(x_34);
return x_38;
}
}
else
{
lean_dec_ref(x_34);
return x_36;
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
x_9 = lean_string_utf8_get_fast(x_2, x_3);
x_10 = 61;
x_11 = lean_uint32_dec_eq(x_9, x_10);
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
lean_object* x_10; 
x_10 = lean_apply_1(x_1, lean_box(0));
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
x_12 = x_10;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec_ref(x_10);
x_24 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_25 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_26 = l_IO_eprint___redArg(x_25, x_24);
lean_dec_ref(x_26);
goto block_23;
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_io_error_to_string(x_19);
x_21 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_22 = l_IO_eprint___redArg(x_21, x_20);
lean_dec_ref(x_22);
goto block_9;
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_7 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_8 = l_IO_eprint___redArg(x_7, x_6);
lean_dec_ref(x_8);
goto block_5;
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
lean_object* x_11; 
x_11 = lean_apply_1(x_2, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_11, 0);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
x_13 = x_11;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
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
else
{
lean_object* x_20; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec_ref(x_11);
x_25 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_26 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_27 = l_IO_eprint___redArg(x_26, x_25);
lean_dec_ref(x_27);
goto block_24;
block_24:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_io_error_to_string(x_20);
x_22 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_23 = l_IO_eprint___redArg(x_22, x_21);
lean_dec_ref(x_23);
goto block_10;
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
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_8 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_9 = l_IO_eprint___redArg(x_8, x_7);
lean_dec_ref(x_9);
goto block_6;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__0));
x_7 = lean_string_append(x_6, x_1);
x_8 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
x_9 = lean_string_append(x_7, x_8);
x_10 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_11 = l_IO_eprint___redArg(x_10, x_9);
lean_dec_ref(x_11);
goto block_5;
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__0));
x_7 = lean_string_append(x_6, x_1);
x_8 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwTooLarge___closed__1));
x_9 = lean_string_append(x_7, x_8);
x_10 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_eprint___closed__0));
x_11 = l_IO_eprint___redArg(x_10, x_9);
lean_dec_ref(x_11);
goto block_5;
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
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
lean_object* x_104; uint32_t x_201; uint8_t x_202; 
x_201 = 101;
x_202 = lean_uint32_dec_eq(x_2, x_201);
if (x_202 == 0)
{
uint32_t x_203; uint8_t x_204; 
x_203 = 106;
x_204 = lean_uint32_dec_eq(x_2, x_203);
if (x_204 == 0)
{
uint32_t x_205; uint8_t x_206; 
x_205 = 118;
x_206 = lean_uint32_dec_eq(x_2, x_205);
if (x_206 == 0)
{
uint32_t x_207; uint8_t x_208; 
x_207 = 86;
x_208 = lean_uint32_dec_eq(x_2, x_207);
if (x_208 == 0)
{
uint32_t x_209; uint8_t x_210; 
x_209 = 103;
x_210 = lean_uint32_dec_eq(x_2, x_209);
if (x_210 == 0)
{
uint32_t x_211; uint8_t x_212; 
x_211 = 104;
x_212 = lean_uint32_dec_eq(x_2, x_211);
if (x_212 == 0)
{
uint32_t x_213; uint8_t x_214; 
x_213 = 102;
x_214 = lean_uint32_dec_eq(x_2, x_213);
if (x_214 == 0)
{
uint32_t x_215; uint8_t x_216; 
x_215 = 99;
x_216 = lean_uint32_dec_eq(x_2, x_215);
if (x_216 == 0)
{
uint32_t x_217; uint8_t x_218; 
x_217 = 98;
x_218 = lean_uint32_dec_eq(x_2, x_217);
if (x_218 == 0)
{
uint32_t x_219; uint8_t x_220; 
x_219 = 115;
x_220 = lean_uint32_dec_eq(x_2, x_219);
if (x_220 == 0)
{
uint32_t x_221; uint8_t x_222; 
x_221 = 73;
x_222 = lean_uint32_dec_eq(x_2, x_221);
if (x_222 == 0)
{
uint32_t x_223; uint8_t x_224; 
x_223 = 114;
x_224 = lean_uint32_dec_eq(x_2, x_223);
if (x_224 == 0)
{
uint32_t x_225; uint8_t x_226; 
x_225 = 111;
x_226 = lean_uint32_dec_eq(x_2, x_225);
if (x_226 == 0)
{
uint32_t x_227; uint8_t x_228; 
x_227 = 105;
x_228 = lean_uint32_dec_eq(x_2, x_227);
if (x_228 == 0)
{
uint32_t x_229; uint8_t x_230; 
x_229 = 82;
x_230 = lean_uint32_dec_eq(x_2, x_229);
if (x_230 == 0)
{
uint32_t x_231; uint8_t x_232; 
x_231 = 77;
x_232 = lean_uint32_dec_eq(x_2, x_231);
if (x_232 == 0)
{
uint32_t x_233; uint8_t x_234; 
x_233 = 84;
x_234 = lean_uint32_dec_eq(x_2, x_233);
if (x_234 == 0)
{
uint32_t x_235; uint8_t x_236; 
x_235 = 116;
x_236 = lean_uint32_dec_eq(x_2, x_235);
if (x_236 == 0)
{
uint32_t x_237; uint8_t x_238; 
x_237 = 113;
x_238 = lean_uint32_dec_eq(x_2, x_237);
if (x_238 == 0)
{
uint32_t x_239; uint8_t x_240; 
x_239 = 100;
x_240 = lean_uint32_dec_eq(x_2, x_239);
if (x_240 == 0)
{
uint32_t x_241; uint8_t x_242; 
x_241 = 79;
x_242 = lean_uint32_dec_eq(x_2, x_241);
if (x_242 == 0)
{
uint32_t x_243; uint8_t x_244; 
x_243 = 78;
x_244 = lean_uint32_dec_eq(x_2, x_243);
if (x_244 == 0)
{
uint32_t x_245; uint8_t x_246; 
x_245 = 74;
x_246 = lean_uint32_dec_eq(x_2, x_245);
if (x_246 == 0)
{
uint32_t x_247; uint8_t x_248; 
x_247 = 97;
x_248 = lean_uint32_dec_eq(x_2, x_247);
if (x_248 == 0)
{
uint32_t x_249; uint8_t x_250; 
x_249 = 120;
x_250 = lean_uint32_dec_eq(x_2, x_249);
if (x_250 == 0)
{
uint32_t x_251; uint8_t x_252; 
x_251 = 76;
x_252 = lean_uint32_dec_eq(x_2, x_251);
if (x_252 == 0)
{
uint32_t x_253; uint8_t x_254; 
x_253 = 68;
x_254 = lean_uint32_dec_eq(x_2, x_253);
if (x_254 == 0)
{
uint32_t x_255; uint8_t x_256; 
x_255 = 83;
x_256 = lean_uint32_dec_eq(x_2, x_255);
if (x_256 == 0)
{
uint32_t x_257; uint8_t x_258; 
x_257 = 87;
x_258 = lean_uint32_dec_eq(x_2, x_257);
if (x_258 == 0)
{
uint32_t x_259; uint8_t x_260; 
x_259 = 80;
x_260 = lean_uint32_dec_eq(x_2, x_259);
if (x_260 == 0)
{
uint32_t x_261; uint8_t x_262; 
x_261 = 66;
x_262 = lean_uint32_dec_eq(x_2, x_261);
if (x_262 == 0)
{
uint32_t x_263; uint8_t x_264; 
x_263 = 112;
x_264 = lean_uint32_dec_eq(x_2, x_263);
if (x_264 == 0)
{
uint32_t x_265; uint8_t x_266; 
x_265 = 108;
x_266 = lean_uint32_dec_eq(x_2, x_265);
if (x_266 == 0)
{
uint32_t x_267; uint8_t x_268; 
x_267 = 117;
x_268 = lean_uint32_dec_eq(x_2, x_267);
if (x_268 == 0)
{
uint32_t x_269; uint8_t x_270; 
x_269 = 69;
x_270 = lean_uint32_dec_eq(x_2, x_269);
if (x_270 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_125;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__1));
x_272 = l___private_Lean_Shell_0__Lean_checkOptArg(x_271, x_3);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; uint8_t x_311; 
x_273 = lean_ctor_get(x_272, 0);
x_311 = !lean_is_exclusive(x_272);
if (x_311 == 0)
{
x_274 = x_272;
x_275 = x_311;
goto block_310;
}
else
{
lean_inc(x_273);
lean_dec(x_272);
x_274 = lean_box(0);
x_275 = x_311;
goto block_310;
}
block_310:
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; uint8_t x_279; uint8_t x_280; uint8_t x_281; uint8_t x_282; uint8_t x_283; uint8_t x_284; lean_object* x_285; uint32_t x_286; uint32_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; lean_object* x_295; uint8_t x_296; uint8_t x_297; lean_object* x_298; uint8_t x_299; uint8_t x_309; 
x_276 = lean_ctor_get(x_1, 0);
x_277 = lean_ctor_get(x_1, 1);
x_278 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_279 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_280 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_281 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_282 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_283 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_284 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_285 = lean_ctor_get(x_1, 2);
x_286 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_287 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_288 = lean_ctor_get(x_1, 3);
x_289 = lean_ctor_get(x_1, 4);
x_290 = lean_ctor_get(x_1, 5);
x_291 = lean_ctor_get(x_1, 6);
x_292 = lean_ctor_get(x_1, 7);
x_293 = lean_ctor_get(x_1, 8);
x_294 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_295 = lean_ctor_get(x_1, 9);
x_296 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_297 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_309 = !lean_is_exclusive(x_1);
if (x_309 == 0)
{
x_298 = x_1;
x_299 = x_309;
goto block_308;
}
else
{
lean_inc(x_295);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_285);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_1);
x_298 = lean_box(0);
x_299 = x_309;
goto block_308;
}
block_308:
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = l_String_toName(x_273);
x_301 = lean_array_push(x_295, x_300);
if (x_299 == 0)
{
lean_ctor_set(x_298, 9, x_301);
x_302 = x_298;
goto block_306;
}
else
{
lean_object* x_307; 
x_307 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_307, 0, x_276);
lean_ctor_set(x_307, 1, x_277);
lean_ctor_set(x_307, 2, x_285);
lean_ctor_set(x_307, 3, x_288);
lean_ctor_set(x_307, 4, x_289);
lean_ctor_set(x_307, 5, x_290);
lean_ctor_set(x_307, 6, x_291);
lean_ctor_set(x_307, 7, x_292);
lean_ctor_set(x_307, 8, x_293);
lean_ctor_set(x_307, 9, x_301);
lean_ctor_set_uint8(x_307, sizeof(void*)*10 + 8, x_278);
lean_ctor_set_uint8(x_307, sizeof(void*)*10 + 9, x_279);
lean_ctor_set_uint8(x_307, sizeof(void*)*10 + 10, x_280);
lean_ctor_set_uint8(x_307, sizeof(void*)*10 + 11, x_281);
lean_ctor_set_uint8(x_307, sizeof(void*)*10 + 12, x_282);
lean_ctor_set_uint8(x_307, sizeof(void*)*10 + 13, x_283);
lean_ctor_set_uint8(x_307, sizeof(void*)*10 + 14, x_284);
lean_ctor_set_uint32(x_307, sizeof(void*)*10, x_286);
lean_ctor_set_uint32(x_307, sizeof(void*)*10 + 4, x_287);
lean_ctor_set_uint8(x_307, sizeof(void*)*10 + 15, x_294);
lean_ctor_set_uint8(x_307, sizeof(void*)*10 + 16, x_296);
lean_ctor_set_uint8(x_307, sizeof(void*)*10 + 17, x_297);
x_302 = x_307;
goto block_306;
}
block_306:
{
lean_object* x_303; 
if (x_275 == 0)
{
lean_ctor_set(x_274, 0, x_302);
x_303 = x_274;
goto block_304;
}
else
{
lean_object* x_305; 
x_305 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_305, 0, x_302);
x_303 = x_305;
goto block_304;
}
block_304:
{
return x_303;
}
}
}
}
}
else
{
lean_object* x_312; lean_object* x_316; lean_object* x_317; 
lean_dec_ref(x_1);
x_312 = lean_ctor_get(x_272, 0);
lean_inc(x_312);
lean_dec_ref(x_272);
x_316 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_317 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_316);
lean_dec_ref(x_317);
goto block_315;
block_315:
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_io_error_to_string(x_312);
x_314 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_313);
lean_dec_ref(x_314);
goto block_131;
}
}
}
}
else
{
lean_object* x_318; lean_object* x_319; 
x_318 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__2));
x_319 = l___private_Lean_Shell_0__Lean_checkOptArg(x_318, x_3);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; uint8_t x_322; uint8_t x_357; 
x_320 = lean_ctor_get(x_319, 0);
x_357 = !lean_is_exclusive(x_319);
if (x_357 == 0)
{
x_321 = x_319;
x_322 = x_357;
goto block_356;
}
else
{
lean_inc(x_320);
lean_dec(x_319);
x_321 = lean_box(0);
x_322 = x_357;
goto block_356;
}
block_356:
{
lean_object* x_323; lean_object* x_324; uint8_t x_325; uint8_t x_326; uint8_t x_327; uint8_t x_328; uint8_t x_329; uint8_t x_330; uint8_t x_331; lean_object* x_332; uint32_t x_333; uint32_t x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; lean_object* x_341; uint8_t x_342; uint8_t x_343; lean_object* x_344; uint8_t x_345; uint8_t x_354; 
x_323 = lean_ctor_get(x_1, 0);
x_324 = lean_ctor_get(x_1, 1);
x_325 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_326 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_327 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_328 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_329 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_330 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_331 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_332 = lean_ctor_get(x_1, 2);
x_333 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_334 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_335 = lean_ctor_get(x_1, 3);
x_336 = lean_ctor_get(x_1, 5);
x_337 = lean_ctor_get(x_1, 6);
x_338 = lean_ctor_get(x_1, 7);
x_339 = lean_ctor_get(x_1, 8);
x_340 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_341 = lean_ctor_get(x_1, 9);
x_342 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_343 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_354 = !lean_is_exclusive(x_1);
if (x_354 == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_1, 4);
lean_dec(x_355);
x_344 = x_1;
x_345 = x_354;
goto block_353;
}
else
{
lean_inc(x_341);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_332);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_1);
x_344 = lean_box(0);
x_345 = x_354;
goto block_353;
}
block_353:
{
lean_object* x_346; lean_object* x_347; 
x_346 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_346, 0, x_320);
if (x_345 == 0)
{
lean_ctor_set(x_344, 4, x_346);
x_347 = x_344;
goto block_351;
}
else
{
lean_object* x_352; 
x_352 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_352, 0, x_323);
lean_ctor_set(x_352, 1, x_324);
lean_ctor_set(x_352, 2, x_332);
lean_ctor_set(x_352, 3, x_335);
lean_ctor_set(x_352, 4, x_346);
lean_ctor_set(x_352, 5, x_336);
lean_ctor_set(x_352, 6, x_337);
lean_ctor_set(x_352, 7, x_338);
lean_ctor_set(x_352, 8, x_339);
lean_ctor_set(x_352, 9, x_341);
lean_ctor_set_uint8(x_352, sizeof(void*)*10 + 8, x_325);
lean_ctor_set_uint8(x_352, sizeof(void*)*10 + 9, x_326);
lean_ctor_set_uint8(x_352, sizeof(void*)*10 + 10, x_327);
lean_ctor_set_uint8(x_352, sizeof(void*)*10 + 11, x_328);
lean_ctor_set_uint8(x_352, sizeof(void*)*10 + 12, x_329);
lean_ctor_set_uint8(x_352, sizeof(void*)*10 + 13, x_330);
lean_ctor_set_uint8(x_352, sizeof(void*)*10 + 14, x_331);
lean_ctor_set_uint32(x_352, sizeof(void*)*10, x_333);
lean_ctor_set_uint32(x_352, sizeof(void*)*10 + 4, x_334);
lean_ctor_set_uint8(x_352, sizeof(void*)*10 + 15, x_340);
lean_ctor_set_uint8(x_352, sizeof(void*)*10 + 16, x_342);
lean_ctor_set_uint8(x_352, sizeof(void*)*10 + 17, x_343);
x_347 = x_352;
goto block_351;
}
block_351:
{
lean_object* x_348; 
if (x_322 == 0)
{
lean_ctor_set(x_321, 0, x_347);
x_348 = x_321;
goto block_349;
}
else
{
lean_object* x_350; 
x_350 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_350, 0, x_347);
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
}
else
{
lean_object* x_358; lean_object* x_362; lean_object* x_363; 
lean_dec_ref(x_1);
x_358 = lean_ctor_get(x_319, 0);
lean_inc(x_358);
lean_dec_ref(x_319);
x_362 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_363 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_362);
lean_dec_ref(x_363);
goto block_361;
block_361:
{
lean_object* x_359; lean_object* x_360; 
x_359 = lean_io_error_to_string(x_358);
x_360 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_359);
lean_dec_ref(x_360);
goto block_97;
}
}
}
}
else
{
lean_object* x_364; lean_object* x_365; 
x_364 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__3));
x_365 = l___private_Lean_Shell_0__Lean_checkOptArg(x_364, x_3);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
lean_dec_ref(x_365);
lean_inc(x_366);
x_367 = lean_load_dynlib(x_366);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; uint8_t x_369; uint8_t x_406; 
x_406 = !lean_is_exclusive(x_367);
if (x_406 == 0)
{
lean_object* x_407; 
x_407 = lean_ctor_get(x_367, 0);
lean_dec(x_407);
x_368 = x_367;
x_369 = x_406;
goto block_405;
}
else
{
lean_dec(x_367);
x_368 = lean_box(0);
x_369 = x_406;
goto block_405;
}
block_405:
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint8_t x_373; uint8_t x_374; uint8_t x_375; uint8_t x_376; uint8_t x_377; uint8_t x_378; lean_object* x_379; uint32_t x_380; uint32_t x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; uint8_t x_390; uint8_t x_391; lean_object* x_392; uint8_t x_393; uint8_t x_404; 
x_370 = lean_ctor_get(x_1, 0);
x_371 = lean_ctor_get(x_1, 1);
x_372 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_373 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_374 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_375 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_376 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_377 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_378 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_379 = lean_ctor_get(x_1, 2);
x_380 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_381 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_382 = lean_ctor_get(x_1, 3);
x_383 = lean_ctor_get(x_1, 4);
x_384 = lean_ctor_get(x_1, 5);
x_385 = lean_ctor_get(x_1, 6);
x_386 = lean_ctor_get(x_1, 7);
x_387 = lean_ctor_get(x_1, 8);
x_388 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_389 = lean_ctor_get(x_1, 9);
x_390 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_391 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_404 = !lean_is_exclusive(x_1);
if (x_404 == 0)
{
x_392 = x_1;
x_393 = x_404;
goto block_403;
}
else
{
lean_inc(x_389);
lean_inc(x_387);
lean_inc(x_386);
lean_inc(x_385);
lean_inc(x_384);
lean_inc(x_383);
lean_inc(x_382);
lean_inc(x_379);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_1);
x_392 = lean_box(0);
x_393 = x_404;
goto block_403;
}
block_403:
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_394 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__4));
x_395 = lean_string_append(x_394, x_366);
lean_dec(x_366);
x_396 = lean_array_push(x_371, x_395);
if (x_393 == 0)
{
lean_ctor_set(x_392, 1, x_396);
x_397 = x_392;
goto block_401;
}
else
{
lean_object* x_402; 
x_402 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_402, 0, x_370);
lean_ctor_set(x_402, 1, x_396);
lean_ctor_set(x_402, 2, x_379);
lean_ctor_set(x_402, 3, x_382);
lean_ctor_set(x_402, 4, x_383);
lean_ctor_set(x_402, 5, x_384);
lean_ctor_set(x_402, 6, x_385);
lean_ctor_set(x_402, 7, x_386);
lean_ctor_set(x_402, 8, x_387);
lean_ctor_set(x_402, 9, x_389);
lean_ctor_set_uint8(x_402, sizeof(void*)*10 + 8, x_372);
lean_ctor_set_uint8(x_402, sizeof(void*)*10 + 9, x_373);
lean_ctor_set_uint8(x_402, sizeof(void*)*10 + 10, x_374);
lean_ctor_set_uint8(x_402, sizeof(void*)*10 + 11, x_375);
lean_ctor_set_uint8(x_402, sizeof(void*)*10 + 12, x_376);
lean_ctor_set_uint8(x_402, sizeof(void*)*10 + 13, x_377);
lean_ctor_set_uint8(x_402, sizeof(void*)*10 + 14, x_378);
lean_ctor_set_uint32(x_402, sizeof(void*)*10, x_380);
lean_ctor_set_uint32(x_402, sizeof(void*)*10 + 4, x_381);
lean_ctor_set_uint8(x_402, sizeof(void*)*10 + 15, x_388);
lean_ctor_set_uint8(x_402, sizeof(void*)*10 + 16, x_390);
lean_ctor_set_uint8(x_402, sizeof(void*)*10 + 17, x_391);
x_397 = x_402;
goto block_401;
}
block_401:
{
lean_object* x_398; 
if (x_369 == 0)
{
lean_ctor_set(x_368, 0, x_397);
x_398 = x_368;
goto block_399;
}
else
{
lean_object* x_400; 
x_400 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_400, 0, x_397);
x_398 = x_400;
goto block_399;
}
block_399:
{
return x_398;
}
}
}
}
}
else
{
lean_object* x_408; lean_object* x_412; lean_object* x_413; 
lean_dec(x_366);
lean_dec_ref(x_1);
x_408 = lean_ctor_get(x_367, 0);
lean_inc(x_408);
lean_dec_ref(x_367);
x_412 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_413 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_412);
lean_dec_ref(x_413);
goto block_411;
block_411:
{
lean_object* x_409; lean_object* x_410; 
x_409 = lean_io_error_to_string(x_408);
x_410 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_409);
lean_dec_ref(x_410);
goto block_137;
}
}
}
else
{
lean_object* x_414; lean_object* x_418; lean_object* x_419; 
lean_dec_ref(x_1);
x_414 = lean_ctor_get(x_365, 0);
lean_inc(x_414);
lean_dec_ref(x_365);
x_418 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_419 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_418);
lean_dec_ref(x_419);
goto block_417;
block_417:
{
lean_object* x_415; lean_object* x_416; 
x_415 = lean_io_error_to_string(x_414);
x_416 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_415);
lean_dec_ref(x_416);
goto block_91;
}
}
}
}
else
{
lean_object* x_420; lean_object* x_421; 
x_420 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__5));
x_421 = l___private_Lean_Shell_0__Lean_checkOptArg(x_420, x_3);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
lean_dec_ref(x_421);
lean_inc(x_422);
x_423 = lean_load_plugin(x_422);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; uint8_t x_425; uint8_t x_462; 
x_462 = !lean_is_exclusive(x_423);
if (x_462 == 0)
{
lean_object* x_463; 
x_463 = lean_ctor_get(x_423, 0);
lean_dec(x_463);
x_424 = x_423;
x_425 = x_462;
goto block_461;
}
else
{
lean_dec(x_423);
x_424 = lean_box(0);
x_425 = x_462;
goto block_461;
}
block_461:
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; uint8_t x_429; uint8_t x_430; uint8_t x_431; uint8_t x_432; uint8_t x_433; uint8_t x_434; lean_object* x_435; uint32_t x_436; uint32_t x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; uint8_t x_446; uint8_t x_447; lean_object* x_448; uint8_t x_449; uint8_t x_460; 
x_426 = lean_ctor_get(x_1, 0);
x_427 = lean_ctor_get(x_1, 1);
x_428 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_429 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_430 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_431 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_432 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_433 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_434 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_435 = lean_ctor_get(x_1, 2);
x_436 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_437 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_438 = lean_ctor_get(x_1, 3);
x_439 = lean_ctor_get(x_1, 4);
x_440 = lean_ctor_get(x_1, 5);
x_441 = lean_ctor_get(x_1, 6);
x_442 = lean_ctor_get(x_1, 7);
x_443 = lean_ctor_get(x_1, 8);
x_444 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_445 = lean_ctor_get(x_1, 9);
x_446 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_447 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_460 = !lean_is_exclusive(x_1);
if (x_460 == 0)
{
x_448 = x_1;
x_449 = x_460;
goto block_459;
}
else
{
lean_inc(x_445);
lean_inc(x_443);
lean_inc(x_442);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_inc(x_435);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_1);
x_448 = lean_box(0);
x_449 = x_460;
goto block_459;
}
block_459:
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_450 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__6));
x_451 = lean_string_append(x_450, x_422);
lean_dec(x_422);
x_452 = lean_array_push(x_427, x_451);
if (x_449 == 0)
{
lean_ctor_set(x_448, 1, x_452);
x_453 = x_448;
goto block_457;
}
else
{
lean_object* x_458; 
x_458 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_458, 0, x_426);
lean_ctor_set(x_458, 1, x_452);
lean_ctor_set(x_458, 2, x_435);
lean_ctor_set(x_458, 3, x_438);
lean_ctor_set(x_458, 4, x_439);
lean_ctor_set(x_458, 5, x_440);
lean_ctor_set(x_458, 6, x_441);
lean_ctor_set(x_458, 7, x_442);
lean_ctor_set(x_458, 8, x_443);
lean_ctor_set(x_458, 9, x_445);
lean_ctor_set_uint8(x_458, sizeof(void*)*10 + 8, x_428);
lean_ctor_set_uint8(x_458, sizeof(void*)*10 + 9, x_429);
lean_ctor_set_uint8(x_458, sizeof(void*)*10 + 10, x_430);
lean_ctor_set_uint8(x_458, sizeof(void*)*10 + 11, x_431);
lean_ctor_set_uint8(x_458, sizeof(void*)*10 + 12, x_432);
lean_ctor_set_uint8(x_458, sizeof(void*)*10 + 13, x_433);
lean_ctor_set_uint8(x_458, sizeof(void*)*10 + 14, x_434);
lean_ctor_set_uint32(x_458, sizeof(void*)*10, x_436);
lean_ctor_set_uint32(x_458, sizeof(void*)*10 + 4, x_437);
lean_ctor_set_uint8(x_458, sizeof(void*)*10 + 15, x_444);
lean_ctor_set_uint8(x_458, sizeof(void*)*10 + 16, x_446);
lean_ctor_set_uint8(x_458, sizeof(void*)*10 + 17, x_447);
x_453 = x_458;
goto block_457;
}
block_457:
{
lean_object* x_454; 
if (x_425 == 0)
{
lean_ctor_set(x_424, 0, x_453);
x_454 = x_424;
goto block_455;
}
else
{
lean_object* x_456; 
x_456 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_456, 0, x_453);
x_454 = x_456;
goto block_455;
}
block_455:
{
return x_454;
}
}
}
}
}
else
{
lean_object* x_464; lean_object* x_468; lean_object* x_469; 
lean_dec(x_422);
lean_dec_ref(x_1);
x_464 = lean_ctor_get(x_423, 0);
lean_inc(x_464);
lean_dec_ref(x_423);
x_468 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_469 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_468);
lean_dec_ref(x_469);
goto block_467;
block_467:
{
lean_object* x_465; lean_object* x_466; 
x_465 = lean_io_error_to_string(x_464);
x_466 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_465);
lean_dec_ref(x_466);
goto block_143;
}
}
}
else
{
lean_object* x_470; lean_object* x_474; lean_object* x_475; 
lean_dec_ref(x_1);
x_470 = lean_ctor_get(x_421, 0);
lean_inc(x_470);
lean_dec_ref(x_421);
x_474 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_475 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_474);
lean_dec_ref(x_475);
goto block_473;
block_473:
{
lean_object* x_471; lean_object* x_472; 
x_471 = lean_io_error_to_string(x_470);
x_472 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_471);
lean_dec_ref(x_472);
goto block_85;
}
}
}
}
else
{
uint8_t x_476; 
x_476 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_displayHelp___closed__12, &l___private_Lean_Shell_0__Lean_displayHelp___closed__12_once, _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12);
if (x_476 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_125;
}
else
{
lean_object* x_477; lean_object* x_478; 
x_477 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__7));
x_478 = l___private_Lean_Shell_0__Lean_checkOptArg(x_477, x_3);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; uint8_t x_481; uint8_t x_487; 
x_479 = lean_ctor_get(x_478, 0);
x_487 = !lean_is_exclusive(x_478);
if (x_487 == 0)
{
x_480 = x_478;
x_481 = x_487;
goto block_486;
}
else
{
lean_inc(x_479);
lean_dec(x_478);
x_480 = lean_box(0);
x_481 = x_487;
goto block_486;
}
block_486:
{
lean_object* x_482; lean_object* x_483; 
x_482 = lean_internal_enable_debug(x_479);
lean_dec(x_479);
if (x_481 == 0)
{
lean_ctor_set(x_480, 0, x_1);
x_483 = x_480;
goto block_484;
}
else
{
lean_object* x_485; 
x_485 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_485, 0, x_1);
x_483 = x_485;
goto block_484;
}
block_484:
{
return x_483;
}
}
}
else
{
lean_object* x_488; lean_object* x_492; lean_object* x_493; 
lean_dec_ref(x_1);
x_488 = lean_ctor_get(x_478, 0);
lean_inc(x_488);
lean_dec_ref(x_478);
x_492 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_493 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_492);
lean_dec_ref(x_493);
goto block_491;
block_491:
{
lean_object* x_489; lean_object* x_490; 
x_489 = lean_io_error_to_string(x_488);
x_490 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_489);
lean_dec_ref(x_490);
goto block_149;
}
}
}
}
}
else
{
lean_object* x_494; lean_object* x_495; uint8_t x_496; uint8_t x_497; uint8_t x_498; uint8_t x_499; uint8_t x_500; uint8_t x_501; uint8_t x_502; lean_object* x_503; uint32_t x_504; uint32_t x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; lean_object* x_513; uint8_t x_514; uint8_t x_515; lean_object* x_516; uint8_t x_517; uint8_t x_525; 
lean_dec(x_3);
x_494 = lean_ctor_get(x_1, 0);
x_495 = lean_ctor_get(x_1, 1);
x_496 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_497 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_498 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_499 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_500 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_501 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_502 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_503 = lean_ctor_get(x_1, 2);
x_504 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_505 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_506 = lean_ctor_get(x_1, 3);
x_507 = lean_ctor_get(x_1, 4);
x_508 = lean_ctor_get(x_1, 5);
x_509 = lean_ctor_get(x_1, 6);
x_510 = lean_ctor_get(x_1, 7);
x_511 = lean_ctor_get(x_1, 8);
x_512 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_513 = lean_ctor_get(x_1, 9);
x_514 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_515 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_525 = !lean_is_exclusive(x_1);
if (x_525 == 0)
{
x_516 = x_1;
x_517 = x_525;
goto block_524;
}
else
{
lean_inc(x_513);
lean_inc(x_511);
lean_inc(x_510);
lean_inc(x_509);
lean_inc(x_508);
lean_inc(x_507);
lean_inc(x_506);
lean_inc(x_503);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_1);
x_516 = lean_box(0);
x_517 = x_525;
goto block_524;
}
block_524:
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = l_Lean_profiler;
x_519 = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(x_494, x_518, x_260);
if (x_517 == 0)
{
lean_ctor_set(x_516, 0, x_519);
x_520 = x_516;
goto block_522;
}
else
{
lean_object* x_523; 
x_523 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_523, 0, x_519);
lean_ctor_set(x_523, 1, x_495);
lean_ctor_set(x_523, 2, x_503);
lean_ctor_set(x_523, 3, x_506);
lean_ctor_set(x_523, 4, x_507);
lean_ctor_set(x_523, 5, x_508);
lean_ctor_set(x_523, 6, x_509);
lean_ctor_set(x_523, 7, x_510);
lean_ctor_set(x_523, 8, x_511);
lean_ctor_set(x_523, 9, x_513);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 8, x_496);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 9, x_497);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 10, x_498);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 11, x_499);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 12, x_500);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 13, x_501);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 14, x_502);
lean_ctor_set_uint32(x_523, sizeof(void*)*10, x_504);
lean_ctor_set_uint32(x_523, sizeof(void*)*10 + 4, x_505);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 15, x_512);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 16, x_514);
lean_ctor_set_uint8(x_523, sizeof(void*)*10 + 17, x_515);
x_520 = x_523;
goto block_522;
}
block_522:
{
lean_object* x_521; 
x_521 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_521, 0, x_520);
return x_521;
}
}
}
}
else
{
lean_object* x_526; lean_object* x_527; uint8_t x_528; uint8_t x_529; uint8_t x_530; uint8_t x_531; uint8_t x_532; uint8_t x_533; lean_object* x_534; uint32_t x_535; uint32_t x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; uint8_t x_545; uint8_t x_546; lean_object* x_547; uint8_t x_548; uint8_t x_555; 
lean_dec(x_3);
x_526 = lean_ctor_get(x_1, 0);
x_527 = lean_ctor_get(x_1, 1);
x_528 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_529 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_530 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_531 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_532 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_533 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_534 = lean_ctor_get(x_1, 2);
x_535 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_536 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_537 = lean_ctor_get(x_1, 3);
x_538 = lean_ctor_get(x_1, 4);
x_539 = lean_ctor_get(x_1, 5);
x_540 = lean_ctor_get(x_1, 6);
x_541 = lean_ctor_get(x_1, 7);
x_542 = lean_ctor_get(x_1, 8);
x_543 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_544 = lean_ctor_get(x_1, 9);
x_545 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_546 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_555 = !lean_is_exclusive(x_1);
if (x_555 == 0)
{
x_547 = x_1;
x_548 = x_555;
goto block_554;
}
else
{
lean_inc(x_544);
lean_inc(x_542);
lean_inc(x_541);
lean_inc(x_540);
lean_inc(x_539);
lean_inc(x_538);
lean_inc(x_537);
lean_inc(x_534);
lean_inc(x_527);
lean_inc(x_526);
lean_dec(x_1);
x_547 = lean_box(0);
x_548 = x_555;
goto block_554;
}
block_554:
{
uint8_t x_549; lean_object* x_550; 
x_549 = 2;
if (x_548 == 0)
{
x_550 = x_547;
goto block_552;
}
else
{
lean_object* x_553; 
x_553 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_553, 0, x_526);
lean_ctor_set(x_553, 1, x_527);
lean_ctor_set(x_553, 2, x_534);
lean_ctor_set(x_553, 3, x_537);
lean_ctor_set(x_553, 4, x_538);
lean_ctor_set(x_553, 5, x_539);
lean_ctor_set(x_553, 6, x_540);
lean_ctor_set(x_553, 7, x_541);
lean_ctor_set(x_553, 8, x_542);
lean_ctor_set(x_553, 9, x_544);
lean_ctor_set_uint8(x_553, sizeof(void*)*10 + 9, x_528);
lean_ctor_set_uint8(x_553, sizeof(void*)*10 + 10, x_529);
lean_ctor_set_uint8(x_553, sizeof(void*)*10 + 11, x_530);
lean_ctor_set_uint8(x_553, sizeof(void*)*10 + 12, x_531);
lean_ctor_set_uint8(x_553, sizeof(void*)*10 + 13, x_532);
lean_ctor_set_uint8(x_553, sizeof(void*)*10 + 14, x_533);
lean_ctor_set_uint32(x_553, sizeof(void*)*10, x_535);
lean_ctor_set_uint32(x_553, sizeof(void*)*10 + 4, x_536);
lean_ctor_set_uint8(x_553, sizeof(void*)*10 + 15, x_543);
lean_ctor_set_uint8(x_553, sizeof(void*)*10 + 16, x_545);
lean_ctor_set_uint8(x_553, sizeof(void*)*10 + 17, x_546);
x_550 = x_553;
goto block_552;
}
block_552:
{
lean_object* x_551; 
lean_ctor_set_uint8(x_550, sizeof(void*)*10 + 8, x_549);
x_551 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_551, 0, x_550);
return x_551;
}
}
}
}
else
{
lean_object* x_556; lean_object* x_557; uint8_t x_558; uint8_t x_559; uint8_t x_560; uint8_t x_561; uint8_t x_562; uint8_t x_563; lean_object* x_564; uint32_t x_565; uint32_t x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; lean_object* x_574; uint8_t x_575; uint8_t x_576; lean_object* x_577; uint8_t x_578; uint8_t x_585; 
lean_dec(x_3);
x_556 = lean_ctor_get(x_1, 0);
x_557 = lean_ctor_get(x_1, 1);
x_558 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_559 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_560 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_561 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_562 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_563 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_564 = lean_ctor_get(x_1, 2);
x_565 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_566 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_567 = lean_ctor_get(x_1, 3);
x_568 = lean_ctor_get(x_1, 4);
x_569 = lean_ctor_get(x_1, 5);
x_570 = lean_ctor_get(x_1, 6);
x_571 = lean_ctor_get(x_1, 7);
x_572 = lean_ctor_get(x_1, 8);
x_573 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_574 = lean_ctor_get(x_1, 9);
x_575 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_576 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_585 = !lean_is_exclusive(x_1);
if (x_585 == 0)
{
x_577 = x_1;
x_578 = x_585;
goto block_584;
}
else
{
lean_inc(x_574);
lean_inc(x_572);
lean_inc(x_571);
lean_inc(x_570);
lean_inc(x_569);
lean_inc(x_568);
lean_inc(x_567);
lean_inc(x_564);
lean_inc(x_557);
lean_inc(x_556);
lean_dec(x_1);
x_577 = lean_box(0);
x_578 = x_585;
goto block_584;
}
block_584:
{
uint8_t x_579; lean_object* x_580; 
x_579 = 1;
if (x_578 == 0)
{
x_580 = x_577;
goto block_582;
}
else
{
lean_object* x_583; 
x_583 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_583, 0, x_556);
lean_ctor_set(x_583, 1, x_557);
lean_ctor_set(x_583, 2, x_564);
lean_ctor_set(x_583, 3, x_567);
lean_ctor_set(x_583, 4, x_568);
lean_ctor_set(x_583, 5, x_569);
lean_ctor_set(x_583, 6, x_570);
lean_ctor_set(x_583, 7, x_571);
lean_ctor_set(x_583, 8, x_572);
lean_ctor_set(x_583, 9, x_574);
lean_ctor_set_uint8(x_583, sizeof(void*)*10 + 9, x_558);
lean_ctor_set_uint8(x_583, sizeof(void*)*10 + 10, x_559);
lean_ctor_set_uint8(x_583, sizeof(void*)*10 + 11, x_560);
lean_ctor_set_uint8(x_583, sizeof(void*)*10 + 12, x_561);
lean_ctor_set_uint8(x_583, sizeof(void*)*10 + 13, x_562);
lean_ctor_set_uint8(x_583, sizeof(void*)*10 + 14, x_563);
lean_ctor_set_uint32(x_583, sizeof(void*)*10, x_565);
lean_ctor_set_uint32(x_583, sizeof(void*)*10 + 4, x_566);
lean_ctor_set_uint8(x_583, sizeof(void*)*10 + 15, x_573);
lean_ctor_set_uint8(x_583, sizeof(void*)*10 + 16, x_575);
lean_ctor_set_uint8(x_583, sizeof(void*)*10 + 17, x_576);
x_580 = x_583;
goto block_582;
}
block_582:
{
lean_object* x_581; 
lean_ctor_set_uint8(x_580, sizeof(void*)*10 + 8, x_579);
x_581 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_581, 0, x_580);
return x_581;
}
}
}
}
else
{
lean_object* x_586; lean_object* x_587; 
x_586 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__8));
x_587 = l___private_Lean_Shell_0__Lean_checkOptArg(x_586, x_3);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; uint8_t x_592; uint8_t x_593; uint8_t x_594; uint8_t x_595; uint8_t x_596; uint8_t x_597; lean_object* x_598; uint32_t x_599; uint32_t x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_607; lean_object* x_608; uint8_t x_609; uint8_t x_610; lean_object* x_611; uint8_t x_612; uint8_t x_635; 
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
lean_dec_ref(x_587);
x_589 = lean_ctor_get(x_1, 0);
x_590 = lean_ctor_get(x_1, 1);
x_591 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_592 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_593 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_594 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_595 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_596 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_597 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_598 = lean_ctor_get(x_1, 2);
x_599 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_600 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_601 = lean_ctor_get(x_1, 3);
x_602 = lean_ctor_get(x_1, 4);
x_603 = lean_ctor_get(x_1, 5);
x_604 = lean_ctor_get(x_1, 6);
x_605 = lean_ctor_get(x_1, 7);
x_606 = lean_ctor_get(x_1, 8);
x_607 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_608 = lean_ctor_get(x_1, 9);
x_609 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_610 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_635 = !lean_is_exclusive(x_1);
if (x_635 == 0)
{
x_611 = x_1;
x_612 = x_635;
goto block_634;
}
else
{
lean_inc(x_608);
lean_inc(x_606);
lean_inc(x_605);
lean_inc(x_604);
lean_inc(x_603);
lean_inc(x_602);
lean_inc(x_601);
lean_inc(x_598);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_1);
x_611 = lean_box(0);
x_612 = x_635;
goto block_634;
}
block_634:
{
lean_object* x_613; 
lean_inc(x_588);
x_613 = l___private_Lean_Shell_0__Lean_setConfigOption(x_589, x_588);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; uint8_t x_616; uint8_t x_627; 
x_614 = lean_ctor_get(x_613, 0);
x_627 = !lean_is_exclusive(x_613);
if (x_627 == 0)
{
x_615 = x_613;
x_616 = x_627;
goto block_626;
}
else
{
lean_inc(x_614);
lean_dec(x_613);
x_615 = lean_box(0);
x_616 = x_627;
goto block_626;
}
block_626:
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_617 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__9));
x_618 = lean_string_append(x_617, x_588);
lean_dec(x_588);
x_619 = lean_array_push(x_590, x_618);
if (x_612 == 0)
{
lean_ctor_set(x_611, 1, x_619);
lean_ctor_set(x_611, 0, x_614);
x_620 = x_611;
goto block_624;
}
else
{
lean_object* x_625; 
x_625 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_625, 0, x_614);
lean_ctor_set(x_625, 1, x_619);
lean_ctor_set(x_625, 2, x_598);
lean_ctor_set(x_625, 3, x_601);
lean_ctor_set(x_625, 4, x_602);
lean_ctor_set(x_625, 5, x_603);
lean_ctor_set(x_625, 6, x_604);
lean_ctor_set(x_625, 7, x_605);
lean_ctor_set(x_625, 8, x_606);
lean_ctor_set(x_625, 9, x_608);
lean_ctor_set_uint8(x_625, sizeof(void*)*10 + 8, x_591);
lean_ctor_set_uint8(x_625, sizeof(void*)*10 + 9, x_592);
lean_ctor_set_uint8(x_625, sizeof(void*)*10 + 10, x_593);
lean_ctor_set_uint8(x_625, sizeof(void*)*10 + 11, x_594);
lean_ctor_set_uint8(x_625, sizeof(void*)*10 + 12, x_595);
lean_ctor_set_uint8(x_625, sizeof(void*)*10 + 13, x_596);
lean_ctor_set_uint8(x_625, sizeof(void*)*10 + 14, x_597);
lean_ctor_set_uint32(x_625, sizeof(void*)*10, x_599);
lean_ctor_set_uint32(x_625, sizeof(void*)*10 + 4, x_600);
lean_ctor_set_uint8(x_625, sizeof(void*)*10 + 15, x_607);
lean_ctor_set_uint8(x_625, sizeof(void*)*10 + 16, x_609);
lean_ctor_set_uint8(x_625, sizeof(void*)*10 + 17, x_610);
x_620 = x_625;
goto block_624;
}
block_624:
{
lean_object* x_621; 
if (x_616 == 0)
{
lean_ctor_set(x_615, 0, x_620);
x_621 = x_615;
goto block_622;
}
else
{
lean_object* x_623; 
x_623 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_623, 0, x_620);
x_621 = x_623;
goto block_622;
}
block_622:
{
return x_621;
}
}
}
}
else
{
lean_object* x_628; lean_object* x_632; lean_object* x_633; 
lean_del_object(x_611);
lean_dec_ref(x_608);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_602);
lean_dec(x_601);
lean_dec_ref(x_598);
lean_dec_ref(x_590);
lean_dec(x_588);
x_628 = lean_ctor_get(x_613, 0);
lean_inc(x_628);
lean_dec_ref(x_613);
x_632 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_633 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_632);
lean_dec_ref(x_633);
goto block_631;
block_631:
{
lean_object* x_629; lean_object* x_630; 
x_629 = lean_io_error_to_string(x_628);
x_630 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_629);
lean_dec_ref(x_630);
goto block_79;
}
}
}
}
else
{
lean_object* x_636; lean_object* x_640; lean_object* x_641; 
lean_dec_ref(x_1);
x_636 = lean_ctor_get(x_587, 0);
lean_inc(x_636);
lean_dec_ref(x_587);
x_640 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_641 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_640);
lean_dec_ref(x_641);
goto block_639;
block_639:
{
lean_object* x_637; lean_object* x_638; 
x_637 = lean_io_error_to_string(x_636);
x_638 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_637);
lean_dec_ref(x_638);
goto block_155;
}
}
}
}
else
{
lean_object* x_642; lean_object* x_643; uint8_t x_644; uint8_t x_645; uint8_t x_646; uint8_t x_647; uint8_t x_648; uint8_t x_649; lean_object* x_650; uint32_t x_651; uint32_t x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; uint8_t x_659; lean_object* x_660; uint8_t x_661; uint8_t x_662; lean_object* x_663; uint8_t x_664; uint8_t x_670; 
lean_dec(x_3);
x_642 = lean_ctor_get(x_1, 0);
x_643 = lean_ctor_get(x_1, 1);
x_644 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_645 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_646 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_647 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_648 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_649 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_650 = lean_ctor_get(x_1, 2);
x_651 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_652 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_653 = lean_ctor_get(x_1, 3);
x_654 = lean_ctor_get(x_1, 4);
x_655 = lean_ctor_get(x_1, 5);
x_656 = lean_ctor_get(x_1, 6);
x_657 = lean_ctor_get(x_1, 7);
x_658 = lean_ctor_get(x_1, 8);
x_659 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_660 = lean_ctor_get(x_1, 9);
x_661 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_662 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_670 = !lean_is_exclusive(x_1);
if (x_670 == 0)
{
x_663 = x_1;
x_664 = x_670;
goto block_669;
}
else
{
lean_inc(x_660);
lean_inc(x_658);
lean_inc(x_657);
lean_inc(x_656);
lean_inc(x_655);
lean_inc(x_654);
lean_inc(x_653);
lean_inc(x_650);
lean_inc(x_643);
lean_inc(x_642);
lean_dec(x_1);
x_663 = lean_box(0);
x_664 = x_670;
goto block_669;
}
block_669:
{
lean_object* x_665; 
if (x_664 == 0)
{
x_665 = x_663;
goto block_667;
}
else
{
lean_object* x_668; 
x_668 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_668, 0, x_642);
lean_ctor_set(x_668, 1, x_643);
lean_ctor_set(x_668, 2, x_650);
lean_ctor_set(x_668, 3, x_653);
lean_ctor_set(x_668, 4, x_654);
lean_ctor_set(x_668, 5, x_655);
lean_ctor_set(x_668, 6, x_656);
lean_ctor_set(x_668, 7, x_657);
lean_ctor_set(x_668, 8, x_658);
lean_ctor_set(x_668, 9, x_660);
lean_ctor_set_uint8(x_668, sizeof(void*)*10 + 8, x_644);
lean_ctor_set_uint8(x_668, sizeof(void*)*10 + 9, x_645);
lean_ctor_set_uint8(x_668, sizeof(void*)*10 + 11, x_646);
lean_ctor_set_uint8(x_668, sizeof(void*)*10 + 12, x_647);
lean_ctor_set_uint8(x_668, sizeof(void*)*10 + 13, x_648);
lean_ctor_set_uint8(x_668, sizeof(void*)*10 + 14, x_649);
lean_ctor_set_uint32(x_668, sizeof(void*)*10, x_651);
lean_ctor_set_uint32(x_668, sizeof(void*)*10 + 4, x_652);
lean_ctor_set_uint8(x_668, sizeof(void*)*10 + 15, x_659);
lean_ctor_set_uint8(x_668, sizeof(void*)*10 + 16, x_661);
lean_ctor_set_uint8(x_668, sizeof(void*)*10 + 17, x_662);
x_665 = x_668;
goto block_667;
}
block_667:
{
lean_object* x_666; 
lean_ctor_set_uint8(x_665, sizeof(void*)*10 + 10, x_252);
x_666 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_666, 0, x_665);
return x_666;
}
}
}
}
else
{
lean_object* x_671; lean_object* x_672; uint8_t x_673; uint8_t x_674; uint8_t x_675; uint8_t x_676; uint8_t x_677; uint8_t x_678; lean_object* x_679; uint32_t x_680; uint32_t x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; uint8_t x_688; lean_object* x_689; uint8_t x_690; uint8_t x_691; lean_object* x_692; uint8_t x_693; uint8_t x_699; 
lean_dec(x_3);
x_671 = lean_ctor_get(x_1, 0);
x_672 = lean_ctor_get(x_1, 1);
x_673 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_674 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_675 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_676 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_677 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_678 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_679 = lean_ctor_get(x_1, 2);
x_680 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_681 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_682 = lean_ctor_get(x_1, 3);
x_683 = lean_ctor_get(x_1, 4);
x_684 = lean_ctor_get(x_1, 5);
x_685 = lean_ctor_get(x_1, 6);
x_686 = lean_ctor_get(x_1, 7);
x_687 = lean_ctor_get(x_1, 8);
x_688 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_689 = lean_ctor_get(x_1, 9);
x_690 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_691 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_699 = !lean_is_exclusive(x_1);
if (x_699 == 0)
{
x_692 = x_1;
x_693 = x_699;
goto block_698;
}
else
{
lean_inc(x_689);
lean_inc(x_687);
lean_inc(x_686);
lean_inc(x_685);
lean_inc(x_684);
lean_inc(x_683);
lean_inc(x_682);
lean_inc(x_679);
lean_inc(x_672);
lean_inc(x_671);
lean_dec(x_1);
x_692 = lean_box(0);
x_693 = x_699;
goto block_698;
}
block_698:
{
lean_object* x_694; 
if (x_693 == 0)
{
x_694 = x_692;
goto block_696;
}
else
{
lean_object* x_697; 
x_697 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_697, 0, x_671);
lean_ctor_set(x_697, 1, x_672);
lean_ctor_set(x_697, 2, x_679);
lean_ctor_set(x_697, 3, x_682);
lean_ctor_set(x_697, 4, x_683);
lean_ctor_set(x_697, 5, x_684);
lean_ctor_set(x_697, 6, x_685);
lean_ctor_set(x_697, 7, x_686);
lean_ctor_set(x_697, 8, x_687);
lean_ctor_set(x_697, 9, x_689);
lean_ctor_set_uint8(x_697, sizeof(void*)*10 + 8, x_673);
lean_ctor_set_uint8(x_697, sizeof(void*)*10 + 10, x_674);
lean_ctor_set_uint8(x_697, sizeof(void*)*10 + 11, x_675);
lean_ctor_set_uint8(x_697, sizeof(void*)*10 + 12, x_676);
lean_ctor_set_uint8(x_697, sizeof(void*)*10 + 13, x_677);
lean_ctor_set_uint8(x_697, sizeof(void*)*10 + 14, x_678);
lean_ctor_set_uint32(x_697, sizeof(void*)*10, x_680);
lean_ctor_set_uint32(x_697, sizeof(void*)*10 + 4, x_681);
lean_ctor_set_uint8(x_697, sizeof(void*)*10 + 15, x_688);
lean_ctor_set_uint8(x_697, sizeof(void*)*10 + 16, x_690);
lean_ctor_set_uint8(x_697, sizeof(void*)*10 + 17, x_691);
x_694 = x_697;
goto block_696;
}
block_696:
{
lean_object* x_695; 
lean_ctor_set_uint8(x_694, sizeof(void*)*10 + 9, x_250);
x_695 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_695, 0, x_694);
return x_695;
}
}
}
}
else
{
lean_object* x_700; lean_object* x_701; uint8_t x_702; uint8_t x_703; uint8_t x_704; uint8_t x_705; uint8_t x_706; uint8_t x_707; uint8_t x_708; lean_object* x_709; uint32_t x_710; uint32_t x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; uint8_t x_718; lean_object* x_719; uint8_t x_720; lean_object* x_721; uint8_t x_722; uint8_t x_728; 
lean_dec(x_3);
x_700 = lean_ctor_get(x_1, 0);
x_701 = lean_ctor_get(x_1, 1);
x_702 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_703 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_704 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_705 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_706 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_707 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_708 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_709 = lean_ctor_get(x_1, 2);
x_710 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_711 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_712 = lean_ctor_get(x_1, 3);
x_713 = lean_ctor_get(x_1, 4);
x_714 = lean_ctor_get(x_1, 5);
x_715 = lean_ctor_get(x_1, 6);
x_716 = lean_ctor_get(x_1, 7);
x_717 = lean_ctor_get(x_1, 8);
x_718 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_719 = lean_ctor_get(x_1, 9);
x_720 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_728 = !lean_is_exclusive(x_1);
if (x_728 == 0)
{
x_721 = x_1;
x_722 = x_728;
goto block_727;
}
else
{
lean_inc(x_719);
lean_inc(x_717);
lean_inc(x_716);
lean_inc(x_715);
lean_inc(x_714);
lean_inc(x_713);
lean_inc(x_712);
lean_inc(x_709);
lean_inc(x_701);
lean_inc(x_700);
lean_dec(x_1);
x_721 = lean_box(0);
x_722 = x_728;
goto block_727;
}
block_727:
{
lean_object* x_723; 
if (x_722 == 0)
{
x_723 = x_721;
goto block_725;
}
else
{
lean_object* x_726; 
x_726 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_726, 0, x_700);
lean_ctor_set(x_726, 1, x_701);
lean_ctor_set(x_726, 2, x_709);
lean_ctor_set(x_726, 3, x_712);
lean_ctor_set(x_726, 4, x_713);
lean_ctor_set(x_726, 5, x_714);
lean_ctor_set(x_726, 6, x_715);
lean_ctor_set(x_726, 7, x_716);
lean_ctor_set(x_726, 8, x_717);
lean_ctor_set(x_726, 9, x_719);
lean_ctor_set_uint8(x_726, sizeof(void*)*10 + 8, x_702);
lean_ctor_set_uint8(x_726, sizeof(void*)*10 + 9, x_703);
lean_ctor_set_uint8(x_726, sizeof(void*)*10 + 10, x_704);
lean_ctor_set_uint8(x_726, sizeof(void*)*10 + 11, x_705);
lean_ctor_set_uint8(x_726, sizeof(void*)*10 + 12, x_706);
lean_ctor_set_uint8(x_726, sizeof(void*)*10 + 13, x_707);
lean_ctor_set_uint8(x_726, sizeof(void*)*10 + 14, x_708);
lean_ctor_set_uint32(x_726, sizeof(void*)*10, x_710);
lean_ctor_set_uint32(x_726, sizeof(void*)*10 + 4, x_711);
lean_ctor_set_uint8(x_726, sizeof(void*)*10 + 15, x_718);
lean_ctor_set_uint8(x_726, sizeof(void*)*10 + 17, x_720);
x_723 = x_726;
goto block_725;
}
block_725:
{
lean_object* x_724; 
lean_ctor_set_uint8(x_723, sizeof(void*)*10 + 16, x_248);
x_724 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_724, 0, x_723);
return x_724;
}
}
}
}
else
{
lean_object* x_729; lean_object* x_730; uint8_t x_731; uint8_t x_732; uint8_t x_733; uint8_t x_734; uint8_t x_735; uint8_t x_736; uint8_t x_737; lean_object* x_738; uint32_t x_739; uint32_t x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; uint8_t x_748; uint8_t x_749; lean_object* x_750; uint8_t x_751; uint8_t x_757; 
lean_dec(x_3);
x_729 = lean_ctor_get(x_1, 0);
x_730 = lean_ctor_get(x_1, 1);
x_731 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_732 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_733 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_734 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_735 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_736 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_737 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_738 = lean_ctor_get(x_1, 2);
x_739 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_740 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_741 = lean_ctor_get(x_1, 3);
x_742 = lean_ctor_get(x_1, 4);
x_743 = lean_ctor_get(x_1, 5);
x_744 = lean_ctor_get(x_1, 6);
x_745 = lean_ctor_get(x_1, 7);
x_746 = lean_ctor_get(x_1, 8);
x_747 = lean_ctor_get(x_1, 9);
x_748 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_749 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_757 = !lean_is_exclusive(x_1);
if (x_757 == 0)
{
x_750 = x_1;
x_751 = x_757;
goto block_756;
}
else
{
lean_inc(x_747);
lean_inc(x_746);
lean_inc(x_745);
lean_inc(x_744);
lean_inc(x_743);
lean_inc(x_742);
lean_inc(x_741);
lean_inc(x_738);
lean_inc(x_730);
lean_inc(x_729);
lean_dec(x_1);
x_750 = lean_box(0);
x_751 = x_757;
goto block_756;
}
block_756:
{
lean_object* x_752; 
if (x_751 == 0)
{
x_752 = x_750;
goto block_754;
}
else
{
lean_object* x_755; 
x_755 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_755, 0, x_729);
lean_ctor_set(x_755, 1, x_730);
lean_ctor_set(x_755, 2, x_738);
lean_ctor_set(x_755, 3, x_741);
lean_ctor_set(x_755, 4, x_742);
lean_ctor_set(x_755, 5, x_743);
lean_ctor_set(x_755, 6, x_744);
lean_ctor_set(x_755, 7, x_745);
lean_ctor_set(x_755, 8, x_746);
lean_ctor_set(x_755, 9, x_747);
lean_ctor_set_uint8(x_755, sizeof(void*)*10 + 8, x_731);
lean_ctor_set_uint8(x_755, sizeof(void*)*10 + 9, x_732);
lean_ctor_set_uint8(x_755, sizeof(void*)*10 + 10, x_733);
lean_ctor_set_uint8(x_755, sizeof(void*)*10 + 11, x_734);
lean_ctor_set_uint8(x_755, sizeof(void*)*10 + 12, x_735);
lean_ctor_set_uint8(x_755, sizeof(void*)*10 + 13, x_736);
lean_ctor_set_uint8(x_755, sizeof(void*)*10 + 14, x_737);
lean_ctor_set_uint32(x_755, sizeof(void*)*10, x_739);
lean_ctor_set_uint32(x_755, sizeof(void*)*10 + 4, x_740);
lean_ctor_set_uint8(x_755, sizeof(void*)*10 + 16, x_748);
lean_ctor_set_uint8(x_755, sizeof(void*)*10 + 17, x_749);
x_752 = x_755;
goto block_754;
}
block_754:
{
lean_object* x_753; 
lean_ctor_set_uint8(x_752, sizeof(void*)*10 + 15, x_246);
x_753 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_753, 0, x_752);
return x_753;
}
}
}
}
else
{
lean_object* x_758; lean_object* x_759; uint8_t x_760; uint8_t x_761; uint8_t x_762; uint8_t x_763; uint8_t x_764; lean_object* x_765; uint32_t x_766; uint32_t x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; uint8_t x_774; lean_object* x_775; uint8_t x_776; uint8_t x_777; lean_object* x_778; uint8_t x_779; uint8_t x_785; 
lean_dec(x_3);
x_758 = lean_ctor_get(x_1, 0);
x_759 = lean_ctor_get(x_1, 1);
x_760 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_761 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_762 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_763 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_764 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_765 = lean_ctor_get(x_1, 2);
x_766 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_767 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_768 = lean_ctor_get(x_1, 3);
x_769 = lean_ctor_get(x_1, 4);
x_770 = lean_ctor_get(x_1, 5);
x_771 = lean_ctor_get(x_1, 6);
x_772 = lean_ctor_get(x_1, 7);
x_773 = lean_ctor_get(x_1, 8);
x_774 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_775 = lean_ctor_get(x_1, 9);
x_776 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_777 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_785 = !lean_is_exclusive(x_1);
if (x_785 == 0)
{
x_778 = x_1;
x_779 = x_785;
goto block_784;
}
else
{
lean_inc(x_775);
lean_inc(x_773);
lean_inc(x_772);
lean_inc(x_771);
lean_inc(x_770);
lean_inc(x_769);
lean_inc(x_768);
lean_inc(x_765);
lean_inc(x_759);
lean_inc(x_758);
lean_dec(x_1);
x_778 = lean_box(0);
x_779 = x_785;
goto block_784;
}
block_784:
{
lean_object* x_780; 
if (x_779 == 0)
{
x_780 = x_778;
goto block_782;
}
else
{
lean_object* x_783; 
x_783 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_783, 0, x_758);
lean_ctor_set(x_783, 1, x_759);
lean_ctor_set(x_783, 2, x_765);
lean_ctor_set(x_783, 3, x_768);
lean_ctor_set(x_783, 4, x_769);
lean_ctor_set(x_783, 5, x_770);
lean_ctor_set(x_783, 6, x_771);
lean_ctor_set(x_783, 7, x_772);
lean_ctor_set(x_783, 8, x_773);
lean_ctor_set(x_783, 9, x_775);
lean_ctor_set_uint8(x_783, sizeof(void*)*10 + 8, x_760);
lean_ctor_set_uint8(x_783, sizeof(void*)*10 + 9, x_761);
lean_ctor_set_uint8(x_783, sizeof(void*)*10 + 10, x_762);
lean_ctor_set_uint8(x_783, sizeof(void*)*10 + 11, x_763);
lean_ctor_set_uint8(x_783, sizeof(void*)*10 + 13, x_764);
lean_ctor_set_uint32(x_783, sizeof(void*)*10, x_766);
lean_ctor_set_uint32(x_783, sizeof(void*)*10 + 4, x_767);
lean_ctor_set_uint8(x_783, sizeof(void*)*10 + 15, x_774);
lean_ctor_set_uint8(x_783, sizeof(void*)*10 + 16, x_776);
lean_ctor_set_uint8(x_783, sizeof(void*)*10 + 17, x_777);
x_780 = x_783;
goto block_782;
}
block_782:
{
lean_object* x_781; 
lean_ctor_set_uint8(x_780, sizeof(void*)*10 + 12, x_244);
lean_ctor_set_uint8(x_780, sizeof(void*)*10 + 14, x_244);
x_781 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_781, 0, x_780);
return x_781;
}
}
}
}
else
{
lean_object* x_786; lean_object* x_787; uint8_t x_788; uint8_t x_789; uint8_t x_790; uint8_t x_791; uint8_t x_792; uint8_t x_793; lean_object* x_794; uint32_t x_795; uint32_t x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; uint8_t x_803; lean_object* x_804; uint8_t x_805; uint8_t x_806; lean_object* x_807; uint8_t x_808; uint8_t x_814; 
lean_dec(x_3);
x_786 = lean_ctor_get(x_1, 0);
x_787 = lean_ctor_get(x_1, 1);
x_788 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_789 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_790 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_791 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_792 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_793 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_794 = lean_ctor_get(x_1, 2);
x_795 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_796 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_797 = lean_ctor_get(x_1, 3);
x_798 = lean_ctor_get(x_1, 4);
x_799 = lean_ctor_get(x_1, 5);
x_800 = lean_ctor_get(x_1, 6);
x_801 = lean_ctor_get(x_1, 7);
x_802 = lean_ctor_get(x_1, 8);
x_803 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_804 = lean_ctor_get(x_1, 9);
x_805 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_806 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_814 = !lean_is_exclusive(x_1);
if (x_814 == 0)
{
x_807 = x_1;
x_808 = x_814;
goto block_813;
}
else
{
lean_inc(x_804);
lean_inc(x_802);
lean_inc(x_801);
lean_inc(x_800);
lean_inc(x_799);
lean_inc(x_798);
lean_inc(x_797);
lean_inc(x_794);
lean_inc(x_787);
lean_inc(x_786);
lean_dec(x_1);
x_807 = lean_box(0);
x_808 = x_814;
goto block_813;
}
block_813:
{
lean_object* x_809; 
if (x_808 == 0)
{
x_809 = x_807;
goto block_811;
}
else
{
lean_object* x_812; 
x_812 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_812, 0, x_786);
lean_ctor_set(x_812, 1, x_787);
lean_ctor_set(x_812, 2, x_794);
lean_ctor_set(x_812, 3, x_797);
lean_ctor_set(x_812, 4, x_798);
lean_ctor_set(x_812, 5, x_799);
lean_ctor_set(x_812, 6, x_800);
lean_ctor_set(x_812, 7, x_801);
lean_ctor_set(x_812, 8, x_802);
lean_ctor_set(x_812, 9, x_804);
lean_ctor_set_uint8(x_812, sizeof(void*)*10 + 8, x_788);
lean_ctor_set_uint8(x_812, sizeof(void*)*10 + 9, x_789);
lean_ctor_set_uint8(x_812, sizeof(void*)*10 + 10, x_790);
lean_ctor_set_uint8(x_812, sizeof(void*)*10 + 11, x_791);
lean_ctor_set_uint8(x_812, sizeof(void*)*10 + 12, x_792);
lean_ctor_set_uint8(x_812, sizeof(void*)*10 + 14, x_793);
lean_ctor_set_uint32(x_812, sizeof(void*)*10, x_795);
lean_ctor_set_uint32(x_812, sizeof(void*)*10 + 4, x_796);
lean_ctor_set_uint8(x_812, sizeof(void*)*10 + 15, x_803);
lean_ctor_set_uint8(x_812, sizeof(void*)*10 + 16, x_805);
lean_ctor_set_uint8(x_812, sizeof(void*)*10 + 17, x_806);
x_809 = x_812;
goto block_811;
}
block_811:
{
lean_object* x_810; 
lean_ctor_set_uint8(x_809, sizeof(void*)*10 + 13, x_242);
x_810 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_810, 0, x_809);
return x_810;
}
}
}
}
else
{
lean_object* x_815; lean_object* x_816; uint8_t x_817; uint8_t x_818; uint8_t x_819; uint8_t x_820; uint8_t x_821; uint8_t x_822; lean_object* x_823; uint32_t x_824; uint32_t x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; uint8_t x_832; lean_object* x_833; uint8_t x_834; uint8_t x_835; lean_object* x_836; uint8_t x_837; uint8_t x_843; 
lean_dec(x_3);
x_815 = lean_ctor_get(x_1, 0);
x_816 = lean_ctor_get(x_1, 1);
x_817 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_818 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_819 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_820 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_821 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_822 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_823 = lean_ctor_get(x_1, 2);
x_824 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_825 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_826 = lean_ctor_get(x_1, 3);
x_827 = lean_ctor_get(x_1, 4);
x_828 = lean_ctor_get(x_1, 5);
x_829 = lean_ctor_get(x_1, 6);
x_830 = lean_ctor_get(x_1, 7);
x_831 = lean_ctor_get(x_1, 8);
x_832 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_833 = lean_ctor_get(x_1, 9);
x_834 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_835 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_843 = !lean_is_exclusive(x_1);
if (x_843 == 0)
{
x_836 = x_1;
x_837 = x_843;
goto block_842;
}
else
{
lean_inc(x_833);
lean_inc(x_831);
lean_inc(x_830);
lean_inc(x_829);
lean_inc(x_828);
lean_inc(x_827);
lean_inc(x_826);
lean_inc(x_823);
lean_inc(x_816);
lean_inc(x_815);
lean_dec(x_1);
x_836 = lean_box(0);
x_837 = x_843;
goto block_842;
}
block_842:
{
lean_object* x_838; 
if (x_837 == 0)
{
x_838 = x_836;
goto block_840;
}
else
{
lean_object* x_841; 
x_841 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_841, 0, x_815);
lean_ctor_set(x_841, 1, x_816);
lean_ctor_set(x_841, 2, x_823);
lean_ctor_set(x_841, 3, x_826);
lean_ctor_set(x_841, 4, x_827);
lean_ctor_set(x_841, 5, x_828);
lean_ctor_set(x_841, 6, x_829);
lean_ctor_set(x_841, 7, x_830);
lean_ctor_set(x_841, 8, x_831);
lean_ctor_set(x_841, 9, x_833);
lean_ctor_set_uint8(x_841, sizeof(void*)*10 + 8, x_817);
lean_ctor_set_uint8(x_841, sizeof(void*)*10 + 9, x_818);
lean_ctor_set_uint8(x_841, sizeof(void*)*10 + 10, x_819);
lean_ctor_set_uint8(x_841, sizeof(void*)*10 + 11, x_820);
lean_ctor_set_uint8(x_841, sizeof(void*)*10 + 13, x_821);
lean_ctor_set_uint8(x_841, sizeof(void*)*10 + 14, x_822);
lean_ctor_set_uint32(x_841, sizeof(void*)*10, x_824);
lean_ctor_set_uint32(x_841, sizeof(void*)*10 + 4, x_825);
lean_ctor_set_uint8(x_841, sizeof(void*)*10 + 15, x_832);
lean_ctor_set_uint8(x_841, sizeof(void*)*10 + 16, x_834);
lean_ctor_set_uint8(x_841, sizeof(void*)*10 + 17, x_835);
x_838 = x_841;
goto block_840;
}
block_840:
{
lean_object* x_839; 
lean_ctor_set_uint8(x_838, sizeof(void*)*10 + 12, x_240);
x_839 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_839, 0, x_838);
return x_839;
}
}
}
}
else
{
lean_object* x_844; lean_object* x_845; uint8_t x_846; uint8_t x_847; uint8_t x_848; uint8_t x_849; uint8_t x_850; uint8_t x_851; uint8_t x_852; lean_object* x_853; uint32_t x_854; uint32_t x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; uint8_t x_862; lean_object* x_863; uint8_t x_864; uint8_t x_865; lean_object* x_866; uint8_t x_867; uint8_t x_875; 
lean_dec(x_3);
x_844 = lean_ctor_get(x_1, 0);
x_845 = lean_ctor_get(x_1, 1);
x_846 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_847 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_848 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_849 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_850 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_851 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_852 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_853 = lean_ctor_get(x_1, 2);
x_854 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_855 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_856 = lean_ctor_get(x_1, 3);
x_857 = lean_ctor_get(x_1, 4);
x_858 = lean_ctor_get(x_1, 5);
x_859 = lean_ctor_get(x_1, 6);
x_860 = lean_ctor_get(x_1, 7);
x_861 = lean_ctor_get(x_1, 8);
x_862 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_863 = lean_ctor_get(x_1, 9);
x_864 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_865 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_875 = !lean_is_exclusive(x_1);
if (x_875 == 0)
{
x_866 = x_1;
x_867 = x_875;
goto block_874;
}
else
{
lean_inc(x_863);
lean_inc(x_861);
lean_inc(x_860);
lean_inc(x_859);
lean_inc(x_858);
lean_inc(x_857);
lean_inc(x_856);
lean_inc(x_853);
lean_inc(x_845);
lean_inc(x_844);
lean_dec(x_1);
x_866 = lean_box(0);
x_867 = x_875;
goto block_874;
}
block_874:
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = l___private_Lean_Shell_0__Lean_verbose;
x_869 = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__1(x_844, x_868, x_236);
if (x_867 == 0)
{
lean_ctor_set(x_866, 0, x_869);
x_870 = x_866;
goto block_872;
}
else
{
lean_object* x_873; 
x_873 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_873, 0, x_869);
lean_ctor_set(x_873, 1, x_845);
lean_ctor_set(x_873, 2, x_853);
lean_ctor_set(x_873, 3, x_856);
lean_ctor_set(x_873, 4, x_857);
lean_ctor_set(x_873, 5, x_858);
lean_ctor_set(x_873, 6, x_859);
lean_ctor_set(x_873, 7, x_860);
lean_ctor_set(x_873, 8, x_861);
lean_ctor_set(x_873, 9, x_863);
lean_ctor_set_uint8(x_873, sizeof(void*)*10 + 8, x_846);
lean_ctor_set_uint8(x_873, sizeof(void*)*10 + 9, x_847);
lean_ctor_set_uint8(x_873, sizeof(void*)*10 + 10, x_848);
lean_ctor_set_uint8(x_873, sizeof(void*)*10 + 11, x_849);
lean_ctor_set_uint8(x_873, sizeof(void*)*10 + 12, x_850);
lean_ctor_set_uint8(x_873, sizeof(void*)*10 + 13, x_851);
lean_ctor_set_uint8(x_873, sizeof(void*)*10 + 14, x_852);
lean_ctor_set_uint32(x_873, sizeof(void*)*10, x_854);
lean_ctor_set_uint32(x_873, sizeof(void*)*10 + 4, x_855);
lean_ctor_set_uint8(x_873, sizeof(void*)*10 + 15, x_862);
lean_ctor_set_uint8(x_873, sizeof(void*)*10 + 16, x_864);
lean_ctor_set_uint8(x_873, sizeof(void*)*10 + 17, x_865);
x_870 = x_873;
goto block_872;
}
block_872:
{
lean_object* x_871; 
x_871 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_871, 0, x_870);
return x_871;
}
}
}
}
else
{
lean_object* x_876; lean_object* x_877; 
x_876 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__10));
x_877 = l___private_Lean_Shell_0__Lean_checkOptArg(x_876, x_3);
if (lean_obj_tag(x_877) == 0)
{
lean_object* x_878; lean_object* x_879; uint8_t x_880; uint8_t x_928; 
x_878 = lean_ctor_get(x_877, 0);
x_928 = !lean_is_exclusive(x_877);
if (x_928 == 0)
{
x_879 = x_877;
x_880 = x_928;
goto block_927;
}
else
{
lean_inc(x_878);
lean_dec(x_877);
x_879 = lean_box(0);
x_880 = x_928;
goto block_927;
}
block_927:
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_881 = lean_unsigned_to_nat(0u);
x_882 = lean_string_utf8_byte_size(x_878);
lean_inc(x_878);
x_883 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_883, 0, x_878);
lean_ctor_set(x_883, 1, x_881);
lean_ctor_set(x_883, 2, x_882);
x_884 = l_String_Slice_toNat_x3f(x_883);
lean_dec_ref(x_883);
if (lean_obj_tag(x_884) == 1)
{
lean_object* x_885; lean_object* x_886; uint8_t x_887; 
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
lean_dec_ref(x_884);
x_886 = lean_cstr_to_nat("4294967296");
x_887 = lean_nat_dec_lt(x_885, x_886);
if (x_887 == 0)
{
lean_object* x_888; lean_object* x_889; 
lean_dec(x_885);
lean_del_object(x_879);
lean_dec(x_878);
lean_dec_ref(x_1);
x_888 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__11));
x_889 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_888);
lean_dec_ref(x_889);
goto block_73;
}
else
{
lean_object* x_890; lean_object* x_891; uint8_t x_892; uint8_t x_893; uint8_t x_894; uint8_t x_895; uint8_t x_896; uint8_t x_897; uint8_t x_898; lean_object* x_899; uint32_t x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; uint8_t x_907; lean_object* x_908; uint8_t x_909; uint8_t x_910; lean_object* x_911; uint8_t x_912; uint8_t x_924; 
x_890 = lean_ctor_get(x_1, 0);
x_891 = lean_ctor_get(x_1, 1);
x_892 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_893 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_894 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_895 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_896 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_897 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_898 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_899 = lean_ctor_get(x_1, 2);
x_900 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_901 = lean_ctor_get(x_1, 3);
x_902 = lean_ctor_get(x_1, 4);
x_903 = lean_ctor_get(x_1, 5);
x_904 = lean_ctor_get(x_1, 6);
x_905 = lean_ctor_get(x_1, 7);
x_906 = lean_ctor_get(x_1, 8);
x_907 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_908 = lean_ctor_get(x_1, 9);
x_909 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_910 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_924 = !lean_is_exclusive(x_1);
if (x_924 == 0)
{
x_911 = x_1;
x_912 = x_924;
goto block_923;
}
else
{
lean_inc(x_908);
lean_inc(x_906);
lean_inc(x_905);
lean_inc(x_904);
lean_inc(x_903);
lean_inc(x_902);
lean_inc(x_901);
lean_inc(x_899);
lean_inc(x_891);
lean_inc(x_890);
lean_dec(x_1);
x_911 = lean_box(0);
x_912 = x_924;
goto block_923;
}
block_923:
{
uint32_t x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
x_913 = lean_uint32_of_nat(x_885);
lean_dec(x_885);
x_914 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__12));
x_915 = lean_string_append(x_914, x_878);
lean_dec(x_878);
x_916 = lean_array_push(x_891, x_915);
if (x_912 == 0)
{
lean_ctor_set(x_911, 1, x_916);
x_917 = x_911;
goto block_921;
}
else
{
lean_object* x_922; 
x_922 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_922, 0, x_890);
lean_ctor_set(x_922, 1, x_916);
lean_ctor_set(x_922, 2, x_899);
lean_ctor_set(x_922, 3, x_901);
lean_ctor_set(x_922, 4, x_902);
lean_ctor_set(x_922, 5, x_903);
lean_ctor_set(x_922, 6, x_904);
lean_ctor_set(x_922, 7, x_905);
lean_ctor_set(x_922, 8, x_906);
lean_ctor_set(x_922, 9, x_908);
lean_ctor_set_uint8(x_922, sizeof(void*)*10 + 8, x_892);
lean_ctor_set_uint8(x_922, sizeof(void*)*10 + 9, x_893);
lean_ctor_set_uint8(x_922, sizeof(void*)*10 + 10, x_894);
lean_ctor_set_uint8(x_922, sizeof(void*)*10 + 11, x_895);
lean_ctor_set_uint8(x_922, sizeof(void*)*10 + 12, x_896);
lean_ctor_set_uint8(x_922, sizeof(void*)*10 + 13, x_897);
lean_ctor_set_uint8(x_922, sizeof(void*)*10 + 14, x_898);
lean_ctor_set_uint32(x_922, sizeof(void*)*10 + 4, x_900);
lean_ctor_set_uint8(x_922, sizeof(void*)*10 + 15, x_907);
lean_ctor_set_uint8(x_922, sizeof(void*)*10 + 16, x_909);
lean_ctor_set_uint8(x_922, sizeof(void*)*10 + 17, x_910);
x_917 = x_922;
goto block_921;
}
block_921:
{
lean_object* x_918; 
lean_ctor_set_uint32(x_917, sizeof(void*)*10, x_913);
if (x_880 == 0)
{
lean_ctor_set(x_879, 0, x_917);
x_918 = x_879;
goto block_919;
}
else
{
lean_object* x_920; 
x_920 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_920, 0, x_917);
x_918 = x_920;
goto block_919;
}
block_919:
{
return x_918;
}
}
}
}
}
else
{
lean_object* x_925; lean_object* x_926; 
lean_dec(x_884);
lean_del_object(x_879);
lean_dec(x_878);
lean_dec_ref(x_1);
x_925 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__13));
x_926 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_925);
lean_dec_ref(x_926);
goto block_70;
}
}
}
else
{
lean_object* x_929; lean_object* x_933; lean_object* x_934; 
lean_dec_ref(x_1);
x_929 = lean_ctor_get(x_877, 0);
lean_inc(x_929);
lean_dec_ref(x_877);
x_933 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_934 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_933);
lean_dec_ref(x_934);
goto block_932;
block_932:
{
lean_object* x_930; lean_object* x_931; 
x_930 = lean_io_error_to_string(x_929);
x_931 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_930);
lean_dec_ref(x_931);
goto block_67;
}
}
}
}
else
{
lean_object* x_935; lean_object* x_936; 
x_935 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__14));
x_936 = l___private_Lean_Shell_0__Lean_checkOptArg(x_935, x_3);
if (lean_obj_tag(x_936) == 0)
{
lean_object* x_937; lean_object* x_938; uint8_t x_939; uint8_t x_985; 
x_937 = lean_ctor_get(x_936, 0);
x_985 = !lean_is_exclusive(x_936);
if (x_985 == 0)
{
x_938 = x_936;
x_939 = x_985;
goto block_984;
}
else
{
lean_inc(x_937);
lean_dec(x_936);
x_938 = lean_box(0);
x_939 = x_985;
goto block_984;
}
block_984:
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; 
x_940 = lean_unsigned_to_nat(0u);
x_941 = lean_string_utf8_byte_size(x_937);
lean_inc(x_937);
x_942 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_942, 0, x_937);
lean_ctor_set(x_942, 1, x_940);
lean_ctor_set(x_942, 2, x_941);
x_943 = l_String_Slice_toNat_x3f(x_942);
lean_dec_ref(x_942);
if (lean_obj_tag(x_943) == 1)
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; uint8_t x_947; uint8_t x_948; uint8_t x_949; uint8_t x_950; uint8_t x_951; uint8_t x_952; uint8_t x_953; lean_object* x_954; uint32_t x_955; uint32_t x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; uint8_t x_963; lean_object* x_964; uint8_t x_965; uint8_t x_966; lean_object* x_967; uint8_t x_968; uint8_t x_981; 
x_944 = lean_ctor_get(x_943, 0);
lean_inc(x_944);
lean_dec_ref(x_943);
x_945 = lean_ctor_get(x_1, 0);
x_946 = lean_ctor_get(x_1, 1);
x_947 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_948 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_949 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_950 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_951 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_952 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_953 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_954 = lean_ctor_get(x_1, 2);
x_955 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_956 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_957 = lean_ctor_get(x_1, 3);
x_958 = lean_ctor_get(x_1, 4);
x_959 = lean_ctor_get(x_1, 5);
x_960 = lean_ctor_get(x_1, 6);
x_961 = lean_ctor_get(x_1, 7);
x_962 = lean_ctor_get(x_1, 8);
x_963 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_964 = lean_ctor_get(x_1, 9);
x_965 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_966 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_981 = !lean_is_exclusive(x_1);
if (x_981 == 0)
{
x_967 = x_1;
x_968 = x_981;
goto block_980;
}
else
{
lean_inc(x_964);
lean_inc(x_962);
lean_inc(x_961);
lean_inc(x_960);
lean_inc(x_959);
lean_inc(x_958);
lean_inc(x_957);
lean_inc(x_954);
lean_inc(x_946);
lean_inc(x_945);
lean_dec(x_1);
x_967 = lean_box(0);
x_968 = x_981;
goto block_980;
}
block_980:
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
x_969 = l___private_Lean_Shell_0__Lean_timeout;
x_970 = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(x_945, x_969, x_944);
x_971 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__15));
x_972 = lean_string_append(x_971, x_937);
lean_dec(x_937);
x_973 = lean_array_push(x_946, x_972);
if (x_968 == 0)
{
lean_ctor_set(x_967, 1, x_973);
lean_ctor_set(x_967, 0, x_970);
x_974 = x_967;
goto block_978;
}
else
{
lean_object* x_979; 
x_979 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_979, 0, x_970);
lean_ctor_set(x_979, 1, x_973);
lean_ctor_set(x_979, 2, x_954);
lean_ctor_set(x_979, 3, x_957);
lean_ctor_set(x_979, 4, x_958);
lean_ctor_set(x_979, 5, x_959);
lean_ctor_set(x_979, 6, x_960);
lean_ctor_set(x_979, 7, x_961);
lean_ctor_set(x_979, 8, x_962);
lean_ctor_set(x_979, 9, x_964);
lean_ctor_set_uint8(x_979, sizeof(void*)*10 + 8, x_947);
lean_ctor_set_uint8(x_979, sizeof(void*)*10 + 9, x_948);
lean_ctor_set_uint8(x_979, sizeof(void*)*10 + 10, x_949);
lean_ctor_set_uint8(x_979, sizeof(void*)*10 + 11, x_950);
lean_ctor_set_uint8(x_979, sizeof(void*)*10 + 12, x_951);
lean_ctor_set_uint8(x_979, sizeof(void*)*10 + 13, x_952);
lean_ctor_set_uint8(x_979, sizeof(void*)*10 + 14, x_953);
lean_ctor_set_uint32(x_979, sizeof(void*)*10, x_955);
lean_ctor_set_uint32(x_979, sizeof(void*)*10 + 4, x_956);
lean_ctor_set_uint8(x_979, sizeof(void*)*10 + 15, x_963);
lean_ctor_set_uint8(x_979, sizeof(void*)*10 + 16, x_965);
lean_ctor_set_uint8(x_979, sizeof(void*)*10 + 17, x_966);
x_974 = x_979;
goto block_978;
}
block_978:
{
lean_object* x_975; 
if (x_939 == 0)
{
lean_ctor_set(x_938, 0, x_974);
x_975 = x_938;
goto block_976;
}
else
{
lean_object* x_977; 
x_977 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_977, 0, x_974);
x_975 = x_977;
goto block_976;
}
block_976:
{
return x_975;
}
}
}
}
else
{
lean_object* x_982; lean_object* x_983; 
lean_dec(x_943);
lean_del_object(x_938);
lean_dec(x_937);
lean_dec_ref(x_1);
x_982 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__16));
x_983 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_982);
lean_dec_ref(x_983);
goto block_158;
}
}
}
else
{
lean_object* x_986; lean_object* x_990; lean_object* x_991; 
lean_dec_ref(x_1);
x_986 = lean_ctor_get(x_936, 0);
lean_inc(x_986);
lean_dec_ref(x_936);
x_990 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_991 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_990);
lean_dec_ref(x_991);
goto block_989;
block_989:
{
lean_object* x_987; lean_object* x_988; 
x_987 = lean_io_error_to_string(x_986);
x_988 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_987);
lean_dec_ref(x_988);
goto block_164;
}
}
}
}
else
{
lean_object* x_992; lean_object* x_993; 
x_992 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__17));
x_993 = l___private_Lean_Shell_0__Lean_checkOptArg(x_992, x_3);
if (lean_obj_tag(x_993) == 0)
{
lean_object* x_994; lean_object* x_995; uint8_t x_996; uint8_t x_1042; 
x_994 = lean_ctor_get(x_993, 0);
x_1042 = !lean_is_exclusive(x_993);
if (x_1042 == 0)
{
x_995 = x_993;
x_996 = x_1042;
goto block_1041;
}
else
{
lean_inc(x_994);
lean_dec(x_993);
x_995 = lean_box(0);
x_996 = x_1042;
goto block_1041;
}
block_1041:
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_997 = lean_unsigned_to_nat(0u);
x_998 = lean_string_utf8_byte_size(x_994);
lean_inc(x_994);
x_999 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_999, 0, x_994);
lean_ctor_set(x_999, 1, x_997);
lean_ctor_set(x_999, 2, x_998);
x_1000 = l_String_Slice_toNat_x3f(x_999);
lean_dec_ref(x_999);
if (lean_obj_tag(x_1000) == 1)
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; uint8_t x_1004; uint8_t x_1005; uint8_t x_1006; uint8_t x_1007; uint8_t x_1008; uint8_t x_1009; uint8_t x_1010; lean_object* x_1011; uint32_t x_1012; uint32_t x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; uint8_t x_1020; lean_object* x_1021; uint8_t x_1022; uint8_t x_1023; lean_object* x_1024; uint8_t x_1025; uint8_t x_1038; 
x_1001 = lean_ctor_get(x_1000, 0);
lean_inc(x_1001);
lean_dec_ref(x_1000);
x_1002 = lean_ctor_get(x_1, 0);
x_1003 = lean_ctor_get(x_1, 1);
x_1004 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1005 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1006 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1007 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1008 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1009 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1010 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1011 = lean_ctor_get(x_1, 2);
x_1012 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1013 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1014 = lean_ctor_get(x_1, 3);
x_1015 = lean_ctor_get(x_1, 4);
x_1016 = lean_ctor_get(x_1, 5);
x_1017 = lean_ctor_get(x_1, 6);
x_1018 = lean_ctor_get(x_1, 7);
x_1019 = lean_ctor_get(x_1, 8);
x_1020 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1021 = lean_ctor_get(x_1, 9);
x_1022 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1023 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1038 = !lean_is_exclusive(x_1);
if (x_1038 == 0)
{
x_1024 = x_1;
x_1025 = x_1038;
goto block_1037;
}
else
{
lean_inc(x_1021);
lean_inc(x_1019);
lean_inc(x_1018);
lean_inc(x_1017);
lean_inc(x_1016);
lean_inc(x_1015);
lean_inc(x_1014);
lean_inc(x_1011);
lean_inc(x_1003);
lean_inc(x_1002);
lean_dec(x_1);
x_1024 = lean_box(0);
x_1025 = x_1038;
goto block_1037;
}
block_1037:
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
x_1026 = l___private_Lean_Shell_0__Lean_maxMemory;
x_1027 = l_Lean_Option_set___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__2(x_1002, x_1026, x_1001);
x_1028 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__18));
x_1029 = lean_string_append(x_1028, x_994);
lean_dec(x_994);
x_1030 = lean_array_push(x_1003, x_1029);
if (x_1025 == 0)
{
lean_ctor_set(x_1024, 1, x_1030);
lean_ctor_set(x_1024, 0, x_1027);
x_1031 = x_1024;
goto block_1035;
}
else
{
lean_object* x_1036; 
x_1036 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1036, 0, x_1027);
lean_ctor_set(x_1036, 1, x_1030);
lean_ctor_set(x_1036, 2, x_1011);
lean_ctor_set(x_1036, 3, x_1014);
lean_ctor_set(x_1036, 4, x_1015);
lean_ctor_set(x_1036, 5, x_1016);
lean_ctor_set(x_1036, 6, x_1017);
lean_ctor_set(x_1036, 7, x_1018);
lean_ctor_set(x_1036, 8, x_1019);
lean_ctor_set(x_1036, 9, x_1021);
lean_ctor_set_uint8(x_1036, sizeof(void*)*10 + 8, x_1004);
lean_ctor_set_uint8(x_1036, sizeof(void*)*10 + 9, x_1005);
lean_ctor_set_uint8(x_1036, sizeof(void*)*10 + 10, x_1006);
lean_ctor_set_uint8(x_1036, sizeof(void*)*10 + 11, x_1007);
lean_ctor_set_uint8(x_1036, sizeof(void*)*10 + 12, x_1008);
lean_ctor_set_uint8(x_1036, sizeof(void*)*10 + 13, x_1009);
lean_ctor_set_uint8(x_1036, sizeof(void*)*10 + 14, x_1010);
lean_ctor_set_uint32(x_1036, sizeof(void*)*10, x_1012);
lean_ctor_set_uint32(x_1036, sizeof(void*)*10 + 4, x_1013);
lean_ctor_set_uint8(x_1036, sizeof(void*)*10 + 15, x_1020);
lean_ctor_set_uint8(x_1036, sizeof(void*)*10 + 16, x_1022);
lean_ctor_set_uint8(x_1036, sizeof(void*)*10 + 17, x_1023);
x_1031 = x_1036;
goto block_1035;
}
block_1035:
{
lean_object* x_1032; 
if (x_996 == 0)
{
lean_ctor_set(x_995, 0, x_1031);
x_1032 = x_995;
goto block_1033;
}
else
{
lean_object* x_1034; 
x_1034 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1034, 0, x_1031);
x_1032 = x_1034;
goto block_1033;
}
block_1033:
{
return x_1032;
}
}
}
}
else
{
lean_object* x_1039; lean_object* x_1040; 
lean_dec(x_1000);
lean_del_object(x_995);
lean_dec(x_994);
lean_dec_ref(x_1);
x_1039 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__19));
x_1040 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1039);
lean_dec_ref(x_1040);
goto block_61;
}
}
}
else
{
lean_object* x_1043; lean_object* x_1047; lean_object* x_1048; 
lean_dec_ref(x_1);
x_1043 = lean_ctor_get(x_993, 0);
lean_inc(x_1043);
lean_dec_ref(x_993);
x_1047 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1048 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1047);
lean_dec_ref(x_1048);
goto block_1046;
block_1046:
{
lean_object* x_1044; lean_object* x_1045; 
x_1044 = lean_io_error_to_string(x_1043);
x_1045 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1044);
lean_dec_ref(x_1045);
goto block_58;
}
}
}
}
else
{
lean_object* x_1049; lean_object* x_1050; 
x_1049 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__20));
x_1050 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1049, x_3);
if (lean_obj_tag(x_1050) == 0)
{
lean_object* x_1051; lean_object* x_1052; uint8_t x_1053; uint8_t x_1091; 
x_1051 = lean_ctor_get(x_1050, 0);
x_1091 = !lean_is_exclusive(x_1050);
if (x_1091 == 0)
{
x_1052 = x_1050;
x_1053 = x_1091;
goto block_1090;
}
else
{
lean_inc(x_1051);
lean_dec(x_1050);
x_1052 = lean_box(0);
x_1053 = x_1091;
goto block_1090;
}
block_1090:
{
lean_object* x_1054; lean_object* x_1055; uint8_t x_1056; uint8_t x_1057; uint8_t x_1058; uint8_t x_1059; uint8_t x_1060; uint8_t x_1061; uint8_t x_1062; lean_object* x_1063; uint32_t x_1064; uint32_t x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; uint8_t x_1071; lean_object* x_1072; uint8_t x_1073; uint8_t x_1074; lean_object* x_1075; uint8_t x_1076; uint8_t x_1088; 
x_1054 = lean_ctor_get(x_1, 0);
x_1055 = lean_ctor_get(x_1, 1);
x_1056 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1057 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1058 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1059 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1060 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1061 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1062 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1063 = lean_ctor_get(x_1, 2);
x_1064 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1065 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1066 = lean_ctor_get(x_1, 4);
x_1067 = lean_ctor_get(x_1, 5);
x_1068 = lean_ctor_get(x_1, 6);
x_1069 = lean_ctor_get(x_1, 7);
x_1070 = lean_ctor_get(x_1, 8);
x_1071 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1072 = lean_ctor_get(x_1, 9);
x_1073 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1074 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1088 = !lean_is_exclusive(x_1);
if (x_1088 == 0)
{
lean_object* x_1089; 
x_1089 = lean_ctor_get(x_1, 3);
lean_dec(x_1089);
x_1075 = x_1;
x_1076 = x_1088;
goto block_1087;
}
else
{
lean_inc(x_1072);
lean_inc(x_1070);
lean_inc(x_1069);
lean_inc(x_1068);
lean_inc(x_1067);
lean_inc(x_1066);
lean_inc(x_1063);
lean_inc(x_1055);
lean_inc(x_1054);
lean_dec(x_1);
x_1075 = lean_box(0);
x_1076 = x_1088;
goto block_1087;
}
block_1087:
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
x_1077 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__21));
x_1078 = lean_string_append(x_1077, x_1051);
x_1079 = lean_array_push(x_1055, x_1078);
x_1080 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1080, 0, x_1051);
if (x_1076 == 0)
{
lean_ctor_set(x_1075, 3, x_1080);
lean_ctor_set(x_1075, 1, x_1079);
x_1081 = x_1075;
goto block_1085;
}
else
{
lean_object* x_1086; 
x_1086 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1086, 0, x_1054);
lean_ctor_set(x_1086, 1, x_1079);
lean_ctor_set(x_1086, 2, x_1063);
lean_ctor_set(x_1086, 3, x_1080);
lean_ctor_set(x_1086, 4, x_1066);
lean_ctor_set(x_1086, 5, x_1067);
lean_ctor_set(x_1086, 6, x_1068);
lean_ctor_set(x_1086, 7, x_1069);
lean_ctor_set(x_1086, 8, x_1070);
lean_ctor_set(x_1086, 9, x_1072);
lean_ctor_set_uint8(x_1086, sizeof(void*)*10 + 8, x_1056);
lean_ctor_set_uint8(x_1086, sizeof(void*)*10 + 9, x_1057);
lean_ctor_set_uint8(x_1086, sizeof(void*)*10 + 10, x_1058);
lean_ctor_set_uint8(x_1086, sizeof(void*)*10 + 11, x_1059);
lean_ctor_set_uint8(x_1086, sizeof(void*)*10 + 12, x_1060);
lean_ctor_set_uint8(x_1086, sizeof(void*)*10 + 13, x_1061);
lean_ctor_set_uint8(x_1086, sizeof(void*)*10 + 14, x_1062);
lean_ctor_set_uint32(x_1086, sizeof(void*)*10, x_1064);
lean_ctor_set_uint32(x_1086, sizeof(void*)*10 + 4, x_1065);
lean_ctor_set_uint8(x_1086, sizeof(void*)*10 + 15, x_1071);
lean_ctor_set_uint8(x_1086, sizeof(void*)*10 + 16, x_1073);
lean_ctor_set_uint8(x_1086, sizeof(void*)*10 + 17, x_1074);
x_1081 = x_1086;
goto block_1085;
}
block_1085:
{
lean_object* x_1082; 
if (x_1053 == 0)
{
lean_ctor_set(x_1052, 0, x_1081);
x_1082 = x_1052;
goto block_1083;
}
else
{
lean_object* x_1084; 
x_1084 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1084, 0, x_1081);
x_1082 = x_1084;
goto block_1083;
}
block_1083:
{
return x_1082;
}
}
}
}
}
else
{
lean_object* x_1092; lean_object* x_1096; lean_object* x_1097; 
lean_dec_ref(x_1);
x_1092 = lean_ctor_get(x_1050, 0);
lean_inc(x_1092);
lean_dec_ref(x_1050);
x_1096 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1097 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1096);
lean_dec_ref(x_1097);
goto block_1095;
block_1095:
{
lean_object* x_1093; lean_object* x_1094; 
x_1093 = lean_io_error_to_string(x_1092);
x_1094 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1093);
lean_dec_ref(x_1094);
goto block_170;
}
}
}
}
else
{
lean_object* x_1098; lean_object* x_1099; 
x_1098 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__22));
x_1099 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1098, x_3);
if (lean_obj_tag(x_1099) == 0)
{
lean_object* x_1100; lean_object* x_1101; uint8_t x_1102; uint8_t x_1137; 
x_1100 = lean_ctor_get(x_1099, 0);
x_1137 = !lean_is_exclusive(x_1099);
if (x_1137 == 0)
{
x_1101 = x_1099;
x_1102 = x_1137;
goto block_1136;
}
else
{
lean_inc(x_1100);
lean_dec(x_1099);
x_1101 = lean_box(0);
x_1102 = x_1137;
goto block_1136;
}
block_1136:
{
lean_object* x_1103; lean_object* x_1104; uint8_t x_1105; uint8_t x_1106; uint8_t x_1107; uint8_t x_1108; uint8_t x_1109; uint8_t x_1110; uint8_t x_1111; lean_object* x_1112; uint32_t x_1113; uint32_t x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; uint8_t x_1120; lean_object* x_1121; uint8_t x_1122; uint8_t x_1123; lean_object* x_1124; uint8_t x_1125; uint8_t x_1134; 
x_1103 = lean_ctor_get(x_1, 0);
x_1104 = lean_ctor_get(x_1, 1);
x_1105 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1106 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1107 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1108 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1109 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1110 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1111 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1112 = lean_ctor_get(x_1, 2);
x_1113 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1114 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1115 = lean_ctor_get(x_1, 3);
x_1116 = lean_ctor_get(x_1, 4);
x_1117 = lean_ctor_get(x_1, 5);
x_1118 = lean_ctor_get(x_1, 7);
x_1119 = lean_ctor_get(x_1, 8);
x_1120 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1121 = lean_ctor_get(x_1, 9);
x_1122 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1123 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1134 = !lean_is_exclusive(x_1);
if (x_1134 == 0)
{
lean_object* x_1135; 
x_1135 = lean_ctor_get(x_1, 6);
lean_dec(x_1135);
x_1124 = x_1;
x_1125 = x_1134;
goto block_1133;
}
else
{
lean_inc(x_1121);
lean_inc(x_1119);
lean_inc(x_1118);
lean_inc(x_1117);
lean_inc(x_1116);
lean_inc(x_1115);
lean_inc(x_1112);
lean_inc(x_1104);
lean_inc(x_1103);
lean_dec(x_1);
x_1124 = lean_box(0);
x_1125 = x_1134;
goto block_1133;
}
block_1133:
{
lean_object* x_1126; lean_object* x_1127; 
x_1126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1126, 0, x_1100);
if (x_1125 == 0)
{
lean_ctor_set(x_1124, 6, x_1126);
x_1127 = x_1124;
goto block_1131;
}
else
{
lean_object* x_1132; 
x_1132 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1132, 0, x_1103);
lean_ctor_set(x_1132, 1, x_1104);
lean_ctor_set(x_1132, 2, x_1112);
lean_ctor_set(x_1132, 3, x_1115);
lean_ctor_set(x_1132, 4, x_1116);
lean_ctor_set(x_1132, 5, x_1117);
lean_ctor_set(x_1132, 6, x_1126);
lean_ctor_set(x_1132, 7, x_1118);
lean_ctor_set(x_1132, 8, x_1119);
lean_ctor_set(x_1132, 9, x_1121);
lean_ctor_set_uint8(x_1132, sizeof(void*)*10 + 8, x_1105);
lean_ctor_set_uint8(x_1132, sizeof(void*)*10 + 9, x_1106);
lean_ctor_set_uint8(x_1132, sizeof(void*)*10 + 10, x_1107);
lean_ctor_set_uint8(x_1132, sizeof(void*)*10 + 11, x_1108);
lean_ctor_set_uint8(x_1132, sizeof(void*)*10 + 12, x_1109);
lean_ctor_set_uint8(x_1132, sizeof(void*)*10 + 13, x_1110);
lean_ctor_set_uint8(x_1132, sizeof(void*)*10 + 14, x_1111);
lean_ctor_set_uint32(x_1132, sizeof(void*)*10, x_1113);
lean_ctor_set_uint32(x_1132, sizeof(void*)*10 + 4, x_1114);
lean_ctor_set_uint8(x_1132, sizeof(void*)*10 + 15, x_1120);
lean_ctor_set_uint8(x_1132, sizeof(void*)*10 + 16, x_1122);
lean_ctor_set_uint8(x_1132, sizeof(void*)*10 + 17, x_1123);
x_1127 = x_1132;
goto block_1131;
}
block_1131:
{
lean_object* x_1128; 
if (x_1102 == 0)
{
lean_ctor_set(x_1101, 0, x_1127);
x_1128 = x_1101;
goto block_1129;
}
else
{
lean_object* x_1130; 
x_1130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1130, 0, x_1127);
x_1128 = x_1130;
goto block_1129;
}
block_1129:
{
return x_1128;
}
}
}
}
}
else
{
lean_object* x_1138; lean_object* x_1142; lean_object* x_1143; 
lean_dec_ref(x_1);
x_1138 = lean_ctor_get(x_1099, 0);
lean_inc(x_1138);
lean_dec_ref(x_1099);
x_1142 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1143 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1142);
lean_dec_ref(x_1143);
goto block_1141;
block_1141:
{
lean_object* x_1139; lean_object* x_1140; 
x_1139 = lean_io_error_to_string(x_1138);
x_1140 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1139);
lean_dec_ref(x_1140);
goto block_52;
}
}
}
}
else
{
lean_object* x_1144; lean_object* x_1145; 
x_1144 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__23));
x_1145 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1144, x_3);
if (lean_obj_tag(x_1145) == 0)
{
lean_object* x_1146; lean_object* x_1147; uint8_t x_1148; uint8_t x_1183; 
x_1146 = lean_ctor_get(x_1145, 0);
x_1183 = !lean_is_exclusive(x_1145);
if (x_1183 == 0)
{
x_1147 = x_1145;
x_1148 = x_1183;
goto block_1182;
}
else
{
lean_inc(x_1146);
lean_dec(x_1145);
x_1147 = lean_box(0);
x_1148 = x_1183;
goto block_1182;
}
block_1182:
{
lean_object* x_1149; lean_object* x_1150; uint8_t x_1151; uint8_t x_1152; uint8_t x_1153; uint8_t x_1154; uint8_t x_1155; uint8_t x_1156; uint8_t x_1157; lean_object* x_1158; uint32_t x_1159; uint32_t x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; uint8_t x_1166; lean_object* x_1167; uint8_t x_1168; uint8_t x_1169; lean_object* x_1170; uint8_t x_1171; uint8_t x_1180; 
x_1149 = lean_ctor_get(x_1, 0);
x_1150 = lean_ctor_get(x_1, 1);
x_1151 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1152 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1153 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1154 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1155 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1156 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1157 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1158 = lean_ctor_get(x_1, 2);
x_1159 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1160 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1161 = lean_ctor_get(x_1, 3);
x_1162 = lean_ctor_get(x_1, 4);
x_1163 = lean_ctor_get(x_1, 6);
x_1164 = lean_ctor_get(x_1, 7);
x_1165 = lean_ctor_get(x_1, 8);
x_1166 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1167 = lean_ctor_get(x_1, 9);
x_1168 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1169 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1180 = !lean_is_exclusive(x_1);
if (x_1180 == 0)
{
lean_object* x_1181; 
x_1181 = lean_ctor_get(x_1, 5);
lean_dec(x_1181);
x_1170 = x_1;
x_1171 = x_1180;
goto block_1179;
}
else
{
lean_inc(x_1167);
lean_inc(x_1165);
lean_inc(x_1164);
lean_inc(x_1163);
lean_inc(x_1162);
lean_inc(x_1161);
lean_inc(x_1158);
lean_inc(x_1150);
lean_inc(x_1149);
lean_dec(x_1);
x_1170 = lean_box(0);
x_1171 = x_1180;
goto block_1179;
}
block_1179:
{
lean_object* x_1172; lean_object* x_1173; 
x_1172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1172, 0, x_1146);
if (x_1171 == 0)
{
lean_ctor_set(x_1170, 5, x_1172);
x_1173 = x_1170;
goto block_1177;
}
else
{
lean_object* x_1178; 
x_1178 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1178, 0, x_1149);
lean_ctor_set(x_1178, 1, x_1150);
lean_ctor_set(x_1178, 2, x_1158);
lean_ctor_set(x_1178, 3, x_1161);
lean_ctor_set(x_1178, 4, x_1162);
lean_ctor_set(x_1178, 5, x_1172);
lean_ctor_set(x_1178, 6, x_1163);
lean_ctor_set(x_1178, 7, x_1164);
lean_ctor_set(x_1178, 8, x_1165);
lean_ctor_set(x_1178, 9, x_1167);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 8, x_1151);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 9, x_1152);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 10, x_1153);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 11, x_1154);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 12, x_1155);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 13, x_1156);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 14, x_1157);
lean_ctor_set_uint32(x_1178, sizeof(void*)*10, x_1159);
lean_ctor_set_uint32(x_1178, sizeof(void*)*10 + 4, x_1160);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 15, x_1166);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 16, x_1168);
lean_ctor_set_uint8(x_1178, sizeof(void*)*10 + 17, x_1169);
x_1173 = x_1178;
goto block_1177;
}
block_1177:
{
lean_object* x_1174; 
if (x_1148 == 0)
{
lean_ctor_set(x_1147, 0, x_1173);
x_1174 = x_1147;
goto block_1175;
}
else
{
lean_object* x_1176; 
x_1176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1176, 0, x_1173);
x_1174 = x_1176;
goto block_1175;
}
block_1175:
{
return x_1174;
}
}
}
}
}
else
{
lean_object* x_1184; lean_object* x_1188; lean_object* x_1189; 
lean_dec_ref(x_1);
x_1184 = lean_ctor_get(x_1145, 0);
lean_inc(x_1184);
lean_dec_ref(x_1145);
x_1188 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1189 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1188);
lean_dec_ref(x_1189);
goto block_1187;
block_1187:
{
lean_object* x_1185; lean_object* x_1186; 
x_1185 = lean_io_error_to_string(x_1184);
x_1186 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1185);
lean_dec_ref(x_1186);
goto block_176;
}
}
}
}
else
{
lean_object* x_1190; lean_object* x_1191; uint8_t x_1192; uint8_t x_1193; uint8_t x_1194; uint8_t x_1195; uint8_t x_1196; uint8_t x_1197; uint8_t x_1198; lean_object* x_1199; uint32_t x_1200; uint32_t x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; uint8_t x_1208; lean_object* x_1209; uint8_t x_1210; lean_object* x_1211; uint8_t x_1212; uint8_t x_1218; 
lean_dec(x_3);
x_1190 = lean_ctor_get(x_1, 0);
x_1191 = lean_ctor_get(x_1, 1);
x_1192 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1193 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1194 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1195 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1196 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1197 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1198 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1199 = lean_ctor_get(x_1, 2);
x_1200 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1201 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1202 = lean_ctor_get(x_1, 3);
x_1203 = lean_ctor_get(x_1, 4);
x_1204 = lean_ctor_get(x_1, 5);
x_1205 = lean_ctor_get(x_1, 6);
x_1206 = lean_ctor_get(x_1, 7);
x_1207 = lean_ctor_get(x_1, 8);
x_1208 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1209 = lean_ctor_get(x_1, 9);
x_1210 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1218 = !lean_is_exclusive(x_1);
if (x_1218 == 0)
{
x_1211 = x_1;
x_1212 = x_1218;
goto block_1217;
}
else
{
lean_inc(x_1209);
lean_inc(x_1207);
lean_inc(x_1206);
lean_inc(x_1205);
lean_inc(x_1204);
lean_inc(x_1203);
lean_inc(x_1202);
lean_inc(x_1199);
lean_inc(x_1191);
lean_inc(x_1190);
lean_dec(x_1);
x_1211 = lean_box(0);
x_1212 = x_1218;
goto block_1217;
}
block_1217:
{
lean_object* x_1213; 
if (x_1212 == 0)
{
x_1213 = x_1211;
goto block_1215;
}
else
{
lean_object* x_1216; 
x_1216 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1216, 0, x_1190);
lean_ctor_set(x_1216, 1, x_1191);
lean_ctor_set(x_1216, 2, x_1199);
lean_ctor_set(x_1216, 3, x_1202);
lean_ctor_set(x_1216, 4, x_1203);
lean_ctor_set(x_1216, 5, x_1204);
lean_ctor_set(x_1216, 6, x_1205);
lean_ctor_set(x_1216, 7, x_1206);
lean_ctor_set(x_1216, 8, x_1207);
lean_ctor_set(x_1216, 9, x_1209);
lean_ctor_set_uint8(x_1216, sizeof(void*)*10 + 8, x_1192);
lean_ctor_set_uint8(x_1216, sizeof(void*)*10 + 9, x_1193);
lean_ctor_set_uint8(x_1216, sizeof(void*)*10 + 10, x_1194);
lean_ctor_set_uint8(x_1216, sizeof(void*)*10 + 11, x_1195);
lean_ctor_set_uint8(x_1216, sizeof(void*)*10 + 12, x_1196);
lean_ctor_set_uint8(x_1216, sizeof(void*)*10 + 13, x_1197);
lean_ctor_set_uint8(x_1216, sizeof(void*)*10 + 14, x_1198);
lean_ctor_set_uint32(x_1216, sizeof(void*)*10, x_1200);
lean_ctor_set_uint32(x_1216, sizeof(void*)*10 + 4, x_1201);
lean_ctor_set_uint8(x_1216, sizeof(void*)*10 + 15, x_1208);
lean_ctor_set_uint8(x_1216, sizeof(void*)*10 + 16, x_1210);
x_1213 = x_1216;
goto block_1215;
}
block_1215:
{
lean_object* x_1214; 
lean_ctor_set_uint8(x_1213, sizeof(void*)*10 + 17, x_224);
x_1214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1214, 0, x_1213);
return x_1214;
}
}
}
}
else
{
lean_object* x_1219; lean_object* x_1220; uint8_t x_1221; uint8_t x_1222; uint8_t x_1223; uint8_t x_1224; uint8_t x_1225; uint8_t x_1226; lean_object* x_1227; uint32_t x_1228; uint32_t x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; uint8_t x_1236; lean_object* x_1237; uint8_t x_1238; uint8_t x_1239; lean_object* x_1240; uint8_t x_1241; uint8_t x_1247; 
lean_dec(x_3);
x_1219 = lean_ctor_get(x_1, 0);
x_1220 = lean_ctor_get(x_1, 1);
x_1221 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1222 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1223 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1224 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1225 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1226 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1227 = lean_ctor_get(x_1, 2);
x_1228 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1229 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1230 = lean_ctor_get(x_1, 3);
x_1231 = lean_ctor_get(x_1, 4);
x_1232 = lean_ctor_get(x_1, 5);
x_1233 = lean_ctor_get(x_1, 6);
x_1234 = lean_ctor_get(x_1, 7);
x_1235 = lean_ctor_get(x_1, 8);
x_1236 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1237 = lean_ctor_get(x_1, 9);
x_1238 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1239 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1247 = !lean_is_exclusive(x_1);
if (x_1247 == 0)
{
x_1240 = x_1;
x_1241 = x_1247;
goto block_1246;
}
else
{
lean_inc(x_1237);
lean_inc(x_1235);
lean_inc(x_1234);
lean_inc(x_1233);
lean_inc(x_1232);
lean_inc(x_1231);
lean_inc(x_1230);
lean_inc(x_1227);
lean_inc(x_1220);
lean_inc(x_1219);
lean_dec(x_1);
x_1240 = lean_box(0);
x_1241 = x_1247;
goto block_1246;
}
block_1246:
{
lean_object* x_1242; 
if (x_1241 == 0)
{
x_1242 = x_1240;
goto block_1244;
}
else
{
lean_object* x_1245; 
x_1245 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1245, 0, x_1219);
lean_ctor_set(x_1245, 1, x_1220);
lean_ctor_set(x_1245, 2, x_1227);
lean_ctor_set(x_1245, 3, x_1230);
lean_ctor_set(x_1245, 4, x_1231);
lean_ctor_set(x_1245, 5, x_1232);
lean_ctor_set(x_1245, 6, x_1233);
lean_ctor_set(x_1245, 7, x_1234);
lean_ctor_set(x_1245, 8, x_1235);
lean_ctor_set(x_1245, 9, x_1237);
lean_ctor_set_uint8(x_1245, sizeof(void*)*10 + 8, x_1221);
lean_ctor_set_uint8(x_1245, sizeof(void*)*10 + 9, x_1222);
lean_ctor_set_uint8(x_1245, sizeof(void*)*10 + 10, x_1223);
lean_ctor_set_uint8(x_1245, sizeof(void*)*10 + 12, x_1224);
lean_ctor_set_uint8(x_1245, sizeof(void*)*10 + 13, x_1225);
lean_ctor_set_uint8(x_1245, sizeof(void*)*10 + 14, x_1226);
lean_ctor_set_uint32(x_1245, sizeof(void*)*10, x_1228);
lean_ctor_set_uint32(x_1245, sizeof(void*)*10 + 4, x_1229);
lean_ctor_set_uint8(x_1245, sizeof(void*)*10 + 15, x_1236);
lean_ctor_set_uint8(x_1245, sizeof(void*)*10 + 16, x_1238);
lean_ctor_set_uint8(x_1245, sizeof(void*)*10 + 17, x_1239);
x_1242 = x_1245;
goto block_1244;
}
block_1244:
{
lean_object* x_1243; 
lean_ctor_set_uint8(x_1242, sizeof(void*)*10 + 11, x_222);
x_1243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1243, 0, x_1242);
return x_1243;
}
}
}
}
else
{
lean_object* x_1248; lean_object* x_1249; 
x_1248 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__24));
x_1249 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1248, x_3);
if (lean_obj_tag(x_1249) == 0)
{
lean_object* x_1250; lean_object* x_1251; uint8_t x_1252; uint8_t x_1308; 
x_1250 = lean_ctor_get(x_1249, 0);
x_1308 = !lean_is_exclusive(x_1249);
if (x_1308 == 0)
{
x_1251 = x_1249;
x_1252 = x_1308;
goto block_1307;
}
else
{
lean_inc(x_1250);
lean_dec(x_1249);
x_1251 = lean_box(0);
x_1252 = x_1308;
goto block_1307;
}
block_1307:
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
x_1253 = lean_unsigned_to_nat(0u);
x_1254 = lean_string_utf8_byte_size(x_1250);
lean_inc(x_1250);
x_1255 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1255, 0, x_1250);
lean_ctor_set(x_1255, 1, x_1253);
lean_ctor_set(x_1255, 2, x_1254);
x_1256 = l_String_Slice_toNat_x3f(x_1255);
lean_dec_ref(x_1255);
if (lean_obj_tag(x_1256) == 1)
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; uint8_t x_1265; 
x_1257 = lean_ctor_get(x_1256, 0);
lean_inc(x_1257);
lean_dec_ref(x_1256);
x_1258 = lean_unsigned_to_nat(4u);
x_1259 = lean_unsigned_to_nat(2u);
x_1260 = lean_nat_shiftr(x_1257, x_1259);
lean_dec(x_1257);
x_1261 = lean_nat_mul(x_1260, x_1258);
lean_dec(x_1260);
x_1262 = lean_unsigned_to_nat(1024u);
x_1263 = lean_nat_mul(x_1261, x_1262);
lean_dec(x_1261);
x_1264 = lean_obj_once(&l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25, &l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25_once, _init_l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__25);
x_1265 = lean_nat_dec_lt(x_1263, x_1264);
if (x_1265 == 0)
{
lean_object* x_1266; lean_object* x_1267; 
lean_dec(x_1263);
lean_del_object(x_1251);
lean_dec(x_1250);
lean_dec_ref(x_1);
x_1266 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__26));
x_1267 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1266);
lean_dec_ref(x_1267);
goto block_46;
}
else
{
size_t x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; uint8_t x_1272; uint8_t x_1273; uint8_t x_1274; uint8_t x_1275; uint8_t x_1276; uint8_t x_1277; uint8_t x_1278; lean_object* x_1279; uint32_t x_1280; uint32_t x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; uint8_t x_1288; lean_object* x_1289; uint8_t x_1290; uint8_t x_1291; lean_object* x_1292; uint8_t x_1293; uint8_t x_1304; 
x_1268 = lean_usize_of_nat(x_1263);
lean_dec(x_1263);
x_1269 = lean_internal_set_thread_stack_size(x_1268);
x_1270 = lean_ctor_get(x_1, 0);
x_1271 = lean_ctor_get(x_1, 1);
x_1272 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1273 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1274 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1275 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1276 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1277 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1278 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1279 = lean_ctor_get(x_1, 2);
x_1280 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1281 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1282 = lean_ctor_get(x_1, 3);
x_1283 = lean_ctor_get(x_1, 4);
x_1284 = lean_ctor_get(x_1, 5);
x_1285 = lean_ctor_get(x_1, 6);
x_1286 = lean_ctor_get(x_1, 7);
x_1287 = lean_ctor_get(x_1, 8);
x_1288 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1289 = lean_ctor_get(x_1, 9);
x_1290 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1291 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1304 = !lean_is_exclusive(x_1);
if (x_1304 == 0)
{
x_1292 = x_1;
x_1293 = x_1304;
goto block_1303;
}
else
{
lean_inc(x_1289);
lean_inc(x_1287);
lean_inc(x_1286);
lean_inc(x_1285);
lean_inc(x_1284);
lean_inc(x_1283);
lean_inc(x_1282);
lean_inc(x_1279);
lean_inc(x_1271);
lean_inc(x_1270);
lean_dec(x_1);
x_1292 = lean_box(0);
x_1293 = x_1304;
goto block_1303;
}
block_1303:
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; 
x_1294 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__27));
x_1295 = lean_string_append(x_1294, x_1250);
lean_dec(x_1250);
x_1296 = lean_array_push(x_1271, x_1295);
if (x_1293 == 0)
{
lean_ctor_set(x_1292, 1, x_1296);
x_1297 = x_1292;
goto block_1301;
}
else
{
lean_object* x_1302; 
x_1302 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1302, 0, x_1270);
lean_ctor_set(x_1302, 1, x_1296);
lean_ctor_set(x_1302, 2, x_1279);
lean_ctor_set(x_1302, 3, x_1282);
lean_ctor_set(x_1302, 4, x_1283);
lean_ctor_set(x_1302, 5, x_1284);
lean_ctor_set(x_1302, 6, x_1285);
lean_ctor_set(x_1302, 7, x_1286);
lean_ctor_set(x_1302, 8, x_1287);
lean_ctor_set(x_1302, 9, x_1289);
lean_ctor_set_uint8(x_1302, sizeof(void*)*10 + 8, x_1272);
lean_ctor_set_uint8(x_1302, sizeof(void*)*10 + 9, x_1273);
lean_ctor_set_uint8(x_1302, sizeof(void*)*10 + 10, x_1274);
lean_ctor_set_uint8(x_1302, sizeof(void*)*10 + 11, x_1275);
lean_ctor_set_uint8(x_1302, sizeof(void*)*10 + 12, x_1276);
lean_ctor_set_uint8(x_1302, sizeof(void*)*10 + 13, x_1277);
lean_ctor_set_uint8(x_1302, sizeof(void*)*10 + 14, x_1278);
lean_ctor_set_uint32(x_1302, sizeof(void*)*10, x_1280);
lean_ctor_set_uint32(x_1302, sizeof(void*)*10 + 4, x_1281);
lean_ctor_set_uint8(x_1302, sizeof(void*)*10 + 15, x_1288);
lean_ctor_set_uint8(x_1302, sizeof(void*)*10 + 16, x_1290);
lean_ctor_set_uint8(x_1302, sizeof(void*)*10 + 17, x_1291);
x_1297 = x_1302;
goto block_1301;
}
block_1301:
{
lean_object* x_1298; 
if (x_1252 == 0)
{
lean_ctor_set(x_1251, 0, x_1297);
x_1298 = x_1251;
goto block_1299;
}
else
{
lean_object* x_1300; 
x_1300 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1300, 0, x_1297);
x_1298 = x_1300;
goto block_1299;
}
block_1299:
{
return x_1298;
}
}
}
}
}
else
{
lean_object* x_1305; lean_object* x_1306; 
lean_dec(x_1256);
lean_del_object(x_1251);
lean_dec(x_1250);
lean_dec_ref(x_1);
x_1305 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__28));
x_1306 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1305);
lean_dec_ref(x_1306);
goto block_43;
}
}
}
else
{
lean_object* x_1309; lean_object* x_1313; lean_object* x_1314; 
lean_dec_ref(x_1);
x_1309 = lean_ctor_get(x_1249, 0);
lean_inc(x_1309);
lean_dec_ref(x_1249);
x_1313 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1314 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1313);
lean_dec_ref(x_1314);
goto block_1312;
block_1312:
{
lean_object* x_1310; lean_object* x_1311; 
x_1310 = lean_io_error_to_string(x_1309);
x_1311 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1310);
lean_dec_ref(x_1311);
goto block_40;
}
}
}
}
else
{
lean_object* x_1315; lean_object* x_1316; 
x_1315 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__29));
x_1316 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1315, x_3);
if (lean_obj_tag(x_1316) == 0)
{
lean_object* x_1317; lean_object* x_1318; uint8_t x_1319; uint8_t x_1354; 
x_1317 = lean_ctor_get(x_1316, 0);
x_1354 = !lean_is_exclusive(x_1316);
if (x_1354 == 0)
{
x_1318 = x_1316;
x_1319 = x_1354;
goto block_1353;
}
else
{
lean_inc(x_1317);
lean_dec(x_1316);
x_1318 = lean_box(0);
x_1319 = x_1354;
goto block_1353;
}
block_1353:
{
lean_object* x_1320; lean_object* x_1321; uint8_t x_1322; uint8_t x_1323; uint8_t x_1324; uint8_t x_1325; uint8_t x_1326; uint8_t x_1327; uint8_t x_1328; lean_object* x_1329; uint32_t x_1330; uint32_t x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; uint8_t x_1337; lean_object* x_1338; uint8_t x_1339; uint8_t x_1340; lean_object* x_1341; uint8_t x_1342; uint8_t x_1351; 
x_1320 = lean_ctor_get(x_1, 0);
x_1321 = lean_ctor_get(x_1, 1);
x_1322 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1323 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1324 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1325 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1326 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1327 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1328 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1329 = lean_ctor_get(x_1, 2);
x_1330 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1331 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1332 = lean_ctor_get(x_1, 3);
x_1333 = lean_ctor_get(x_1, 4);
x_1334 = lean_ctor_get(x_1, 5);
x_1335 = lean_ctor_get(x_1, 6);
x_1336 = lean_ctor_get(x_1, 7);
x_1337 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1338 = lean_ctor_get(x_1, 9);
x_1339 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1340 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1351 = !lean_is_exclusive(x_1);
if (x_1351 == 0)
{
lean_object* x_1352; 
x_1352 = lean_ctor_get(x_1, 8);
lean_dec(x_1352);
x_1341 = x_1;
x_1342 = x_1351;
goto block_1350;
}
else
{
lean_inc(x_1338);
lean_inc(x_1336);
lean_inc(x_1335);
lean_inc(x_1334);
lean_inc(x_1333);
lean_inc(x_1332);
lean_inc(x_1329);
lean_inc(x_1321);
lean_inc(x_1320);
lean_dec(x_1);
x_1341 = lean_box(0);
x_1342 = x_1351;
goto block_1350;
}
block_1350:
{
lean_object* x_1343; lean_object* x_1344; 
x_1343 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1343, 0, x_1317);
if (x_1342 == 0)
{
lean_ctor_set(x_1341, 8, x_1343);
x_1344 = x_1341;
goto block_1348;
}
else
{
lean_object* x_1349; 
x_1349 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1349, 0, x_1320);
lean_ctor_set(x_1349, 1, x_1321);
lean_ctor_set(x_1349, 2, x_1329);
lean_ctor_set(x_1349, 3, x_1332);
lean_ctor_set(x_1349, 4, x_1333);
lean_ctor_set(x_1349, 5, x_1334);
lean_ctor_set(x_1349, 6, x_1335);
lean_ctor_set(x_1349, 7, x_1336);
lean_ctor_set(x_1349, 8, x_1343);
lean_ctor_set(x_1349, 9, x_1338);
lean_ctor_set_uint8(x_1349, sizeof(void*)*10 + 8, x_1322);
lean_ctor_set_uint8(x_1349, sizeof(void*)*10 + 9, x_1323);
lean_ctor_set_uint8(x_1349, sizeof(void*)*10 + 10, x_1324);
lean_ctor_set_uint8(x_1349, sizeof(void*)*10 + 11, x_1325);
lean_ctor_set_uint8(x_1349, sizeof(void*)*10 + 12, x_1326);
lean_ctor_set_uint8(x_1349, sizeof(void*)*10 + 13, x_1327);
lean_ctor_set_uint8(x_1349, sizeof(void*)*10 + 14, x_1328);
lean_ctor_set_uint32(x_1349, sizeof(void*)*10, x_1330);
lean_ctor_set_uint32(x_1349, sizeof(void*)*10 + 4, x_1331);
lean_ctor_set_uint8(x_1349, sizeof(void*)*10 + 15, x_1337);
lean_ctor_set_uint8(x_1349, sizeof(void*)*10 + 16, x_1339);
lean_ctor_set_uint8(x_1349, sizeof(void*)*10 + 17, x_1340);
x_1344 = x_1349;
goto block_1348;
}
block_1348:
{
lean_object* x_1345; 
if (x_1319 == 0)
{
lean_ctor_set(x_1318, 0, x_1344);
x_1345 = x_1318;
goto block_1346;
}
else
{
lean_object* x_1347; 
x_1347 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1347, 0, x_1344);
x_1345 = x_1347;
goto block_1346;
}
block_1346:
{
return x_1345;
}
}
}
}
}
else
{
lean_object* x_1355; lean_object* x_1359; lean_object* x_1360; 
lean_dec_ref(x_1);
x_1355 = lean_ctor_get(x_1316, 0);
lean_inc(x_1355);
lean_dec_ref(x_1316);
x_1359 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1360 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1359);
lean_dec_ref(x_1360);
goto block_1358;
block_1358:
{
lean_object* x_1356; lean_object* x_1357; 
x_1356 = lean_io_error_to_string(x_1355);
x_1357 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1356);
lean_dec_ref(x_1357);
goto block_182;
}
}
}
}
else
{
lean_object* x_1361; lean_object* x_1362; 
x_1361 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__30));
x_1362 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1361, x_3);
if (lean_obj_tag(x_1362) == 0)
{
lean_object* x_1363; lean_object* x_1364; uint8_t x_1365; uint8_t x_1400; 
x_1363 = lean_ctor_get(x_1362, 0);
x_1400 = !lean_is_exclusive(x_1362);
if (x_1400 == 0)
{
x_1364 = x_1362;
x_1365 = x_1400;
goto block_1399;
}
else
{
lean_inc(x_1363);
lean_dec(x_1362);
x_1364 = lean_box(0);
x_1365 = x_1400;
goto block_1399;
}
block_1399:
{
lean_object* x_1366; lean_object* x_1367; uint8_t x_1368; uint8_t x_1369; uint8_t x_1370; uint8_t x_1371; uint8_t x_1372; uint8_t x_1373; uint8_t x_1374; lean_object* x_1375; uint32_t x_1376; uint32_t x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; uint8_t x_1383; lean_object* x_1384; uint8_t x_1385; uint8_t x_1386; lean_object* x_1387; uint8_t x_1388; uint8_t x_1397; 
x_1366 = lean_ctor_get(x_1, 0);
x_1367 = lean_ctor_get(x_1, 1);
x_1368 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1369 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1370 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1371 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1372 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1373 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1374 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1375 = lean_ctor_get(x_1, 2);
x_1376 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1377 = lean_ctor_get_uint32(x_1, sizeof(void*)*10 + 4);
x_1378 = lean_ctor_get(x_1, 3);
x_1379 = lean_ctor_get(x_1, 4);
x_1380 = lean_ctor_get(x_1, 5);
x_1381 = lean_ctor_get(x_1, 6);
x_1382 = lean_ctor_get(x_1, 8);
x_1383 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1384 = lean_ctor_get(x_1, 9);
x_1385 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1386 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1397 = !lean_is_exclusive(x_1);
if (x_1397 == 0)
{
lean_object* x_1398; 
x_1398 = lean_ctor_get(x_1, 7);
lean_dec(x_1398);
x_1387 = x_1;
x_1388 = x_1397;
goto block_1396;
}
else
{
lean_inc(x_1384);
lean_inc(x_1382);
lean_inc(x_1381);
lean_inc(x_1380);
lean_inc(x_1379);
lean_inc(x_1378);
lean_inc(x_1375);
lean_inc(x_1367);
lean_inc(x_1366);
lean_dec(x_1);
x_1387 = lean_box(0);
x_1388 = x_1397;
goto block_1396;
}
block_1396:
{
lean_object* x_1389; lean_object* x_1390; 
x_1389 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1389, 0, x_1363);
if (x_1388 == 0)
{
lean_ctor_set(x_1387, 7, x_1389);
x_1390 = x_1387;
goto block_1394;
}
else
{
lean_object* x_1395; 
x_1395 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1395, 0, x_1366);
lean_ctor_set(x_1395, 1, x_1367);
lean_ctor_set(x_1395, 2, x_1375);
lean_ctor_set(x_1395, 3, x_1378);
lean_ctor_set(x_1395, 4, x_1379);
lean_ctor_set(x_1395, 5, x_1380);
lean_ctor_set(x_1395, 6, x_1381);
lean_ctor_set(x_1395, 7, x_1389);
lean_ctor_set(x_1395, 8, x_1382);
lean_ctor_set(x_1395, 9, x_1384);
lean_ctor_set_uint8(x_1395, sizeof(void*)*10 + 8, x_1368);
lean_ctor_set_uint8(x_1395, sizeof(void*)*10 + 9, x_1369);
lean_ctor_set_uint8(x_1395, sizeof(void*)*10 + 10, x_1370);
lean_ctor_set_uint8(x_1395, sizeof(void*)*10 + 11, x_1371);
lean_ctor_set_uint8(x_1395, sizeof(void*)*10 + 12, x_1372);
lean_ctor_set_uint8(x_1395, sizeof(void*)*10 + 13, x_1373);
lean_ctor_set_uint8(x_1395, sizeof(void*)*10 + 14, x_1374);
lean_ctor_set_uint32(x_1395, sizeof(void*)*10, x_1376);
lean_ctor_set_uint32(x_1395, sizeof(void*)*10 + 4, x_1377);
lean_ctor_set_uint8(x_1395, sizeof(void*)*10 + 15, x_1383);
lean_ctor_set_uint8(x_1395, sizeof(void*)*10 + 16, x_1385);
lean_ctor_set_uint8(x_1395, sizeof(void*)*10 + 17, x_1386);
x_1390 = x_1395;
goto block_1394;
}
block_1394:
{
lean_object* x_1391; 
if (x_1365 == 0)
{
lean_ctor_set(x_1364, 0, x_1390);
x_1391 = x_1364;
goto block_1392;
}
else
{
lean_object* x_1393; 
x_1393 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1393, 0, x_1390);
x_1391 = x_1393;
goto block_1392;
}
block_1392:
{
return x_1391;
}
}
}
}
}
else
{
lean_object* x_1401; lean_object* x_1405; lean_object* x_1406; 
lean_dec_ref(x_1);
x_1401 = lean_ctor_get(x_1362, 0);
lean_inc(x_1401);
lean_dec_ref(x_1362);
x_1405 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1406 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1405);
lean_dec_ref(x_1406);
goto block_1404;
block_1404:
{
lean_object* x_1402; lean_object* x_1403; 
x_1402 = lean_io_error_to_string(x_1401);
x_1403 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1402);
lean_dec_ref(x_1403);
goto block_34;
}
}
}
}
else
{
lean_object* x_1407; lean_object* x_1408; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1407 = l___private_Lean_Shell_0__Lean_featuresString;
x_1408 = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(x_1407);
if (lean_obj_tag(x_1408) == 0)
{
lean_object* x_1409; uint8_t x_1410; uint8_t x_1416; 
x_1416 = !lean_is_exclusive(x_1408);
if (x_1416 == 0)
{
lean_object* x_1417; 
x_1417 = lean_ctor_get(x_1408, 0);
lean_dec(x_1417);
x_1409 = x_1408;
x_1410 = x_1416;
goto block_1415;
}
else
{
lean_dec(x_1408);
x_1409 = lean_box(0);
x_1410 = x_1416;
goto block_1415;
}
block_1415:
{
lean_object* x_1411; lean_object* x_1412; 
x_1411 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_1410 == 0)
{
lean_ctor_set_tag(x_1409, 1);
lean_ctor_set(x_1409, 0, x_1411);
x_1412 = x_1409;
goto block_1413;
}
else
{
lean_object* x_1414; 
x_1414 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1414, 0, x_1411);
x_1412 = x_1414;
goto block_1413;
}
block_1413:
{
return x_1412;
}
}
}
else
{
lean_object* x_1418; lean_object* x_1422; lean_object* x_1423; 
x_1418 = lean_ctor_get(x_1408, 0);
lean_inc(x_1418);
lean_dec_ref(x_1408);
x_1422 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1423 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1422);
lean_dec_ref(x_1423);
goto block_1421;
block_1421:
{
lean_object* x_1419; lean_object* x_1420; 
x_1419 = lean_io_error_to_string(x_1418);
x_1420 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1419);
lean_dec_ref(x_1420);
goto block_188;
}
}
}
}
else
{
lean_object* x_1424; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1424 = l___private_Lean_Shell_0__Lean_displayHelp(x_210);
if (lean_obj_tag(x_1424) == 0)
{
lean_object* x_1425; uint8_t x_1426; uint8_t x_1432; 
x_1432 = !lean_is_exclusive(x_1424);
if (x_1432 == 0)
{
lean_object* x_1433; 
x_1433 = lean_ctor_get(x_1424, 0);
lean_dec(x_1433);
x_1425 = x_1424;
x_1426 = x_1432;
goto block_1431;
}
else
{
lean_dec(x_1424);
x_1425 = lean_box(0);
x_1426 = x_1432;
goto block_1431;
}
block_1431:
{
lean_object* x_1427; lean_object* x_1428; 
x_1427 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_1426 == 0)
{
lean_ctor_set_tag(x_1425, 1);
lean_ctor_set(x_1425, 0, x_1427);
x_1428 = x_1425;
goto block_1429;
}
else
{
lean_object* x_1430; 
x_1430 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1430, 0, x_1427);
x_1428 = x_1430;
goto block_1429;
}
block_1429:
{
return x_1428;
}
}
}
else
{
lean_object* x_1434; lean_object* x_1438; lean_object* x_1439; 
x_1434 = lean_ctor_get(x_1424, 0);
lean_inc(x_1434);
lean_dec_ref(x_1424);
x_1438 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1439 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1438);
lean_dec_ref(x_1439);
goto block_1437;
block_1437:
{
lean_object* x_1435; lean_object* x_1436; 
x_1435 = lean_io_error_to_string(x_1434);
x_1436 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1435);
lean_dec_ref(x_1436);
goto block_28;
}
}
}
}
else
{
lean_object* x_1440; lean_object* x_1441; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1440 = l_Lean_githash;
x_1441 = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(x_1440);
if (lean_obj_tag(x_1441) == 0)
{
lean_object* x_1442; uint8_t x_1443; uint8_t x_1449; 
x_1449 = !lean_is_exclusive(x_1441);
if (x_1449 == 0)
{
lean_object* x_1450; 
x_1450 = lean_ctor_get(x_1441, 0);
lean_dec(x_1450);
x_1442 = x_1441;
x_1443 = x_1449;
goto block_1448;
}
else
{
lean_dec(x_1441);
x_1442 = lean_box(0);
x_1443 = x_1449;
goto block_1448;
}
block_1448:
{
lean_object* x_1444; lean_object* x_1445; 
x_1444 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_1443 == 0)
{
lean_ctor_set_tag(x_1442, 1);
lean_ctor_set(x_1442, 0, x_1444);
x_1445 = x_1442;
goto block_1446;
}
else
{
lean_object* x_1447; 
x_1447 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1447, 0, x_1444);
x_1445 = x_1447;
goto block_1446;
}
block_1446:
{
return x_1445;
}
}
}
else
{
lean_object* x_1451; lean_object* x_1455; lean_object* x_1456; 
x_1451 = lean_ctor_get(x_1441, 0);
lean_inc(x_1451);
lean_dec_ref(x_1441);
x_1455 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1456 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1455);
lean_dec_ref(x_1456);
goto block_1454;
block_1454:
{
lean_object* x_1452; lean_object* x_1453; 
x_1452 = lean_io_error_to_string(x_1451);
x_1453 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1452);
lean_dec_ref(x_1453);
goto block_194;
}
}
}
}
else
{
lean_object* x_1457; lean_object* x_1458; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1457 = l___private_Lean_Shell_0__Lean_shortVersionString;
x_1458 = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(x_1457);
if (lean_obj_tag(x_1458) == 0)
{
lean_object* x_1459; uint8_t x_1460; uint8_t x_1466; 
x_1466 = !lean_is_exclusive(x_1458);
if (x_1466 == 0)
{
lean_object* x_1467; 
x_1467 = lean_ctor_get(x_1458, 0);
lean_dec(x_1467);
x_1459 = x_1458;
x_1460 = x_1466;
goto block_1465;
}
else
{
lean_dec(x_1458);
x_1459 = lean_box(0);
x_1460 = x_1466;
goto block_1465;
}
block_1465:
{
lean_object* x_1461; lean_object* x_1462; 
x_1461 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_1460 == 0)
{
lean_ctor_set_tag(x_1459, 1);
lean_ctor_set(x_1459, 0, x_1461);
x_1462 = x_1459;
goto block_1463;
}
else
{
lean_object* x_1464; 
x_1464 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1464, 0, x_1461);
x_1462 = x_1464;
goto block_1463;
}
block_1463:
{
return x_1462;
}
}
}
else
{
lean_object* x_1468; lean_object* x_1472; lean_object* x_1473; 
x_1468 = lean_ctor_get(x_1458, 0);
lean_inc(x_1468);
lean_dec_ref(x_1458);
x_1472 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1473 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1472);
lean_dec_ref(x_1473);
goto block_1471;
block_1471:
{
lean_object* x_1469; lean_object* x_1470; 
x_1469 = lean_io_error_to_string(x_1468);
x_1470 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1469);
lean_dec_ref(x_1470);
goto block_22;
}
}
}
}
else
{
lean_object* x_1474; lean_object* x_1475; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_1474 = l___private_Lean_Shell_0__Lean_versionHeader;
x_1475 = l_IO_println___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__3(x_1474);
if (lean_obj_tag(x_1475) == 0)
{
lean_object* x_1476; uint8_t x_1477; uint8_t x_1483; 
x_1483 = !lean_is_exclusive(x_1475);
if (x_1483 == 0)
{
lean_object* x_1484; 
x_1484 = lean_ctor_get(x_1475, 0);
lean_dec(x_1484);
x_1476 = x_1475;
x_1477 = x_1483;
goto block_1482;
}
else
{
lean_dec(x_1475);
x_1476 = lean_box(0);
x_1477 = x_1483;
goto block_1482;
}
block_1482:
{
lean_object* x_1478; lean_object* x_1479; 
x_1478 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_1477 == 0)
{
lean_ctor_set_tag(x_1476, 1);
lean_ctor_set(x_1476, 0, x_1478);
x_1479 = x_1476;
goto block_1480;
}
else
{
lean_object* x_1481; 
x_1481 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1481, 0, x_1478);
x_1479 = x_1481;
goto block_1480;
}
block_1480:
{
return x_1479;
}
}
}
else
{
lean_object* x_1485; lean_object* x_1489; lean_object* x_1490; 
x_1485 = lean_ctor_get(x_1475, 0);
lean_inc(x_1485);
lean_dec_ref(x_1475);
x_1489 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1490 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1489);
lean_dec_ref(x_1490);
goto block_1488;
block_1488:
{
lean_object* x_1486; lean_object* x_1487; 
x_1486 = lean_io_error_to_string(x_1485);
x_1487 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1486);
lean_dec_ref(x_1487);
goto block_200;
}
}
}
}
else
{
lean_object* x_1491; lean_object* x_1492; 
x_1491 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__31));
x_1492 = l___private_Lean_Shell_0__Lean_checkOptArg(x_1491, x_3);
if (lean_obj_tag(x_1492) == 0)
{
lean_object* x_1493; lean_object* x_1494; uint8_t x_1495; uint8_t x_1543; 
x_1493 = lean_ctor_get(x_1492, 0);
x_1543 = !lean_is_exclusive(x_1492);
if (x_1543 == 0)
{
x_1494 = x_1492;
x_1495 = x_1543;
goto block_1542;
}
else
{
lean_inc(x_1493);
lean_dec(x_1492);
x_1494 = lean_box(0);
x_1495 = x_1543;
goto block_1542;
}
block_1542:
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; 
x_1496 = lean_unsigned_to_nat(0u);
x_1497 = lean_string_utf8_byte_size(x_1493);
lean_inc(x_1493);
x_1498 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1498, 0, x_1493);
lean_ctor_set(x_1498, 1, x_1496);
lean_ctor_set(x_1498, 2, x_1497);
x_1499 = l_String_Slice_toNat_x3f(x_1498);
lean_dec_ref(x_1498);
if (lean_obj_tag(x_1499) == 1)
{
lean_object* x_1500; lean_object* x_1501; uint8_t x_1502; 
x_1500 = lean_ctor_get(x_1499, 0);
lean_inc(x_1500);
lean_dec_ref(x_1499);
x_1501 = lean_cstr_to_nat("4294967296");
x_1502 = lean_nat_dec_lt(x_1500, x_1501);
if (x_1502 == 0)
{
lean_object* x_1503; lean_object* x_1504; 
lean_dec(x_1500);
lean_del_object(x_1494);
lean_dec(x_1493);
lean_dec_ref(x_1);
x_1503 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__32));
x_1504 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1503);
lean_dec_ref(x_1504);
goto block_16;
}
else
{
lean_object* x_1505; lean_object* x_1506; uint8_t x_1507; uint8_t x_1508; uint8_t x_1509; uint8_t x_1510; uint8_t x_1511; uint8_t x_1512; uint8_t x_1513; lean_object* x_1514; uint32_t x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; uint8_t x_1522; lean_object* x_1523; uint8_t x_1524; uint8_t x_1525; lean_object* x_1526; uint8_t x_1527; uint8_t x_1539; 
x_1505 = lean_ctor_get(x_1, 0);
x_1506 = lean_ctor_get(x_1, 1);
x_1507 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 8);
x_1508 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 9);
x_1509 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 10);
x_1510 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 11);
x_1511 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 12);
x_1512 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 13);
x_1513 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 14);
x_1514 = lean_ctor_get(x_1, 2);
x_1515 = lean_ctor_get_uint32(x_1, sizeof(void*)*10);
x_1516 = lean_ctor_get(x_1, 3);
x_1517 = lean_ctor_get(x_1, 4);
x_1518 = lean_ctor_get(x_1, 5);
x_1519 = lean_ctor_get(x_1, 6);
x_1520 = lean_ctor_get(x_1, 7);
x_1521 = lean_ctor_get(x_1, 8);
x_1522 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 15);
x_1523 = lean_ctor_get(x_1, 9);
x_1524 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 16);
x_1525 = lean_ctor_get_uint8(x_1, sizeof(void*)*10 + 17);
x_1539 = !lean_is_exclusive(x_1);
if (x_1539 == 0)
{
x_1526 = x_1;
x_1527 = x_1539;
goto block_1538;
}
else
{
lean_inc(x_1523);
lean_inc(x_1521);
lean_inc(x_1520);
lean_inc(x_1519);
lean_inc(x_1518);
lean_inc(x_1517);
lean_inc(x_1516);
lean_inc(x_1514);
lean_inc(x_1506);
lean_inc(x_1505);
lean_dec(x_1);
x_1526 = lean_box(0);
x_1527 = x_1539;
goto block_1538;
}
block_1538:
{
uint32_t x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; 
x_1528 = lean_uint32_of_nat(x_1500);
lean_dec(x_1500);
x_1529 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__33));
x_1530 = lean_string_append(x_1529, x_1493);
lean_dec(x_1493);
x_1531 = lean_array_push(x_1506, x_1530);
if (x_1527 == 0)
{
lean_ctor_set(x_1526, 1, x_1531);
x_1532 = x_1526;
goto block_1536;
}
else
{
lean_object* x_1537; 
x_1537 = lean_alloc_ctor(0, 10, 18);
lean_ctor_set(x_1537, 0, x_1505);
lean_ctor_set(x_1537, 1, x_1531);
lean_ctor_set(x_1537, 2, x_1514);
lean_ctor_set(x_1537, 3, x_1516);
lean_ctor_set(x_1537, 4, x_1517);
lean_ctor_set(x_1537, 5, x_1518);
lean_ctor_set(x_1537, 6, x_1519);
lean_ctor_set(x_1537, 7, x_1520);
lean_ctor_set(x_1537, 8, x_1521);
lean_ctor_set(x_1537, 9, x_1523);
lean_ctor_set_uint8(x_1537, sizeof(void*)*10 + 8, x_1507);
lean_ctor_set_uint8(x_1537, sizeof(void*)*10 + 9, x_1508);
lean_ctor_set_uint8(x_1537, sizeof(void*)*10 + 10, x_1509);
lean_ctor_set_uint8(x_1537, sizeof(void*)*10 + 11, x_1510);
lean_ctor_set_uint8(x_1537, sizeof(void*)*10 + 12, x_1511);
lean_ctor_set_uint8(x_1537, sizeof(void*)*10 + 13, x_1512);
lean_ctor_set_uint8(x_1537, sizeof(void*)*10 + 14, x_1513);
lean_ctor_set_uint32(x_1537, sizeof(void*)*10, x_1515);
lean_ctor_set_uint8(x_1537, sizeof(void*)*10 + 15, x_1522);
lean_ctor_set_uint8(x_1537, sizeof(void*)*10 + 16, x_1524);
lean_ctor_set_uint8(x_1537, sizeof(void*)*10 + 17, x_1525);
x_1532 = x_1537;
goto block_1536;
}
block_1536:
{
lean_object* x_1533; 
lean_ctor_set_uint32(x_1532, sizeof(void*)*10 + 4, x_1528);
if (x_1495 == 0)
{
lean_ctor_set(x_1494, 0, x_1532);
x_1533 = x_1494;
goto block_1534;
}
else
{
lean_object* x_1535; 
x_1535 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1535, 0, x_1532);
x_1533 = x_1535;
goto block_1534;
}
block_1534:
{
return x_1533;
}
}
}
}
}
else
{
lean_object* x_1540; lean_object* x_1541; 
lean_dec(x_1499);
lean_del_object(x_1494);
lean_dec(x_1493);
lean_dec_ref(x_1);
x_1540 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__34));
x_1541 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1540);
lean_dec_ref(x_1541);
goto block_13;
}
}
}
else
{
lean_object* x_1544; lean_object* x_1548; lean_object* x_1549; 
lean_dec_ref(x_1);
x_1544 = lean_ctor_get(x_1492, 0);
lean_inc(x_1544);
lean_dec_ref(x_1492);
x_1548 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_1549 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1548);
lean_dec_ref(x_1549);
goto block_1547;
block_1547:
{
lean_object* x_1545; lean_object* x_1546; 
x_1545 = lean_io_error_to_string(x_1544);
x_1546 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_1545);
lean_dec_ref(x_1546);
goto block_10;
}
}
}
}
else
{
lean_object* x_1550; lean_object* x_1551; 
lean_dec(x_3);
x_1550 = lean_internal_set_exit_on_panic(x_202);
x_1551 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1551, 0, x_1);
return x_1551;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_9 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_8);
lean_dec_ref(x_9);
goto block_7;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_21 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_20);
lean_dec_ref(x_21);
goto block_19;
}
block_25:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_27 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_26);
lean_dec_ref(x_27);
goto block_25;
}
block_31:
{
lean_object* x_29; lean_object* x_30; 
x_29 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
block_34:
{
lean_object* x_32; lean_object* x_33; 
x_32 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_33 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_32);
lean_dec_ref(x_33);
goto block_31;
}
block_37:
{
lean_object* x_35; lean_object* x_36; 
x_35 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
block_40:
{
lean_object* x_38; lean_object* x_39; 
x_38 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_39 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_38);
lean_dec_ref(x_39);
goto block_37;
}
block_43:
{
lean_object* x_41; lean_object* x_42; 
x_41 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
block_46:
{
lean_object* x_44; lean_object* x_45; 
x_44 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
block_49:
{
lean_object* x_47; lean_object* x_48; 
x_47 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
block_52:
{
lean_object* x_50; lean_object* x_51; 
x_50 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_51 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_50);
lean_dec_ref(x_51);
goto block_49;
}
block_55:
{
lean_object* x_53; lean_object* x_54; 
x_53 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
block_58:
{
lean_object* x_56; lean_object* x_57; 
x_56 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_57 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_56);
lean_dec_ref(x_57);
goto block_55;
}
block_61:
{
lean_object* x_59; lean_object* x_60; 
x_59 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
block_64:
{
lean_object* x_62; lean_object* x_63; 
x_62 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
block_67:
{
lean_object* x_65; lean_object* x_66; 
x_65 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_66 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_65);
lean_dec_ref(x_66);
goto block_64;
}
block_70:
{
lean_object* x_68; lean_object* x_69; 
x_68 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
block_73:
{
lean_object* x_71; lean_object* x_72; 
x_71 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
block_76:
{
lean_object* x_74; lean_object* x_75; 
x_74 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
block_79:
{
lean_object* x_77; lean_object* x_78; 
x_77 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_78 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_77);
lean_dec_ref(x_78);
goto block_76;
}
block_82:
{
lean_object* x_80; lean_object* x_81; 
x_80 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
block_85:
{
lean_object* x_83; lean_object* x_84; 
x_83 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_84 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_83);
lean_dec_ref(x_84);
goto block_82;
}
block_88:
{
lean_object* x_86; lean_object* x_87; 
x_86 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
block_91:
{
lean_object* x_89; lean_object* x_90; 
x_89 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_90 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_89);
lean_dec_ref(x_90);
goto block_88;
}
block_94:
{
lean_object* x_92; lean_object* x_93; 
x_92 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
block_97:
{
lean_object* x_95; lean_object* x_96; 
x_95 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_96 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_95);
lean_dec_ref(x_96);
goto block_94;
}
block_100:
{
lean_object* x_98; lean_object* x_99; 
x_98 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
block_103:
{
lean_object* x_101; lean_object* x_102; 
x_101 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_102 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_101);
lean_dec_ref(x_102);
goto block_100;
}
block_107:
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_io_error_to_string(x_104);
x_106 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_105);
lean_dec_ref(x_106);
goto block_103;
}
block_122:
{
uint8_t x_108; lean_object* x_109; 
x_108 = 1;
x_109 = l___private_Lean_Shell_0__Lean_displayHelp(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; uint8_t x_111; uint8_t x_117; 
x_117 = !lean_is_exclusive(x_109);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_109, 0);
lean_dec(x_118);
x_110 = x_109;
x_111 = x_117;
goto block_116;
}
else
{
lean_dec(x_109);
x_110 = lean_box(0);
x_111 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_112; lean_object* x_113; 
x_112 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (x_111 == 0)
{
lean_ctor_set_tag(x_110, 1);
lean_ctor_set(x_110, 0, x_112);
x_113 = x_110;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_112);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_109, 0);
lean_inc(x_119);
lean_dec_ref(x_109);
x_120 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__1));
x_121 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_120);
lean_dec_ref(x_121);
x_104 = x_119;
goto block_107;
}
}
block_125:
{
lean_object* x_123; lean_object* x_124; 
x_123 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process___closed__0));
x_124 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_123);
lean_dec_ref(x_124);
goto block_122;
}
block_128:
{
lean_object* x_126; lean_object* x_127; 
x_126 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
block_131:
{
lean_object* x_129; lean_object* x_130; 
x_129 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_130 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_129);
lean_dec_ref(x_130);
goto block_128;
}
block_134:
{
lean_object* x_132; lean_object* x_133; 
x_132 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
block_137:
{
lean_object* x_135; lean_object* x_136; 
x_135 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_136 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_135);
lean_dec_ref(x_136);
goto block_134;
}
block_140:
{
lean_object* x_138; lean_object* x_139; 
x_138 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
block_143:
{
lean_object* x_141; lean_object* x_142; 
x_141 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_142 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_141);
lean_dec_ref(x_142);
goto block_140;
}
block_146:
{
lean_object* x_144; lean_object* x_145; 
x_144 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
return x_145;
}
block_149:
{
lean_object* x_147; lean_object* x_148; 
x_147 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_148 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_147);
lean_dec_ref(x_148);
goto block_146;
}
block_152:
{
lean_object* x_150; lean_object* x_151; 
x_150 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
block_155:
{
lean_object* x_153; lean_object* x_154; 
x_153 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_154 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_153);
lean_dec_ref(x_154);
goto block_152;
}
block_158:
{
lean_object* x_156; lean_object* x_157; 
x_156 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
block_161:
{
lean_object* x_159; lean_object* x_160; 
x_159 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
block_164:
{
lean_object* x_162; lean_object* x_163; 
x_162 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_163 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_162);
lean_dec_ref(x_163);
goto block_161;
}
block_167:
{
lean_object* x_165; lean_object* x_166; 
x_165 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
block_170:
{
lean_object* x_168; lean_object* x_169; 
x_168 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_169 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_168);
lean_dec_ref(x_169);
goto block_167;
}
block_173:
{
lean_object* x_171; lean_object* x_172; 
x_171 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
block_176:
{
lean_object* x_174; lean_object* x_175; 
x_174 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_175 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_174);
lean_dec_ref(x_175);
goto block_173;
}
block_179:
{
lean_object* x_177; lean_object* x_178; 
x_177 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
return x_178;
}
block_182:
{
lean_object* x_180; lean_object* x_181; 
x_180 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_181 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_180);
lean_dec_ref(x_181);
goto block_179;
}
block_185:
{
lean_object* x_183; lean_object* x_184; 
x_183 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
block_188:
{
lean_object* x_186; lean_object* x_187; 
x_186 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_187 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_186);
lean_dec_ref(x_187);
goto block_185;
}
block_191:
{
lean_object* x_189; lean_object* x_190; 
x_189 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
return x_190;
}
block_194:
{
lean_object* x_192; lean_object* x_193; 
x_192 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_193 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_192);
lean_dec_ref(x_193);
goto block_191;
}
block_197:
{
lean_object* x_195; lean_object* x_196; 
x_195 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_195);
return x_196;
}
block_200:
{
lean_object* x_198; lean_object* x_199; 
x_198 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___closed__0));
x_199 = l_IO_eprint___at___00__private_Lean_Shell_0__Lean_ShellOptions_process_spec__0(x_198);
lean_dec_ref(x_199);
goto block_197;
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
lean_object* x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
lean_dec(x_3);
x_9 = lean_nat_add(x_5, x_2);
x_10 = lean_string_utf8_get_fast(x_4, x_9);
x_11 = 10;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_string_utf8_next_fast(x_4, x_9);
lean_dec(x_9);
x_15 = lean_nat_sub(x_14, x_5);
x_2 = x_15;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_9);
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
lean_object* x_7; lean_object* x_24; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint32_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_312; lean_object* x_313; lean_object* x_346; lean_object* x_347; 
x_44 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_45);
x_46 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 8);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 9);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 10);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 11);
x_50 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 12);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 13);
x_52 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 14);
x_53 = lean_ctor_get_uint32(x_2, sizeof(void*)*10);
x_54 = lean_ctor_get(x_2, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 5);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 6);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 7);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 8);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 15);
x_61 = lean_ctor_get(x_2, 9);
lean_inc_ref(x_61);
x_62 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 16);
x_63 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 17);
lean_dec_ref(x_2);
if (x_47 == 0)
{
if (x_48 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
x_409 = l___private_Lean_Shell_0__Lean_maxMemory;
x_410 = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(x_44, x_409);
x_411 = lean_unsigned_to_nat(0u);
x_412 = lean_nat_dec_eq(x_410, x_411);
if (x_412 == 0)
{
size_t x_413; size_t x_414; size_t x_415; size_t x_416; lean_object* x_417; 
x_413 = lean_usize_of_nat(x_410);
lean_dec(x_410);
x_414 = 1024;
x_415 = lean_usize_mul(x_413, x_414);
x_416 = lean_usize_mul(x_415, x_414);
x_417 = lean_internal_set_max_memory(x_416);
goto block_408;
}
else
{
lean_dec(x_410);
goto block_408;
}
}
else
{
lean_object* x_418; 
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec(x_1);
x_418 = l_Lean_getBuildDir();
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
lean_dec_ref(x_418);
x_420 = l_Lean_getLibDir(x_419);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
lean_dec_ref(x_420);
x_422 = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__5(x_421);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; uint8_t x_424; uint8_t x_430; 
x_430 = !lean_is_exclusive(x_422);
if (x_430 == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_422, 0);
lean_dec(x_431);
x_423 = x_422;
x_424 = x_430;
goto block_429;
}
else
{
lean_dec(x_422);
x_423 = lean_box(0);
x_424 = x_430;
goto block_429;
}
block_429:
{
lean_object* x_425; lean_object* x_426; 
x_425 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_424 == 0)
{
lean_ctor_set(x_423, 0, x_425);
x_426 = x_423;
goto block_427;
}
else
{
lean_object* x_428; 
x_428 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_428, 0, x_425);
x_426 = x_428;
goto block_427;
}
block_427:
{
return x_426;
}
}
}
else
{
lean_object* x_432; lean_object* x_433; uint8_t x_434; uint8_t x_439; 
x_432 = lean_ctor_get(x_422, 0);
x_439 = !lean_is_exclusive(x_422);
if (x_439 == 0)
{
x_433 = x_422;
x_434 = x_439;
goto block_438;
}
else
{
lean_inc(x_432);
lean_dec(x_422);
x_433 = lean_box(0);
x_434 = x_439;
goto block_438;
}
block_438:
{
lean_object* x_435; 
if (x_434 == 0)
{
x_435 = x_433;
goto block_436;
}
else
{
lean_object* x_437; 
x_437 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_437, 0, x_432);
x_435 = x_437;
goto block_436;
}
block_436:
{
return x_435;
}
}
}
}
else
{
lean_object* x_440; lean_object* x_441; uint8_t x_442; uint8_t x_447; 
x_440 = lean_ctor_get(x_420, 0);
x_447 = !lean_is_exclusive(x_420);
if (x_447 == 0)
{
x_441 = x_420;
x_442 = x_447;
goto block_446;
}
else
{
lean_inc(x_440);
lean_dec(x_420);
x_441 = lean_box(0);
x_442 = x_447;
goto block_446;
}
block_446:
{
lean_object* x_443; 
if (x_442 == 0)
{
x_443 = x_441;
goto block_444;
}
else
{
lean_object* x_445; 
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_440);
x_443 = x_445;
goto block_444;
}
block_444:
{
return x_443;
}
}
}
}
else
{
lean_object* x_448; lean_object* x_449; uint8_t x_450; uint8_t x_455; 
x_448 = lean_ctor_get(x_418, 0);
x_455 = !lean_is_exclusive(x_418);
if (x_455 == 0)
{
x_449 = x_418;
x_450 = x_455;
goto block_454;
}
else
{
lean_inc(x_448);
lean_dec(x_418);
x_449 = lean_box(0);
x_450 = x_455;
goto block_454;
}
block_454:
{
lean_object* x_451; 
if (x_450 == 0)
{
x_451 = x_449;
goto block_452;
}
else
{
lean_object* x_453; 
x_453 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_453, 0, x_448);
x_451 = x_453;
goto block_452;
}
block_452:
{
return x_451;
}
}
}
}
}
else
{
lean_object* x_456; 
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec(x_1);
x_456 = l_Lean_getBuildDir();
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
lean_dec_ref(x_456);
x_458 = l_IO_println___at___00__private_Lean_Shell_0__Lean_shellMain_spec__5(x_457);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; uint8_t x_460; uint8_t x_466; 
x_466 = !lean_is_exclusive(x_458);
if (x_466 == 0)
{
lean_object* x_467; 
x_467 = lean_ctor_get(x_458, 0);
lean_dec(x_467);
x_459 = x_458;
x_460 = x_466;
goto block_465;
}
else
{
lean_dec(x_458);
x_459 = lean_box(0);
x_460 = x_466;
goto block_465;
}
block_465:
{
lean_object* x_461; lean_object* x_462; 
x_461 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_460 == 0)
{
lean_ctor_set(x_459, 0, x_461);
x_462 = x_459;
goto block_463;
}
else
{
lean_object* x_464; 
x_464 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_464, 0, x_461);
x_462 = x_464;
goto block_463;
}
block_463:
{
return x_462;
}
}
}
else
{
lean_object* x_468; lean_object* x_469; uint8_t x_470; uint8_t x_475; 
x_468 = lean_ctor_get(x_458, 0);
x_475 = !lean_is_exclusive(x_458);
if (x_475 == 0)
{
x_469 = x_458;
x_470 = x_475;
goto block_474;
}
else
{
lean_inc(x_468);
lean_dec(x_458);
x_469 = lean_box(0);
x_470 = x_475;
goto block_474;
}
block_474:
{
lean_object* x_471; 
if (x_470 == 0)
{
x_471 = x_469;
goto block_472;
}
else
{
lean_object* x_473; 
x_473 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_473, 0, x_468);
x_471 = x_473;
goto block_472;
}
block_472:
{
return x_471;
}
}
}
}
else
{
lean_object* x_476; lean_object* x_477; uint8_t x_478; uint8_t x_483; 
x_476 = lean_ctor_get(x_456, 0);
x_483 = !lean_is_exclusive(x_456);
if (x_483 == 0)
{
x_477 = x_456;
x_478 = x_483;
goto block_482;
}
else
{
lean_inc(x_476);
lean_dec(x_456);
x_477 = lean_box(0);
x_478 = x_483;
goto block_482;
}
block_482:
{
lean_object* x_479; 
if (x_478 == 0)
{
x_479 = x_477;
goto block_480;
}
else
{
lean_object* x_481; 
x_481 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_481, 0, x_476);
x_479 = x_481;
goto block_480;
}
block_480:
{
return x_479;
}
}
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
block_23:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_display_cumulative_profiling_times();
x_9 = lean_uint8_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__0, &l___private_Lean_Shell_0__Lean_shellMain___closed__0_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0);
if (x_9 == 0)
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = lean_io_exit(x_10);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; 
lean_dec_ref(x_7);
x_12 = 0;
x_13 = lean_io_exit(x_12);
return x_13;
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
goto block_6;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_21; 
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_7, 0);
lean_dec(x_22);
x_14 = x_7;
x_15 = x_21;
goto block_20;
}
else
{
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
if (x_9 == 0)
{
lean_del_object(x_14);
goto block_6;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
}
block_43:
{
lean_object* x_25; 
x_25 = l_Lean_printImportsJson(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; uint8_t x_33; 
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_25, 0);
lean_dec(x_34);
x_26 = x_25;
x_27 = x_33;
goto block_32;
}
else
{
lean_dec(x_25);
x_26 = lean_box(0);
x_27 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_28);
x_29 = x_26;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
x_35 = lean_ctor_get(x_25, 0);
x_42 = !lean_is_exclusive(x_25);
if (x_42 == 0)
{
x_36 = x_25;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
block_89:
{
if (lean_obj_tag(x_59) == 1)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
lean_dec_ref(x_59);
x_68 = lean_init_llvm();
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_68);
x_69 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__1));
x_70 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(x_70, 0, x_65);
lean_closure_set(x_70, 1, x_64);
lean_closure_set(x_70, 2, x_67);
x_71 = lean_box(0);
x_72 = l_Lean_profileitIOUnsafe___redArg(x_69, x_44, x_70, x_71);
lean_dec_ref(x_44);
if (lean_obj_tag(x_72) == 0)
{
lean_dec_ref(x_72);
x_7 = x_66;
goto block_23;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_dec(x_66);
x_73 = lean_ctor_get(x_72, 0);
x_80 = !lean_is_exclusive(x_72);
if (x_80 == 0)
{
x_74 = x_72;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_44);
x_81 = lean_ctor_get(x_68, 0);
x_88 = !lean_is_exclusive(x_68);
if (x_88 == 0)
{
x_82 = x_68;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_68);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
else
{
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec(x_59);
lean_dec_ref(x_44);
x_7 = x_66;
goto block_23;
}
}
block_157:
{
lean_object* x_95; lean_object* x_96; 
x_95 = ((lean_object*)(l___private_Lean_Shell_0__Lean_mkShellOptions___closed__1));
lean_inc(x_94);
lean_inc_ref(x_44);
x_96 = l_Lean_Elab_runFrontend(x_92, x_44, x_90, x_94, x_53, x_56, x_57, x_60, x_61, x_95, x_62, x_91);
lean_dec_ref(x_61);
lean_dec(x_57);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_148; 
x_97 = lean_ctor_get(x_96, 0);
x_148 = !lean_is_exclusive(x_96);
if (x_148 == 0)
{
x_98 = x_96;
x_99 = x_148;
goto block_147;
}
else
{
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_box(0);
x_99 = x_148;
goto block_147;
}
block_147:
{
if (lean_obj_tag(x_97) == 1)
{
if (x_63 == 0)
{
lean_del_object(x_98);
lean_dec(x_93);
if (lean_obj_tag(x_58) == 1)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_97, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_58, 0);
lean_inc(x_101);
lean_dec_ref(x_58);
x_102 = 1;
x_103 = lean_io_prim_handle_mk(x_101, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_101);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__2));
lean_inc(x_94);
lean_inc(x_100);
x_106 = l_Lean_IR_emitC(x_100, x_94);
x_107 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 3, 2);
lean_closure_set(x_107, 0, x_106);
lean_closure_set(x_107, 1, x_104);
x_108 = lean_box(0);
x_109 = l_Lean_profileitIOUnsafe___redArg(x_105, x_44, x_107, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_dec_ref(x_109);
x_64 = x_94;
x_65 = x_100;
x_66 = x_97;
goto block_89;
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_117; 
lean_dec(x_100);
lean_dec_ref(x_97);
lean_dec(x_94);
lean_dec(x_59);
lean_dec_ref(x_44);
x_110 = lean_ctor_get(x_109, 0);
x_117 = !lean_is_exclusive(x_109);
if (x_117 == 0)
{
x_111 = x_109;
x_112 = x_117;
goto block_116;
}
else
{
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_box(0);
x_112 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_113; 
if (x_112 == 0)
{
x_113 = x_111;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_110);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec_ref(x_103);
lean_dec(x_100);
lean_dec_ref(x_97);
lean_dec(x_94);
lean_dec(x_59);
lean_dec_ref(x_44);
x_118 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__3));
x_119 = lean_string_append(x_118, x_101);
lean_dec(x_101);
x_120 = ((lean_object*)(l___private_Lean_Shell_0__Lean_checkOptArg___closed__1));
x_121 = lean_string_append(x_119, x_120);
x_122 = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; uint8_t x_124; uint8_t x_130; 
x_130 = !lean_is_exclusive(x_122);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_122, 0);
lean_dec(x_131);
x_123 = x_122;
x_124 = x_130;
goto block_129;
}
else
{
lean_dec(x_122);
x_123 = lean_box(0);
x_124 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_125; lean_object* x_126; 
x_125 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (x_124 == 0)
{
lean_ctor_set(x_123, 0, x_125);
x_126 = x_123;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_125);
x_126 = x_128;
goto block_127;
}
block_127:
{
return x_126;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_139; 
x_132 = lean_ctor_get(x_122, 0);
x_139 = !lean_is_exclusive(x_122);
if (x_139 == 0)
{
x_133 = x_122;
x_134 = x_139;
goto block_138;
}
else
{
lean_inc(x_132);
lean_dec(x_122);
x_133 = lean_box(0);
x_134 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_135; 
if (x_134 == 0)
{
x_135 = x_133;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_132);
x_135 = x_137;
goto block_136;
}
block_136:
{
return x_135;
}
}
}
}
}
else
{
lean_object* x_140; 
lean_dec(x_58);
x_140 = lean_ctor_get(x_97, 0);
lean_inc(x_140);
x_64 = x_94;
x_65 = x_140;
x_66 = x_97;
goto block_89;
}
}
else
{
lean_object* x_141; uint32_t x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_94);
lean_dec(x_59);
lean_dec(x_58);
x_141 = lean_ctor_get(x_97, 0);
lean_inc(x_141);
lean_dec_ref(x_97);
x_142 = lean_run_main(x_141, x_44, x_93);
lean_dec(x_93);
lean_dec_ref(x_44);
lean_dec(x_141);
x_143 = lean_box_uint32(x_142);
if (x_99 == 0)
{
lean_ctor_set(x_98, 0, x_143);
x_144 = x_98;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_143);
x_144 = x_146;
goto block_145;
}
block_145:
{
return x_144;
}
}
}
else
{
lean_del_object(x_98);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_59);
lean_dec(x_58);
lean_dec_ref(x_44);
x_7 = x_97;
goto block_23;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_156; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_59);
lean_dec(x_58);
lean_dec_ref(x_44);
x_149 = lean_ctor_get(x_96, 0);
x_156 = !lean_is_exclusive(x_96);
if (x_156 == 0)
{
x_150 = x_96;
x_151 = x_156;
goto block_155;
}
else
{
lean_inc(x_149);
lean_dec(x_96);
x_150 = lean_box(0);
x_151 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_152; 
if (x_151 == 0)
{
x_152 = x_150;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_149);
x_152 = x_154;
goto block_153;
}
block_153:
{
return x_152;
}
}
}
}
block_172:
{
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec_ref(x_162);
x_90 = x_158;
x_91 = x_159;
x_92 = x_160;
x_93 = x_161;
x_94 = x_163;
goto block_157;
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; uint8_t x_171; 
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_44);
x_164 = lean_ctor_get(x_162, 0);
x_171 = !lean_is_exclusive(x_162);
if (x_171 == 0)
{
x_165 = x_162;
x_166 = x_171;
goto block_170;
}
else
{
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_box(0);
x_166 = x_171;
goto block_170;
}
block_170:
{
lean_object* x_167; 
if (x_166 == 0)
{
x_167 = x_165;
goto block_168;
}
else
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_164);
x_167 = x_169;
goto block_168;
}
block_168:
{
return x_167;
}
}
}
}
block_201:
{
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_177; 
x_177 = lean_box(0);
if (lean_obj_tag(x_174) == 1)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_174, 0);
lean_inc(x_178);
lean_dec_ref(x_174);
x_179 = l_Lean_moduleNameOfFileName(x_178, x_54);
if (lean_obj_tag(x_179) == 0)
{
x_158 = x_173;
x_159 = x_177;
x_160 = x_176;
x_161 = x_175;
x_162 = x_179;
goto block_172;
}
else
{
if (lean_obj_tag(x_56) == 0)
{
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_180; 
lean_dec_ref(x_179);
x_180 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__5));
x_90 = x_173;
x_91 = x_177;
x_92 = x_176;
x_93 = x_175;
x_94 = x_180;
goto block_157;
}
else
{
x_158 = x_173;
x_159 = x_177;
x_160 = x_176;
x_161 = x_175;
x_162 = x_179;
goto block_172;
}
}
else
{
x_158 = x_173;
x_159 = x_177;
x_160 = x_176;
x_161 = x_175;
x_162 = x_179;
goto block_172;
}
}
}
else
{
lean_object* x_181; 
lean_dec(x_174);
lean_dec(x_54);
x_181 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__5));
x_90 = x_173;
x_91 = x_177;
x_92 = x_176;
x_93 = x_175;
x_94 = x_181;
goto block_157;
}
}
else
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_200; 
lean_dec(x_174);
lean_dec(x_54);
x_182 = lean_ctor_get(x_55, 0);
x_200 = !lean_is_exclusive(x_55);
if (x_200 == 0)
{
x_183 = x_55;
x_184 = x_200;
goto block_199;
}
else
{
lean_inc(x_182);
lean_dec(x_55);
x_183 = lean_box(0);
x_184 = x_200;
goto block_199;
}
block_199:
{
lean_object* x_185; 
x_185 = l_Lean_ModuleSetup_load(x_182);
lean_dec(x_182);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec_ref(x_185);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (x_184 == 0)
{
lean_ctor_set(x_183, 0, x_186);
x_188 = x_183;
goto block_189;
}
else
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_186);
x_188 = x_190;
goto block_189;
}
block_189:
{
x_90 = x_173;
x_91 = x_188;
x_92 = x_176;
x_93 = x_175;
x_94 = x_187;
goto block_157;
}
}
else
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_198; 
lean_del_object(x_183);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_173);
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_44);
x_191 = lean_ctor_get(x_185, 0);
x_198 = !lean_is_exclusive(x_185);
if (x_198 == 0)
{
x_192 = x_185;
x_193 = x_198;
goto block_197;
}
else
{
lean_inc(x_191);
lean_dec(x_185);
x_192 = lean_box(0);
x_193 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_194; 
if (x_193 == 0)
{
x_194 = x_192;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_191);
x_194 = x_196;
goto block_195;
}
block_195:
{
return x_194;
}
}
}
}
}
}
block_238:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_209 = lean_nat_add(x_204, x_208);
lean_dec(x_208);
lean_inc(x_209);
lean_inc_ref(x_203);
x_210 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_210, 0, x_203);
lean_ctor_set(x_210, 1, x_204);
lean_ctor_set(x_210, 2, x_209);
x_211 = l_String_Slice_trimAscii(x_210);
lean_dec_ref(x_210);
x_212 = lean_obj_once(&l___private_Lean_Shell_0__Lean_shellMain___closed__8, &l___private_Lean_Shell_0__Lean_shellMain___closed__8_once, _init_l___private_Lean_Shell_0__Lean_shellMain___closed__8);
x_213 = l_String_Slice_beq(x_211, x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_209);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec_ref(x_203);
lean_dec_ref(x_202);
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_44);
x_214 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__9));
x_215 = l_String_Slice_toString(x_211);
lean_dec_ref(x_211);
x_216 = lean_string_append(x_214, x_215);
lean_dec_ref(x_215);
x_217 = ((lean_object*)(l___private_Lean_Shell_0__Lean_ShellOptions_process_throwExpectedNumeric___closed__1));
x_218 = lean_string_append(x_216, x_217);
x_219 = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; uint8_t x_221; uint8_t x_227; 
x_227 = !lean_is_exclusive(x_219);
if (x_227 == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_219, 0);
lean_dec(x_228);
x_220 = x_219;
x_221 = x_227;
goto block_226;
}
else
{
lean_dec(x_219);
x_220 = lean_box(0);
x_221 = x_227;
goto block_226;
}
block_226:
{
lean_object* x_222; lean_object* x_223; 
x_222 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (x_221 == 0)
{
lean_ctor_set(x_220, 0, x_222);
x_223 = x_220;
goto block_224;
}
else
{
lean_object* x_225; 
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_222);
x_223 = x_225;
goto block_224;
}
block_224:
{
return x_223;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_236; 
x_229 = lean_ctor_get(x_219, 0);
x_236 = !lean_is_exclusive(x_219);
if (x_236 == 0)
{
x_230 = x_219;
x_231 = x_236;
goto block_235;
}
else
{
lean_inc(x_229);
lean_dec(x_219);
x_230 = lean_box(0);
x_231 = x_236;
goto block_235;
}
block_235:
{
lean_object* x_232; 
if (x_231 == 0)
{
x_232 = x_230;
goto block_233;
}
else
{
lean_object* x_234; 
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_229);
x_232 = x_234;
goto block_233;
}
block_233:
{
return x_232;
}
}
}
}
else
{
lean_object* x_237; 
lean_dec_ref(x_211);
x_237 = lean_string_utf8_extract(x_203, x_209, x_205);
lean_dec(x_205);
lean_dec(x_209);
lean_dec_ref(x_203);
x_173 = x_202;
x_174 = x_206;
x_175 = x_207;
x_176 = x_237;
goto block_201;
}
}
block_304:
{
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
lean_dec_ref(x_242);
x_244 = lean_decode_lossy_utf8(x_243);
lean_dec(x_243);
if (x_50 == 0)
{
if (x_51 == 0)
{
lean_object* x_245; 
lean_inc_ref(x_244);
x_245 = l_String_dropPrefix_x3f___at___00__private_Lean_Shell_0__Lean_shellMain_spec__2___redArg(x_244);
if (lean_obj_tag(x_245) == 1)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec_ref(x_244);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
x_247 = lean_unsigned_to_nat(0u);
x_248 = lean_box(0);
x_249 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Shell_0__Lean_shellMain_spec__3___redArg(x_246, x_247, x_248);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_ctor_get(x_246, 0);
lean_inc_ref(x_250);
x_251 = lean_ctor_get(x_246, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_246, 2);
lean_inc(x_252);
lean_dec(x_246);
x_253 = lean_nat_sub(x_252, x_251);
x_202 = x_239;
x_203 = x_250;
x_204 = x_251;
x_205 = x_252;
x_206 = x_240;
x_207 = x_241;
x_208 = x_253;
goto block_238;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_249, 0);
lean_inc(x_254);
lean_dec_ref(x_249);
x_255 = lean_ctor_get(x_246, 0);
lean_inc_ref(x_255);
x_256 = lean_ctor_get(x_246, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_246, 2);
lean_inc(x_257);
lean_dec(x_246);
x_202 = x_239;
x_203 = x_255;
x_204 = x_256;
x_205 = x_257;
x_206 = x_240;
x_207 = x_241;
x_208 = x_254;
goto block_238;
}
}
else
{
lean_dec(x_245);
x_173 = x_239;
x_174 = x_240;
x_175 = x_241;
x_176 = x_244;
goto block_201;
}
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_241);
lean_dec(x_240);
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_44);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_239);
x_259 = l_Lean_Elab_printImportSrcs(x_244, x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; uint8_t x_261; uint8_t x_267; 
x_267 = !lean_is_exclusive(x_259);
if (x_267 == 0)
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_259, 0);
lean_dec(x_268);
x_260 = x_259;
x_261 = x_267;
goto block_266;
}
else
{
lean_dec(x_259);
x_260 = lean_box(0);
x_261 = x_267;
goto block_266;
}
block_266:
{
lean_object* x_262; lean_object* x_263; 
x_262 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_261 == 0)
{
lean_ctor_set(x_260, 0, x_262);
x_263 = x_260;
goto block_264;
}
else
{
lean_object* x_265; 
x_265 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_265, 0, x_262);
x_263 = x_265;
goto block_264;
}
block_264:
{
return x_263;
}
}
}
else
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; uint8_t x_276; 
x_269 = lean_ctor_get(x_259, 0);
x_276 = !lean_is_exclusive(x_259);
if (x_276 == 0)
{
x_270 = x_259;
x_271 = x_276;
goto block_275;
}
else
{
lean_inc(x_269);
lean_dec(x_259);
x_270 = lean_box(0);
x_271 = x_276;
goto block_275;
}
block_275:
{
lean_object* x_272; 
if (x_271 == 0)
{
x_272 = x_270;
goto block_273;
}
else
{
lean_object* x_274; 
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_269);
x_272 = x_274;
goto block_273;
}
block_273:
{
return x_272;
}
}
}
}
}
else
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_241);
lean_dec(x_240);
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_44);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_239);
x_278 = l_Lean_Elab_printImports(x_244, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; uint8_t x_280; uint8_t x_286; 
x_286 = !lean_is_exclusive(x_278);
if (x_286 == 0)
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_278, 0);
lean_dec(x_287);
x_279 = x_278;
x_280 = x_286;
goto block_285;
}
else
{
lean_dec(x_278);
x_279 = lean_box(0);
x_280 = x_286;
goto block_285;
}
block_285:
{
lean_object* x_281; lean_object* x_282; 
x_281 = l___private_Lean_Shell_0__Lean_ShellOptions_process___boxed__const__1;
if (x_280 == 0)
{
lean_ctor_set(x_279, 0, x_281);
x_282 = x_279;
goto block_283;
}
else
{
lean_object* x_284; 
x_284 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_284, 0, x_281);
x_282 = x_284;
goto block_283;
}
block_283:
{
return x_282;
}
}
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; uint8_t x_295; 
x_288 = lean_ctor_get(x_278, 0);
x_295 = !lean_is_exclusive(x_278);
if (x_295 == 0)
{
x_289 = x_278;
x_290 = x_295;
goto block_294;
}
else
{
lean_inc(x_288);
lean_dec(x_278);
x_289 = lean_box(0);
x_290 = x_295;
goto block_294;
}
block_294:
{
lean_object* x_291; 
if (x_290 == 0)
{
x_291 = x_289;
goto block_292;
}
else
{
lean_object* x_293; 
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_288);
x_291 = x_293;
goto block_292;
}
block_292:
{
return x_291;
}
}
}
}
}
else
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; uint8_t x_303; 
lean_dec(x_241);
lean_dec(x_240);
lean_dec_ref(x_239);
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_44);
x_296 = lean_ctor_get(x_242, 0);
x_303 = !lean_is_exclusive(x_242);
if (x_303 == 0)
{
x_297 = x_242;
x_298 = x_303;
goto block_302;
}
else
{
lean_inc(x_296);
lean_dec(x_242);
x_297 = lean_box(0);
x_298 = x_303;
goto block_302;
}
block_302:
{
lean_object* x_299; 
if (x_298 == 0)
{
x_299 = x_297;
goto block_300;
}
else
{
lean_object* x_301; 
x_301 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_301, 0, x_296);
x_299 = x_301;
goto block_300;
}
block_300:
{
return x_299;
}
}
}
}
block_311:
{
if (x_49 == 0)
{
lean_object* x_308; 
x_308 = l_IO_FS_readBinFile(x_307);
x_239 = x_307;
x_240 = x_305;
x_241 = x_306;
x_242 = x_308;
goto block_304;
}
else
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_get_stdin();
x_310 = l_IO_FS_Stream_readBinToEnd(x_309);
x_239 = x_307;
x_240 = x_305;
x_241 = x_306;
x_242 = x_310;
goto block_304;
}
}
block_345:
{
if (lean_obj_tag(x_312) == 1)
{
lean_object* x_314; 
x_314 = lean_ctor_get(x_312, 0);
lean_inc(x_314);
x_305 = x_312;
x_306 = x_313;
x_307 = x_314;
goto block_311;
}
else
{
if (x_49 == 0)
{
lean_object* x_315; lean_object* x_316; 
lean_dec(x_313);
lean_dec(x_312);
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_44);
x_315 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__10));
x_316 = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(x_315);
if (lean_obj_tag(x_316) == 0)
{
uint8_t x_317; lean_object* x_318; 
lean_dec_ref(x_316);
x_317 = 1;
x_318 = l___private_Lean_Shell_0__Lean_displayHelp(x_317);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; uint8_t x_320; uint8_t x_326; 
x_326 = !lean_is_exclusive(x_318);
if (x_326 == 0)
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_318, 0);
lean_dec(x_327);
x_319 = x_318;
x_320 = x_326;
goto block_325;
}
else
{
lean_dec(x_318);
x_319 = lean_box(0);
x_320 = x_326;
goto block_325;
}
block_325:
{
lean_object* x_321; lean_object* x_322; 
x_321 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (x_320 == 0)
{
lean_ctor_set(x_319, 0, x_321);
x_322 = x_319;
goto block_323;
}
else
{
lean_object* x_324; 
x_324 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_324, 0, x_321);
x_322 = x_324;
goto block_323;
}
block_323:
{
return x_322;
}
}
}
else
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_335; 
x_328 = lean_ctor_get(x_318, 0);
x_335 = !lean_is_exclusive(x_318);
if (x_335 == 0)
{
x_329 = x_318;
x_330 = x_335;
goto block_334;
}
else
{
lean_inc(x_328);
lean_dec(x_318);
x_329 = lean_box(0);
x_330 = x_335;
goto block_334;
}
block_334:
{
lean_object* x_331; 
if (x_330 == 0)
{
x_331 = x_329;
goto block_332;
}
else
{
lean_object* x_333; 
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_328);
x_331 = x_333;
goto block_332;
}
block_332:
{
return x_331;
}
}
}
}
else
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; uint8_t x_343; 
x_336 = lean_ctor_get(x_316, 0);
x_343 = !lean_is_exclusive(x_316);
if (x_343 == 0)
{
x_337 = x_316;
x_338 = x_343;
goto block_342;
}
else
{
lean_inc(x_336);
lean_dec(x_316);
x_337 = lean_box(0);
x_338 = x_343;
goto block_342;
}
block_342:
{
lean_object* x_339; 
if (x_338 == 0)
{
x_339 = x_337;
goto block_340;
}
else
{
lean_object* x_341; 
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_336);
x_339 = x_341;
goto block_340;
}
block_340:
{
return x_339;
}
}
}
}
else
{
lean_object* x_344; 
x_344 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__11));
x_305 = x_312;
x_306 = x_313;
x_307 = x_344;
goto block_311;
}
}
}
block_378:
{
if (x_63 == 0)
{
uint8_t x_348; 
x_348 = l_List_isEmpty___redArg(x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_347);
lean_dec(x_346);
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_44);
x_349 = ((lean_object*)(l___private_Lean_Shell_0__Lean_shellMain___closed__10));
x_350 = l_IO_eprintln___at___00__private_Lean_Shell_0__Lean_shellMain_spec__1(x_349);
if (lean_obj_tag(x_350) == 0)
{
uint8_t x_351; lean_object* x_352; 
lean_dec_ref(x_350);
x_351 = 1;
x_352 = l___private_Lean_Shell_0__Lean_displayHelp(x_351);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; uint8_t x_354; uint8_t x_360; 
x_360 = !lean_is_exclusive(x_352);
if (x_360 == 0)
{
lean_object* x_361; 
x_361 = lean_ctor_get(x_352, 0);
lean_dec(x_361);
x_353 = x_352;
x_354 = x_360;
goto block_359;
}
else
{
lean_dec(x_352);
x_353 = lean_box(0);
x_354 = x_360;
goto block_359;
}
block_359:
{
lean_object* x_355; lean_object* x_356; 
x_355 = l___private_Lean_Shell_0__Lean_ShellOptions_process_liftIO___redArg___boxed__const__1;
if (x_354 == 0)
{
lean_ctor_set(x_353, 0, x_355);
x_356 = x_353;
goto block_357;
}
else
{
lean_object* x_358; 
x_358 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_358, 0, x_355);
x_356 = x_358;
goto block_357;
}
block_357:
{
return x_356;
}
}
}
else
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; uint8_t x_369; 
x_362 = lean_ctor_get(x_352, 0);
x_369 = !lean_is_exclusive(x_352);
if (x_369 == 0)
{
x_363 = x_352;
x_364 = x_369;
goto block_368;
}
else
{
lean_inc(x_362);
lean_dec(x_352);
x_363 = lean_box(0);
x_364 = x_369;
goto block_368;
}
block_368:
{
lean_object* x_365; 
if (x_364 == 0)
{
x_365 = x_363;
goto block_366;
}
else
{
lean_object* x_367; 
x_367 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_367, 0, x_362);
x_365 = x_367;
goto block_366;
}
block_366:
{
return x_365;
}
}
}
}
else
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint8_t x_377; 
x_370 = lean_ctor_get(x_350, 0);
x_377 = !lean_is_exclusive(x_350);
if (x_377 == 0)
{
x_371 = x_350;
x_372 = x_377;
goto block_376;
}
else
{
lean_inc(x_370);
lean_dec(x_350);
x_371 = lean_box(0);
x_372 = x_377;
goto block_376;
}
block_376:
{
lean_object* x_373; 
if (x_372 == 0)
{
x_373 = x_371;
goto block_374;
}
else
{
lean_object* x_375; 
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_370);
x_373 = x_375;
goto block_374;
}
block_374:
{
return x_373;
}
}
}
}
else
{
x_312 = x_346;
x_313 = x_347;
goto block_345;
}
}
else
{
x_312 = x_346;
x_313 = x_347;
goto block_345;
}
}
block_383:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_379; 
x_379 = lean_box(0);
x_346 = x_379;
x_347 = x_1;
goto block_378;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_1, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_1, 1);
lean_inc(x_381);
lean_dec_ref(x_1);
x_382 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_382, 0, x_380);
x_346 = x_382;
x_347 = x_381;
goto block_378;
}
}
block_399:
{
switch (x_46) {
case 0:
{
lean_dec_ref(x_45);
if (x_50 == 0)
{
goto block_383;
}
else
{
if (x_52 == 0)
{
goto block_383;
}
else
{
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_44);
if (x_49 == 0)
{
lean_object* x_384; 
x_384 = lean_array_mk(x_1);
x_24 = x_384;
goto block_43;
}
else
{
lean_object* x_385; lean_object* x_386; 
lean_dec(x_1);
x_385 = lean_get_stdin();
x_386 = l_IO_FS_Stream_lines(x_385);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
lean_dec_ref(x_386);
x_24 = x_387;
goto block_43;
}
else
{
lean_object* x_388; lean_object* x_389; uint8_t x_390; uint8_t x_395; 
x_388 = lean_ctor_get(x_386, 0);
x_395 = !lean_is_exclusive(x_386);
if (x_395 == 0)
{
x_389 = x_386;
x_390 = x_395;
goto block_394;
}
else
{
lean_inc(x_388);
lean_dec(x_386);
x_389 = lean_box(0);
x_390 = x_395;
goto block_394;
}
block_394:
{
lean_object* x_391; 
if (x_390 == 0)
{
x_391 = x_389;
goto block_392;
}
else
{
lean_object* x_393; 
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_388);
x_391 = x_393;
goto block_392;
}
block_392:
{
return x_391;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_396; lean_object* x_397; 
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_44);
lean_dec(x_1);
x_396 = lean_array_to_list(x_45);
x_397 = l_Lean_Server_Watchdog_watchdogMain(x_396);
return x_397;
}
default: 
{
lean_object* x_398; 
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_45);
lean_dec(x_1);
x_398 = l_Lean_Server_FileWorker_workerMain(x_44);
return x_398;
}
}
}
block_408:
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
x_400 = l___private_Lean_Shell_0__Lean_timeout;
x_401 = l_Lean_Option_get___at___00__private_Lean_Shell_0__Lean_shellMain_spec__4(x_44, x_400);
x_402 = lean_unsigned_to_nat(0u);
x_403 = lean_nat_dec_eq(x_401, x_402);
if (x_403 == 0)
{
size_t x_404; size_t x_405; size_t x_406; lean_object* x_407; 
x_404 = lean_usize_of_nat(x_401);
lean_dec(x_401);
x_405 = 1000;
x_406 = lean_usize_mul(x_404, x_405);
x_407 = lean_internal_set_max_heartbeat(x_406);
goto block_399;
}
else
{
lean_dec(x_401);
goto block_399;
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
