// Lean compiler output
// Module: Lake.Build.Actions
// Imports: public import Lake.Util.Log import Lake.Util.Proc import Lake.Util.FilePath import Lake.Util.IO import Init.Data.String.Search import Init.Data.String.TakeDrop import Init.System.Platform import Lean.CoreM import Lean.Compiler.Options
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern uint8_t l_System_Platform_isOSX;
lean_object* lean_io_getenv(lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_instToJsonModuleSetup_toJson(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
lean_object* l_Lake_mkCmdLog(lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_io_remove_file(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_compileLeanModule___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean exited with code "};
static const lean_object* l_Lake_compileLeanModule___lam__0___closed__0 = (const lean_object*)&l_Lake_compileLeanModule___lam__0___closed__0_value;
static const lean_string_object l_Lake_compileLeanModule___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stderr:\n"};
static const lean_object* l_Lake_compileLeanModule___lam__0___closed__1 = (const lean_object*)&l_Lake_compileLeanModule___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint32_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stdout:\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_compileLeanModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--setup"};
static const lean_object* l_Lake_compileLeanModule___closed__0 = (const lean_object*)&l_Lake_compileLeanModule___closed__0_value;
static lean_once_cell_t l_Lake_compileLeanModule___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileLeanModule___closed__1;
static const lean_string_object l_Lake_compileLeanModule___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--json"};
static const lean_object* l_Lake_compileLeanModule___closed__2 = (const lean_object*)&l_Lake_compileLeanModule___closed__2_value;
static const lean_ctor_object l_Lake_compileLeanModule___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_compileLeanModule___closed__3 = (const lean_object*)&l_Lake_compileLeanModule___closed__3_value;
static const lean_string_object l_Lake_compileLeanModule___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LEAN_PATH"};
static const lean_object* l_Lake_compileLeanModule___closed__4 = (const lean_object*)&l_Lake_compileLeanModule___closed__4_value;
static const lean_string_object l_Lake_compileLeanModule___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_compileLeanModule___closed__5 = (const lean_object*)&l_Lake_compileLeanModule___closed__5_value;
static const lean_string_object l_Lake_compileLeanModule___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "failed to execute '"};
static const lean_object* l_Lake_compileLeanModule___closed__6 = (const lean_object*)&l_Lake_compileLeanModule___closed__6_value;
static const lean_string_object l_Lake_compileLeanModule___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "': "};
static const lean_object* l_Lake_compileLeanModule___closed__7 = (const lean_object*)&l_Lake_compileLeanModule___closed__7_value;
static const lean_string_object l_Lake_compileLeanModule___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-b"};
static const lean_object* l_Lake_compileLeanModule___closed__8 = (const lean_object*)&l_Lake_compileLeanModule___closed__8_value;
static lean_once_cell_t l_Lake_compileLeanModule___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileLeanModule___closed__9;
static const lean_string_object l_Lake_compileLeanModule___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-c"};
static const lean_object* l_Lake_compileLeanModule___closed__10 = (const lean_object*)&l_Lake_compileLeanModule___closed__10_value;
static lean_once_cell_t l_Lake_compileLeanModule___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileLeanModule___closed__11;
static const lean_string_object l_Lake_compileLeanModule___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-i"};
static const lean_object* l_Lake_compileLeanModule___closed__12 = (const lean_object*)&l_Lake_compileLeanModule___closed__12_value;
static lean_once_cell_t l_Lake_compileLeanModule___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileLeanModule___closed__13;
static const lean_string_object l_Lake_compileLeanModule___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-o"};
static const lean_object* l_Lake_compileLeanModule___closed__14 = (const lean_object*)&l_Lake_compileLeanModule___closed__14_value;
static lean_once_cell_t l_Lake_compileLeanModule___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileLeanModule___closed__15;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_compileO___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileO___closed__0;
static lean_once_cell_t l_Lake_compileO___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileO___closed__1;
static const lean_array_object l_Lake_compileO___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_compileO___closed__2 = (const lean_object*)&l_Lake_compileO___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\"\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_mkArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rsp"};
static const lean_object* l_Lake_mkArgs___closed__0 = (const lean_object*)&l_Lake_mkArgs___closed__0_value;
static const lean_string_object l_Lake_mkArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Lake_mkArgs___closed__1 = (const lean_object*)&l_Lake_mkArgs___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_compileStaticLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rcs"};
static const lean_object* l_Lake_compileStaticLib___closed__0 = (const lean_object*)&l_Lake_compileStaticLib___closed__0_value;
static const lean_array_object l_Lake_compileStaticLib___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_compileStaticLib___closed__0_value)}};
static const lean_object* l_Lake_compileStaticLib___closed__1 = (const lean_object*)&l_Lake_compileStaticLib___closed__1_value;
static const lean_string_object l_Lake_compileStaticLib___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--thin"};
static const lean_object* l_Lake_compileStaticLib___closed__2 = (const lean_object*)&l_Lake_compileStaticLib___closed__2_value;
static lean_once_cell_t l_Lake_compileStaticLib___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileStaticLib___closed__3;
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "MACOSX_DEPLOYMENT_TARGET"};
static const lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0 = (const lean_object*)&l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0_value;
static const lean_string_object l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "99.0"};
static const lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1 = (const lean_object*)&l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1_value;
static const lean_ctor_object l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1_value)}};
static const lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2 = (const lean_object*)&l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2_value;
static const lean_ctor_object l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0_value),((lean_object*)&l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2_value)}};
static const lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3 = (const lean_object*)&l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3_value;
static const lean_array_object l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3_value)}};
static const lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4 = (const lean_object*)&l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___boxed(lean_object*);
static const lean_string_object l_Lake_compileSharedLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "-shared"};
static const lean_object* l_Lake_compileSharedLib___closed__0 = (const lean_object*)&l_Lake_compileSharedLib___closed__0_value;
static lean_once_cell_t l_Lake_compileSharedLib___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileSharedLib___closed__1;
static lean_once_cell_t l_Lake_compileSharedLib___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileSharedLib___closed__2;
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-H"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_download___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "curl"};
static const lean_object* l_Lake_download___closed__0 = (const lean_object*)&l_Lake_download___closed__0_value;
static const lean_string_object l_Lake_download___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-s"};
static const lean_object* l_Lake_download___closed__1 = (const lean_object*)&l_Lake_download___closed__1_value;
static const lean_string_object l_Lake_download___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-S"};
static const lean_object* l_Lake_download___closed__2 = (const lean_object*)&l_Lake_download___closed__2_value;
static const lean_string_object l_Lake_download___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-f"};
static const lean_object* l_Lake_download___closed__3 = (const lean_object*)&l_Lake_download___closed__3_value;
static const lean_string_object l_Lake_download___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-L"};
static const lean_object* l_Lake_download___closed__4 = (const lean_object*)&l_Lake_download___closed__4_value;
static lean_once_cell_t l_Lake_download___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_download___closed__5;
static lean_once_cell_t l_Lake_download___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_download___closed__6;
static lean_once_cell_t l_Lake_download___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_download___closed__7;
static lean_once_cell_t l_Lake_download___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_download___closed__8;
LEAN_EXPORT lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_untar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tar"};
static const lean_object* l_Lake_untar___closed__0 = (const lean_object*)&l_Lake_untar___closed__0_value;
static const lean_string_object l_Lake_untar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-C"};
static const lean_object* l_Lake_untar___closed__1 = (const lean_object*)&l_Lake_untar___closed__1_value;
static const lean_string_object l_Lake_untar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "-xvv"};
static const lean_object* l_Lake_untar___closed__2 = (const lean_object*)&l_Lake_untar___closed__2_value;
static lean_once_cell_t l_Lake_untar___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_untar___closed__3;
LEAN_EXPORT lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "--exclude="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_tar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_tar___closed__0 = (const lean_object*)&l_Lake_tar___closed__0_value;
static lean_once_cell_t l_Lake_tar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_tar___closed__1;
static const lean_string_object l_Lake_tar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "COPYFILE_DISABLE"};
static const lean_object* l_Lake_tar___closed__2 = (const lean_object*)&l_Lake_tar___closed__2_value;
static const lean_string_object l_Lake_tar___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lake_tar___closed__3 = (const lean_object*)&l_Lake_tar___closed__3_value;
static const lean_ctor_object l_Lake_tar___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_tar___closed__3_value)}};
static const lean_object* l_Lake_tar___closed__4 = (const lean_object*)&l_Lake_tar___closed__4_value;
static const lean_ctor_object l_Lake_tar___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_tar___closed__2_value),((lean_object*)&l_Lake_tar___closed__4_value)}};
static const lean_object* l_Lake_tar___closed__5 = (const lean_object*)&l_Lake_tar___closed__5_value;
static const lean_array_object l_Lake_tar___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_tar___closed__5_value)}};
static const lean_object* l_Lake_tar___closed__6 = (const lean_object*)&l_Lake_tar___closed__6_value;
static const lean_string_object l_Lake_tar___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "-cvv"};
static const lean_object* l_Lake_tar___closed__7 = (const lean_object*)&l_Lake_tar___closed__7_value;
static const lean_array_object l_Lake_tar___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_tar___closed__7_value)}};
static const lean_object* l_Lake_tar___closed__8 = (const lean_object*)&l_Lake_tar___closed__8_value;
static const lean_string_object l_Lake_tar___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-z"};
static const lean_object* l_Lake_tar___closed__9 = (const lean_object*)&l_Lake_tar___closed__9_value;
static lean_once_cell_t l_Lake_tar___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_tar___closed__10;
LEAN_EXPORT lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0(lean_object* v_s_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0));
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___boxed(lean_object* v_s_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0(v_s_5_);
lean_dec_ref(v_s_5_);
return v_res_6_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2(lean_object* v_opts_7_, lean_object* v_opt_8_){
_start:
{
lean_object* v_name_9_; lean_object* v_defValue_10_; lean_object* v_map_11_; lean_object* v___x_12_; 
v_name_9_ = lean_ctor_get(v_opt_8_, 0);
v_defValue_10_ = lean_ctor_get(v_opt_8_, 1);
v_map_11_ = lean_ctor_get(v_opts_7_, 0);
v___x_12_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_11_, v_name_9_);
if (lean_obj_tag(v___x_12_) == 0)
{
uint8_t v___x_13_; 
v___x_13_ = lean_unbox(v_defValue_10_);
return v___x_13_;
}
else
{
lean_object* v_val_14_; 
v_val_14_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_val_14_);
lean_dec_ref(v___x_12_);
if (lean_obj_tag(v_val_14_) == 1)
{
uint8_t v_v_15_; 
v_v_15_ = lean_ctor_get_uint8(v_val_14_, 0);
lean_dec_ref(v_val_14_);
return v_v_15_;
}
else
{
uint8_t v___x_16_; 
lean_dec(v_val_14_);
v___x_16_ = lean_unbox(v_defValue_10_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2___boxed(lean_object* v_opts_17_, lean_object* v_opt_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2(v_opts_17_, v_opt_18_);
lean_dec_ref(v_opt_18_);
lean_dec_ref(v_opts_17_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint32_t v_exitCode_23_, uint8_t v___y_24_, lean_object* v_ir_x3f_25_, lean_object* v_c_x3f_26_, lean_object* v_setupFile_27_, lean_object* v___x_28_, lean_object* v_leanir_29_, lean_object* v___x_30_, lean_object* v___x_31_, uint8_t v___x_32_, uint8_t v___x_33_, lean_object* v_olean_x3f_34_, lean_object* v_stderr_35_, lean_object* v_____r_36_, lean_object* v___y_37_){
_start:
{
lean_object* v___y_40_; lean_object* v___y_44_; lean_object* v___y_45_; lean_object* v___y_48_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_106_ = lean_string_utf8_byte_size(v_stderr_35_);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_nat_dec_eq(v___x_106_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_109_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__1));
v___x_110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_110_, 0, v_stderr_35_);
lean_ctor_set(v___x_110_, 1, v___x_107_);
lean_ctor_set(v___x_110_, 2, v___x_106_);
v___x_111_ = l_String_Slice_trimAscii(v___x_110_);
v___x_112_ = l_String_Slice_toString(v___x_111_);
lean_dec_ref(v___x_111_);
v___x_113_ = lean_string_append(v___x_109_, v___x_112_);
lean_dec_ref(v___x_112_);
v___x_114_ = 1;
v___x_115_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*1, v___x_114_);
v___x_116_ = lean_array_push(v___y_37_, v___x_115_);
v___y_48_ = v___x_116_;
goto v___jp_47_;
}
else
{
lean_dec_ref(v_stderr_35_);
v___y_48_ = v___y_37_;
goto v___jp_47_;
}
v___jp_39_:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_box(0);
v___x_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___y_40_);
return v___x_42_;
}
v___jp_43_:
{
lean_object* v___x_46_; 
v___x_46_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_46_, 0, v___y_44_);
lean_ctor_set(v___x_46_, 1, v___y_45_);
return v___x_46_;
}
v___jp_47_:
{
uint32_t v___x_49_; uint8_t v___x_50_; 
v___x_49_ = 0;
v___x_50_ = lean_uint32_dec_eq(v_exitCode_23_, v___x_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec_ref(v___x_31_);
lean_dec(v___x_30_);
lean_dec_ref(v_leanir_29_);
lean_dec_ref(v___x_28_);
lean_dec_ref(v_setupFile_27_);
lean_dec(v_c_x3f_26_);
lean_dec(v_ir_x3f_25_);
v___x_51_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__0));
v___x_52_ = lean_uint32_to_nat(v_exitCode_23_);
v___x_53_ = l_Nat_reprFast(v___x_52_);
v___x_54_ = lean_string_append(v___x_51_, v___x_53_);
lean_dec_ref(v___x_53_);
v___x_55_ = 3;
v___x_56_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_56_, 0, v___x_54_);
lean_ctor_set_uint8(v___x_56_, sizeof(void*)*1, v___x_55_);
v___x_57_ = lean_array_get_size(v___y_48_);
v___x_58_ = lean_array_push(v___y_48_, v___x_56_);
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_57_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
return v___x_59_;
}
else
{
if (v___y_24_ == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; 
lean_dec_ref(v___x_31_);
lean_dec(v___x_30_);
lean_dec_ref(v_leanir_29_);
lean_dec_ref(v___x_28_);
lean_dec_ref(v_setupFile_27_);
lean_dec(v_c_x3f_26_);
lean_dec(v_ir_x3f_25_);
v___x_60_ = lean_box(0);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___y_48_);
return v___x_61_;
}
else
{
if (lean_obj_tag(v_ir_x3f_25_) == 1)
{
if (lean_obj_tag(v_c_x3f_26_) == 1)
{
lean_object* v_val_62_; lean_object* v_val_63_; lean_object* v___x_64_; 
v_val_62_ = lean_ctor_get(v_ir_x3f_25_, 0);
lean_inc_n(v_val_62_, 2);
lean_dec_ref(v_ir_x3f_25_);
v_val_63_ = lean_ctor_get(v_c_x3f_26_, 0);
lean_inc(v_val_63_);
lean_dec_ref(v_c_x3f_26_);
v___x_64_ = l_Lake_createParentDirs(v_val_62_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v___x_65_; 
lean_dec_ref(v___x_64_);
lean_inc(v_val_63_);
v___x_65_ = l_Lake_createParentDirs(v_val_63_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec_ref(v___x_65_);
v___x_66_ = lean_unsigned_to_nat(3u);
v___x_67_ = lean_mk_empty_array_with_capacity(v___x_66_);
v___x_68_ = lean_array_push(v___x_67_, v_setupFile_27_);
v___x_69_ = lean_array_push(v___x_68_, v_val_62_);
v___x_70_ = lean_array_push(v___x_69_, v_val_63_);
v___x_71_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_71_, 0, v___x_28_);
lean_ctor_set(v___x_71_, 1, v_leanir_29_);
lean_ctor_set(v___x_71_, 2, v___x_70_);
lean_ctor_set(v___x_71_, 3, v___x_30_);
lean_ctor_set(v___x_71_, 4, v___x_31_);
lean_ctor_set_uint8(v___x_71_, sizeof(void*)*5, v___x_32_);
lean_ctor_set_uint8(v___x_71_, sizeof(void*)*5 + 1, v___x_33_);
v___x_72_ = l_Lake_proc(v___x_71_, v___x_33_, v___y_48_);
if (lean_obj_tag(v___x_72_) == 0)
{
return v___x_72_;
}
else
{
if (lean_obj_tag(v_olean_x3f_34_) == 1)
{
lean_object* v_a_73_; lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_89_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
v_a_74_ = lean_ctor_get(v___x_72_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_89_ == 0)
{
v___x_76_ = v___x_72_;
v_isShared_77_ = v_isSharedCheck_89_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_inc(v_a_73_);
lean_dec(v___x_72_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_89_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v_val_78_; lean_object* v___x_79_; 
v_val_78_ = lean_ctor_get(v_olean_x3f_34_, 0);
v___x_79_ = l_Lake_removeFileIfExists(v_val_78_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_dec_ref(v___x_79_);
lean_del_object(v___x_76_);
v___y_44_ = v_a_73_;
v___y_45_ = v_a_74_;
goto v___jp_43_;
}
else
{
lean_object* v_a_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
lean_dec(v_a_73_);
v_a_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_a_80_);
lean_dec_ref(v___x_79_);
v___x_81_ = lean_io_error_to_string(v_a_80_);
v___x_82_ = 3;
v___x_83_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1, v___x_82_);
v___x_84_ = lean_array_get_size(v_a_74_);
v___x_85_ = lean_array_push(v_a_74_, v___x_83_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v___x_85_);
lean_ctor_set(v___x_76_, 0, v___x_84_);
v___x_87_ = v___x_76_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
else
{
lean_object* v_a_90_; lean_object* v_a_91_; 
v_a_90_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_90_);
v_a_91_ = lean_ctor_get(v___x_72_, 1);
lean_inc(v_a_91_);
lean_dec_ref(v___x_72_);
v___y_44_ = v_a_90_;
v___y_45_ = v_a_91_;
goto v___jp_43_;
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec(v_val_63_);
lean_dec(v_val_62_);
lean_dec_ref(v___x_31_);
lean_dec(v___x_30_);
lean_dec_ref(v_leanir_29_);
lean_dec_ref(v___x_28_);
lean_dec_ref(v_setupFile_27_);
v_a_92_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_92_);
lean_dec_ref(v___x_65_);
v___x_93_ = lean_io_error_to_string(v_a_92_);
v___x_94_ = 3;
v___x_95_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_94_);
v___x_96_ = lean_array_get_size(v___y_48_);
v___x_97_ = lean_array_push(v___y_48_, v___x_95_);
v___x_98_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
return v___x_98_;
}
}
else
{
lean_object* v_a_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_val_63_);
lean_dec(v_val_62_);
lean_dec_ref(v___x_31_);
lean_dec(v___x_30_);
lean_dec_ref(v_leanir_29_);
lean_dec_ref(v___x_28_);
lean_dec_ref(v_setupFile_27_);
v_a_99_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_a_99_);
lean_dec_ref(v___x_64_);
v___x_100_ = lean_io_error_to_string(v_a_99_);
v___x_101_ = 3;
v___x_102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*1, v___x_101_);
v___x_103_ = lean_array_get_size(v___y_48_);
v___x_104_ = lean_array_push(v___y_48_, v___x_102_);
v___x_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
return v___x_105_;
}
}
else
{
lean_dec_ref(v_ir_x3f_25_);
lean_dec_ref(v___x_31_);
lean_dec(v___x_30_);
lean_dec_ref(v_leanir_29_);
lean_dec_ref(v___x_28_);
lean_dec_ref(v_setupFile_27_);
lean_dec(v_c_x3f_26_);
v___y_40_ = v___y_48_;
goto v___jp_39_;
}
}
else
{
lean_dec_ref(v___x_31_);
lean_dec(v___x_30_);
lean_dec_ref(v_leanir_29_);
lean_dec_ref(v___x_28_);
lean_dec_ref(v_setupFile_27_);
lean_dec(v_c_x3f_26_);
lean_dec(v_ir_x3f_25_);
v___y_40_ = v___y_48_;
goto v___jp_39_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object* v_exitCode_117_, lean_object* v___y_118_, lean_object* v_ir_x3f_119_, lean_object* v_c_x3f_120_, lean_object* v_setupFile_121_, lean_object* v___x_122_, lean_object* v_leanir_123_, lean_object* v___x_124_, lean_object* v___x_125_, lean_object* v___x_126_, lean_object* v___x_127_, lean_object* v_olean_x3f_128_, lean_object* v_stderr_129_, lean_object* v_____r_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
uint32_t v_exitCode_boxed_133_; uint8_t v___y_30459__boxed_134_; uint8_t v___x_30463__boxed_135_; uint8_t v___x_30464__boxed_136_; lean_object* v_res_137_; 
v_exitCode_boxed_133_ = lean_unbox_uint32(v_exitCode_117_);
lean_dec(v_exitCode_117_);
v___y_30459__boxed_134_ = lean_unbox(v___y_118_);
v___x_30463__boxed_135_ = lean_unbox(v___x_126_);
v___x_30464__boxed_136_ = lean_unbox(v___x_127_);
v_res_137_ = l_Lake_compileLeanModule___lam__0(v_exitCode_boxed_133_, v___y_30459__boxed_134_, v_ir_x3f_119_, v_c_x3f_120_, v_setupFile_121_, v___x_122_, v_leanir_123_, v___x_124_, v___x_125_, v___x_30463__boxed_135_, v___x_30464__boxed_136_, v_olean_x3f_128_, v_stderr_129_, v_____r_130_, v___y_131_);
lean_dec(v_olean_x3f_128_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(lean_object* v_a_138_, lean_object* v_b_139_, lean_object* v_relLeanFile_140_, lean_object* v_____r_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_a_145_; lean_object* v_toBaseMessage_147_; uint8_t v_isSilent_148_; 
v_toBaseMessage_147_ = lean_ctor_get(v_a_138_, 0);
lean_inc_ref(v_toBaseMessage_147_);
v_isSilent_148_ = lean_ctor_get_uint8(v_toBaseMessage_147_, sizeof(void*)*5 + 2);
if (v_isSilent_148_ == 0)
{
lean_object* v_kind_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_173_; 
v_kind_149_ = lean_ctor_get(v_a_138_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v_a_138_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; 
v_unused_174_ = lean_ctor_get(v_a_138_, 0);
lean_dec(v_unused_174_);
v___x_151_ = v_a_138_;
v_isShared_152_ = v_isSharedCheck_173_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_kind_149_);
lean_dec(v_a_138_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_173_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v_pos_153_; lean_object* v_endPos_154_; uint8_t v_keepFullRange_155_; uint8_t v_severity_156_; lean_object* v_caption_157_; lean_object* v_data_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_171_; 
v_pos_153_ = lean_ctor_get(v_toBaseMessage_147_, 1);
v_endPos_154_ = lean_ctor_get(v_toBaseMessage_147_, 2);
v_keepFullRange_155_ = lean_ctor_get_uint8(v_toBaseMessage_147_, sizeof(void*)*5);
v_severity_156_ = lean_ctor_get_uint8(v_toBaseMessage_147_, sizeof(void*)*5 + 1);
v_caption_157_ = lean_ctor_get(v_toBaseMessage_147_, 3);
v_data_158_ = lean_ctor_get(v_toBaseMessage_147_, 4);
v_isSharedCheck_171_ = !lean_is_exclusive(v_toBaseMessage_147_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; 
v_unused_172_ = lean_ctor_get(v_toBaseMessage_147_, 0);
lean_dec(v_unused_172_);
v___x_160_ = v_toBaseMessage_147_;
v_isShared_161_ = v_isSharedCheck_171_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_data_158_);
lean_inc(v_caption_157_);
lean_inc(v_endPos_154_);
lean_inc(v_pos_153_);
lean_dec(v_toBaseMessage_147_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_171_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = l_Lake_mkRelPathString(v_relLeanFile_140_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_pos_153_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v_endPos_154_);
lean_ctor_set(v_reuseFailAlloc_170_, 3, v_caption_157_);
lean_ctor_set(v_reuseFailAlloc_170_, 4, v_data_158_);
lean_ctor_set_uint8(v_reuseFailAlloc_170_, sizeof(void*)*5, v_keepFullRange_155_);
lean_ctor_set_uint8(v_reuseFailAlloc_170_, sizeof(void*)*5 + 1, v_severity_156_);
lean_ctor_set_uint8(v_reuseFailAlloc_170_, sizeof(void*)*5 + 2, v_isSilent_148_);
v___x_164_ = v_reuseFailAlloc_170_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_166_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_164_);
v___x_166_ = v___x_151_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_kind_149_);
v___x_166_ = v_reuseFailAlloc_169_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = l_Lake_LogEntry_ofSerialMessage(v___x_166_);
v___x_168_ = lean_array_push(v___y_142_, v___x_167_);
v_a_145_ = v___x_168_;
goto v___jp_144_;
}
}
}
}
}
else
{
lean_dec_ref(v_toBaseMessage_147_);
lean_dec_ref(v_relLeanFile_140_);
lean_dec_ref(v_a_138_);
v_a_145_ = v___y_142_;
goto v___jp_144_;
}
v___jp_144_:
{
lean_object* v___x_146_; 
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v_b_139_);
lean_ctor_set(v___x_146_, 1, v_a_145_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0___boxed(lean_object* v_a_175_, lean_object* v_b_176_, lean_object* v_relLeanFile_177_, lean_object* v_____r_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(v_a_175_, v_b_176_, v_relLeanFile_177_, v_____r_178_, v___y_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(lean_object* v_relLeanFile_184_, lean_object* v___x_185_, lean_object* v___x_186_, lean_object* v___x_187_, lean_object* v_a_188_, lean_object* v_b_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___y_193_; lean_object* v___y_194_; uint8_t v___y_195_; lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v_it_216_; lean_object* v_startInclusive_217_; lean_object* v_endExclusive_218_; 
if (lean_obj_tag(v_a_188_) == 0)
{
lean_object* v_currPos_236_; lean_object* v_searcher_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_263_; 
v_currPos_236_ = lean_ctor_get(v_a_188_, 0);
v_searcher_237_ = lean_ctor_get(v_a_188_, 1);
v_isSharedCheck_263_ = !lean_is_exclusive(v_a_188_);
if (v_isSharedCheck_263_ == 0)
{
v___x_239_ = v_a_188_;
v_isShared_240_ = v_isSharedCheck_263_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_searcher_237_);
lean_inc(v_currPos_236_);
lean_dec(v_a_188_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_263_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_startInclusive_241_; lean_object* v_endExclusive_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_startInclusive_241_ = lean_ctor_get(v___x_186_, 1);
v_endExclusive_242_ = lean_ctor_get(v___x_186_, 2);
v___x_243_ = lean_nat_sub(v_endExclusive_242_, v_startInclusive_241_);
v___x_244_ = lean_nat_dec_eq(v_searcher_237_, v___x_243_);
lean_dec(v___x_243_);
if (v___x_244_ == 0)
{
uint32_t v___x_245_; uint32_t v___x_246_; uint8_t v___x_247_; 
v___x_245_ = 10;
v___x_246_ = lean_string_utf8_get_fast(v___x_185_, v_searcher_237_);
v___x_247_ = lean_uint32_dec_eq(v___x_246_, v___x_245_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = lean_string_utf8_next_fast(v___x_185_, v_searcher_237_);
lean_dec(v_searcher_237_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_248_);
v___x_250_ = v___x_239_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_currPos_236_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_248_);
v___x_250_ = v_reuseFailAlloc_252_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
v_a_188_ = v___x_250_;
goto _start;
}
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_slice_256_; lean_object* v_nextIt_258_; 
v___x_253_ = lean_string_utf8_next_fast(v___x_185_, v_searcher_237_);
v___x_254_ = lean_nat_sub(v___x_253_, v_searcher_237_);
v___x_255_ = lean_nat_add(v_searcher_237_, v___x_254_);
lean_dec(v___x_254_);
v_slice_256_ = l_String_Slice_subslice_x21(v___x_186_, v_currPos_236_, v_searcher_237_);
lean_inc(v___x_255_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_255_);
lean_ctor_set(v___x_239_, 0, v___x_255_);
v_nextIt_258_ = v___x_239_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_255_);
v_nextIt_258_ = v_reuseFailAlloc_261_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v_startInclusive_259_; lean_object* v_endExclusive_260_; 
v_startInclusive_259_ = lean_ctor_get(v_slice_256_, 0);
lean_inc(v_startInclusive_259_);
v_endExclusive_260_ = lean_ctor_get(v_slice_256_, 1);
lean_inc(v_endExclusive_260_);
lean_dec_ref(v_slice_256_);
v_it_216_ = v_nextIt_258_;
v_startInclusive_217_ = v_startInclusive_259_;
v_endExclusive_218_ = v_endExclusive_260_;
goto v___jp_215_;
}
}
}
else
{
lean_object* v___x_262_; 
lean_del_object(v___x_239_);
lean_dec(v_searcher_237_);
v___x_262_ = lean_box(1);
lean_inc(v___x_187_);
v_it_216_ = v___x_262_;
v_startInclusive_217_ = v_currPos_236_;
v_endExclusive_218_ = v___x_187_;
goto v___jp_215_;
}
}
}
else
{
lean_object* v___x_264_; 
lean_dec(v___x_187_);
lean_dec_ref(v_relLeanFile_184_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_b_189_);
lean_ctor_set(v___x_264_, 1, v___y_190_);
return v___x_264_;
}
v___jp_192_:
{
if (v___y_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_string_append(v_b_189_, v___y_194_);
lean_dec_ref(v___y_194_);
v___x_197_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0));
v___x_198_ = lean_string_append(v___x_196_, v___x_197_);
v_a_188_ = v___y_193_;
v_b_189_ = v___x_198_;
goto _start;
}
else
{
lean_dec_ref(v___y_194_);
v_a_188_ = v___y_193_;
goto _start;
}
}
v___jp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_204_ = lean_string_utf8_byte_size(v_b_189_);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_nat_dec_eq(v___x_204_, v___x_205_);
if (v___x_206_ == 0)
{
v___y_193_ = v___y_202_;
v___y_194_ = v___y_203_;
v___y_195_ = v___x_206_;
goto v___jp_192_;
}
else
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_string_utf8_byte_size(v___y_203_);
v___x_208_ = lean_nat_dec_eq(v___x_207_, v___x_205_);
v___y_193_ = v___y_202_;
v___y_194_ = v___y_203_;
v___y_195_ = v___x_208_;
goto v___jp_192_;
}
}
v___jp_209_:
{
if (lean_obj_tag(v___y_211_) == 0)
{
lean_object* v_a_212_; lean_object* v_a_213_; 
v_a_212_ = lean_ctor_get(v___y_211_, 0);
lean_inc(v_a_212_);
v_a_213_ = lean_ctor_get(v___y_211_, 1);
lean_inc(v_a_213_);
lean_dec_ref(v___y_211_);
v_a_188_ = v___y_210_;
v_b_189_ = v_a_212_;
v___y_190_ = v_a_213_;
goto _start;
}
else
{
lean_dec(v___y_210_);
lean_dec(v___x_187_);
lean_dec_ref(v_relLeanFile_184_);
return v___y_211_;
}
}
v___jp_215_:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_string_utf8_extract(v___x_185_, v_startInclusive_217_, v_endExclusive_218_);
lean_dec(v_endExclusive_218_);
lean_dec(v_startInclusive_217_);
lean_inc_ref(v___x_219_);
v___x_220_ = l_Lean_Json_parse(v___x_219_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_dec_ref(v___x_220_);
v___y_202_ = v_it_216_;
v___y_203_ = v___x_219_;
goto v___jp_201_;
}
else
{
lean_object* v_a_221_; lean_object* v___x_222_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref(v___x_220_);
v___x_222_ = l_Lean_instFromJsonSerialMessage_fromJson(v_a_221_);
if (lean_obj_tag(v___x_222_) == 1)
{
lean_object* v_a_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
lean_dec_ref(v___x_219_);
v_a_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_223_);
lean_dec_ref(v___x_222_);
v___x_224_ = lean_string_utf8_byte_size(v_b_189_);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_nat_dec_eq(v___x_224_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_227_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1));
v___x_228_ = lean_string_append(v___x_227_, v_b_189_);
v___x_229_ = 1;
v___x_230_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*1, v___x_229_);
v___x_231_ = lean_box(0);
v___x_232_ = lean_array_push(v___y_190_, v___x_230_);
lean_inc_ref(v_relLeanFile_184_);
v___x_233_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(v_a_223_, v_b_189_, v_relLeanFile_184_, v___x_231_, v___x_232_);
v___y_210_ = v_it_216_;
v___y_211_ = v___x_233_;
goto v___jp_209_;
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_box(0);
lean_inc_ref(v_relLeanFile_184_);
v___x_235_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(v_a_223_, v_b_189_, v_relLeanFile_184_, v___x_234_, v___y_190_);
v___y_210_ = v_it_216_;
v___y_211_ = v___x_235_;
goto v___jp_209_;
}
}
else
{
lean_dec_ref(v___x_222_);
v___y_202_ = v_it_216_;
v___y_203_ = v___x_219_;
goto v___jp_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___boxed(lean_object* v_relLeanFile_265_, lean_object* v___x_266_, lean_object* v___x_267_, lean_object* v___x_268_, lean_object* v_a_269_, lean_object* v_b_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(v_relLeanFile_265_, v___x_266_, v___x_267_, v___x_268_, v_a_269_, v_b_270_, v___y_271_);
lean_dec_ref(v___x_267_);
lean_dec_ref(v___x_266_);
return v_res_273_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__1(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_275_ = ((lean_object*)(l_Lake_compileLeanModule___closed__0));
v___x_276_ = lean_unsigned_to_nat(2u);
v___x_277_ = lean_mk_empty_array_with_capacity(v___x_276_);
v___x_278_ = lean_array_push(v___x_277_, v___x_275_);
return v___x_278_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__9(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_287_ = ((lean_object*)(l_Lake_compileLeanModule___closed__8));
v___x_288_ = lean_unsigned_to_nat(2u);
v___x_289_ = lean_mk_empty_array_with_capacity(v___x_288_);
v___x_290_ = lean_array_push(v___x_289_, v___x_287_);
return v___x_290_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__11(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = ((lean_object*)(l_Lake_compileLeanModule___closed__10));
v___x_293_ = lean_unsigned_to_nat(2u);
v___x_294_ = lean_mk_empty_array_with_capacity(v___x_293_);
v___x_295_ = lean_array_push(v___x_294_, v___x_292_);
return v___x_295_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__13(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_297_ = ((lean_object*)(l_Lake_compileLeanModule___closed__12));
v___x_298_ = lean_unsigned_to_nat(2u);
v___x_299_ = lean_mk_empty_array_with_capacity(v___x_298_);
v___x_300_ = lean_array_push(v___x_299_, v___x_297_);
return v___x_300_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__15(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_302_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_303_ = lean_unsigned_to_nat(2u);
v___x_304_ = lean_mk_empty_array_with_capacity(v___x_303_);
v___x_305_ = lean_array_push(v___x_304_, v___x_302_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object* v_leanFile_306_, lean_object* v_relLeanFile_307_, lean_object* v_setup_308_, lean_object* v_setupFile_309_, lean_object* v_arts_310_, lean_object* v_leanArgs_311_, lean_object* v_leanPath_312_, lean_object* v_lean_313_, lean_object* v_leanir_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___y_318_; lean_object* v_a_319_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v_olean_x3f_325_; lean_object* v_ilean_x3f_326_; lean_object* v_ir_x3f_327_; lean_object* v_c_x3f_328_; lean_object* v_bc_x3f_329_; uint8_t v___y_331_; lean_object* v_args_332_; lean_object* v___y_333_; lean_object* v___y_421_; uint8_t v___y_422_; lean_object* v_args_423_; lean_object* v___y_437_; lean_object* v___y_438_; uint8_t v___y_439_; lean_object* v_args_453_; lean_object* v___y_454_; lean_object* v_args_461_; lean_object* v___y_462_; lean_object* v_args_475_; 
v_olean_x3f_325_ = lean_ctor_get(v_arts_310_, 1);
lean_inc(v_olean_x3f_325_);
v_ilean_x3f_326_ = lean_ctor_get(v_arts_310_, 4);
lean_inc(v_ilean_x3f_326_);
v_ir_x3f_327_ = lean_ctor_get(v_arts_310_, 5);
lean_inc(v_ir_x3f_327_);
v_c_x3f_328_ = lean_ctor_get(v_arts_310_, 6);
lean_inc(v_c_x3f_328_);
v_bc_x3f_329_ = lean_ctor_get(v_arts_310_, 7);
lean_inc(v_bc_x3f_329_);
lean_dec_ref(v_arts_310_);
v_args_475_ = lean_array_push(v_leanArgs_311_, v_leanFile_306_);
if (lean_obj_tag(v_olean_x3f_325_) == 1)
{
lean_object* v_val_476_; lean_object* v___x_477_; 
v_val_476_ = lean_ctor_get(v_olean_x3f_325_, 0);
lean_inc(v_val_476_);
v___x_477_ = l_Lake_createParentDirs(v_val_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec_ref(v___x_477_);
v___x_478_ = lean_obj_once(&l_Lake_compileLeanModule___closed__15, &l_Lake_compileLeanModule___closed__15_once, _init_l_Lake_compileLeanModule___closed__15);
lean_inc(v_val_476_);
v___x_479_ = lean_array_push(v___x_478_, v_val_476_);
v___x_480_ = l_Array_append___redArg(v_args_475_, v___x_479_);
lean_dec_ref(v___x_479_);
v_args_461_ = v___x_480_;
v___y_462_ = v_a_315_;
goto v___jp_460_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_482_; uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec_ref(v_olean_x3f_325_);
lean_dec_ref(v_args_475_);
lean_dec(v_bc_x3f_329_);
lean_dec(v_c_x3f_328_);
lean_dec(v_ir_x3f_327_);
lean_dec(v_ilean_x3f_326_);
lean_dec_ref(v_leanir_314_);
lean_dec_ref(v_lean_313_);
lean_dec(v_leanPath_312_);
lean_dec_ref(v_setupFile_309_);
lean_dec_ref(v_setup_308_);
lean_dec_ref(v_relLeanFile_307_);
v_a_481_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_481_);
lean_dec_ref(v___x_477_);
v___x_482_ = lean_io_error_to_string(v_a_481_);
v___x_483_ = 3;
v___x_484_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*1, v___x_483_);
v___x_485_ = lean_array_get_size(v_a_315_);
v___x_486_ = lean_array_push(v_a_315_, v___x_484_);
v___x_487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
return v___x_487_;
}
}
else
{
v_args_461_ = v_args_475_;
v___y_462_ = v_a_315_;
goto v___jp_460_;
}
v___jp_317_:
{
lean_object* v___x_320_; 
v___x_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_320_, 0, v___y_318_);
lean_ctor_set(v___x_320_, 1, v_a_319_);
return v___x_320_;
}
v___jp_321_:
{
if (lean_obj_tag(v___y_323_) == 0)
{
lean_dec(v___y_322_);
return v___y_323_;
}
else
{
lean_object* v_a_324_; 
v_a_324_ = lean_ctor_get(v___y_323_, 1);
lean_inc(v_a_324_);
lean_dec_ref(v___y_323_);
v___y_318_ = v___y_322_;
v_a_319_ = v_a_324_;
goto v___jp_317_;
}
}
v___jp_330_:
{
lean_object* v___x_334_; 
lean_inc_ref(v_setupFile_309_);
v___x_334_ = l_Lake_createParentDirs(v_setupFile_309_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec_ref(v___x_334_);
v___x_335_ = l_Lean_instToJsonModuleSetup_toJson(v_setup_308_);
v___x_336_ = lean_unsigned_to_nat(80u);
v___x_337_ = l_Lean_Json_pretty(v___x_335_, v___x_336_);
v___x_338_ = l_IO_FS_writeFile(v_setupFile_309_, v___x_337_);
lean_dec_ref(v___x_337_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_404_; 
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; 
v_unused_405_ = lean_ctor_get(v___x_338_, 0);
lean_dec(v_unused_405_);
v___x_340_ = v___x_338_;
v_isShared_341_ = v_isSharedCheck_404_;
goto v_resetjp_339_;
}
else
{
lean_dec(v___x_338_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_404_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_342_ = lean_obj_once(&l_Lake_compileLeanModule___closed__1, &l_Lake_compileLeanModule___closed__1_once, _init_l_Lake_compileLeanModule___closed__1);
lean_inc_ref(v_setupFile_309_);
v___x_343_ = lean_array_push(v___x_342_, v_setupFile_309_);
v___x_344_ = l_Array_append___redArg(v_args_332_, v___x_343_);
lean_dec_ref(v___x_343_);
v___x_345_ = ((lean_object*)(l_Lake_compileLeanModule___closed__2));
v___x_346_ = lean_array_push(v___x_344_, v___x_345_);
v___x_347_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_348_ = lean_box(0);
v___x_349_ = ((lean_object*)(l_Lake_compileLeanModule___closed__4));
v___x_350_ = l_System_SearchPath_toString(v_leanPath_312_);
if (v_isShared_341_ == 0)
{
lean_ctor_set_tag(v___x_340_, 1);
lean_ctor_set(v___x_340_, 0, v___x_350_);
v___x_352_ = v___x_340_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_403_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_349_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_mk_empty_array_with_capacity(v___x_354_);
v___x_356_ = lean_array_push(v___x_355_, v___x_353_);
v___x_357_ = 1;
v___x_358_ = 0;
lean_inc_ref(v___x_356_);
lean_inc_ref(v_lean_313_);
v___x_359_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_359_, 0, v___x_347_);
lean_ctor_set(v___x_359_, 1, v_lean_313_);
lean_ctor_set(v___x_359_, 2, v___x_346_);
lean_ctor_set(v___x_359_, 3, v___x_348_);
lean_ctor_set(v___x_359_, 4, v___x_356_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*5, v___x_357_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*5 + 1, v___x_358_);
v___x_360_ = lean_array_get_size(v___y_333_);
lean_inc_ref(v___x_359_);
v___x_361_ = l_Lake_mkCmdLog(v___x_359_);
v___x_362_ = 0;
v___x_363_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*1, v___x_362_);
v___x_364_ = lean_array_push(v___y_333_, v___x_363_);
v___x_365_ = l_IO_Process_output(v___x_359_, v___x_348_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; uint32_t v_exitCode_367_; lean_object* v_stdout_368_; lean_object* v_stderr_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
lean_dec_ref(v_lean_313_);
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
lean_dec_ref(v___x_365_);
v_exitCode_367_ = lean_ctor_get_uint32(v_a_366_, sizeof(void*)*2);
v_stdout_368_ = lean_ctor_get(v_a_366_, 0);
lean_inc_ref(v_stdout_368_);
v_stderr_369_ = lean_ctor_get(v_a_366_, 1);
lean_inc_ref(v_stderr_369_);
lean_dec(v_a_366_);
v___x_370_ = lean_string_utf8_byte_size(v_stdout_368_);
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = lean_nat_dec_eq(v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
lean_inc_ref(v_stdout_368_);
v___x_373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_373_, 0, v_stdout_368_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
lean_ctor_set(v___x_373_, 2, v___x_370_);
v___x_374_ = ((lean_object*)(l_Lake_compileLeanModule___closed__5));
v___x_375_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0(v___x_373_);
v___x_376_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(v_relLeanFile_307_, v_stdout_368_, v___x_373_, v___x_370_, v___x_375_, v___x_374_, v___x_364_);
lean_dec_ref(v___x_373_);
lean_dec_ref(v_stdout_368_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v_a_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
v_a_378_ = lean_ctor_get(v___x_376_, 1);
lean_inc(v_a_378_);
lean_dec_ref(v___x_376_);
v___x_379_ = lean_string_utf8_byte_size(v_a_377_);
v___x_380_ = lean_nat_dec_eq(v___x_379_, v___x_371_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_381_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1));
v___x_382_ = lean_string_append(v___x_381_, v_a_377_);
lean_dec(v_a_377_);
v___x_383_ = 1;
v___x_384_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set_uint8(v___x_384_, sizeof(void*)*1, v___x_383_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_array_push(v_a_378_, v___x_384_);
v___x_387_ = l_Lake_compileLeanModule___lam__0(v_exitCode_367_, v___y_331_, v_ir_x3f_327_, v_c_x3f_328_, v_setupFile_309_, v___x_347_, v_leanir_314_, v___x_348_, v___x_356_, v___x_357_, v___x_358_, v_olean_x3f_325_, v_stderr_369_, v___x_385_, v___x_386_);
lean_dec(v_olean_x3f_325_);
v___y_322_ = v___x_360_;
v___y_323_ = v___x_387_;
goto v___jp_321_;
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec(v_a_377_);
v___x_388_ = lean_box(0);
v___x_389_ = l_Lake_compileLeanModule___lam__0(v_exitCode_367_, v___y_331_, v_ir_x3f_327_, v_c_x3f_328_, v_setupFile_309_, v___x_347_, v_leanir_314_, v___x_348_, v___x_356_, v___x_357_, v___x_358_, v_olean_x3f_325_, v_stderr_369_, v___x_388_, v_a_378_);
lean_dec(v_olean_x3f_325_);
v___y_322_ = v___x_360_;
v___y_323_ = v___x_389_;
goto v___jp_321_;
}
}
else
{
lean_object* v_a_390_; 
lean_dec_ref(v_stderr_369_);
lean_dec_ref(v___x_356_);
lean_dec(v_c_x3f_328_);
lean_dec(v_ir_x3f_327_);
lean_dec(v_olean_x3f_325_);
lean_dec_ref(v_leanir_314_);
lean_dec_ref(v_setupFile_309_);
v_a_390_ = lean_ctor_get(v___x_376_, 1);
lean_inc(v_a_390_);
lean_dec_ref(v___x_376_);
v___y_318_ = v___x_360_;
v_a_319_ = v_a_390_;
goto v___jp_317_;
}
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec_ref(v_stdout_368_);
lean_dec_ref(v_relLeanFile_307_);
v___x_391_ = lean_box(0);
v___x_392_ = l_Lake_compileLeanModule___lam__0(v_exitCode_367_, v___y_331_, v_ir_x3f_327_, v_c_x3f_328_, v_setupFile_309_, v___x_347_, v_leanir_314_, v___x_348_, v___x_356_, v___x_357_, v___x_358_, v_olean_x3f_325_, v_stderr_369_, v___x_391_, v___x_364_);
lean_dec(v_olean_x3f_325_);
v___y_322_ = v___x_360_;
v___y_323_ = v___x_392_;
goto v___jp_321_;
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec_ref(v___x_356_);
lean_dec(v_c_x3f_328_);
lean_dec(v_ir_x3f_327_);
lean_dec(v_olean_x3f_325_);
lean_dec_ref(v_leanir_314_);
lean_dec_ref(v_setupFile_309_);
lean_dec_ref(v_relLeanFile_307_);
v_a_393_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_393_);
lean_dec_ref(v___x_365_);
v___x_394_ = ((lean_object*)(l_Lake_compileLeanModule___closed__6));
v___x_395_ = lean_string_append(v___x_394_, v_lean_313_);
lean_dec_ref(v_lean_313_);
v___x_396_ = ((lean_object*)(l_Lake_compileLeanModule___closed__7));
v___x_397_ = lean_string_append(v___x_395_, v___x_396_);
v___x_398_ = lean_io_error_to_string(v_a_393_);
v___x_399_ = lean_string_append(v___x_397_, v___x_398_);
lean_dec_ref(v___x_398_);
v___x_400_ = 3;
v___x_401_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set_uint8(v___x_401_, sizeof(void*)*1, v___x_400_);
v___x_402_ = lean_array_push(v___x_364_, v___x_401_);
v___y_318_ = v___x_360_;
v_a_319_ = v___x_402_;
goto v___jp_317_;
}
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref(v_args_332_);
lean_dec(v_c_x3f_328_);
lean_dec(v_ir_x3f_327_);
lean_dec(v_olean_x3f_325_);
lean_dec_ref(v_leanir_314_);
lean_dec_ref(v_lean_313_);
lean_dec(v_leanPath_312_);
lean_dec_ref(v_setupFile_309_);
lean_dec_ref(v_relLeanFile_307_);
v_a_406_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_406_);
lean_dec_ref(v___x_338_);
v___x_407_ = lean_io_error_to_string(v_a_406_);
v___x_408_ = 3;
v___x_409_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*1, v___x_408_);
v___x_410_ = lean_array_get_size(v___y_333_);
v___x_411_ = lean_array_push(v___y_333_, v___x_409_);
v___x_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
return v___x_412_;
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec_ref(v_args_332_);
lean_dec(v_c_x3f_328_);
lean_dec(v_ir_x3f_327_);
lean_dec(v_olean_x3f_325_);
lean_dec_ref(v_leanir_314_);
lean_dec_ref(v_lean_313_);
lean_dec(v_leanPath_312_);
lean_dec_ref(v_setupFile_309_);
lean_dec_ref(v_setup_308_);
lean_dec_ref(v_relLeanFile_307_);
v_a_413_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_413_);
lean_dec_ref(v___x_334_);
v___x_414_ = lean_io_error_to_string(v_a_413_);
v___x_415_ = 3;
v___x_416_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*1, v___x_415_);
v___x_417_ = lean_array_get_size(v___y_333_);
v___x_418_ = lean_array_push(v___y_333_, v___x_416_);
v___x_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
return v___x_419_;
}
}
v___jp_420_:
{
if (lean_obj_tag(v_bc_x3f_329_) == 1)
{
lean_object* v_val_424_; lean_object* v___x_425_; 
v_val_424_ = lean_ctor_get(v_bc_x3f_329_, 0);
lean_inc_n(v_val_424_, 2);
lean_dec_ref(v_bc_x3f_329_);
v___x_425_ = l_Lake_createParentDirs(v_val_424_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec_ref(v___x_425_);
v___x_426_ = lean_obj_once(&l_Lake_compileLeanModule___closed__9, &l_Lake_compileLeanModule___closed__9_once, _init_l_Lake_compileLeanModule___closed__9);
v___x_427_ = lean_array_push(v___x_426_, v_val_424_);
v___x_428_ = l_Array_append___redArg(v_args_423_, v___x_427_);
lean_dec_ref(v___x_427_);
v___y_331_ = v___y_422_;
v_args_332_ = v___x_428_;
v___y_333_ = v___y_421_;
goto v___jp_330_;
}
else
{
lean_object* v_a_429_; lean_object* v___x_430_; uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v_val_424_);
lean_dec_ref(v_args_423_);
lean_dec(v_c_x3f_328_);
lean_dec(v_ir_x3f_327_);
lean_dec(v_olean_x3f_325_);
lean_dec_ref(v_leanir_314_);
lean_dec_ref(v_lean_313_);
lean_dec(v_leanPath_312_);
lean_dec_ref(v_setupFile_309_);
lean_dec_ref(v_setup_308_);
lean_dec_ref(v_relLeanFile_307_);
v_a_429_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_429_);
lean_dec_ref(v___x_425_);
v___x_430_ = lean_io_error_to_string(v_a_429_);
v___x_431_ = 3;
v___x_432_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*1, v___x_431_);
v___x_433_ = lean_array_get_size(v___y_421_);
v___x_434_ = lean_array_push(v___y_421_, v___x_432_);
v___x_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
return v___x_435_;
}
}
else
{
lean_dec(v_bc_x3f_329_);
v___y_331_ = v___y_422_;
v_args_332_ = v_args_423_;
v___y_333_ = v___y_421_;
goto v___jp_330_;
}
}
v___jp_436_:
{
if (lean_obj_tag(v_c_x3f_328_) == 1)
{
lean_object* v_val_440_; lean_object* v___x_441_; 
v_val_440_ = lean_ctor_get(v_c_x3f_328_, 0);
lean_inc(v_val_440_);
v___x_441_ = l_Lake_createParentDirs(v_val_440_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec_ref(v___x_441_);
v___x_442_ = lean_obj_once(&l_Lake_compileLeanModule___closed__11, &l_Lake_compileLeanModule___closed__11_once, _init_l_Lake_compileLeanModule___closed__11);
lean_inc(v_val_440_);
v___x_443_ = lean_array_push(v___x_442_, v_val_440_);
v___x_444_ = l_Array_append___redArg(v___y_438_, v___x_443_);
lean_dec_ref(v___x_443_);
v___y_421_ = v___y_437_;
v___y_422_ = v___y_439_;
v_args_423_ = v___x_444_;
goto v___jp_420_;
}
else
{
lean_object* v_a_445_; lean_object* v___x_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec_ref(v_c_x3f_328_);
lean_dec_ref(v___y_438_);
lean_dec(v_bc_x3f_329_);
lean_dec(v_ir_x3f_327_);
lean_dec(v_olean_x3f_325_);
lean_dec_ref(v_leanir_314_);
lean_dec_ref(v_lean_313_);
lean_dec(v_leanPath_312_);
lean_dec_ref(v_setupFile_309_);
lean_dec_ref(v_setup_308_);
lean_dec_ref(v_relLeanFile_307_);
v_a_445_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_445_);
lean_dec_ref(v___x_441_);
v___x_446_ = lean_io_error_to_string(v_a_445_);
v___x_447_ = 3;
v___x_448_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*1, v___x_447_);
v___x_449_ = lean_array_get_size(v___y_437_);
v___x_450_ = lean_array_push(v___y_437_, v___x_448_);
v___x_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
return v___x_451_;
}
}
else
{
v___y_421_ = v___y_437_;
v___y_422_ = v___y_439_;
v_args_423_ = v___y_438_;
goto v___jp_420_;
}
}
v___jp_452_:
{
uint8_t v_isModule_455_; 
v_isModule_455_ = lean_ctor_get_uint8(v_setup_308_, sizeof(void*)*7);
if (v_isModule_455_ == 0)
{
v___y_437_ = v___y_454_;
v___y_438_ = v_args_453_;
v___y_439_ = v_isModule_455_;
goto v___jp_436_;
}
else
{
lean_object* v_options_456_; lean_object* v_opts_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_options_456_ = lean_ctor_get(v_setup_308_, 6);
lean_inc(v_options_456_);
v_opts_457_ = l_Lean_LeanOptions_toOptions(v_options_456_);
v___x_458_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_459_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2(v_opts_457_, v___x_458_);
lean_dec_ref(v_opts_457_);
if (v___x_459_ == 0)
{
v___y_437_ = v___y_454_;
v___y_438_ = v_args_453_;
v___y_439_ = v___x_459_;
goto v___jp_436_;
}
else
{
v___y_421_ = v___y_454_;
v___y_422_ = v___x_459_;
v_args_423_ = v_args_453_;
goto v___jp_420_;
}
}
}
v___jp_460_:
{
if (lean_obj_tag(v_ilean_x3f_326_) == 1)
{
lean_object* v_val_463_; lean_object* v___x_464_; 
v_val_463_ = lean_ctor_get(v_ilean_x3f_326_, 0);
lean_inc_n(v_val_463_, 2);
lean_dec_ref(v_ilean_x3f_326_);
v___x_464_ = l_Lake_createParentDirs(v_val_463_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec_ref(v___x_464_);
v___x_465_ = lean_obj_once(&l_Lake_compileLeanModule___closed__13, &l_Lake_compileLeanModule___closed__13_once, _init_l_Lake_compileLeanModule___closed__13);
v___x_466_ = lean_array_push(v___x_465_, v_val_463_);
v___x_467_ = l_Array_append___redArg(v_args_461_, v___x_466_);
lean_dec_ref(v___x_466_);
v_args_453_ = v___x_467_;
v___y_454_ = v___y_462_;
goto v___jp_452_;
}
else
{
lean_object* v_a_468_; lean_object* v___x_469_; uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v_val_463_);
lean_dec_ref(v_args_461_);
lean_dec(v_bc_x3f_329_);
lean_dec(v_c_x3f_328_);
lean_dec(v_ir_x3f_327_);
lean_dec(v_olean_x3f_325_);
lean_dec_ref(v_leanir_314_);
lean_dec_ref(v_lean_313_);
lean_dec(v_leanPath_312_);
lean_dec_ref(v_setupFile_309_);
lean_dec_ref(v_setup_308_);
lean_dec_ref(v_relLeanFile_307_);
v_a_468_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_468_);
lean_dec_ref(v___x_464_);
v___x_469_ = lean_io_error_to_string(v_a_468_);
v___x_470_ = 3;
v___x_471_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set_uint8(v___x_471_, sizeof(void*)*1, v___x_470_);
v___x_472_ = lean_array_get_size(v___y_462_);
v___x_473_ = lean_array_push(v___y_462_, v___x_471_);
v___x_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
return v___x_474_;
}
}
else
{
lean_dec(v_ilean_x3f_326_);
v_args_453_ = v_args_461_;
v___y_454_ = v___y_462_;
goto v___jp_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object* v_leanFile_488_, lean_object* v_relLeanFile_489_, lean_object* v_setup_490_, lean_object* v_setupFile_491_, lean_object* v_arts_492_, lean_object* v_leanArgs_493_, lean_object* v_leanPath_494_, lean_object* v_lean_495_, lean_object* v_leanir_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lake_compileLeanModule(v_leanFile_488_, v_relLeanFile_489_, v_setup_490_, v_setupFile_491_, v_arts_492_, v_leanArgs_493_, v_leanPath_494_, v_lean_495_, v_leanir_496_, v_a_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1(lean_object* v_relLeanFile_500_, lean_object* v___x_501_, lean_object* v___x_502_, lean_object* v___x_503_, lean_object* v_inst_504_, lean_object* v_R_505_, lean_object* v_a_506_, lean_object* v_b_507_, lean_object* v_c_508_, lean_object* v___y_509_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(v_relLeanFile_500_, v___x_501_, v___x_502_, v___x_503_, v_a_506_, v_b_507_, v___y_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___boxed(lean_object* v_relLeanFile_512_, lean_object* v___x_513_, lean_object* v___x_514_, lean_object* v___x_515_, lean_object* v_inst_516_, lean_object* v_R_517_, lean_object* v_a_518_, lean_object* v_b_519_, lean_object* v_c_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1(v_relLeanFile_512_, v___x_513_, v___x_514_, v___x_515_, v_inst_516_, v_R_517_, v_a_518_, v_b_519_, v_c_520_, v___y_521_);
lean_dec_ref(v___x_514_);
lean_dec_ref(v___x_513_);
return v_res_523_;
}
}
static lean_object* _init_l_Lake_compileO___closed__0(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = ((lean_object*)(l_Lake_compileLeanModule___closed__10));
v___x_525_ = lean_unsigned_to_nat(4u);
v___x_526_ = lean_mk_empty_array_with_capacity(v___x_525_);
v___x_527_ = lean_array_push(v___x_526_, v___x_524_);
return v___x_527_;
}
}
static lean_object* _init_l_Lake_compileO___closed__1(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_529_ = lean_obj_once(&l_Lake_compileO___closed__0, &l_Lake_compileO___closed__0_once, _init_l_Lake_compileO___closed__0);
v___x_530_ = lean_array_push(v___x_529_, v___x_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object* v_oFile_533_, lean_object* v_srcFile_534_, lean_object* v_moreArgs_535_, lean_object* v_compiler_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_539_; 
lean_inc_ref(v_oFile_533_);
v___x_539_ = l_Lake_createParentDirs(v_oFile_533_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec_ref(v___x_539_);
v___x_540_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_541_ = lean_obj_once(&l_Lake_compileO___closed__1, &l_Lake_compileO___closed__1_once, _init_l_Lake_compileO___closed__1);
v___x_542_ = lean_array_push(v___x_541_, v_oFile_533_);
v___x_543_ = lean_array_push(v___x_542_, v_srcFile_534_);
v___x_544_ = l_Array_append___redArg(v___x_543_, v_moreArgs_535_);
v___x_545_ = lean_box(0);
v___x_546_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_547_ = 1;
v___x_548_ = 0;
v___x_549_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_549_, 0, v___x_540_);
lean_ctor_set(v___x_549_, 1, v_compiler_536_);
lean_ctor_set(v___x_549_, 2, v___x_544_);
lean_ctor_set(v___x_549_, 3, v___x_545_);
lean_ctor_set(v___x_549_, 4, v___x_546_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*5, v___x_547_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*5 + 1, v___x_548_);
v___x_550_ = l_Lake_proc(v___x_549_, v___x_548_, v_a_537_);
return v___x_550_;
}
else
{
lean_object* v_a_551_; lean_object* v___x_552_; uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec_ref(v_compiler_536_);
lean_dec_ref(v_srcFile_534_);
lean_dec_ref(v_oFile_533_);
v_a_551_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_551_);
lean_dec_ref(v___x_539_);
v___x_552_ = lean_io_error_to_string(v_a_551_);
v___x_553_ = 3;
v___x_554_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*1, v___x_553_);
v___x_555_ = lean_array_get_size(v_a_537_);
v___x_556_ = lean_array_push(v_a_537_, v___x_554_);
v___x_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object* v_oFile_558_, lean_object* v_srcFile_559_, lean_object* v_moreArgs_560_, lean_object* v_compiler_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lake_compileO(v_oFile_558_, v_srcFile_559_, v_moreArgs_560_, v_compiler_561_, v_a_562_);
lean_dec_ref(v_moreArgs_560_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(lean_object* v___x_565_, lean_object* v___y_566_, lean_object* v_a_567_, lean_object* v_b_568_){
_start:
{
lean_object* v_startInclusive_569_; lean_object* v_endExclusive_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_startInclusive_569_ = lean_ctor_get(v___x_565_, 1);
v_endExclusive_570_ = lean_ctor_get(v___x_565_, 2);
v___x_571_ = lean_nat_sub(v_endExclusive_570_, v_startInclusive_569_);
v___x_572_ = lean_nat_dec_eq(v_a_567_, v___x_571_);
lean_dec(v___x_571_);
if (v___x_572_ == 0)
{
uint32_t v___x_573_; lean_object* v___x_574_; uint32_t v___x_575_; uint8_t v___y_577_; uint8_t v___x_583_; 
v___x_573_ = lean_string_utf8_get_fast(v___y_566_, v_a_567_);
v___x_574_ = lean_string_utf8_next_fast(v___y_566_, v_a_567_);
lean_dec(v_a_567_);
v___x_575_ = 92;
v___x_583_ = lean_uint32_dec_eq(v___x_573_, v___x_575_);
if (v___x_583_ == 0)
{
uint32_t v___x_584_; uint8_t v___x_585_; 
v___x_584_ = 34;
v___x_585_ = lean_uint32_dec_eq(v___x_573_, v___x_584_);
v___y_577_ = v___x_585_;
goto v___jp_576_;
}
else
{
v___y_577_ = v___x_583_;
goto v___jp_576_;
}
v___jp_576_:
{
if (v___y_577_ == 0)
{
lean_object* v___x_578_; 
v___x_578_ = lean_string_push(v_b_568_, v___x_573_);
v_a_567_ = v___x_574_;
v_b_568_ = v___x_578_;
goto _start;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_string_push(v_b_568_, v___x_575_);
v___x_581_ = lean_string_push(v___x_580_, v___x_573_);
v_a_567_ = v___x_574_;
v_b_568_ = v___x_581_;
goto _start;
}
}
}
else
{
lean_dec(v_a_567_);
return v_b_568_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg___boxed(lean_object* v___x_586_, lean_object* v___y_587_, lean_object* v_a_588_, lean_object* v_b_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_586_, v___y_587_, v_a_588_, v_b_589_);
lean_dec_ref(v___y_587_);
lean_dec_ref(v___x_586_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(lean_object* v_a_593_, lean_object* v_as_594_, size_t v_i_595_, size_t v_stop_596_, lean_object* v_b_597_, lean_object* v___y_598_){
_start:
{
uint8_t v___x_600_; 
v___x_600_ = lean_usize_dec_eq(v_i_595_, v_stop_596_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_601_ = lean_array_uget_borrowed(v_as_594_, v_i_595_);
v___x_602_ = ((lean_object*)(l_Lake_compileLeanModule___closed__5));
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_string_utf8_byte_size(v___x_601_);
lean_inc(v___x_601_);
v___x_605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_605_, 0, v___x_601_);
lean_ctor_set(v___x_605_, 1, v___x_603_);
lean_ctor_set(v___x_605_, 2, v___x_604_);
v___x_606_ = l_String_Slice_positions(v___x_605_);
v___x_607_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_605_, v___x_601_, v___x_606_, v___x_602_);
lean_dec_ref(v___x_605_);
v___x_608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0));
v___x_609_ = lean_string_append(v___x_608_, v___x_607_);
lean_dec_ref(v___x_607_);
v___x_610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1));
v___x_611_ = lean_string_append(v___x_609_, v___x_610_);
v___x_612_ = lean_io_prim_handle_put_str(v_a_593_, v___x_611_);
lean_dec_ref(v___x_611_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; size_t v___x_614_; size_t v___x_615_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref(v___x_612_);
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_add(v_i_595_, v___x_614_);
v_i_595_ = v___x_615_;
v_b_597_ = v_a_613_;
goto _start;
}
else
{
lean_object* v_a_617_; lean_object* v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_a_617_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_617_);
lean_dec_ref(v___x_612_);
v___x_618_ = lean_io_error_to_string(v_a_617_);
v___x_619_ = 3;
v___x_620_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set_uint8(v___x_620_, sizeof(void*)*1, v___x_619_);
v___x_621_ = lean_array_get_size(v___y_598_);
v___x_622_ = lean_array_push(v___y_598_, v___x_620_);
v___x_623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
return v___x_623_;
}
}
else
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v_b_597_);
lean_ctor_set(v___x_624_, 1, v___y_598_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___boxed(lean_object* v_a_625_, lean_object* v_as_626_, lean_object* v_i_627_, lean_object* v_stop_628_, lean_object* v_b_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
size_t v_i_boxed_632_; size_t v_stop_boxed_633_; lean_object* v_res_634_; 
v_i_boxed_632_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_stop_boxed_633_ = lean_unbox_usize(v_stop_628_);
lean_dec(v_stop_628_);
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_625_, v_as_626_, v_i_boxed_632_, v_stop_boxed_633_, v_b_629_, v___y_630_);
lean_dec_ref(v_as_626_);
lean_dec(v_a_625_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object* v_basePath_637_, lean_object* v_args_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_641_; lean_object* v_rspFile_642_; lean_object* v_a_644_; lean_object* v___y_652_; uint8_t v___x_663_; lean_object* v___x_664_; 
v___x_641_ = ((lean_object*)(l_Lake_mkArgs___closed__0));
v_rspFile_642_ = l_System_FilePath_addExtension(v_basePath_637_, v___x_641_);
v___x_663_ = 1;
v___x_664_ = lean_io_prim_handle_mk(v_rspFile_642_, v___x_663_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref(v___x_664_);
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_array_get_size(v_args_638_);
v___x_668_ = lean_nat_dec_lt(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_dec(v_a_665_);
v_a_644_ = v_a_639_;
goto v___jp_643_;
}
else
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_box(0);
v___x_670_ = lean_nat_dec_le(v___x_667_, v___x_667_);
if (v___x_670_ == 0)
{
if (v___x_668_ == 0)
{
lean_dec(v_a_665_);
v_a_644_ = v_a_639_;
goto v___jp_643_;
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_667_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_665_, v_args_638_, v___x_671_, v___x_672_, v___x_669_, v_a_639_);
lean_dec(v_a_665_);
v___y_652_ = v___x_673_;
goto v___jp_651_;
}
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v___x_674_ = ((size_t)0ULL);
v___x_675_ = lean_usize_of_nat(v___x_667_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_665_, v_args_638_, v___x_674_, v___x_675_, v___x_669_, v_a_639_);
lean_dec(v_a_665_);
v___y_652_ = v___x_676_;
goto v___jp_651_;
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec_ref(v_rspFile_642_);
v_a_677_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_677_);
lean_dec_ref(v___x_664_);
v___x_678_ = lean_io_error_to_string(v_a_677_);
v___x_679_ = 3;
v___x_680_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*1, v___x_679_);
v___x_681_ = lean_array_get_size(v_a_639_);
v___x_682_ = lean_array_push(v_a_639_, v___x_680_);
v___x_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
return v___x_683_;
}
v___jp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_645_ = ((lean_object*)(l_Lake_mkArgs___closed__1));
v___x_646_ = lean_string_append(v___x_645_, v_rspFile_642_);
lean_dec_ref(v_rspFile_642_);
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_mk_empty_array_with_capacity(v___x_647_);
v___x_649_ = lean_array_push(v___x_648_, v___x_646_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v_a_644_);
return v___x_650_;
}
v___jp_651_:
{
if (lean_obj_tag(v___y_652_) == 0)
{
lean_object* v_a_653_; 
v_a_653_ = lean_ctor_get(v___y_652_, 1);
lean_inc(v_a_653_);
lean_dec_ref(v___y_652_);
v_a_644_ = v_a_653_;
goto v___jp_643_;
}
else
{
lean_object* v_a_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v_rspFile_642_);
v_a_654_ = lean_ctor_get(v___y_652_, 0);
v_a_655_ = lean_ctor_get(v___y_652_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v___y_652_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___y_652_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_inc(v_a_654_);
lean_dec(v___y_652_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_654_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs___boxed(lean_object* v_basePath_684_, lean_object* v_args_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lake_mkArgs(v_basePath_684_, v_args_685_, v_a_686_);
lean_dec_ref(v_args_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(lean_object* v___x_689_, lean_object* v___y_690_, lean_object* v_inst_691_, lean_object* v_R_692_, lean_object* v_a_693_, lean_object* v_b_694_, lean_object* v_c_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_689_, v___y_690_, v_a_693_, v_b_694_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(lean_object* v___x_697_, lean_object* v___y_698_, lean_object* v_inst_699_, lean_object* v_R_700_, lean_object* v_a_701_, lean_object* v_b_702_, lean_object* v_c_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(v___x_697_, v___y_698_, v_inst_699_, v_R_700_, v_a_701_, v_b_702_, v_c_703_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v___x_697_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(size_t v_sz_705_, size_t v_i_706_, lean_object* v_bs_707_){
_start:
{
uint8_t v___x_708_; 
v___x_708_ = lean_usize_dec_lt(v_i_706_, v_sz_705_);
if (v___x_708_ == 0)
{
return v_bs_707_;
}
else
{
lean_object* v_v_709_; lean_object* v___x_710_; lean_object* v_bs_x27_711_; size_t v___x_712_; size_t v___x_713_; lean_object* v___x_714_; 
v_v_709_ = lean_array_uget(v_bs_707_, v_i_706_);
v___x_710_ = lean_unsigned_to_nat(0u);
v_bs_x27_711_ = lean_array_uset(v_bs_707_, v_i_706_, v___x_710_);
v___x_712_ = ((size_t)1ULL);
v___x_713_ = lean_usize_add(v_i_706_, v___x_712_);
v___x_714_ = lean_array_uset(v_bs_x27_711_, v_i_706_, v_v_709_);
v_i_706_ = v___x_713_;
v_bs_707_ = v___x_714_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0___boxed(lean_object* v_sz_716_, lean_object* v_i_717_, lean_object* v_bs_718_){
_start:
{
size_t v_sz_boxed_719_; size_t v_i_boxed_720_; lean_object* v_res_721_; 
v_sz_boxed_719_ = lean_unbox_usize(v_sz_716_);
lean_dec(v_sz_716_);
v_i_boxed_720_ = lean_unbox_usize(v_i_717_);
lean_dec(v_i_717_);
v_res_721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_boxed_719_, v_i_boxed_720_, v_bs_718_);
return v_res_721_;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__3(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_728_ = ((lean_object*)(l_Lake_compileStaticLib___closed__2));
v___x_729_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_730_ = lean_array_push(v___x_729_, v___x_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object* v_libFile_731_, lean_object* v_oFiles_732_, lean_object* v_ar_733_, uint8_t v_thin_734_, lean_object* v_a_735_){
_start:
{
lean_object* v___x_737_; 
lean_inc_ref(v_libFile_731_);
v___x_737_ = l_Lake_createParentDirs(v_libFile_731_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v___x_738_; 
lean_dec_ref(v___x_737_);
v___x_738_ = l_Lake_removeFileIfExists(v_libFile_731_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v___x_739_; uint8_t v___x_740_; lean_object* v___y_742_; 
lean_dec_ref(v___x_738_);
v___x_739_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_740_ = 1;
if (v_thin_734_ == 0)
{
v___y_742_ = v___x_739_;
goto v___jp_741_;
}
else
{
lean_object* v___x_766_; 
v___x_766_ = lean_obj_once(&l_Lake_compileStaticLib___closed__3, &l_Lake_compileStaticLib___closed__3_once, _init_l_Lake_compileStaticLib___closed__3);
v___y_742_ = v___x_766_;
goto v___jp_741_;
}
v___jp_741_:
{
size_t v_sz_743_; size_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_sz_743_ = lean_array_size(v_oFiles_732_);
v___x_744_ = ((size_t)0ULL);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_743_, v___x_744_, v_oFiles_732_);
lean_inc_ref(v_libFile_731_);
v___x_746_ = l_Lake_mkArgs(v_libFile_731_, v___x_745_, v_a_735_);
lean_dec_ref(v___x_745_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v_a_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
v_a_748_ = lean_ctor_get(v___x_746_, 1);
lean_inc(v_a_748_);
lean_dec_ref(v___x_746_);
lean_inc_ref(v___y_742_);
v___x_749_ = lean_array_push(v___y_742_, v_libFile_731_);
v___x_750_ = l_Array_append___redArg(v___x_749_, v_a_747_);
lean_dec(v_a_747_);
v___x_751_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_752_ = lean_box(0);
v___x_753_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_754_ = 0;
v___x_755_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_755_, 0, v___x_751_);
lean_ctor_set(v___x_755_, 1, v_ar_733_);
lean_ctor_set(v___x_755_, 2, v___x_750_);
lean_ctor_set(v___x_755_, 3, v___x_752_);
lean_ctor_set(v___x_755_, 4, v___x_753_);
lean_ctor_set_uint8(v___x_755_, sizeof(void*)*5, v___x_740_);
lean_ctor_set_uint8(v___x_755_, sizeof(void*)*5 + 1, v___x_754_);
v___x_756_ = l_Lake_proc(v___x_755_, v___x_754_, v_a_748_);
return v___x_756_;
}
else
{
lean_object* v_a_757_; lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v_ar_733_);
lean_dec_ref(v_libFile_731_);
v_a_757_ = lean_ctor_get(v___x_746_, 0);
v_a_758_ = lean_ctor_get(v___x_746_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_746_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_inc(v_a_757_);
lean_dec(v___x_746_);
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
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_757_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_768_; uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec_ref(v_ar_733_);
lean_dec_ref(v_oFiles_732_);
lean_dec_ref(v_libFile_731_);
v_a_767_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_767_);
lean_dec_ref(v___x_738_);
v___x_768_ = lean_io_error_to_string(v_a_767_);
v___x_769_ = 3;
v___x_770_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set_uint8(v___x_770_, sizeof(void*)*1, v___x_769_);
v___x_771_ = lean_array_get_size(v_a_735_);
v___x_772_ = lean_array_push(v_a_735_, v___x_770_);
v___x_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
return v___x_773_;
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_775_; uint8_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec_ref(v_ar_733_);
lean_dec_ref(v_oFiles_732_);
lean_dec_ref(v_libFile_731_);
v_a_774_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_774_);
lean_dec_ref(v___x_737_);
v___x_775_ = lean_io_error_to_string(v_a_774_);
v___x_776_ = 3;
v___x_777_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_777_, 0, v___x_775_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*1, v___x_776_);
v___x_778_ = lean_array_get_size(v_a_735_);
v___x_779_ = lean_array_push(v_a_735_, v___x_777_);
v___x_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object* v_libFile_781_, lean_object* v_oFiles_782_, lean_object* v_ar_783_, lean_object* v_thin_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
uint8_t v_thin_boxed_787_; lean_object* v_res_788_; 
v_thin_boxed_787_ = lean_unbox(v_thin_784_);
v_res_788_ = l_Lake_compileStaticLib(v_libFile_781_, v_oFiles_782_, v_ar_783_, v_thin_boxed_787_, v_a_785_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(){
_start:
{
uint8_t v___x_801_; 
v___x_801_ = l_System_Platform_isOSX;
if (v___x_801_ == 0)
{
lean_object* v___x_802_; 
v___x_802_ = ((lean_object*)(l_Lake_compileO___closed__2));
return v___x_802_;
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0));
v___x_804_ = lean_io_getenv(v___x_803_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v___x_805_; 
v___x_805_ = ((lean_object*)(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4));
return v___x_805_;
}
else
{
lean_object* v___x_806_; 
lean_dec_ref(v___x_804_);
v___x_806_ = ((lean_object*)(l_Lake_compileO___closed__2));
return v___x_806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___boxed(lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
return v_res_808_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__1(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_810_ = ((lean_object*)(l_Lake_compileSharedLib___closed__0));
v___x_811_ = lean_unsigned_to_nat(3u);
v___x_812_ = lean_mk_empty_array_with_capacity(v___x_811_);
v___x_813_ = lean_array_push(v___x_812_, v___x_810_);
return v___x_813_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__2(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_815_ = lean_obj_once(&l_Lake_compileSharedLib___closed__1, &l_Lake_compileSharedLib___closed__1_once, _init_l_Lake_compileSharedLib___closed__1);
v___x_816_ = lean_array_push(v___x_815_, v___x_814_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object* v_libFile_817_, lean_object* v_linkArgs_818_, lean_object* v_linker_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___x_822_; 
lean_inc_ref(v_libFile_817_);
v___x_822_ = l_Lake_createParentDirs(v_libFile_817_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v___x_823_; 
lean_dec_ref(v___x_822_);
lean_inc_ref(v_libFile_817_);
v___x_823_ = l_Lake_mkArgs(v_libFile_817_, v_linkArgs_818_, v_a_820_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v_a_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
v_a_825_ = lean_ctor_get(v___x_823_, 1);
lean_inc(v_a_825_);
lean_dec_ref(v___x_823_);
v___x_826_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
v___x_827_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_828_ = lean_obj_once(&l_Lake_compileSharedLib___closed__2, &l_Lake_compileSharedLib___closed__2_once, _init_l_Lake_compileSharedLib___closed__2);
v___x_829_ = lean_array_push(v___x_828_, v_libFile_817_);
v___x_830_ = l_Array_append___redArg(v___x_829_, v_a_824_);
lean_dec(v_a_824_);
v___x_831_ = lean_box(0);
v___x_832_ = 1;
v___x_833_ = 0;
v___x_834_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_834_, 0, v___x_827_);
lean_ctor_set(v___x_834_, 1, v_linker_819_);
lean_ctor_set(v___x_834_, 2, v___x_830_);
lean_ctor_set(v___x_834_, 3, v___x_831_);
lean_ctor_set(v___x_834_, 4, v___x_826_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*5, v___x_832_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*5 + 1, v___x_833_);
v___x_835_ = l_Lake_proc(v___x_834_, v___x_833_, v_a_825_);
return v___x_835_;
}
else
{
lean_object* v_a_836_; lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref(v_linker_819_);
lean_dec_ref(v_libFile_817_);
v_a_836_ = lean_ctor_get(v___x_823_, 0);
v_a_837_ = lean_ctor_get(v___x_823_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_823_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_inc(v_a_836_);
lean_dec(v___x_823_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_836_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref(v_linker_819_);
lean_dec_ref(v_libFile_817_);
v_a_845_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_845_);
lean_dec_ref(v___x_822_);
v___x_846_ = lean_io_error_to_string(v_a_845_);
v___x_847_ = 3;
v___x_848_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*1, v___x_847_);
v___x_849_ = lean_array_get_size(v_a_820_);
v___x_850_ = lean_array_push(v_a_820_, v___x_848_);
v___x_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object* v_libFile_852_, lean_object* v_linkArgs_853_, lean_object* v_linker_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lake_compileSharedLib(v_libFile_852_, v_linkArgs_853_, v_linker_854_, v_a_855_);
lean_dec_ref(v_linkArgs_853_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object* v_binFile_858_, lean_object* v_linkArgs_859_, lean_object* v_linker_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_863_; 
lean_inc_ref(v_binFile_858_);
v___x_863_ = l_Lake_createParentDirs(v_binFile_858_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v___x_864_; 
lean_dec_ref(v___x_863_);
lean_inc_ref(v_binFile_858_);
v___x_864_ = l_Lake_mkArgs(v_binFile_858_, v_linkArgs_859_, v_a_861_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v_a_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
v_a_866_ = lean_ctor_get(v___x_864_, 1);
lean_inc(v_a_866_);
lean_dec_ref(v___x_864_);
v___x_867_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
v___x_868_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_869_ = lean_unsigned_to_nat(2u);
v___x_870_ = lean_mk_empty_array_with_capacity(v___x_869_);
lean_dec_ref(v___x_870_);
v___x_871_ = lean_obj_once(&l_Lake_compileLeanModule___closed__15, &l_Lake_compileLeanModule___closed__15_once, _init_l_Lake_compileLeanModule___closed__15);
v___x_872_ = lean_array_push(v___x_871_, v_binFile_858_);
v___x_873_ = l_Array_append___redArg(v___x_872_, v_a_865_);
lean_dec(v_a_865_);
v___x_874_ = lean_box(0);
v___x_875_ = 1;
v___x_876_ = 0;
v___x_877_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_877_, 0, v___x_868_);
lean_ctor_set(v___x_877_, 1, v_linker_860_);
lean_ctor_set(v___x_877_, 2, v___x_873_);
lean_ctor_set(v___x_877_, 3, v___x_874_);
lean_ctor_set(v___x_877_, 4, v___x_867_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*5, v___x_875_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*5 + 1, v___x_876_);
v___x_878_ = l_Lake_proc(v___x_877_, v___x_876_, v_a_866_);
return v___x_878_;
}
else
{
lean_object* v_a_879_; lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref(v_linker_860_);
lean_dec_ref(v_binFile_858_);
v_a_879_ = lean_ctor_get(v___x_864_, 0);
v_a_880_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_864_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_inc(v_a_879_);
lean_dec(v___x_864_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_879_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_889_; uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec_ref(v_linker_860_);
lean_dec_ref(v_binFile_858_);
v_a_888_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_888_);
lean_dec_ref(v___x_863_);
v___x_889_ = lean_io_error_to_string(v_a_888_);
v___x_890_ = 3;
v___x_891_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set_uint8(v___x_891_, sizeof(void*)*1, v___x_890_);
v___x_892_ = lean_array_get_size(v_a_861_);
v___x_893_ = lean_array_push(v_a_861_, v___x_891_);
v___x_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object* v_binFile_895_, lean_object* v_linkArgs_896_, lean_object* v_linker_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lake_compileExe(v_binFile_895_, v_linkArgs_896_, v_linker_897_, v_a_898_);
lean_dec_ref(v_linkArgs_896_);
return v_res_900_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0));
v___x_903_ = lean_unsigned_to_nat(2u);
v___x_904_ = lean_mk_empty_array_with_capacity(v___x_903_);
v___x_905_ = lean_array_push(v___x_904_, v___x_902_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(lean_object* v_as_906_, size_t v_i_907_, size_t v_stop_908_, lean_object* v_b_909_){
_start:
{
uint8_t v___x_910_; 
v___x_910_ = lean_usize_dec_eq(v_i_907_, v_stop_908_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; size_t v___x_915_; size_t v___x_916_; 
v___x_911_ = lean_array_uget_borrowed(v_as_906_, v_i_907_);
v___x_912_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1);
lean_inc(v___x_911_);
v___x_913_ = lean_array_push(v___x_912_, v___x_911_);
v___x_914_ = l_Array_append___redArg(v_b_909_, v___x_913_);
lean_dec_ref(v___x_913_);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_i_907_, v___x_915_);
v_i_907_ = v___x_916_;
v_b_909_ = v___x_914_;
goto _start;
}
else
{
return v_b_909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___boxed(lean_object* v_as_918_, lean_object* v_i_919_, lean_object* v_stop_920_, lean_object* v_b_921_){
_start:
{
size_t v_i_boxed_922_; size_t v_stop_boxed_923_; lean_object* v_res_924_; 
v_i_boxed_922_ = lean_unbox_usize(v_i_919_);
lean_dec(v_i_919_);
v_stop_boxed_923_ = lean_unbox_usize(v_stop_920_);
lean_dec(v_stop_920_);
v_res_924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_as_918_, v_i_boxed_922_, v_stop_boxed_923_, v_b_921_);
lean_dec_ref(v_as_918_);
return v_res_924_;
}
}
static lean_object* _init_l_Lake_download___closed__5(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_930_ = ((lean_object*)(l_Lake_download___closed__1));
v___x_931_ = lean_unsigned_to_nat(7u);
v___x_932_ = lean_mk_empty_array_with_capacity(v___x_931_);
v___x_933_ = lean_array_push(v___x_932_, v___x_930_);
return v___x_933_;
}
}
static lean_object* _init_l_Lake_download___closed__6(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = ((lean_object*)(l_Lake_download___closed__2));
v___x_935_ = lean_obj_once(&l_Lake_download___closed__5, &l_Lake_download___closed__5_once, _init_l_Lake_download___closed__5);
v___x_936_ = lean_array_push(v___x_935_, v___x_934_);
return v___x_936_;
}
}
static lean_object* _init_l_Lake_download___closed__7(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_938_ = lean_obj_once(&l_Lake_download___closed__6, &l_Lake_download___closed__6_once, _init_l_Lake_download___closed__6);
v___x_939_ = lean_array_push(v___x_938_, v___x_937_);
return v___x_939_;
}
}
static lean_object* _init_l_Lake_download___closed__8(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_941_ = lean_obj_once(&l_Lake_download___closed__7, &l_Lake_download___closed__7_once, _init_l_Lake_download___closed__7);
v___x_942_ = lean_array_push(v___x_941_, v___x_940_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_download(lean_object* v_url_943_, lean_object* v_file_944_, lean_object* v_headers_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_960_; uint8_t v___x_976_; 
v___x_976_ = l_System_FilePath_pathExists(v_file_944_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
lean_inc_ref(v_file_944_);
v___x_977_ = l_Lake_createParentDirs(v_file_944_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_dec_ref(v___x_977_);
v___y_960_ = v_a_946_;
goto v___jp_959_;
}
else
{
lean_object* v_a_978_; lean_object* v___x_979_; uint8_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec_ref(v_file_944_);
lean_dec_ref(v_url_943_);
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref(v___x_977_);
v___x_979_ = lean_io_error_to_string(v_a_978_);
v___x_980_ = 3;
v___x_981_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*1, v___x_980_);
v___x_982_ = lean_array_get_size(v_a_946_);
v___x_983_ = lean_array_push(v_a_946_, v___x_981_);
v___x_984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
return v___x_984_;
}
}
else
{
lean_object* v___x_985_; 
v___x_985_ = lean_io_remove_file(v_file_944_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_dec_ref(v___x_985_);
v___y_960_ = v_a_946_;
goto v___jp_959_;
}
else
{
lean_object* v_a_986_; lean_object* v___x_987_; uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
lean_dec_ref(v_file_944_);
lean_dec_ref(v_url_943_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v___x_985_);
v___x_987_ = lean_io_error_to_string(v_a_986_);
v___x_988_ = 3;
v___x_989_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*1, v___x_988_);
v___x_990_ = lean_array_get_size(v_a_946_);
v___x_991_ = lean_array_push(v_a_946_, v___x_989_);
v___x_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
return v___x_992_;
}
}
v___jp_948_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; uint8_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_951_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_952_ = ((lean_object*)(l_Lake_download___closed__0));
v___x_953_ = lean_box(0);
v___x_954_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_955_ = 1;
v___x_956_ = 0;
v___x_957_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_957_, 0, v___x_951_);
lean_ctor_set(v___x_957_, 1, v___x_952_);
lean_ctor_set(v___x_957_, 2, v___y_950_);
lean_ctor_set(v___x_957_, 3, v___x_953_);
lean_ctor_set(v___x_957_, 4, v___x_954_);
lean_ctor_set_uint8(v___x_957_, sizeof(void*)*5, v___x_955_);
lean_ctor_set_uint8(v___x_957_, sizeof(void*)*5 + 1, v___x_956_);
v___x_958_ = l_Lake_proc(v___x_957_, v___x_955_, v___y_949_);
return v___x_958_;
}
v___jp_959_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_961_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_962_ = lean_obj_once(&l_Lake_download___closed__8, &l_Lake_download___closed__8_once, _init_l_Lake_download___closed__8);
v___x_963_ = lean_array_push(v___x_962_, v_file_944_);
v___x_964_ = lean_array_push(v___x_963_, v___x_961_);
v___x_965_ = lean_array_push(v___x_964_, v_url_943_);
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = lean_array_get_size(v_headers_945_);
v___x_968_ = lean_nat_dec_lt(v___x_966_, v___x_967_);
if (v___x_968_ == 0)
{
v___y_949_ = v___y_960_;
v___y_950_ = v___x_965_;
goto v___jp_948_;
}
else
{
uint8_t v___x_969_; 
v___x_969_ = lean_nat_dec_le(v___x_967_, v___x_967_);
if (v___x_969_ == 0)
{
if (v___x_968_ == 0)
{
v___y_949_ = v___y_960_;
v___y_950_ = v___x_965_;
goto v___jp_948_;
}
else
{
size_t v___x_970_; size_t v___x_971_; lean_object* v___x_972_; 
v___x_970_ = ((size_t)0ULL);
v___x_971_ = lean_usize_of_nat(v___x_967_);
v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_945_, v___x_970_, v___x_971_, v___x_965_);
v___y_949_ = v___y_960_;
v___y_950_ = v___x_972_;
goto v___jp_948_;
}
}
else
{
size_t v___x_973_; size_t v___x_974_; lean_object* v___x_975_; 
v___x_973_ = ((size_t)0ULL);
v___x_974_ = lean_usize_of_nat(v___x_967_);
v___x_975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_945_, v___x_973_, v___x_974_, v___x_965_);
v___y_949_ = v___y_960_;
v___y_950_ = v___x_975_;
goto v___jp_948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object* v_url_993_, lean_object* v_file_994_, lean_object* v_headers_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lake_download(v_url_993_, v_file_994_, v_headers_995_, v_a_996_);
lean_dec_ref(v_headers_995_);
return v_res_998_;
}
}
static lean_object* _init_l_Lake_untar___closed__3(void){
_start:
{
uint32_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = 122;
v___x_1003_ = ((lean_object*)(l_Lake_untar___closed__2));
v___x_1004_ = lean_string_push(v___x_1003_, v___x_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lake_untar(lean_object* v_file_1005_, lean_object* v_dir_1006_, uint8_t v_gzip_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___x_1010_; 
lean_inc_ref(v_dir_1006_);
v___x_1010_ = l_IO_FS_createDirAll(v_dir_1006_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_opts_1012_; lean_object* v___y_1013_; lean_object* v___x_1031_; 
lean_dec_ref(v___x_1010_);
v___x_1031_ = ((lean_object*)(l_Lake_untar___closed__2));
if (v_gzip_1007_ == 0)
{
v_opts_1012_ = v___x_1031_;
v___y_1013_ = v_a_1008_;
goto v___jp_1011_;
}
else
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_obj_once(&l_Lake_untar___closed__3, &l_Lake_untar___closed__3_once, _init_l_Lake_untar___closed__3);
v_opts_1012_ = v___x_1032_;
v___y_1013_ = v_a_1008_;
goto v___jp_1011_;
}
v___jp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1014_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_1015_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_1016_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_1017_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_1018_ = lean_unsigned_to_nat(5u);
v___x_1019_ = lean_mk_empty_array_with_capacity(v___x_1018_);
lean_inc_ref(v_opts_1012_);
v___x_1020_ = lean_array_push(v___x_1019_, v_opts_1012_);
v___x_1021_ = lean_array_push(v___x_1020_, v___x_1016_);
v___x_1022_ = lean_array_push(v___x_1021_, v_file_1005_);
v___x_1023_ = lean_array_push(v___x_1022_, v___x_1017_);
v___x_1024_ = lean_array_push(v___x_1023_, v_dir_1006_);
v___x_1025_ = lean_box(0);
v___x_1026_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_1027_ = 1;
v___x_1028_ = 0;
v___x_1029_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1029_, 0, v___x_1014_);
lean_ctor_set(v___x_1029_, 1, v___x_1015_);
lean_ctor_set(v___x_1029_, 2, v___x_1024_);
lean_ctor_set(v___x_1029_, 3, v___x_1025_);
lean_ctor_set(v___x_1029_, 4, v___x_1026_);
lean_ctor_set_uint8(v___x_1029_, sizeof(void*)*5, v___x_1027_);
lean_ctor_set_uint8(v___x_1029_, sizeof(void*)*5 + 1, v___x_1028_);
v___x_1030_ = l_Lake_proc(v___x_1029_, v___x_1027_, v___y_1013_);
return v___x_1030_;
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec_ref(v_dir_1006_);
lean_dec_ref(v_file_1005_);
v_a_1033_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1033_);
lean_dec_ref(v___x_1010_);
v___x_1034_ = lean_io_error_to_string(v_a_1033_);
v___x_1035_ = 3;
v___x_1036_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*1, v___x_1035_);
v___x_1037_ = lean_array_get_size(v_a_1008_);
v___x_1038_ = lean_array_push(v_a_1008_, v___x_1036_);
v___x_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object* v_file_1040_, lean_object* v_dir_1041_, lean_object* v_gzip_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
uint8_t v_gzip_boxed_1045_; lean_object* v_res_1046_; 
v_gzip_boxed_1045_ = lean_unbox(v_gzip_1042_);
v_res_1046_ = l_Lake_untar(v_file_1040_, v_dir_1041_, v_gzip_boxed_1045_, v_a_1043_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(lean_object* v_as_1048_, size_t v_sz_1049_, size_t v_i_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_){
_start:
{
uint8_t v___x_1054_; 
v___x_1054_ = lean_usize_dec_lt(v_i_1050_, v_sz_1049_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_b_1051_);
lean_ctor_set(v___x_1055_, 1, v___y_1052_);
return v___x_1055_;
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; 
v_a_1056_ = lean_array_uget_borrowed(v_as_1048_, v_i_1050_);
v___x_1057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0));
v___x_1058_ = lean_string_append(v___x_1057_, v_a_1056_);
v___x_1059_ = lean_array_push(v_b_1051_, v___x_1058_);
v___x_1060_ = ((size_t)1ULL);
v___x_1061_ = lean_usize_add(v_i_1050_, v___x_1060_);
v_i_1050_ = v___x_1061_;
v_b_1051_ = v___x_1059_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___boxed(lean_object* v_as_1063_, lean_object* v_sz_1064_, lean_object* v_i_1065_, lean_object* v_b_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
size_t v_sz_boxed_1069_; size_t v_i_boxed_1070_; lean_object* v_res_1071_; 
v_sz_boxed_1069_ = lean_unbox_usize(v_sz_1064_);
lean_dec(v_sz_1064_);
v_i_boxed_1070_ = lean_unbox_usize(v_i_1065_);
lean_dec(v_i_1065_);
v_res_1071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_as_1063_, v_sz_boxed_1069_, v_i_boxed_1070_, v_b_1066_, v___y_1067_);
lean_dec_ref(v_as_1063_);
return v_res_1071_;
}
}
static lean_object* _init_l_Lake_tar___closed__1(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1073_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_1074_ = lean_unsigned_to_nat(5u);
v___x_1075_ = lean_mk_empty_array_with_capacity(v___x_1074_);
v___x_1076_ = lean_array_push(v___x_1075_, v___x_1073_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lake_tar___closed__10(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = ((lean_object*)(l_Lake_tar___closed__9));
v___x_1095_ = ((lean_object*)(l_Lake_tar___closed__8));
v___x_1096_ = lean_array_push(v___x_1095_, v___x_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lake_tar(lean_object* v_dir_1097_, lean_object* v_file_1098_, uint8_t v_gzip_1099_, lean_object* v_excludePaths_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; uint8_t v___y_1109_; lean_object* v___y_1110_; lean_object* v___x_1114_; 
lean_inc_ref(v_file_1098_);
v___x_1114_ = l_Lake_createParentDirs(v_file_1098_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_args_1116_; lean_object* v___y_1117_; lean_object* v___x_1147_; 
lean_dec_ref(v___x_1114_);
v___x_1147_ = ((lean_object*)(l_Lake_tar___closed__8));
if (v_gzip_1099_ == 0)
{
v_args_1116_ = v___x_1147_;
v___y_1117_ = v_a_1101_;
goto v___jp_1115_;
}
else
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_obj_once(&l_Lake_tar___closed__10, &l_Lake_tar___closed__10_once, _init_l_Lake_tar___closed__10);
v_args_1116_ = v___x_1148_;
v___y_1117_ = v_a_1101_;
goto v___jp_1115_;
}
v___jp_1115_:
{
size_t v_sz_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
v_sz_1118_ = lean_array_size(v_excludePaths_1100_);
v___x_1119_ = ((size_t)0ULL);
lean_inc_ref(v_args_1116_);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_excludePaths_1100_, v_sz_1118_, v___x_1119_, v_args_1116_, v___y_1117_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v_a_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; uint8_t v___x_1135_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
v_a_1122_ = lean_ctor_get(v___x_1120_, 1);
lean_inc(v_a_1122_);
lean_dec_ref(v___x_1120_);
v___x_1123_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_1124_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_1125_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_1126_ = ((lean_object*)(l_Lake_tar___closed__0));
v___x_1127_ = lean_obj_once(&l_Lake_tar___closed__1, &l_Lake_tar___closed__1_once, _init_l_Lake_tar___closed__1);
v___x_1128_ = lean_array_push(v___x_1127_, v_file_1098_);
v___x_1129_ = lean_array_push(v___x_1128_, v___x_1125_);
v___x_1130_ = lean_array_push(v___x_1129_, v_dir_1097_);
v___x_1131_ = lean_array_push(v___x_1130_, v___x_1126_);
v___x_1132_ = l_Array_append___redArg(v_a_1121_, v___x_1131_);
lean_dec_ref(v___x_1131_);
v___x_1133_ = lean_box(0);
v___x_1134_ = l_System_Platform_isOSX;
v___x_1135_ = 1;
if (v___x_1134_ == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_1104_ = v_a_1122_;
v___y_1105_ = v___x_1132_;
v___y_1106_ = v___x_1123_;
v___y_1107_ = v___x_1133_;
v___y_1108_ = v___x_1124_;
v___y_1109_ = v___x_1135_;
v___y_1110_ = v___x_1136_;
goto v___jp_1103_;
}
else
{
lean_object* v___x_1137_; 
v___x_1137_ = ((lean_object*)(l_Lake_tar___closed__6));
v___y_1104_ = v_a_1122_;
v___y_1105_ = v___x_1132_;
v___y_1106_ = v___x_1123_;
v___y_1107_ = v___x_1133_;
v___y_1108_ = v___x_1124_;
v___y_1109_ = v___x_1135_;
v___y_1110_ = v___x_1137_;
goto v___jp_1103_;
}
}
else
{
lean_object* v_a_1138_; lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref(v_file_1098_);
lean_dec_ref(v_dir_1097_);
v_a_1138_ = lean_ctor_get(v___x_1120_, 0);
v_a_1139_ = lean_ctor_get(v___x_1120_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1120_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_inc(v_a_1138_);
lean_dec(v___x_1120_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1138_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec_ref(v_file_1098_);
lean_dec_ref(v_dir_1097_);
v_a_1149_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1149_);
lean_dec_ref(v___x_1114_);
v___x_1150_ = lean_io_error_to_string(v_a_1149_);
v___x_1151_ = 3;
v___x_1152_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set_uint8(v___x_1152_, sizeof(void*)*1, v___x_1151_);
v___x_1153_ = lean_array_get_size(v_a_1101_);
v___x_1154_ = lean_array_push(v_a_1101_, v___x_1152_);
v___x_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
return v___x_1155_;
}
v___jp_1103_:
{
uint8_t v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = 0;
lean_inc_ref(v___y_1110_);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1108_);
lean_inc_ref(v___y_1106_);
v___x_1112_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1112_, 0, v___y_1106_);
lean_ctor_set(v___x_1112_, 1, v___y_1108_);
lean_ctor_set(v___x_1112_, 2, v___y_1105_);
lean_ctor_set(v___x_1112_, 3, v___y_1107_);
lean_ctor_set(v___x_1112_, 4, v___y_1110_);
lean_ctor_set_uint8(v___x_1112_, sizeof(void*)*5, v___y_1109_);
lean_ctor_set_uint8(v___x_1112_, sizeof(void*)*5 + 1, v___x_1111_);
v___x_1113_ = l_Lake_proc(v___x_1112_, v___y_1109_, v___y_1104_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object* v_dir_1156_, lean_object* v_file_1157_, lean_object* v_gzip_1158_, lean_object* v_excludePaths_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
uint8_t v_gzip_boxed_1162_; lean_object* v_res_1163_; 
v_gzip_boxed_1162_ = lean_unbox(v_gzip_1158_);
v_res_1163_ = l_Lake_tar(v_dir_1156_, v_file_1157_, v_gzip_boxed_1162_, v_excludePaths_1159_, v_a_1160_);
lean_dec_ref(v_excludePaths_1159_);
return v_res_1163_;
}
}
lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Actions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Actions(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Lake_Util_FilePath(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Actions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Actions(builtin);
}
#ifdef __cplusplus
}
#endif
