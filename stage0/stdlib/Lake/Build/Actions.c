// Lean compiler output
// Module: Lake.Build.Actions
// Imports: public import Lake.Util.Log import Lake.Util.Proc import Lake.Util.FilePath import Lake.Util.IO import Init.Data.String.Search import Init.Data.String.TakeDrop import Init.System.Platform
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
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_io_remove_file(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___boxed(lean_object*);
static const lean_string_object l_Lake_compileLeanModule___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean exited with code "};
static const lean_object* l_Lake_compileLeanModule___lam__0___closed__0 = (const lean_object*)&l_Lake_compileLeanModule___lam__0___closed__0_value;
static const lean_string_object l_Lake_compileLeanModule___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stderr:\n"};
static const lean_object* l_Lake_compileLeanModule___lam__0___closed__1 = (const lean_object*)&l_Lake_compileLeanModule___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint32_t v_exitCode_9_, lean_object* v_stderr_10_, lean_object* v_____r_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___y_15_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_29_ = lean_string_utf8_byte_size(v_stderr_10_);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_nat_dec_eq(v___x_29_, v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_32_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__1));
v___x_33_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_33_, 0, v_stderr_10_);
lean_ctor_set(v___x_33_, 1, v___x_30_);
lean_ctor_set(v___x_33_, 2, v___x_29_);
v___x_34_ = l_String_Slice_trimAscii(v___x_33_);
v___x_35_ = l_String_Slice_toString(v___x_34_);
lean_dec_ref(v___x_34_);
v___x_36_ = lean_string_append(v___x_32_, v___x_35_);
lean_dec_ref(v___x_35_);
v___x_37_ = 1;
v___x_38_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_38_, 0, v___x_36_);
lean_ctor_set_uint8(v___x_38_, sizeof(void*)*1, v___x_37_);
v___x_39_ = lean_array_push(v___y_12_, v___x_38_);
v___y_15_ = v___x_39_;
goto v___jp_14_;
}
else
{
lean_dec_ref(v_stderr_10_);
v___y_15_ = v___y_12_;
goto v___jp_14_;
}
v___jp_14_:
{
uint32_t v___x_16_; uint8_t v___x_17_; 
v___x_16_ = 0;
v___x_17_ = lean_uint32_dec_eq(v_exitCode_9_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_18_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__0));
v___x_19_ = lean_uint32_to_nat(v_exitCode_9_);
v___x_20_ = l_Nat_reprFast(v___x_19_);
v___x_21_ = lean_string_append(v___x_18_, v___x_20_);
lean_dec_ref(v___x_20_);
v___x_22_ = 3;
v___x_23_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_23_, 0, v___x_21_);
lean_ctor_set_uint8(v___x_23_, sizeof(void*)*1, v___x_22_);
v___x_24_ = lean_array_get_size(v___y_15_);
v___x_25_ = lean_array_push(v___y_15_, v___x_23_);
v___x_26_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_24_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
return v___x_26_;
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_box(0);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v___y_15_);
return v___x_28_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object* v_exitCode_40_, lean_object* v_stderr_41_, lean_object* v_____r_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
uint32_t v_exitCode_boxed_45_; lean_object* v_res_46_; 
v_exitCode_boxed_45_ = lean_unbox_uint32(v_exitCode_40_);
lean_dec(v_exitCode_40_);
v_res_46_ = l_Lake_compileLeanModule___lam__0(v_exitCode_boxed_45_, v_stderr_41_, v_____r_42_, v___y_43_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(lean_object* v_a_47_, lean_object* v_b_48_, lean_object* v_relLeanFile_49_, lean_object* v_____r_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_a_54_; lean_object* v_toBaseMessage_56_; uint8_t v_isSilent_57_; 
v_toBaseMessage_56_ = lean_ctor_get(v_a_47_, 0);
lean_inc_ref(v_toBaseMessage_56_);
v_isSilent_57_ = lean_ctor_get_uint8(v_toBaseMessage_56_, sizeof(void*)*5 + 2);
if (v_isSilent_57_ == 0)
{
lean_object* v_kind_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_82_; 
v_kind_58_ = lean_ctor_get(v_a_47_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v_a_47_);
if (v_isSharedCheck_82_ == 0)
{
lean_object* v_unused_83_; 
v_unused_83_ = lean_ctor_get(v_a_47_, 0);
lean_dec(v_unused_83_);
v___x_60_ = v_a_47_;
v_isShared_61_ = v_isSharedCheck_82_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_kind_58_);
lean_dec(v_a_47_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_82_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_pos_62_; lean_object* v_endPos_63_; uint8_t v_keepFullRange_64_; uint8_t v_severity_65_; lean_object* v_caption_66_; lean_object* v_data_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_80_; 
v_pos_62_ = lean_ctor_get(v_toBaseMessage_56_, 1);
v_endPos_63_ = lean_ctor_get(v_toBaseMessage_56_, 2);
v_keepFullRange_64_ = lean_ctor_get_uint8(v_toBaseMessage_56_, sizeof(void*)*5);
v_severity_65_ = lean_ctor_get_uint8(v_toBaseMessage_56_, sizeof(void*)*5 + 1);
v_caption_66_ = lean_ctor_get(v_toBaseMessage_56_, 3);
v_data_67_ = lean_ctor_get(v_toBaseMessage_56_, 4);
v_isSharedCheck_80_ = !lean_is_exclusive(v_toBaseMessage_56_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v_toBaseMessage_56_, 0);
lean_dec(v_unused_81_);
v___x_69_ = v_toBaseMessage_56_;
v_isShared_70_ = v_isSharedCheck_80_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_data_67_);
lean_inc(v_caption_66_);
lean_inc(v_endPos_63_);
lean_inc(v_pos_62_);
lean_dec(v_toBaseMessage_56_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_80_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = l_Lake_mkRelPathString(v_relLeanFile_49_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_71_);
v___x_73_ = v___x_69_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_71_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_pos_62_);
lean_ctor_set(v_reuseFailAlloc_79_, 2, v_endPos_63_);
lean_ctor_set(v_reuseFailAlloc_79_, 3, v_caption_66_);
lean_ctor_set(v_reuseFailAlloc_79_, 4, v_data_67_);
lean_ctor_set_uint8(v_reuseFailAlloc_79_, sizeof(void*)*5, v_keepFullRange_64_);
lean_ctor_set_uint8(v_reuseFailAlloc_79_, sizeof(void*)*5 + 1, v_severity_65_);
lean_ctor_set_uint8(v_reuseFailAlloc_79_, sizeof(void*)*5 + 2, v_isSilent_57_);
v___x_73_ = v_reuseFailAlloc_79_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_75_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_73_);
v___x_75_ = v___x_60_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_kind_58_);
v___x_75_ = v_reuseFailAlloc_78_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = l_Lake_LogEntry_ofSerialMessage(v___x_75_);
v___x_77_ = lean_array_push(v___y_51_, v___x_76_);
v_a_54_ = v___x_77_;
goto v___jp_53_;
}
}
}
}
}
else
{
lean_dec_ref(v_toBaseMessage_56_);
lean_dec_ref(v_relLeanFile_49_);
lean_dec_ref(v_a_47_);
v_a_54_ = v___y_51_;
goto v___jp_53_;
}
v___jp_53_:
{
lean_object* v___x_55_; 
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v_b_48_);
lean_ctor_set(v___x_55_, 1, v_a_54_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0___boxed(lean_object* v_a_84_, lean_object* v_b_85_, lean_object* v_relLeanFile_86_, lean_object* v_____r_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(v_a_84_, v_b_85_, v_relLeanFile_86_, v_____r_87_, v___y_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(lean_object* v_relLeanFile_93_, lean_object* v___x_94_, lean_object* v___x_95_, lean_object* v___x_96_, lean_object* v_a_97_, lean_object* v_b_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_118_; lean_object* v___y_119_; lean_object* v_it_124_; lean_object* v_startInclusive_125_; lean_object* v_endExclusive_126_; 
if (lean_obj_tag(v_a_97_) == 0)
{
lean_object* v_currPos_144_; lean_object* v_searcher_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_171_; 
v_currPos_144_ = lean_ctor_get(v_a_97_, 0);
v_searcher_145_ = lean_ctor_get(v_a_97_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_a_97_);
if (v_isSharedCheck_171_ == 0)
{
v___x_147_ = v_a_97_;
v_isShared_148_ = v_isSharedCheck_171_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_searcher_145_);
lean_inc(v_currPos_144_);
lean_dec(v_a_97_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_171_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_startInclusive_149_; lean_object* v_endExclusive_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_startInclusive_149_ = lean_ctor_get(v___x_95_, 1);
v_endExclusive_150_ = lean_ctor_get(v___x_95_, 2);
v___x_151_ = lean_nat_sub(v_endExclusive_150_, v_startInclusive_149_);
v___x_152_ = lean_nat_dec_eq(v_searcher_145_, v___x_151_);
lean_dec(v___x_151_);
if (v___x_152_ == 0)
{
uint32_t v___x_153_; uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_153_ = 10;
v___x_154_ = lean_string_utf8_get_fast(v___x_94_, v_searcher_145_);
v___x_155_ = lean_uint32_dec_eq(v___x_154_, v___x_153_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = lean_string_utf8_next_fast(v___x_94_, v_searcher_145_);
lean_dec(v_searcher_145_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v___x_156_);
v___x_158_ = v___x_147_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_currPos_144_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_160_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
v_a_97_ = v___x_158_;
goto _start;
}
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_slice_164_; lean_object* v_nextIt_166_; 
v___x_161_ = lean_string_utf8_next_fast(v___x_94_, v_searcher_145_);
v___x_162_ = lean_nat_sub(v___x_161_, v_searcher_145_);
v___x_163_ = lean_nat_add(v_searcher_145_, v___x_162_);
lean_dec(v___x_162_);
v_slice_164_ = l_String_Slice_subslice_x21(v___x_95_, v_currPos_144_, v_searcher_145_);
lean_inc(v___x_163_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v___x_163_);
lean_ctor_set(v___x_147_, 0, v___x_163_);
v_nextIt_166_ = v___x_147_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_163_);
v_nextIt_166_ = v_reuseFailAlloc_169_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v_startInclusive_167_; lean_object* v_endExclusive_168_; 
v_startInclusive_167_ = lean_ctor_get(v_slice_164_, 0);
lean_inc(v_startInclusive_167_);
v_endExclusive_168_ = lean_ctor_get(v_slice_164_, 1);
lean_inc(v_endExclusive_168_);
lean_dec_ref(v_slice_164_);
v_it_124_ = v_nextIt_166_;
v_startInclusive_125_ = v_startInclusive_167_;
v_endExclusive_126_ = v_endExclusive_168_;
goto v___jp_123_;
}
}
}
else
{
lean_object* v___x_170_; 
lean_del_object(v___x_147_);
lean_dec(v_searcher_145_);
v___x_170_ = lean_box(1);
lean_inc(v___x_96_);
v_it_124_ = v___x_170_;
v_startInclusive_125_ = v_currPos_144_;
v_endExclusive_126_ = v___x_96_;
goto v___jp_123_;
}
}
}
else
{
lean_object* v___x_172_; 
lean_dec(v___x_96_);
lean_dec_ref(v_relLeanFile_93_);
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v_b_98_);
lean_ctor_set(v___x_172_, 1, v___y_99_);
return v___x_172_;
}
v___jp_101_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_string_append(v_b_98_, v___y_102_);
lean_dec_ref(v___y_102_);
v___x_105_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0));
v___x_106_ = lean_string_append(v___x_104_, v___x_105_);
v_a_97_ = v___y_103_;
v_b_98_ = v___x_106_;
goto _start;
}
v___jp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_111_ = lean_string_utf8_byte_size(v_b_98_);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_nat_dec_eq(v___x_111_, v___x_112_);
if (v___x_113_ == 0)
{
v___y_102_ = v___y_109_;
v___y_103_ = v___y_110_;
goto v___jp_101_;
}
else
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = lean_string_utf8_byte_size(v___y_109_);
v___x_115_ = lean_nat_dec_eq(v___x_114_, v___x_112_);
if (v___x_115_ == 0)
{
v___y_102_ = v___y_109_;
v___y_103_ = v___y_110_;
goto v___jp_101_;
}
else
{
lean_dec_ref(v___y_109_);
v_a_97_ = v___y_110_;
goto _start;
}
}
}
v___jp_117_:
{
if (lean_obj_tag(v___y_119_) == 0)
{
lean_object* v_a_120_; lean_object* v_a_121_; 
v_a_120_ = lean_ctor_get(v___y_119_, 0);
lean_inc(v_a_120_);
v_a_121_ = lean_ctor_get(v___y_119_, 1);
lean_inc(v_a_121_);
lean_dec_ref(v___y_119_);
v_a_97_ = v___y_118_;
v_b_98_ = v_a_120_;
v___y_99_ = v_a_121_;
goto _start;
}
else
{
lean_dec(v___y_118_);
lean_dec(v___x_96_);
lean_dec_ref(v_relLeanFile_93_);
return v___y_119_;
}
}
v___jp_123_:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_string_utf8_extract(v___x_94_, v_startInclusive_125_, v_endExclusive_126_);
lean_dec(v_endExclusive_126_);
lean_dec(v_startInclusive_125_);
lean_inc_ref(v___x_127_);
v___x_128_ = l_Lean_Json_parse(v___x_127_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_dec_ref(v___x_128_);
v___y_109_ = v___x_127_;
v___y_110_ = v_it_124_;
goto v___jp_108_;
}
else
{
lean_object* v_a_129_; lean_object* v___x_130_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_a_129_);
lean_dec_ref(v___x_128_);
v___x_130_ = l_Lean_instFromJsonSerialMessage_fromJson(v_a_129_);
if (lean_obj_tag(v___x_130_) == 1)
{
lean_object* v_a_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
lean_dec_ref(v___x_127_);
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref(v___x_130_);
v___x_132_ = lean_string_utf8_byte_size(v_b_98_);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_nat_dec_eq(v___x_132_, v___x_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_135_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1));
v___x_136_ = lean_string_append(v___x_135_, v_b_98_);
v___x_137_ = 1;
v___x_138_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_138_, 0, v___x_136_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*1, v___x_137_);
v___x_139_ = lean_box(0);
v___x_140_ = lean_array_push(v___y_99_, v___x_138_);
lean_inc_ref(v_relLeanFile_93_);
v___x_141_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(v_a_131_, v_b_98_, v_relLeanFile_93_, v___x_139_, v___x_140_);
v___y_118_ = v_it_124_;
v___y_119_ = v___x_141_;
goto v___jp_117_;
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_box(0);
lean_inc_ref(v_relLeanFile_93_);
v___x_143_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(v_a_131_, v_b_98_, v_relLeanFile_93_, v___x_142_, v___y_99_);
v___y_118_ = v_it_124_;
v___y_119_ = v___x_143_;
goto v___jp_117_;
}
}
else
{
lean_dec_ref(v___x_130_);
v___y_109_ = v___x_127_;
v___y_110_ = v_it_124_;
goto v___jp_108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___boxed(lean_object* v_relLeanFile_173_, lean_object* v___x_174_, lean_object* v___x_175_, lean_object* v___x_176_, lean_object* v_a_177_, lean_object* v_b_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(v_relLeanFile_173_, v___x_174_, v___x_175_, v___x_176_, v_a_177_, v_b_178_, v___y_179_);
lean_dec_ref(v___x_175_);
lean_dec_ref(v___x_174_);
return v_res_181_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__1(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_183_ = ((lean_object*)(l_Lake_compileLeanModule___closed__0));
v___x_184_ = lean_unsigned_to_nat(2u);
v___x_185_ = lean_mk_empty_array_with_capacity(v___x_184_);
v___x_186_ = lean_array_push(v___x_185_, v___x_183_);
return v___x_186_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__9(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_195_ = ((lean_object*)(l_Lake_compileLeanModule___closed__8));
v___x_196_ = lean_unsigned_to_nat(2u);
v___x_197_ = lean_mk_empty_array_with_capacity(v___x_196_);
v___x_198_ = lean_array_push(v___x_197_, v___x_195_);
return v___x_198_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__11(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_200_ = ((lean_object*)(l_Lake_compileLeanModule___closed__10));
v___x_201_ = lean_unsigned_to_nat(2u);
v___x_202_ = lean_mk_empty_array_with_capacity(v___x_201_);
v___x_203_ = lean_array_push(v___x_202_, v___x_200_);
return v___x_203_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__13(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_205_ = ((lean_object*)(l_Lake_compileLeanModule___closed__12));
v___x_206_ = lean_unsigned_to_nat(2u);
v___x_207_ = lean_mk_empty_array_with_capacity(v___x_206_);
v___x_208_ = lean_array_push(v___x_207_, v___x_205_);
return v___x_208_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__15(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_210_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_211_ = lean_unsigned_to_nat(2u);
v___x_212_ = lean_mk_empty_array_with_capacity(v___x_211_);
v___x_213_ = lean_array_push(v___x_212_, v___x_210_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object* v_leanFile_214_, lean_object* v_relLeanFile_215_, lean_object* v_setup_216_, lean_object* v_setupFile_217_, lean_object* v_arts_218_, lean_object* v_leanArgs_219_, lean_object* v_leanPath_220_, lean_object* v_lean_221_, lean_object* v_a_222_){
_start:
{
lean_object* v___y_225_; lean_object* v_a_226_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v_args_233_; lean_object* v___y_234_; lean_object* v_olean_x3f_321_; lean_object* v_ilean_x3f_322_; lean_object* v_c_x3f_323_; lean_object* v_bc_x3f_324_; lean_object* v_args_326_; lean_object* v___y_327_; lean_object* v_args_341_; lean_object* v___y_342_; lean_object* v_args_356_; lean_object* v___y_357_; lean_object* v_args_370_; 
v_olean_x3f_321_ = lean_ctor_get(v_arts_218_, 1);
lean_inc(v_olean_x3f_321_);
v_ilean_x3f_322_ = lean_ctor_get(v_arts_218_, 4);
lean_inc(v_ilean_x3f_322_);
v_c_x3f_323_ = lean_ctor_get(v_arts_218_, 6);
lean_inc(v_c_x3f_323_);
v_bc_x3f_324_ = lean_ctor_get(v_arts_218_, 7);
lean_inc(v_bc_x3f_324_);
lean_dec_ref(v_arts_218_);
v_args_370_ = lean_array_push(v_leanArgs_219_, v_leanFile_214_);
if (lean_obj_tag(v_olean_x3f_321_) == 1)
{
lean_object* v_val_371_; lean_object* v___x_372_; 
v_val_371_ = lean_ctor_get(v_olean_x3f_321_, 0);
lean_inc(v_val_371_);
lean_dec_ref(v_olean_x3f_321_);
lean_inc(v_val_371_);
v___x_372_ = l_Lake_createParentDirs(v_val_371_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec_ref(v___x_372_);
v___x_373_ = lean_obj_once(&l_Lake_compileLeanModule___closed__15, &l_Lake_compileLeanModule___closed__15_once, _init_l_Lake_compileLeanModule___closed__15);
v___x_374_ = lean_array_push(v___x_373_, v_val_371_);
v___x_375_ = l_Array_append___redArg(v_args_370_, v___x_374_);
lean_dec_ref(v___x_374_);
v_args_356_ = v___x_375_;
v___y_357_ = v_a_222_;
goto v___jp_355_;
}
else
{
lean_object* v_a_376_; lean_object* v___x_377_; uint8_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec(v_val_371_);
lean_dec_ref(v_args_370_);
lean_dec(v_bc_x3f_324_);
lean_dec(v_c_x3f_323_);
lean_dec(v_ilean_x3f_322_);
lean_dec_ref(v_lean_221_);
lean_dec(v_leanPath_220_);
lean_dec_ref(v_setupFile_217_);
lean_dec_ref(v_setup_216_);
lean_dec_ref(v_relLeanFile_215_);
v_a_376_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_376_);
lean_dec_ref(v___x_372_);
v___x_377_ = lean_io_error_to_string(v_a_376_);
v___x_378_ = 3;
v___x_379_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*1, v___x_378_);
v___x_380_ = lean_array_get_size(v_a_222_);
v___x_381_ = lean_array_push(v_a_222_, v___x_379_);
v___x_382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
return v___x_382_;
}
}
else
{
lean_dec(v_olean_x3f_321_);
v_args_356_ = v_args_370_;
v___y_357_ = v_a_222_;
goto v___jp_355_;
}
v___jp_224_:
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_227_, 0, v___y_225_);
lean_ctor_set(v___x_227_, 1, v_a_226_);
return v___x_227_;
}
v___jp_228_:
{
if (lean_obj_tag(v___y_230_) == 0)
{
lean_dec(v___y_229_);
return v___y_230_;
}
else
{
lean_object* v_a_231_; 
v_a_231_ = lean_ctor_get(v___y_230_, 1);
lean_inc(v_a_231_);
lean_dec_ref(v___y_230_);
v___y_225_ = v___y_229_;
v_a_226_ = v_a_231_;
goto v___jp_224_;
}
}
v___jp_232_:
{
lean_object* v___x_235_; 
lean_inc_ref(v_setupFile_217_);
v___x_235_ = l_Lake_createParentDirs(v_setupFile_217_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec_ref(v___x_235_);
v___x_236_ = l_Lean_instToJsonModuleSetup_toJson(v_setup_216_);
v___x_237_ = lean_unsigned_to_nat(80u);
v___x_238_ = l_Lean_Json_pretty(v___x_236_, v___x_237_);
v___x_239_ = l_IO_FS_writeFile(v_setupFile_217_, v___x_238_);
lean_dec_ref(v___x_238_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_305_; 
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_239_, 0);
lean_dec(v_unused_306_);
v___x_241_ = v___x_239_;
v_isShared_242_ = v_isSharedCheck_305_;
goto v_resetjp_240_;
}
else
{
lean_dec(v___x_239_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_305_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_243_ = lean_obj_once(&l_Lake_compileLeanModule___closed__1, &l_Lake_compileLeanModule___closed__1_once, _init_l_Lake_compileLeanModule___closed__1);
v___x_244_ = lean_array_push(v___x_243_, v_setupFile_217_);
v___x_245_ = l_Array_append___redArg(v_args_233_, v___x_244_);
lean_dec_ref(v___x_244_);
v___x_246_ = ((lean_object*)(l_Lake_compileLeanModule___closed__2));
v___x_247_ = lean_array_push(v___x_245_, v___x_246_);
v___x_248_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_249_ = lean_box(0);
v___x_250_ = ((lean_object*)(l_Lake_compileLeanModule___closed__4));
v___x_251_ = l_System_SearchPath_toString(v_leanPath_220_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 1);
lean_ctor_set(v___x_241_, 0, v___x_251_);
v___x_253_ = v___x_241_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_304_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; uint8_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_250_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_mk_empty_array_with_capacity(v___x_255_);
v___x_257_ = lean_array_push(v___x_256_, v___x_254_);
v___x_258_ = 1;
v___x_259_ = 0;
lean_inc_ref(v_lean_221_);
v___x_260_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_260_, 0, v___x_248_);
lean_ctor_set(v___x_260_, 1, v_lean_221_);
lean_ctor_set(v___x_260_, 2, v___x_247_);
lean_ctor_set(v___x_260_, 3, v___x_249_);
lean_ctor_set(v___x_260_, 4, v___x_257_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*5, v___x_258_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*5 + 1, v___x_259_);
v___x_261_ = lean_array_get_size(v___y_234_);
lean_inc_ref(v___x_260_);
v___x_262_ = l_Lake_mkCmdLog(v___x_260_);
v___x_263_ = 0;
v___x_264_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set_uint8(v___x_264_, sizeof(void*)*1, v___x_263_);
v___x_265_ = lean_array_push(v___y_234_, v___x_264_);
v___x_266_ = l_IO_Process_output(v___x_260_, v___x_249_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; uint32_t v_exitCode_268_; lean_object* v_stdout_269_; lean_object* v_stderr_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
lean_dec_ref(v_lean_221_);
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref(v___x_266_);
v_exitCode_268_ = lean_ctor_get_uint32(v_a_267_, sizeof(void*)*2);
v_stdout_269_ = lean_ctor_get(v_a_267_, 0);
lean_inc_ref(v_stdout_269_);
v_stderr_270_ = lean_ctor_get(v_a_267_, 1);
lean_inc_ref(v_stderr_270_);
lean_dec(v_a_267_);
v___x_271_ = lean_string_utf8_byte_size(v_stdout_269_);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_nat_dec_eq(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
lean_inc_ref(v_stdout_269_);
v___x_274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_274_, 0, v_stdout_269_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
lean_ctor_set(v___x_274_, 2, v___x_271_);
v___x_275_ = ((lean_object*)(l_Lake_compileLeanModule___closed__5));
v___x_276_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0(v___x_274_);
v___x_277_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(v_relLeanFile_215_, v_stdout_269_, v___x_274_, v___x_271_, v___x_276_, v___x_275_, v___x_265_);
lean_dec_ref(v___x_274_);
lean_dec_ref(v_stdout_269_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v_a_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_a_278_);
v_a_279_ = lean_ctor_get(v___x_277_, 1);
lean_inc(v_a_279_);
lean_dec_ref(v___x_277_);
v___x_280_ = lean_string_utf8_byte_size(v_a_278_);
v___x_281_ = lean_nat_dec_eq(v___x_280_, v___x_272_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_282_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1));
v___x_283_ = lean_string_append(v___x_282_, v_a_278_);
lean_dec(v_a_278_);
v___x_284_ = 1;
v___x_285_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*1, v___x_284_);
v___x_286_ = lean_box(0);
v___x_287_ = lean_array_push(v_a_279_, v___x_285_);
v___x_288_ = l_Lake_compileLeanModule___lam__0(v_exitCode_268_, v_stderr_270_, v___x_286_, v___x_287_);
v___y_229_ = v___x_261_;
v___y_230_ = v___x_288_;
goto v___jp_228_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_a_278_);
v___x_289_ = lean_box(0);
v___x_290_ = l_Lake_compileLeanModule___lam__0(v_exitCode_268_, v_stderr_270_, v___x_289_, v_a_279_);
v___y_229_ = v___x_261_;
v___y_230_ = v___x_290_;
goto v___jp_228_;
}
}
else
{
lean_object* v_a_291_; 
lean_dec_ref(v_stderr_270_);
v_a_291_ = lean_ctor_get(v___x_277_, 1);
lean_inc(v_a_291_);
lean_dec_ref(v___x_277_);
v___y_225_ = v___x_261_;
v_a_226_ = v_a_291_;
goto v___jp_224_;
}
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec_ref(v_stdout_269_);
lean_dec_ref(v_relLeanFile_215_);
v___x_292_ = lean_box(0);
v___x_293_ = l_Lake_compileLeanModule___lam__0(v_exitCode_268_, v_stderr_270_, v___x_292_, v___x_265_);
v___y_229_ = v___x_261_;
v___y_230_ = v___x_293_;
goto v___jp_228_;
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec_ref(v_relLeanFile_215_);
v_a_294_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_294_);
lean_dec_ref(v___x_266_);
v___x_295_ = ((lean_object*)(l_Lake_compileLeanModule___closed__6));
v___x_296_ = lean_string_append(v___x_295_, v_lean_221_);
lean_dec_ref(v_lean_221_);
v___x_297_ = ((lean_object*)(l_Lake_compileLeanModule___closed__7));
v___x_298_ = lean_string_append(v___x_296_, v___x_297_);
v___x_299_ = lean_io_error_to_string(v_a_294_);
v___x_300_ = lean_string_append(v___x_298_, v___x_299_);
lean_dec_ref(v___x_299_);
v___x_301_ = 3;
v___x_302_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*1, v___x_301_);
v___x_303_ = lean_array_push(v___x_265_, v___x_302_);
v___y_225_ = v___x_261_;
v_a_226_ = v___x_303_;
goto v___jp_224_;
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec_ref(v_args_233_);
lean_dec_ref(v_lean_221_);
lean_dec(v_leanPath_220_);
lean_dec_ref(v_setupFile_217_);
lean_dec_ref(v_relLeanFile_215_);
v_a_307_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_307_);
lean_dec_ref(v___x_239_);
v___x_308_ = lean_io_error_to_string(v_a_307_);
v___x_309_ = 3;
v___x_310_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set_uint8(v___x_310_, sizeof(void*)*1, v___x_309_);
v___x_311_ = lean_array_get_size(v___y_234_);
v___x_312_ = lean_array_push(v___y_234_, v___x_310_);
v___x_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
return v___x_313_;
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v_args_233_);
lean_dec_ref(v_lean_221_);
lean_dec(v_leanPath_220_);
lean_dec_ref(v_setupFile_217_);
lean_dec_ref(v_setup_216_);
lean_dec_ref(v_relLeanFile_215_);
v_a_314_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_314_);
lean_dec_ref(v___x_235_);
v___x_315_ = lean_io_error_to_string(v_a_314_);
v___x_316_ = 3;
v___x_317_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*1, v___x_316_);
v___x_318_ = lean_array_get_size(v___y_234_);
v___x_319_ = lean_array_push(v___y_234_, v___x_317_);
v___x_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
return v___x_320_;
}
}
v___jp_325_:
{
if (lean_obj_tag(v_bc_x3f_324_) == 1)
{
lean_object* v_val_328_; lean_object* v___x_329_; 
v_val_328_ = lean_ctor_get(v_bc_x3f_324_, 0);
lean_inc(v_val_328_);
lean_dec_ref(v_bc_x3f_324_);
lean_inc(v_val_328_);
v___x_329_ = l_Lake_createParentDirs(v_val_328_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec_ref(v___x_329_);
v___x_330_ = lean_obj_once(&l_Lake_compileLeanModule___closed__9, &l_Lake_compileLeanModule___closed__9_once, _init_l_Lake_compileLeanModule___closed__9);
v___x_331_ = lean_array_push(v___x_330_, v_val_328_);
v___x_332_ = l_Array_append___redArg(v_args_326_, v___x_331_);
lean_dec_ref(v___x_331_);
v_args_233_ = v___x_332_;
v___y_234_ = v___y_327_;
goto v___jp_232_;
}
else
{
lean_object* v_a_333_; lean_object* v___x_334_; uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v_val_328_);
lean_dec_ref(v_args_326_);
lean_dec_ref(v_lean_221_);
lean_dec(v_leanPath_220_);
lean_dec_ref(v_setupFile_217_);
lean_dec_ref(v_setup_216_);
lean_dec_ref(v_relLeanFile_215_);
v_a_333_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_333_);
lean_dec_ref(v___x_329_);
v___x_334_ = lean_io_error_to_string(v_a_333_);
v___x_335_ = 3;
v___x_336_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*1, v___x_335_);
v___x_337_ = lean_array_get_size(v___y_327_);
v___x_338_ = lean_array_push(v___y_327_, v___x_336_);
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
return v___x_339_;
}
}
else
{
lean_dec(v_bc_x3f_324_);
v_args_233_ = v_args_326_;
v___y_234_ = v___y_327_;
goto v___jp_232_;
}
}
v___jp_340_:
{
if (lean_obj_tag(v_c_x3f_323_) == 1)
{
lean_object* v_val_343_; lean_object* v___x_344_; 
v_val_343_ = lean_ctor_get(v_c_x3f_323_, 0);
lean_inc(v_val_343_);
lean_dec_ref(v_c_x3f_323_);
lean_inc(v_val_343_);
v___x_344_ = l_Lake_createParentDirs(v_val_343_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec_ref(v___x_344_);
v___x_345_ = lean_obj_once(&l_Lake_compileLeanModule___closed__11, &l_Lake_compileLeanModule___closed__11_once, _init_l_Lake_compileLeanModule___closed__11);
v___x_346_ = lean_array_push(v___x_345_, v_val_343_);
v___x_347_ = l_Array_append___redArg(v_args_341_, v___x_346_);
lean_dec_ref(v___x_346_);
v_args_326_ = v___x_347_;
v___y_327_ = v___y_342_;
goto v___jp_325_;
}
else
{
lean_object* v_a_348_; lean_object* v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v_val_343_);
lean_dec_ref(v_args_341_);
lean_dec(v_bc_x3f_324_);
lean_dec_ref(v_lean_221_);
lean_dec(v_leanPath_220_);
lean_dec_ref(v_setupFile_217_);
lean_dec_ref(v_setup_216_);
lean_dec_ref(v_relLeanFile_215_);
v_a_348_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_348_);
lean_dec_ref(v___x_344_);
v___x_349_ = lean_io_error_to_string(v_a_348_);
v___x_350_ = 3;
v___x_351_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*1, v___x_350_);
v___x_352_ = lean_array_get_size(v___y_342_);
v___x_353_ = lean_array_push(v___y_342_, v___x_351_);
v___x_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
return v___x_354_;
}
}
else
{
lean_dec(v_c_x3f_323_);
v_args_326_ = v_args_341_;
v___y_327_ = v___y_342_;
goto v___jp_325_;
}
}
v___jp_355_:
{
if (lean_obj_tag(v_ilean_x3f_322_) == 1)
{
lean_object* v_val_358_; lean_object* v___x_359_; 
v_val_358_ = lean_ctor_get(v_ilean_x3f_322_, 0);
lean_inc(v_val_358_);
lean_dec_ref(v_ilean_x3f_322_);
lean_inc(v_val_358_);
v___x_359_ = l_Lake_createParentDirs(v_val_358_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec_ref(v___x_359_);
v___x_360_ = lean_obj_once(&l_Lake_compileLeanModule___closed__13, &l_Lake_compileLeanModule___closed__13_once, _init_l_Lake_compileLeanModule___closed__13);
v___x_361_ = lean_array_push(v___x_360_, v_val_358_);
v___x_362_ = l_Array_append___redArg(v_args_356_, v___x_361_);
lean_dec_ref(v___x_361_);
v_args_341_ = v___x_362_;
v___y_342_ = v___y_357_;
goto v___jp_340_;
}
else
{
lean_object* v_a_363_; lean_object* v___x_364_; uint8_t v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec(v_val_358_);
lean_dec_ref(v_args_356_);
lean_dec(v_bc_x3f_324_);
lean_dec(v_c_x3f_323_);
lean_dec_ref(v_lean_221_);
lean_dec(v_leanPath_220_);
lean_dec_ref(v_setupFile_217_);
lean_dec_ref(v_setup_216_);
lean_dec_ref(v_relLeanFile_215_);
v_a_363_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_363_);
lean_dec_ref(v___x_359_);
v___x_364_ = lean_io_error_to_string(v_a_363_);
v___x_365_ = 3;
v___x_366_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*1, v___x_365_);
v___x_367_ = lean_array_get_size(v___y_357_);
v___x_368_ = lean_array_push(v___y_357_, v___x_366_);
v___x_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
return v___x_369_;
}
}
else
{
lean_dec(v_ilean_x3f_322_);
v_args_341_ = v_args_356_;
v___y_342_ = v___y_357_;
goto v___jp_340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object* v_leanFile_383_, lean_object* v_relLeanFile_384_, lean_object* v_setup_385_, lean_object* v_setupFile_386_, lean_object* v_arts_387_, lean_object* v_leanArgs_388_, lean_object* v_leanPath_389_, lean_object* v_lean_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lake_compileLeanModule(v_leanFile_383_, v_relLeanFile_384_, v_setup_385_, v_setupFile_386_, v_arts_387_, v_leanArgs_388_, v_leanPath_389_, v_lean_390_, v_a_391_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1(lean_object* v_relLeanFile_394_, lean_object* v___x_395_, lean_object* v___x_396_, lean_object* v___x_397_, lean_object* v_inst_398_, lean_object* v_R_399_, lean_object* v_a_400_, lean_object* v_b_401_, lean_object* v_c_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(v_relLeanFile_394_, v___x_395_, v___x_396_, v___x_397_, v_a_400_, v_b_401_, v___y_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___boxed(lean_object* v_relLeanFile_406_, lean_object* v___x_407_, lean_object* v___x_408_, lean_object* v___x_409_, lean_object* v_inst_410_, lean_object* v_R_411_, lean_object* v_a_412_, lean_object* v_b_413_, lean_object* v_c_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1(v_relLeanFile_406_, v___x_407_, v___x_408_, v___x_409_, v_inst_410_, v_R_411_, v_a_412_, v_b_413_, v_c_414_, v___y_415_);
lean_dec_ref(v___x_408_);
lean_dec_ref(v___x_407_);
return v_res_417_;
}
}
static lean_object* _init_l_Lake_compileO___closed__0(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_418_ = ((lean_object*)(l_Lake_compileLeanModule___closed__10));
v___x_419_ = lean_unsigned_to_nat(4u);
v___x_420_ = lean_mk_empty_array_with_capacity(v___x_419_);
v___x_421_ = lean_array_push(v___x_420_, v___x_418_);
return v___x_421_;
}
}
static lean_object* _init_l_Lake_compileO___closed__1(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_423_ = lean_obj_once(&l_Lake_compileO___closed__0, &l_Lake_compileO___closed__0_once, _init_l_Lake_compileO___closed__0);
v___x_424_ = lean_array_push(v___x_423_, v___x_422_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object* v_oFile_427_, lean_object* v_srcFile_428_, lean_object* v_moreArgs_429_, lean_object* v_compiler_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; 
lean_inc_ref(v_oFile_427_);
v___x_433_ = l_Lake_createParentDirs(v_oFile_427_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec_ref(v___x_433_);
v___x_434_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_435_ = lean_obj_once(&l_Lake_compileO___closed__1, &l_Lake_compileO___closed__1_once, _init_l_Lake_compileO___closed__1);
v___x_436_ = lean_array_push(v___x_435_, v_oFile_427_);
v___x_437_ = lean_array_push(v___x_436_, v_srcFile_428_);
v___x_438_ = l_Array_append___redArg(v___x_437_, v_moreArgs_429_);
v___x_439_ = lean_box(0);
v___x_440_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_441_ = 1;
v___x_442_ = 0;
v___x_443_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_443_, 0, v___x_434_);
lean_ctor_set(v___x_443_, 1, v_compiler_430_);
lean_ctor_set(v___x_443_, 2, v___x_438_);
lean_ctor_set(v___x_443_, 3, v___x_439_);
lean_ctor_set(v___x_443_, 4, v___x_440_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*5, v___x_441_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*5 + 1, v___x_442_);
v___x_444_ = l_Lake_proc(v___x_443_, v___x_442_, v_a_431_);
return v___x_444_;
}
else
{
lean_object* v_a_445_; lean_object* v___x_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec_ref(v_compiler_430_);
lean_dec_ref(v_srcFile_428_);
lean_dec_ref(v_oFile_427_);
v_a_445_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_445_);
lean_dec_ref(v___x_433_);
v___x_446_ = lean_io_error_to_string(v_a_445_);
v___x_447_ = 3;
v___x_448_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*1, v___x_447_);
v___x_449_ = lean_array_get_size(v_a_431_);
v___x_450_ = lean_array_push(v_a_431_, v___x_448_);
v___x_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object* v_oFile_452_, lean_object* v_srcFile_453_, lean_object* v_moreArgs_454_, lean_object* v_compiler_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lake_compileO(v_oFile_452_, v_srcFile_453_, v_moreArgs_454_, v_compiler_455_, v_a_456_);
lean_dec_ref(v_moreArgs_454_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(lean_object* v___x_459_, lean_object* v___y_460_, lean_object* v_a_461_, lean_object* v_b_462_){
_start:
{
lean_object* v_startInclusive_463_; lean_object* v_endExclusive_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_startInclusive_463_ = lean_ctor_get(v___x_459_, 1);
v_endExclusive_464_ = lean_ctor_get(v___x_459_, 2);
v___x_465_ = lean_nat_sub(v_endExclusive_464_, v_startInclusive_463_);
v___x_466_ = lean_nat_dec_eq(v_a_461_, v___x_465_);
lean_dec(v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; uint32_t v___x_468_; uint32_t v___x_469_; uint8_t v___y_471_; uint8_t v___x_477_; 
v___x_467_ = lean_string_utf8_next_fast(v___y_460_, v_a_461_);
v___x_468_ = lean_string_utf8_get_fast(v___y_460_, v_a_461_);
lean_dec(v_a_461_);
v___x_469_ = 92;
v___x_477_ = lean_uint32_dec_eq(v___x_468_, v___x_469_);
if (v___x_477_ == 0)
{
uint32_t v___x_478_; uint8_t v___x_479_; 
v___x_478_ = 34;
v___x_479_ = lean_uint32_dec_eq(v___x_468_, v___x_478_);
v___y_471_ = v___x_479_;
goto v___jp_470_;
}
else
{
v___y_471_ = v___x_477_;
goto v___jp_470_;
}
v___jp_470_:
{
if (v___y_471_ == 0)
{
lean_object* v___x_472_; 
v___x_472_ = lean_string_push(v_b_462_, v___x_468_);
v_a_461_ = v___x_467_;
v_b_462_ = v___x_472_;
goto _start;
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_string_push(v_b_462_, v___x_469_);
v___x_475_ = lean_string_push(v___x_474_, v___x_468_);
v_a_461_ = v___x_467_;
v_b_462_ = v___x_475_;
goto _start;
}
}
}
else
{
lean_dec(v_a_461_);
return v_b_462_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg___boxed(lean_object* v___x_480_, lean_object* v___y_481_, lean_object* v_a_482_, lean_object* v_b_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_480_, v___y_481_, v_a_482_, v_b_483_);
lean_dec_ref(v___y_481_);
lean_dec_ref(v___x_480_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(lean_object* v_a_487_, lean_object* v_as_488_, size_t v_i_489_, size_t v_stop_490_, lean_object* v_b_491_, lean_object* v___y_492_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = lean_usize_dec_eq(v_i_489_, v_stop_490_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_495_ = lean_array_uget_borrowed(v_as_488_, v_i_489_);
v___x_496_ = ((lean_object*)(l_Lake_compileLeanModule___closed__5));
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = lean_string_utf8_byte_size(v___x_495_);
lean_inc(v___x_495_);
v___x_499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_499_, 0, v___x_495_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
lean_ctor_set(v___x_499_, 2, v___x_498_);
v___x_500_ = l_String_Slice_positions(v___x_499_);
v___x_501_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_499_, v___x_495_, v___x_500_, v___x_496_);
lean_dec_ref(v___x_499_);
v___x_502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0));
v___x_503_ = lean_string_append(v___x_502_, v___x_501_);
lean_dec_ref(v___x_501_);
v___x_504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1));
v___x_505_ = lean_string_append(v___x_503_, v___x_504_);
v___x_506_ = lean_io_prim_handle_put_str(v_a_487_, v___x_505_);
lean_dec_ref(v___x_505_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; size_t v___x_508_; size_t v___x_509_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v___x_506_);
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_add(v_i_489_, v___x_508_);
v_i_489_ = v___x_509_;
v_b_491_ = v_a_507_;
goto _start;
}
else
{
lean_object* v_a_511_; lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_a_511_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v___x_506_);
v___x_512_ = lean_io_error_to_string(v_a_511_);
v___x_513_ = 3;
v___x_514_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*1, v___x_513_);
v___x_515_ = lean_array_get_size(v___y_492_);
v___x_516_ = lean_array_push(v___y_492_, v___x_514_);
v___x_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
return v___x_517_;
}
}
else
{
lean_object* v___x_518_; 
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_b_491_);
lean_ctor_set(v___x_518_, 1, v___y_492_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___boxed(lean_object* v_a_519_, lean_object* v_as_520_, lean_object* v_i_521_, lean_object* v_stop_522_, lean_object* v_b_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
size_t v_i_boxed_526_; size_t v_stop_boxed_527_; lean_object* v_res_528_; 
v_i_boxed_526_ = lean_unbox_usize(v_i_521_);
lean_dec(v_i_521_);
v_stop_boxed_527_ = lean_unbox_usize(v_stop_522_);
lean_dec(v_stop_522_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_519_, v_as_520_, v_i_boxed_526_, v_stop_boxed_527_, v_b_523_, v___y_524_);
lean_dec_ref(v_as_520_);
lean_dec(v_a_519_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object* v_basePath_531_, lean_object* v_args_532_, lean_object* v_a_533_){
_start:
{
lean_object* v___x_535_; lean_object* v_rspFile_536_; lean_object* v_a_538_; lean_object* v___y_546_; uint8_t v___x_557_; lean_object* v___x_558_; 
v___x_535_ = ((lean_object*)(l_Lake_mkArgs___closed__0));
v_rspFile_536_ = l_System_FilePath_addExtension(v_basePath_531_, v___x_535_);
v___x_557_ = 1;
v___x_558_ = lean_io_prim_handle_mk(v_rspFile_536_, v___x_557_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref(v___x_558_);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_array_get_size(v_args_532_);
v___x_562_ = lean_nat_dec_lt(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_dec(v_a_559_);
v_a_538_ = v_a_533_;
goto v___jp_537_;
}
else
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = lean_box(0);
v___x_564_ = lean_nat_dec_le(v___x_561_, v___x_561_);
if (v___x_564_ == 0)
{
if (v___x_562_ == 0)
{
lean_dec(v_a_559_);
v_a_538_ = v_a_533_;
goto v___jp_537_;
}
else
{
size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; 
v___x_565_ = ((size_t)0ULL);
v___x_566_ = lean_usize_of_nat(v___x_561_);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_559_, v_args_532_, v___x_565_, v___x_566_, v___x_563_, v_a_533_);
lean_dec(v_a_559_);
v___y_546_ = v___x_567_;
goto v___jp_545_;
}
}
else
{
size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
v___x_568_ = ((size_t)0ULL);
v___x_569_ = lean_usize_of_nat(v___x_561_);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_559_, v_args_532_, v___x_568_, v___x_569_, v___x_563_, v_a_533_);
lean_dec(v_a_559_);
v___y_546_ = v___x_570_;
goto v___jp_545_;
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec_ref(v_rspFile_536_);
v_a_571_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_571_);
lean_dec_ref(v___x_558_);
v___x_572_ = lean_io_error_to_string(v_a_571_);
v___x_573_ = 3;
v___x_574_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*1, v___x_573_);
v___x_575_ = lean_array_get_size(v_a_533_);
v___x_576_ = lean_array_push(v_a_533_, v___x_574_);
v___x_577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
return v___x_577_;
}
v___jp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_539_ = ((lean_object*)(l_Lake_mkArgs___closed__1));
v___x_540_ = lean_string_append(v___x_539_, v_rspFile_536_);
lean_dec_ref(v_rspFile_536_);
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_mk_empty_array_with_capacity(v___x_541_);
v___x_543_ = lean_array_push(v___x_542_, v___x_540_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v_a_538_);
return v___x_544_;
}
v___jp_545_:
{
if (lean_obj_tag(v___y_546_) == 0)
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v___y_546_, 1);
lean_inc(v_a_547_);
lean_dec_ref(v___y_546_);
v_a_538_ = v_a_547_;
goto v___jp_537_;
}
else
{
lean_object* v_a_548_; lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec_ref(v_rspFile_536_);
v_a_548_ = lean_ctor_get(v___y_546_, 0);
v_a_549_ = lean_ctor_get(v___y_546_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v___y_546_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___y_546_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_inc(v_a_548_);
lean_dec(v___y_546_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_548_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs___boxed(lean_object* v_basePath_578_, lean_object* v_args_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lake_mkArgs(v_basePath_578_, v_args_579_, v_a_580_);
lean_dec_ref(v_args_579_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(lean_object* v___x_583_, lean_object* v___y_584_, lean_object* v_inst_585_, lean_object* v_R_586_, lean_object* v_a_587_, lean_object* v_b_588_, lean_object* v_c_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_583_, v___y_584_, v_a_587_, v_b_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(lean_object* v___x_591_, lean_object* v___y_592_, lean_object* v_inst_593_, lean_object* v_R_594_, lean_object* v_a_595_, lean_object* v_b_596_, lean_object* v_c_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(v___x_591_, v___y_592_, v_inst_593_, v_R_594_, v_a_595_, v_b_596_, v_c_597_);
lean_dec_ref(v___y_592_);
lean_dec_ref(v___x_591_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(size_t v_sz_599_, size_t v_i_600_, lean_object* v_bs_601_){
_start:
{
uint8_t v___x_602_; 
v___x_602_ = lean_usize_dec_lt(v_i_600_, v_sz_599_);
if (v___x_602_ == 0)
{
return v_bs_601_;
}
else
{
lean_object* v_v_603_; lean_object* v___x_604_; lean_object* v_bs_x27_605_; size_t v___x_606_; size_t v___x_607_; lean_object* v___x_608_; 
v_v_603_ = lean_array_uget(v_bs_601_, v_i_600_);
v___x_604_ = lean_unsigned_to_nat(0u);
v_bs_x27_605_ = lean_array_uset(v_bs_601_, v_i_600_, v___x_604_);
v___x_606_ = ((size_t)1ULL);
v___x_607_ = lean_usize_add(v_i_600_, v___x_606_);
v___x_608_ = lean_array_uset(v_bs_x27_605_, v_i_600_, v_v_603_);
v_i_600_ = v___x_607_;
v_bs_601_ = v___x_608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0___boxed(lean_object* v_sz_610_, lean_object* v_i_611_, lean_object* v_bs_612_){
_start:
{
size_t v_sz_boxed_613_; size_t v_i_boxed_614_; lean_object* v_res_615_; 
v_sz_boxed_613_ = lean_unbox_usize(v_sz_610_);
lean_dec(v_sz_610_);
v_i_boxed_614_ = lean_unbox_usize(v_i_611_);
lean_dec(v_i_611_);
v_res_615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_boxed_613_, v_i_boxed_614_, v_bs_612_);
return v_res_615_;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__3(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = ((lean_object*)(l_Lake_compileStaticLib___closed__2));
v___x_623_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_624_ = lean_array_push(v___x_623_, v___x_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object* v_libFile_625_, lean_object* v_oFiles_626_, lean_object* v_ar_627_, uint8_t v_thin_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_631_; 
lean_inc_ref(v_libFile_625_);
v___x_631_ = l_Lake_createParentDirs(v_libFile_625_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v___x_632_; 
lean_dec_ref(v___x_631_);
v___x_632_ = l_Lake_removeFileIfExists(v_libFile_625_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v___x_633_; uint8_t v___x_634_; lean_object* v___y_636_; 
lean_dec_ref(v___x_632_);
v___x_633_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_634_ = 1;
if (v_thin_628_ == 0)
{
v___y_636_ = v___x_633_;
goto v___jp_635_;
}
else
{
lean_object* v___x_660_; 
v___x_660_ = lean_obj_once(&l_Lake_compileStaticLib___closed__3, &l_Lake_compileStaticLib___closed__3_once, _init_l_Lake_compileStaticLib___closed__3);
v___y_636_ = v___x_660_;
goto v___jp_635_;
}
v___jp_635_:
{
size_t v_sz_637_; size_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_sz_637_ = lean_array_size(v_oFiles_626_);
v___x_638_ = ((size_t)0ULL);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_637_, v___x_638_, v_oFiles_626_);
lean_inc_ref(v_libFile_625_);
v___x_640_ = l_Lake_mkArgs(v_libFile_625_, v___x_639_, v_a_629_);
lean_dec_ref(v___x_639_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v_a_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
v_a_642_ = lean_ctor_get(v___x_640_, 1);
lean_inc(v_a_642_);
lean_dec_ref(v___x_640_);
v___x_643_ = lean_array_push(v___y_636_, v_libFile_625_);
v___x_644_ = l_Array_append___redArg(v___x_643_, v_a_641_);
lean_dec(v_a_641_);
v___x_645_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_646_ = lean_box(0);
v___x_647_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_648_ = 0;
v___x_649_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_649_, 0, v___x_645_);
lean_ctor_set(v___x_649_, 1, v_ar_627_);
lean_ctor_set(v___x_649_, 2, v___x_644_);
lean_ctor_set(v___x_649_, 3, v___x_646_);
lean_ctor_set(v___x_649_, 4, v___x_647_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*5, v___x_634_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*5 + 1, v___x_648_);
v___x_650_ = l_Lake_proc(v___x_649_, v___x_648_, v_a_642_);
return v___x_650_;
}
else
{
lean_object* v_a_651_; lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref(v___y_636_);
lean_dec_ref(v_ar_627_);
lean_dec_ref(v_libFile_625_);
v_a_651_ = lean_ctor_get(v___x_640_, 0);
v_a_652_ = lean_ctor_get(v___x_640_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_640_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_inc(v_a_651_);
lean_dec(v___x_640_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_651_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_a_652_);
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
}
else
{
lean_object* v_a_661_; lean_object* v___x_662_; uint8_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec_ref(v_ar_627_);
lean_dec_ref(v_oFiles_626_);
lean_dec_ref(v_libFile_625_);
v_a_661_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_661_);
lean_dec_ref(v___x_632_);
v___x_662_ = lean_io_error_to_string(v_a_661_);
v___x_663_ = 3;
v___x_664_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*1, v___x_663_);
v___x_665_ = lean_array_get_size(v_a_629_);
v___x_666_ = lean_array_push(v_a_629_, v___x_664_);
v___x_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
return v___x_667_;
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec_ref(v_ar_627_);
lean_dec_ref(v_oFiles_626_);
lean_dec_ref(v_libFile_625_);
v_a_668_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_668_);
lean_dec_ref(v___x_631_);
v___x_669_ = lean_io_error_to_string(v_a_668_);
v___x_670_ = 3;
v___x_671_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*1, v___x_670_);
v___x_672_ = lean_array_get_size(v_a_629_);
v___x_673_ = lean_array_push(v_a_629_, v___x_671_);
v___x_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object* v_libFile_675_, lean_object* v_oFiles_676_, lean_object* v_ar_677_, lean_object* v_thin_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
uint8_t v_thin_boxed_681_; lean_object* v_res_682_; 
v_thin_boxed_681_ = lean_unbox(v_thin_678_);
v_res_682_ = l_Lake_compileStaticLib(v_libFile_675_, v_oFiles_676_, v_ar_677_, v_thin_boxed_681_, v_a_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(){
_start:
{
uint8_t v___x_695_; 
v___x_695_ = l_System_Platform_isOSX;
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
v___x_696_ = ((lean_object*)(l_Lake_compileO___closed__2));
return v___x_696_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0));
v___x_698_ = lean_io_getenv(v___x_697_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v___x_699_; 
v___x_699_ = ((lean_object*)(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4));
return v___x_699_;
}
else
{
lean_object* v___x_700_; 
lean_dec_ref(v___x_698_);
v___x_700_ = ((lean_object*)(l_Lake_compileO___closed__2));
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___boxed(lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
return v_res_702_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__1(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_704_ = ((lean_object*)(l_Lake_compileSharedLib___closed__0));
v___x_705_ = lean_unsigned_to_nat(3u);
v___x_706_ = lean_mk_empty_array_with_capacity(v___x_705_);
v___x_707_ = lean_array_push(v___x_706_, v___x_704_);
return v___x_707_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__2(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_708_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_709_ = lean_obj_once(&l_Lake_compileSharedLib___closed__1, &l_Lake_compileSharedLib___closed__1_once, _init_l_Lake_compileSharedLib___closed__1);
v___x_710_ = lean_array_push(v___x_709_, v___x_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object* v_libFile_711_, lean_object* v_linkArgs_712_, lean_object* v_linker_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_716_; 
lean_inc_ref(v_libFile_711_);
v___x_716_ = l_Lake_createParentDirs(v_libFile_711_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v___x_717_; 
lean_dec_ref(v___x_716_);
lean_inc_ref(v_libFile_711_);
v___x_717_ = l_Lake_mkArgs(v_libFile_711_, v_linkArgs_712_, v_a_714_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
v_a_719_ = lean_ctor_get(v___x_717_, 1);
lean_inc(v_a_719_);
lean_dec_ref(v___x_717_);
v___x_720_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
v___x_721_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_722_ = lean_obj_once(&l_Lake_compileSharedLib___closed__2, &l_Lake_compileSharedLib___closed__2_once, _init_l_Lake_compileSharedLib___closed__2);
v___x_723_ = lean_array_push(v___x_722_, v_libFile_711_);
v___x_724_ = l_Array_append___redArg(v___x_723_, v_a_718_);
lean_dec(v_a_718_);
v___x_725_ = lean_box(0);
v___x_726_ = 1;
v___x_727_ = 0;
v___x_728_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_728_, 0, v___x_721_);
lean_ctor_set(v___x_728_, 1, v_linker_713_);
lean_ctor_set(v___x_728_, 2, v___x_724_);
lean_ctor_set(v___x_728_, 3, v___x_725_);
lean_ctor_set(v___x_728_, 4, v___x_720_);
lean_ctor_set_uint8(v___x_728_, sizeof(void*)*5, v___x_726_);
lean_ctor_set_uint8(v___x_728_, sizeof(void*)*5 + 1, v___x_727_);
v___x_729_ = l_Lake_proc(v___x_728_, v___x_727_, v_a_719_);
return v___x_729_;
}
else
{
lean_object* v_a_730_; lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v_linker_713_);
lean_dec_ref(v_libFile_711_);
v_a_730_ = lean_ctor_get(v___x_717_, 0);
v_a_731_ = lean_ctor_get(v___x_717_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_717_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_inc(v_a_730_);
lean_dec(v___x_717_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_730_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_740_; uint8_t v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec_ref(v_linker_713_);
lean_dec_ref(v_libFile_711_);
v_a_739_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_739_);
lean_dec_ref(v___x_716_);
v___x_740_ = lean_io_error_to_string(v_a_739_);
v___x_741_ = 3;
v___x_742_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set_uint8(v___x_742_, sizeof(void*)*1, v___x_741_);
v___x_743_ = lean_array_get_size(v_a_714_);
v___x_744_ = lean_array_push(v_a_714_, v___x_742_);
v___x_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object* v_libFile_746_, lean_object* v_linkArgs_747_, lean_object* v_linker_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lake_compileSharedLib(v_libFile_746_, v_linkArgs_747_, v_linker_748_, v_a_749_);
lean_dec_ref(v_linkArgs_747_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object* v_binFile_752_, lean_object* v_linkArgs_753_, lean_object* v_linker_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_757_; 
lean_inc_ref(v_binFile_752_);
v___x_757_ = l_Lake_createParentDirs(v_binFile_752_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v___x_758_; 
lean_dec_ref(v___x_757_);
lean_inc_ref(v_binFile_752_);
v___x_758_ = l_Lake_mkArgs(v_binFile_752_, v_linkArgs_753_, v_a_755_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v_a_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
v_a_760_ = lean_ctor_get(v___x_758_, 1);
lean_inc(v_a_760_);
lean_dec_ref(v___x_758_);
v___x_761_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
v___x_762_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_763_ = lean_unsigned_to_nat(2u);
v___x_764_ = lean_mk_empty_array_with_capacity(v___x_763_);
lean_dec_ref(v___x_764_);
v___x_765_ = lean_obj_once(&l_Lake_compileLeanModule___closed__15, &l_Lake_compileLeanModule___closed__15_once, _init_l_Lake_compileLeanModule___closed__15);
v___x_766_ = lean_array_push(v___x_765_, v_binFile_752_);
v___x_767_ = l_Array_append___redArg(v___x_766_, v_a_759_);
lean_dec(v_a_759_);
v___x_768_ = lean_box(0);
v___x_769_ = 1;
v___x_770_ = 0;
v___x_771_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_771_, 0, v___x_762_);
lean_ctor_set(v___x_771_, 1, v_linker_754_);
lean_ctor_set(v___x_771_, 2, v___x_767_);
lean_ctor_set(v___x_771_, 3, v___x_768_);
lean_ctor_set(v___x_771_, 4, v___x_761_);
lean_ctor_set_uint8(v___x_771_, sizeof(void*)*5, v___x_769_);
lean_ctor_set_uint8(v___x_771_, sizeof(void*)*5 + 1, v___x_770_);
v___x_772_ = l_Lake_proc(v___x_771_, v___x_770_, v_a_760_);
return v___x_772_;
}
else
{
lean_object* v_a_773_; lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v_linker_754_);
lean_dec_ref(v_binFile_752_);
v_a_773_ = lean_ctor_get(v___x_758_, 0);
v_a_774_ = lean_ctor_get(v___x_758_, 1);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_758_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_inc(v_a_773_);
lean_dec(v___x_758_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_773_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_783_; uint8_t v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref(v_linker_754_);
lean_dec_ref(v_binFile_752_);
v_a_782_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_782_);
lean_dec_ref(v___x_757_);
v___x_783_ = lean_io_error_to_string(v_a_782_);
v___x_784_ = 3;
v___x_785_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*1, v___x_784_);
v___x_786_ = lean_array_get_size(v_a_755_);
v___x_787_ = lean_array_push(v_a_755_, v___x_785_);
v___x_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
return v___x_788_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object* v_binFile_789_, lean_object* v_linkArgs_790_, lean_object* v_linker_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lake_compileExe(v_binFile_789_, v_linkArgs_790_, v_linker_791_, v_a_792_);
lean_dec_ref(v_linkArgs_790_);
return v_res_794_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0));
v___x_797_ = lean_unsigned_to_nat(2u);
v___x_798_ = lean_mk_empty_array_with_capacity(v___x_797_);
v___x_799_ = lean_array_push(v___x_798_, v___x_796_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(lean_object* v_as_800_, size_t v_i_801_, size_t v_stop_802_, lean_object* v_b_803_){
_start:
{
uint8_t v___x_804_; 
v___x_804_ = lean_usize_dec_eq(v_i_801_, v_stop_802_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; size_t v___x_809_; size_t v___x_810_; 
v___x_805_ = lean_array_uget_borrowed(v_as_800_, v_i_801_);
v___x_806_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1);
lean_inc(v___x_805_);
v___x_807_ = lean_array_push(v___x_806_, v___x_805_);
v___x_808_ = l_Array_append___redArg(v_b_803_, v___x_807_);
lean_dec_ref(v___x_807_);
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_add(v_i_801_, v___x_809_);
v_i_801_ = v___x_810_;
v_b_803_ = v___x_808_;
goto _start;
}
else
{
return v_b_803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___boxed(lean_object* v_as_812_, lean_object* v_i_813_, lean_object* v_stop_814_, lean_object* v_b_815_){
_start:
{
size_t v_i_boxed_816_; size_t v_stop_boxed_817_; lean_object* v_res_818_; 
v_i_boxed_816_ = lean_unbox_usize(v_i_813_);
lean_dec(v_i_813_);
v_stop_boxed_817_ = lean_unbox_usize(v_stop_814_);
lean_dec(v_stop_814_);
v_res_818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_as_812_, v_i_boxed_816_, v_stop_boxed_817_, v_b_815_);
lean_dec_ref(v_as_812_);
return v_res_818_;
}
}
static lean_object* _init_l_Lake_download___closed__5(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_824_ = ((lean_object*)(l_Lake_download___closed__1));
v___x_825_ = lean_unsigned_to_nat(7u);
v___x_826_ = lean_mk_empty_array_with_capacity(v___x_825_);
v___x_827_ = lean_array_push(v___x_826_, v___x_824_);
return v___x_827_;
}
}
static lean_object* _init_l_Lake_download___closed__6(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = ((lean_object*)(l_Lake_download___closed__2));
v___x_829_ = lean_obj_once(&l_Lake_download___closed__5, &l_Lake_download___closed__5_once, _init_l_Lake_download___closed__5);
v___x_830_ = lean_array_push(v___x_829_, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l_Lake_download___closed__7(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_832_ = lean_obj_once(&l_Lake_download___closed__6, &l_Lake_download___closed__6_once, _init_l_Lake_download___closed__6);
v___x_833_ = lean_array_push(v___x_832_, v___x_831_);
return v___x_833_;
}
}
static lean_object* _init_l_Lake_download___closed__8(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_835_ = lean_obj_once(&l_Lake_download___closed__7, &l_Lake_download___closed__7_once, _init_l_Lake_download___closed__7);
v___x_836_ = lean_array_push(v___x_835_, v___x_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lake_download(lean_object* v_url_837_, lean_object* v_file_838_, lean_object* v_headers_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_854_; uint8_t v___x_870_; 
v___x_870_ = l_System_FilePath_pathExists(v_file_838_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
lean_inc_ref(v_file_838_);
v___x_871_ = l_Lake_createParentDirs(v_file_838_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_dec_ref(v___x_871_);
v___y_854_ = v_a_840_;
goto v___jp_853_;
}
else
{
lean_object* v_a_872_; lean_object* v___x_873_; uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec_ref(v_file_838_);
lean_dec_ref(v_url_837_);
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref(v___x_871_);
v___x_873_ = lean_io_error_to_string(v_a_872_);
v___x_874_ = 3;
v___x_875_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*1, v___x_874_);
v___x_876_ = lean_array_get_size(v_a_840_);
v___x_877_ = lean_array_push(v_a_840_, v___x_875_);
v___x_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
return v___x_878_;
}
}
else
{
lean_object* v___x_879_; 
v___x_879_ = lean_io_remove_file(v_file_838_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_dec_ref(v___x_879_);
v___y_854_ = v_a_840_;
goto v___jp_853_;
}
else
{
lean_object* v_a_880_; lean_object* v___x_881_; uint8_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec_ref(v_file_838_);
lean_dec_ref(v_url_837_);
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref(v___x_879_);
v___x_881_ = lean_io_error_to_string(v_a_880_);
v___x_882_ = 3;
v___x_883_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*1, v___x_882_);
v___x_884_ = lean_array_get_size(v_a_840_);
v___x_885_ = lean_array_push(v_a_840_, v___x_883_);
v___x_886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
return v___x_886_;
}
}
v___jp_842_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_845_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_846_ = ((lean_object*)(l_Lake_download___closed__0));
v___x_847_ = lean_box(0);
v___x_848_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_849_ = 1;
v___x_850_ = 0;
v___x_851_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_851_, 0, v___x_845_);
lean_ctor_set(v___x_851_, 1, v___x_846_);
lean_ctor_set(v___x_851_, 2, v___y_844_);
lean_ctor_set(v___x_851_, 3, v___x_847_);
lean_ctor_set(v___x_851_, 4, v___x_848_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*5, v___x_849_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*5 + 1, v___x_850_);
v___x_852_ = l_Lake_proc(v___x_851_, v___x_849_, v___y_843_);
return v___x_852_;
}
v___jp_853_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_855_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_856_ = lean_obj_once(&l_Lake_download___closed__8, &l_Lake_download___closed__8_once, _init_l_Lake_download___closed__8);
v___x_857_ = lean_array_push(v___x_856_, v_file_838_);
v___x_858_ = lean_array_push(v___x_857_, v___x_855_);
v___x_859_ = lean_array_push(v___x_858_, v_url_837_);
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_array_get_size(v_headers_839_);
v___x_862_ = lean_nat_dec_lt(v___x_860_, v___x_861_);
if (v___x_862_ == 0)
{
v___y_843_ = v___y_854_;
v___y_844_ = v___x_859_;
goto v___jp_842_;
}
else
{
uint8_t v___x_863_; 
v___x_863_ = lean_nat_dec_le(v___x_861_, v___x_861_);
if (v___x_863_ == 0)
{
if (v___x_862_ == 0)
{
v___y_843_ = v___y_854_;
v___y_844_ = v___x_859_;
goto v___jp_842_;
}
else
{
size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; 
v___x_864_ = ((size_t)0ULL);
v___x_865_ = lean_usize_of_nat(v___x_861_);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_839_, v___x_864_, v___x_865_, v___x_859_);
v___y_843_ = v___y_854_;
v___y_844_ = v___x_866_;
goto v___jp_842_;
}
}
else
{
size_t v___x_867_; size_t v___x_868_; lean_object* v___x_869_; 
v___x_867_ = ((size_t)0ULL);
v___x_868_ = lean_usize_of_nat(v___x_861_);
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_839_, v___x_867_, v___x_868_, v___x_859_);
v___y_843_ = v___y_854_;
v___y_844_ = v___x_869_;
goto v___jp_842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object* v_url_887_, lean_object* v_file_888_, lean_object* v_headers_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lake_download(v_url_887_, v_file_888_, v_headers_889_, v_a_890_);
lean_dec_ref(v_headers_889_);
return v_res_892_;
}
}
static lean_object* _init_l_Lake_untar___closed__3(void){
_start:
{
uint32_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = 122;
v___x_897_ = ((lean_object*)(l_Lake_untar___closed__2));
v___x_898_ = lean_string_push(v___x_897_, v___x_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lake_untar(lean_object* v_file_899_, lean_object* v_dir_900_, uint8_t v_gzip_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_904_; 
lean_inc_ref(v_dir_900_);
v___x_904_ = l_IO_FS_createDirAll(v_dir_900_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_opts_906_; lean_object* v___y_907_; lean_object* v___x_925_; 
lean_dec_ref(v___x_904_);
v___x_925_ = ((lean_object*)(l_Lake_untar___closed__2));
if (v_gzip_901_ == 0)
{
v_opts_906_ = v___x_925_;
v___y_907_ = v_a_902_;
goto v___jp_905_;
}
else
{
lean_object* v___x_926_; 
v___x_926_ = lean_obj_once(&l_Lake_untar___closed__3, &l_Lake_untar___closed__3_once, _init_l_Lake_untar___closed__3);
v_opts_906_ = v___x_926_;
v___y_907_ = v_a_902_;
goto v___jp_905_;
}
v___jp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_908_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_909_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_910_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_911_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_912_ = lean_unsigned_to_nat(5u);
v___x_913_ = lean_mk_empty_array_with_capacity(v___x_912_);
v___x_914_ = lean_array_push(v___x_913_, v_opts_906_);
v___x_915_ = lean_array_push(v___x_914_, v___x_910_);
v___x_916_ = lean_array_push(v___x_915_, v_file_899_);
v___x_917_ = lean_array_push(v___x_916_, v___x_911_);
v___x_918_ = lean_array_push(v___x_917_, v_dir_900_);
v___x_919_ = lean_box(0);
v___x_920_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_921_ = 1;
v___x_922_ = 0;
v___x_923_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_923_, 0, v___x_908_);
lean_ctor_set(v___x_923_, 1, v___x_909_);
lean_ctor_set(v___x_923_, 2, v___x_918_);
lean_ctor_set(v___x_923_, 3, v___x_919_);
lean_ctor_set(v___x_923_, 4, v___x_920_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*5, v___x_921_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*5 + 1, v___x_922_);
v___x_924_ = l_Lake_proc(v___x_923_, v___x_921_, v___y_907_);
return v___x_924_;
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_928_; uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref(v_dir_900_);
lean_dec_ref(v_file_899_);
v_a_927_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_904_);
v___x_928_ = lean_io_error_to_string(v_a_927_);
v___x_929_ = 3;
v___x_930_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_930_, 0, v___x_928_);
lean_ctor_set_uint8(v___x_930_, sizeof(void*)*1, v___x_929_);
v___x_931_ = lean_array_get_size(v_a_902_);
v___x_932_ = lean_array_push(v_a_902_, v___x_930_);
v___x_933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object* v_file_934_, lean_object* v_dir_935_, lean_object* v_gzip_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
uint8_t v_gzip_boxed_939_; lean_object* v_res_940_; 
v_gzip_boxed_939_ = lean_unbox(v_gzip_936_);
v_res_940_ = l_Lake_untar(v_file_934_, v_dir_935_, v_gzip_boxed_939_, v_a_937_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(lean_object* v_as_942_, size_t v_sz_943_, size_t v_i_944_, lean_object* v_b_945_, lean_object* v___y_946_){
_start:
{
uint8_t v___x_948_; 
v___x_948_ = lean_usize_dec_lt(v_i_944_, v_sz_943_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_b_945_);
lean_ctor_set(v___x_949_, 1, v___y_946_);
return v___x_949_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; size_t v___x_954_; size_t v___x_955_; 
v_a_950_ = lean_array_uget_borrowed(v_as_942_, v_i_944_);
v___x_951_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0));
v___x_952_ = lean_string_append(v___x_951_, v_a_950_);
v___x_953_ = lean_array_push(v_b_945_, v___x_952_);
v___x_954_ = ((size_t)1ULL);
v___x_955_ = lean_usize_add(v_i_944_, v___x_954_);
v_i_944_ = v___x_955_;
v_b_945_ = v___x_953_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___boxed(lean_object* v_as_957_, lean_object* v_sz_958_, lean_object* v_i_959_, lean_object* v_b_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
size_t v_sz_boxed_963_; size_t v_i_boxed_964_; lean_object* v_res_965_; 
v_sz_boxed_963_ = lean_unbox_usize(v_sz_958_);
lean_dec(v_sz_958_);
v_i_boxed_964_ = lean_unbox_usize(v_i_959_);
lean_dec(v_i_959_);
v_res_965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_as_957_, v_sz_boxed_963_, v_i_boxed_964_, v_b_960_, v___y_961_);
lean_dec_ref(v_as_957_);
return v_res_965_;
}
}
static lean_object* _init_l_Lake_tar___closed__1(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_967_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_968_ = lean_unsigned_to_nat(5u);
v___x_969_ = lean_mk_empty_array_with_capacity(v___x_968_);
v___x_970_ = lean_array_push(v___x_969_, v___x_967_);
return v___x_970_;
}
}
static lean_object* _init_l_Lake_tar___closed__10(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = ((lean_object*)(l_Lake_tar___closed__9));
v___x_989_ = ((lean_object*)(l_Lake_tar___closed__8));
v___x_990_ = lean_array_push(v___x_989_, v___x_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lake_tar(lean_object* v_dir_991_, lean_object* v_file_992_, uint8_t v_gzip_993_, lean_object* v_excludePaths_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; uint8_t v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___x_1008_; 
lean_inc_ref(v_file_992_);
v___x_1008_ = l_Lake_createParentDirs(v_file_992_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_args_1010_; lean_object* v___y_1011_; lean_object* v___x_1041_; 
lean_dec_ref(v___x_1008_);
v___x_1041_ = ((lean_object*)(l_Lake_tar___closed__8));
if (v_gzip_993_ == 0)
{
v_args_1010_ = v___x_1041_;
v___y_1011_ = v_a_995_;
goto v___jp_1009_;
}
else
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_obj_once(&l_Lake_tar___closed__10, &l_Lake_tar___closed__10_once, _init_l_Lake_tar___closed__10);
v_args_1010_ = v___x_1042_;
v___y_1011_ = v_a_995_;
goto v___jp_1009_;
}
v___jp_1009_:
{
size_t v_sz_1012_; size_t v___x_1013_; lean_object* v___x_1014_; 
v_sz_1012_ = lean_array_size(v_excludePaths_994_);
v___x_1013_ = ((size_t)0ULL);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_excludePaths_994_, v_sz_1012_, v___x_1013_, v_args_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; uint8_t v___x_1029_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
v_a_1016_ = lean_ctor_get(v___x_1014_, 1);
lean_inc(v_a_1016_);
lean_dec_ref(v___x_1014_);
v___x_1017_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_1018_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_1019_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_1020_ = ((lean_object*)(l_Lake_tar___closed__0));
v___x_1021_ = lean_obj_once(&l_Lake_tar___closed__1, &l_Lake_tar___closed__1_once, _init_l_Lake_tar___closed__1);
v___x_1022_ = lean_array_push(v___x_1021_, v_file_992_);
v___x_1023_ = lean_array_push(v___x_1022_, v___x_1019_);
v___x_1024_ = lean_array_push(v___x_1023_, v_dir_991_);
v___x_1025_ = lean_array_push(v___x_1024_, v___x_1020_);
v___x_1026_ = l_Array_append___redArg(v_a_1015_, v___x_1025_);
lean_dec_ref(v___x_1025_);
v___x_1027_ = lean_box(0);
v___x_1028_ = l_System_Platform_isOSX;
v___x_1029_ = 1;
if (v___x_1028_ == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_998_ = v___x_1027_;
v___y_999_ = v___x_1017_;
v___y_1000_ = v_a_1016_;
v___y_1001_ = v___x_1029_;
v___y_1002_ = v___x_1018_;
v___y_1003_ = v___x_1026_;
v___y_1004_ = v___x_1030_;
goto v___jp_997_;
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = ((lean_object*)(l_Lake_tar___closed__6));
v___y_998_ = v___x_1027_;
v___y_999_ = v___x_1017_;
v___y_1000_ = v_a_1016_;
v___y_1001_ = v___x_1029_;
v___y_1002_ = v___x_1018_;
v___y_1003_ = v___x_1026_;
v___y_1004_ = v___x_1031_;
goto v___jp_997_;
}
}
else
{
lean_object* v_a_1032_; lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec_ref(v_file_992_);
lean_dec_ref(v_dir_991_);
v_a_1032_ = lean_ctor_get(v___x_1014_, 0);
v_a_1033_ = lean_ctor_get(v___x_1014_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1014_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_inc(v_a_1032_);
lean_dec(v___x_1014_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1032_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec_ref(v_file_992_);
lean_dec_ref(v_dir_991_);
v_a_1043_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1043_);
lean_dec_ref(v___x_1008_);
v___x_1044_ = lean_io_error_to_string(v_a_1043_);
v___x_1045_ = 3;
v___x_1046_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*1, v___x_1045_);
v___x_1047_ = lean_array_get_size(v_a_995_);
v___x_1048_ = lean_array_push(v_a_995_, v___x_1046_);
v___x_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
return v___x_1049_;
}
v___jp_997_:
{
uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = 0;
v___x_1006_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1006_, 0, v___y_999_);
lean_ctor_set(v___x_1006_, 1, v___y_1002_);
lean_ctor_set(v___x_1006_, 2, v___y_1003_);
lean_ctor_set(v___x_1006_, 3, v___y_998_);
lean_ctor_set(v___x_1006_, 4, v___y_1004_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*5, v___y_1001_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*5 + 1, v___x_1005_);
v___x_1007_ = l_Lake_proc(v___x_1006_, v___y_1001_, v___y_1000_);
return v___x_1007_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object* v_dir_1050_, lean_object* v_file_1051_, lean_object* v_gzip_1052_, lean_object* v_excludePaths_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
uint8_t v_gzip_boxed_1056_; lean_object* v_res_1057_; 
v_gzip_boxed_1056_ = lean_unbox(v_gzip_1052_);
v_res_1057_ = l_Lake_tar(v_dir_1050_, v_file_1051_, v_gzip_boxed_1056_, v_excludePaths_1053_, v_a_1054_);
lean_dec_ref(v_excludePaths_1053_);
return v_res_1057_;
}
}
lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
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
