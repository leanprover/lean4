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
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint32_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object**);
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
lean_dec_ref_known(v___x_12_, 1);
if (lean_obj_tag(v_val_14_) == 1)
{
uint8_t v_v_15_; 
v_v_15_ = lean_ctor_get_uint8(v_val_14_, 0);
lean_dec_ref_known(v_val_14_, 0);
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
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint32_t v_exitCode_23_, uint8_t v___y_24_, lean_object* v_ir_x3f_25_, lean_object* v_c_x3f_26_, lean_object* v_setupFile_27_, lean_object* v___x_28_, lean_object* v_leanir_29_, lean_object* v___x_30_, lean_object* v___x_31_, uint8_t v___x_32_, uint8_t v___x_33_, lean_object* v___x_34_, lean_object* v_olean_x3f_35_, lean_object* v_stderr_36_, lean_object* v_____r_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___y_41_; lean_object* v___y_45_; lean_object* v___y_46_; lean_object* v___y_49_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_107_ = lean_string_utf8_byte_size(v_stderr_36_);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_nat_dec_eq(v___x_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_110_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__1));
v___x_111_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_111_, 0, v_stderr_36_);
lean_ctor_set(v___x_111_, 1, v___x_108_);
lean_ctor_set(v___x_111_, 2, v___x_107_);
v___x_112_ = l_String_Slice_trimAscii(v___x_111_);
v___x_113_ = l_String_Slice_toString(v___x_112_);
lean_dec_ref(v___x_112_);
v___x_114_ = lean_string_append(v___x_110_, v___x_113_);
lean_dec_ref(v___x_113_);
v___x_115_ = 1;
v___x_116_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*1, v___x_115_);
v___x_117_ = lean_array_push(v___y_38_, v___x_116_);
v___y_49_ = v___x_117_;
goto v___jp_48_;
}
else
{
lean_dec_ref(v_stderr_36_);
v___y_49_ = v___y_38_;
goto v___jp_48_;
}
v___jp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_box(0);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___y_41_);
return v___x_43_;
}
v___jp_44_:
{
lean_object* v___x_47_; 
v___x_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_47_, 0, v___y_45_);
lean_ctor_set(v___x_47_, 1, v___y_46_);
return v___x_47_;
}
v___jp_48_:
{
uint32_t v___x_50_; uint8_t v___x_51_; 
v___x_50_ = 0;
v___x_51_ = lean_uint32_dec_eq(v_exitCode_23_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec_ref(v___x_31_);
lean_dec(v___x_30_);
lean_dec_ref(v_leanir_29_);
lean_dec_ref(v___x_28_);
lean_dec_ref(v_setupFile_27_);
lean_dec(v_c_x3f_26_);
lean_dec(v_ir_x3f_25_);
v___x_52_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__0));
v___x_53_ = lean_uint32_to_nat(v_exitCode_23_);
v___x_54_ = l_Nat_reprFast(v___x_53_);
v___x_55_ = lean_string_append(v___x_52_, v___x_54_);
lean_dec_ref(v___x_54_);
v___x_56_ = 3;
v___x_57_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*1, v___x_56_);
v___x_58_ = lean_array_get_size(v___y_49_);
v___x_59_ = lean_array_push(v___y_49_, v___x_57_);
v___x_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
return v___x_60_;
}
else
{
if (v___y_24_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec_ref(v___x_31_);
lean_dec(v___x_30_);
lean_dec_ref(v_leanir_29_);
lean_dec_ref(v___x_28_);
lean_dec_ref(v_setupFile_27_);
lean_dec(v_c_x3f_26_);
lean_dec(v_ir_x3f_25_);
v___x_61_ = lean_box(0);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___y_49_);
return v___x_62_;
}
else
{
if (lean_obj_tag(v_ir_x3f_25_) == 1)
{
if (lean_obj_tag(v_c_x3f_26_) == 1)
{
lean_object* v_val_63_; lean_object* v_val_64_; lean_object* v___x_65_; 
v_val_63_ = lean_ctor_get(v_ir_x3f_25_, 0);
lean_inc_n(v_val_63_, 2);
lean_dec_ref_known(v_ir_x3f_25_, 1);
v_val_64_ = lean_ctor_get(v_c_x3f_26_, 0);
lean_inc(v_val_64_);
lean_dec_ref_known(v_c_x3f_26_, 1);
v___x_65_ = l_Lake_createParentDirs(v_val_63_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v___x_66_; 
lean_dec_ref_known(v___x_65_, 1);
lean_inc(v_val_64_);
v___x_66_ = l_Lake_createParentDirs(v_val_64_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec_ref_known(v___x_66_, 1);
v___x_67_ = lean_unsigned_to_nat(3u);
v___x_68_ = lean_mk_empty_array_with_capacity(v___x_67_);
v___x_69_ = lean_array_push(v___x_68_, v_setupFile_27_);
v___x_70_ = lean_array_push(v___x_69_, v_val_63_);
v___x_71_ = lean_array_push(v___x_70_, v_val_64_);
v___x_72_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_72_, 0, v___x_28_);
lean_ctor_set(v___x_72_, 1, v_leanir_29_);
lean_ctor_set(v___x_72_, 2, v___x_71_);
lean_ctor_set(v___x_72_, 3, v___x_30_);
lean_ctor_set(v___x_72_, 4, v___x_31_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*5, v___x_32_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*5 + 1, v___x_33_);
v___x_73_ = l_Lake_proc(v___x_72_, v___x_33_, v___x_34_, v___y_49_);
if (lean_obj_tag(v___x_73_) == 0)
{
return v___x_73_;
}
else
{
if (lean_obj_tag(v_olean_x3f_35_) == 1)
{
lean_object* v_a_74_; lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_90_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_a_75_ = lean_ctor_get(v___x_73_, 1);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_90_ == 0)
{
v___x_77_ = v___x_73_;
v_isShared_78_ = v_isSharedCheck_90_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_90_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v_val_79_; lean_object* v___x_80_; 
v_val_79_ = lean_ctor_get(v_olean_x3f_35_, 0);
v___x_80_ = l_Lake_removeFileIfExists(v_val_79_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_dec_ref_known(v___x_80_, 1);
lean_del_object(v___x_77_);
v___y_45_ = v_a_74_;
v___y_46_ = v_a_75_;
goto v___jp_44_;
}
else
{
lean_object* v_a_81_; lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
lean_dec(v_a_74_);
v_a_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_a_81_);
lean_dec_ref_known(v___x_80_, 1);
v___x_82_ = lean_io_error_to_string(v_a_81_);
v___x_83_ = 3;
v___x_84_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_83_);
v___x_85_ = lean_array_get_size(v_a_75_);
v___x_86_ = lean_array_push(v_a_75_, v___x_84_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_86_);
lean_ctor_set(v___x_77_, 0, v___x_85_);
v___x_88_ = v___x_77_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
else
{
lean_object* v_a_91_; lean_object* v_a_92_; 
v_a_91_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_a_91_);
v_a_92_ = lean_ctor_get(v___x_73_, 1);
lean_inc(v_a_92_);
lean_dec_ref_known(v___x_73_, 2);
v___y_45_ = v_a_91_;
v___y_46_ = v_a_92_;
goto v___jp_44_;
}
}
}
else
{
lean_object* v_a_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v_val_64_);
lean_dec(v_val_63_);
lean_dec_ref(v___x_31_);
lean_dec(v___x_30_);
lean_dec_ref(v_leanir_29_);
lean_dec_ref(v___x_28_);
lean_dec_ref(v_setupFile_27_);
v_a_93_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_93_);
lean_dec_ref_known(v___x_66_, 1);
v___x_94_ = lean_io_error_to_string(v_a_93_);
v___x_95_ = 3;
v___x_96_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = lean_array_get_size(v___y_49_);
v___x_98_ = lean_array_push(v___y_49_, v___x_96_);
v___x_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
return v___x_99_;
}
}
else
{
lean_object* v_a_100_; lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_val_64_);
lean_dec(v_val_63_);
lean_dec_ref(v___x_31_);
lean_dec(v___x_30_);
lean_dec_ref(v_leanir_29_);
lean_dec_ref(v___x_28_);
lean_dec_ref(v_setupFile_27_);
v_a_100_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_100_);
lean_dec_ref_known(v___x_65_, 1);
v___x_101_ = lean_io_error_to_string(v_a_100_);
v___x_102_ = 3;
v___x_103_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_102_);
v___x_104_ = lean_array_get_size(v___y_49_);
v___x_105_ = lean_array_push(v___y_49_, v___x_103_);
v___x_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
return v___x_106_;
}
}
else
{
lean_dec_ref_known(v_ir_x3f_25_, 1);
lean_dec_ref(v___x_31_);
lean_dec(v___x_30_);
lean_dec_ref(v_leanir_29_);
lean_dec_ref(v___x_28_);
lean_dec_ref(v_setupFile_27_);
lean_dec(v_c_x3f_26_);
v___y_41_ = v___y_49_;
goto v___jp_40_;
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
v___y_41_ = v___y_49_;
goto v___jp_40_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object** _args){
lean_object* v_exitCode_118_ = _args[0];
lean_object* v___y_119_ = _args[1];
lean_object* v_ir_x3f_120_ = _args[2];
lean_object* v_c_x3f_121_ = _args[3];
lean_object* v_setupFile_122_ = _args[4];
lean_object* v___x_123_ = _args[5];
lean_object* v_leanir_124_ = _args[6];
lean_object* v___x_125_ = _args[7];
lean_object* v___x_126_ = _args[8];
lean_object* v___x_127_ = _args[9];
lean_object* v___x_128_ = _args[10];
lean_object* v___x_129_ = _args[11];
lean_object* v_olean_x3f_130_ = _args[12];
lean_object* v_stderr_131_ = _args[13];
lean_object* v_____r_132_ = _args[14];
lean_object* v___y_133_ = _args[15];
lean_object* v___y_134_ = _args[16];
_start:
{
uint32_t v_exitCode_boxed_135_; uint8_t v___y_30464__boxed_136_; uint8_t v___x_30468__boxed_137_; uint8_t v___x_30469__boxed_138_; lean_object* v_res_139_; 
v_exitCode_boxed_135_ = lean_unbox_uint32(v_exitCode_118_);
lean_dec(v_exitCode_118_);
v___y_30464__boxed_136_ = lean_unbox(v___y_119_);
v___x_30468__boxed_137_ = lean_unbox(v___x_127_);
v___x_30469__boxed_138_ = lean_unbox(v___x_128_);
v_res_139_ = l_Lake_compileLeanModule___lam__0(v_exitCode_boxed_135_, v___y_30464__boxed_136_, v_ir_x3f_120_, v_c_x3f_121_, v_setupFile_122_, v___x_123_, v_leanir_124_, v___x_125_, v___x_126_, v___x_30468__boxed_137_, v___x_30469__boxed_138_, v___x_129_, v_olean_x3f_130_, v_stderr_131_, v_____r_132_, v___y_133_);
lean_dec(v_olean_x3f_130_);
lean_dec(v___x_129_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(lean_object* v_a_140_, lean_object* v_b_141_, lean_object* v_relLeanFile_142_, lean_object* v_____r_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_a_147_; lean_object* v_toBaseMessage_149_; uint8_t v_isSilent_150_; 
v_toBaseMessage_149_ = lean_ctor_get(v_a_140_, 0);
lean_inc_ref(v_toBaseMessage_149_);
v_isSilent_150_ = lean_ctor_get_uint8(v_toBaseMessage_149_, sizeof(void*)*5 + 2);
if (v_isSilent_150_ == 0)
{
lean_object* v_kind_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_175_; 
v_kind_151_ = lean_ctor_get(v_a_140_, 1);
v_isSharedCheck_175_ = !lean_is_exclusive(v_a_140_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; 
v_unused_176_ = lean_ctor_get(v_a_140_, 0);
lean_dec(v_unused_176_);
v___x_153_ = v_a_140_;
v_isShared_154_ = v_isSharedCheck_175_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_kind_151_);
lean_dec(v_a_140_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_175_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v_pos_155_; lean_object* v_endPos_156_; uint8_t v_keepFullRange_157_; uint8_t v_severity_158_; lean_object* v_caption_159_; lean_object* v_data_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_173_; 
v_pos_155_ = lean_ctor_get(v_toBaseMessage_149_, 1);
v_endPos_156_ = lean_ctor_get(v_toBaseMessage_149_, 2);
v_keepFullRange_157_ = lean_ctor_get_uint8(v_toBaseMessage_149_, sizeof(void*)*5);
v_severity_158_ = lean_ctor_get_uint8(v_toBaseMessage_149_, sizeof(void*)*5 + 1);
v_caption_159_ = lean_ctor_get(v_toBaseMessage_149_, 3);
v_data_160_ = lean_ctor_get(v_toBaseMessage_149_, 4);
v_isSharedCheck_173_ = !lean_is_exclusive(v_toBaseMessage_149_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; 
v_unused_174_ = lean_ctor_get(v_toBaseMessage_149_, 0);
lean_dec(v_unused_174_);
v___x_162_ = v_toBaseMessage_149_;
v_isShared_163_ = v_isSharedCheck_173_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_data_160_);
lean_inc(v_caption_159_);
lean_inc(v_endPos_156_);
lean_inc(v_pos_155_);
lean_dec(v_toBaseMessage_149_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_173_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = l_Lake_mkRelPathString(v_relLeanFile_142_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_164_);
v___x_166_ = v___x_162_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_pos_155_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_endPos_156_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_caption_159_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v_data_160_);
lean_ctor_set_uint8(v_reuseFailAlloc_172_, sizeof(void*)*5, v_keepFullRange_157_);
lean_ctor_set_uint8(v_reuseFailAlloc_172_, sizeof(void*)*5 + 1, v_severity_158_);
lean_ctor_set_uint8(v_reuseFailAlloc_172_, sizeof(void*)*5 + 2, v_isSilent_150_);
v___x_166_ = v_reuseFailAlloc_172_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_166_);
v___x_168_ = v___x_153_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_kind_151_);
v___x_168_ = v_reuseFailAlloc_171_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = l_Lake_LogEntry_ofSerialMessage(v___x_168_);
v___x_170_ = lean_array_push(v___y_144_, v___x_169_);
v_a_147_ = v___x_170_;
goto v___jp_146_;
}
}
}
}
}
else
{
lean_dec_ref(v_toBaseMessage_149_);
lean_dec_ref(v_relLeanFile_142_);
lean_dec_ref(v_a_140_);
v_a_147_ = v___y_144_;
goto v___jp_146_;
}
v___jp_146_:
{
lean_object* v___x_148_; 
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v_b_141_);
lean_ctor_set(v___x_148_, 1, v_a_147_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0___boxed(lean_object* v_a_177_, lean_object* v_b_178_, lean_object* v_relLeanFile_179_, lean_object* v_____r_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(v_a_177_, v_b_178_, v_relLeanFile_179_, v_____r_180_, v___y_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(lean_object* v_relLeanFile_186_, lean_object* v___x_187_, lean_object* v___x_188_, lean_object* v___x_189_, lean_object* v_a_190_, lean_object* v_b_191_, lean_object* v___y_192_){
_start:
{
lean_object* v___y_195_; lean_object* v___y_196_; uint8_t v___y_197_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v_it_218_; lean_object* v_startInclusive_219_; lean_object* v_endExclusive_220_; 
if (lean_obj_tag(v_a_190_) == 0)
{
lean_object* v_currPos_238_; lean_object* v_searcher_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_265_; 
v_currPos_238_ = lean_ctor_get(v_a_190_, 0);
v_searcher_239_ = lean_ctor_get(v_a_190_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_a_190_);
if (v_isSharedCheck_265_ == 0)
{
v___x_241_ = v_a_190_;
v_isShared_242_ = v_isSharedCheck_265_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_searcher_239_);
lean_inc(v_currPos_238_);
lean_dec(v_a_190_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_265_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_startInclusive_243_; lean_object* v_endExclusive_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_startInclusive_243_ = lean_ctor_get(v___x_188_, 1);
v_endExclusive_244_ = lean_ctor_get(v___x_188_, 2);
v___x_245_ = lean_nat_sub(v_endExclusive_244_, v_startInclusive_243_);
v___x_246_ = lean_nat_dec_eq(v_searcher_239_, v___x_245_);
lean_dec(v___x_245_);
if (v___x_246_ == 0)
{
uint32_t v___x_247_; uint32_t v___x_248_; uint8_t v___x_249_; 
v___x_247_ = 10;
v___x_248_ = lean_string_utf8_get_fast(v___x_187_, v_searcher_239_);
v___x_249_ = lean_uint32_dec_eq(v___x_248_, v___x_247_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_250_ = lean_string_utf8_next_fast(v___x_187_, v_searcher_239_);
lean_dec(v_searcher_239_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_250_);
v___x_252_ = v___x_241_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_currPos_238_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v___x_250_);
v___x_252_ = v_reuseFailAlloc_254_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
v_a_190_ = v___x_252_;
goto _start;
}
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v_slice_258_; lean_object* v_nextIt_260_; 
v___x_255_ = lean_string_utf8_next_fast(v___x_187_, v_searcher_239_);
v___x_256_ = lean_nat_sub(v___x_255_, v_searcher_239_);
v___x_257_ = lean_nat_add(v_searcher_239_, v___x_256_);
lean_dec(v___x_256_);
v_slice_258_ = l_String_Slice_subslice_x21(v___x_188_, v_currPos_238_, v_searcher_239_);
lean_inc(v___x_257_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v___x_257_);
lean_ctor_set(v___x_241_, 0, v___x_257_);
v_nextIt_260_ = v___x_241_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_257_);
v_nextIt_260_ = v_reuseFailAlloc_263_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v_startInclusive_261_; lean_object* v_endExclusive_262_; 
v_startInclusive_261_ = lean_ctor_get(v_slice_258_, 0);
lean_inc(v_startInclusive_261_);
v_endExclusive_262_ = lean_ctor_get(v_slice_258_, 1);
lean_inc(v_endExclusive_262_);
lean_dec_ref(v_slice_258_);
v_it_218_ = v_nextIt_260_;
v_startInclusive_219_ = v_startInclusive_261_;
v_endExclusive_220_ = v_endExclusive_262_;
goto v___jp_217_;
}
}
}
else
{
lean_object* v___x_264_; 
lean_del_object(v___x_241_);
lean_dec(v_searcher_239_);
v___x_264_ = lean_box(1);
lean_inc(v___x_189_);
v_it_218_ = v___x_264_;
v_startInclusive_219_ = v_currPos_238_;
v_endExclusive_220_ = v___x_189_;
goto v___jp_217_;
}
}
}
else
{
lean_object* v___x_266_; 
lean_dec(v___x_189_);
lean_dec_ref(v_relLeanFile_186_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v_b_191_);
lean_ctor_set(v___x_266_, 1, v___y_192_);
return v___x_266_;
}
v___jp_194_:
{
if (v___y_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_string_append(v_b_191_, v___y_196_);
lean_dec_ref(v___y_196_);
v___x_199_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0));
v___x_200_ = lean_string_append(v___x_198_, v___x_199_);
v_a_190_ = v___y_195_;
v_b_191_ = v___x_200_;
goto _start;
}
else
{
lean_dec_ref(v___y_196_);
v_a_190_ = v___y_195_;
goto _start;
}
}
v___jp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_206_ = lean_string_utf8_byte_size(v_b_191_);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_nat_dec_eq(v___x_206_, v___x_207_);
if (v___x_208_ == 0)
{
v___y_195_ = v___y_204_;
v___y_196_ = v___y_205_;
v___y_197_ = v___x_208_;
goto v___jp_194_;
}
else
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = lean_string_utf8_byte_size(v___y_205_);
v___x_210_ = lean_nat_dec_eq(v___x_209_, v___x_207_);
v___y_195_ = v___y_204_;
v___y_196_ = v___y_205_;
v___y_197_ = v___x_210_;
goto v___jp_194_;
}
}
v___jp_211_:
{
if (lean_obj_tag(v___y_213_) == 0)
{
lean_object* v_a_214_; lean_object* v_a_215_; 
v_a_214_ = lean_ctor_get(v___y_213_, 0);
lean_inc(v_a_214_);
v_a_215_ = lean_ctor_get(v___y_213_, 1);
lean_inc(v_a_215_);
lean_dec_ref_known(v___y_213_, 2);
v_a_190_ = v___y_212_;
v_b_191_ = v_a_214_;
v___y_192_ = v_a_215_;
goto _start;
}
else
{
lean_dec(v___y_212_);
lean_dec(v___x_189_);
lean_dec_ref(v_relLeanFile_186_);
return v___y_213_;
}
}
v___jp_217_:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_string_utf8_extract(v___x_187_, v_startInclusive_219_, v_endExclusive_220_);
lean_dec(v_endExclusive_220_);
lean_dec(v_startInclusive_219_);
lean_inc_ref(v___x_221_);
v___x_222_ = l_Lean_Json_parse(v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_dec_ref_known(v___x_222_, 1);
v___y_204_ = v_it_218_;
v___y_205_ = v___x_221_;
goto v___jp_203_;
}
else
{
lean_object* v_a_223_; lean_object* v___x_224_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_223_);
lean_dec_ref_known(v___x_222_, 1);
v___x_224_ = l_Lean_instFromJsonSerialMessage_fromJson(v_a_223_);
if (lean_obj_tag(v___x_224_) == 1)
{
lean_object* v_a_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
lean_dec_ref(v___x_221_);
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 1);
v___x_226_ = lean_string_utf8_byte_size(v_b_191_);
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_nat_dec_eq(v___x_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_229_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1));
v___x_230_ = lean_string_append(v___x_229_, v_b_191_);
v___x_231_ = 1;
v___x_232_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*1, v___x_231_);
v___x_233_ = lean_box(0);
v___x_234_ = lean_array_push(v___y_192_, v___x_232_);
lean_inc_ref(v_relLeanFile_186_);
v___x_235_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(v_a_225_, v_b_191_, v_relLeanFile_186_, v___x_233_, v___x_234_);
v___y_212_ = v_it_218_;
v___y_213_ = v___x_235_;
goto v___jp_211_;
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_box(0);
lean_inc_ref(v_relLeanFile_186_);
v___x_237_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(v_a_225_, v_b_191_, v_relLeanFile_186_, v___x_236_, v___y_192_);
v___y_212_ = v_it_218_;
v___y_213_ = v___x_237_;
goto v___jp_211_;
}
}
else
{
lean_dec_ref(v___x_224_);
v___y_204_ = v_it_218_;
v___y_205_ = v___x_221_;
goto v___jp_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___boxed(lean_object* v_relLeanFile_267_, lean_object* v___x_268_, lean_object* v___x_269_, lean_object* v___x_270_, lean_object* v_a_271_, lean_object* v_b_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(v_relLeanFile_267_, v___x_268_, v___x_269_, v___x_270_, v_a_271_, v_b_272_, v___y_273_);
lean_dec_ref(v___x_269_);
lean_dec_ref(v___x_268_);
return v_res_275_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__1(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = ((lean_object*)(l_Lake_compileLeanModule___closed__0));
v___x_278_ = lean_unsigned_to_nat(2u);
v___x_279_ = lean_mk_empty_array_with_capacity(v___x_278_);
v___x_280_ = lean_array_push(v___x_279_, v___x_277_);
return v___x_280_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__9(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = ((lean_object*)(l_Lake_compileLeanModule___closed__8));
v___x_290_ = lean_unsigned_to_nat(2u);
v___x_291_ = lean_mk_empty_array_with_capacity(v___x_290_);
v___x_292_ = lean_array_push(v___x_291_, v___x_289_);
return v___x_292_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__11(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_294_ = ((lean_object*)(l_Lake_compileLeanModule___closed__10));
v___x_295_ = lean_unsigned_to_nat(2u);
v___x_296_ = lean_mk_empty_array_with_capacity(v___x_295_);
v___x_297_ = lean_array_push(v___x_296_, v___x_294_);
return v___x_297_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__13(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = ((lean_object*)(l_Lake_compileLeanModule___closed__12));
v___x_300_ = lean_unsigned_to_nat(2u);
v___x_301_ = lean_mk_empty_array_with_capacity(v___x_300_);
v___x_302_ = lean_array_push(v___x_301_, v___x_299_);
return v___x_302_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__15(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_305_ = lean_unsigned_to_nat(2u);
v___x_306_ = lean_mk_empty_array_with_capacity(v___x_305_);
v___x_307_ = lean_array_push(v___x_306_, v___x_304_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object* v_leanFile_308_, lean_object* v_relLeanFile_309_, lean_object* v_setup_310_, lean_object* v_setupFile_311_, lean_object* v_arts_312_, lean_object* v_leanArgs_313_, lean_object* v_leanPath_314_, lean_object* v_lean_315_, lean_object* v_leanir_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___y_320_; lean_object* v_a_321_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v_olean_x3f_327_; lean_object* v_ilean_x3f_328_; lean_object* v_ir_x3f_329_; lean_object* v_c_x3f_330_; lean_object* v_bc_x3f_331_; uint8_t v___y_333_; lean_object* v_args_334_; lean_object* v___y_335_; lean_object* v___y_423_; uint8_t v___y_424_; lean_object* v_args_425_; lean_object* v___y_439_; lean_object* v___y_440_; uint8_t v___y_441_; lean_object* v_args_455_; lean_object* v___y_456_; lean_object* v_args_463_; lean_object* v___y_464_; lean_object* v_args_477_; 
v_olean_x3f_327_ = lean_ctor_get(v_arts_312_, 1);
lean_inc(v_olean_x3f_327_);
v_ilean_x3f_328_ = lean_ctor_get(v_arts_312_, 4);
lean_inc(v_ilean_x3f_328_);
v_ir_x3f_329_ = lean_ctor_get(v_arts_312_, 6);
lean_inc(v_ir_x3f_329_);
v_c_x3f_330_ = lean_ctor_get(v_arts_312_, 7);
lean_inc(v_c_x3f_330_);
v_bc_x3f_331_ = lean_ctor_get(v_arts_312_, 8);
lean_inc(v_bc_x3f_331_);
lean_dec_ref(v_arts_312_);
v_args_477_ = lean_array_push(v_leanArgs_313_, v_leanFile_308_);
if (lean_obj_tag(v_olean_x3f_327_) == 1)
{
lean_object* v_val_478_; lean_object* v___x_479_; 
v_val_478_ = lean_ctor_get(v_olean_x3f_327_, 0);
lean_inc(v_val_478_);
v___x_479_ = l_Lake_createParentDirs(v_val_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec_ref_known(v___x_479_, 1);
v___x_480_ = lean_obj_once(&l_Lake_compileLeanModule___closed__15, &l_Lake_compileLeanModule___closed__15_once, _init_l_Lake_compileLeanModule___closed__15);
lean_inc(v_val_478_);
v___x_481_ = lean_array_push(v___x_480_, v_val_478_);
v___x_482_ = l_Array_append___redArg(v_args_477_, v___x_481_);
lean_dec_ref(v___x_481_);
v_args_463_ = v___x_482_;
v___y_464_ = v_a_317_;
goto v___jp_462_;
}
else
{
lean_object* v_a_483_; lean_object* v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec_ref_known(v_olean_x3f_327_, 1);
lean_dec_ref(v_args_477_);
lean_dec(v_bc_x3f_331_);
lean_dec(v_c_x3f_330_);
lean_dec(v_ir_x3f_329_);
lean_dec(v_ilean_x3f_328_);
lean_dec_ref(v_leanir_316_);
lean_dec_ref(v_lean_315_);
lean_dec(v_leanPath_314_);
lean_dec_ref(v_setupFile_311_);
lean_dec_ref(v_setup_310_);
lean_dec_ref(v_relLeanFile_309_);
v_a_483_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_479_, 1);
v___x_484_ = lean_io_error_to_string(v_a_483_);
v___x_485_ = 3;
v___x_486_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*1, v___x_485_);
v___x_487_ = lean_array_get_size(v_a_317_);
v___x_488_ = lean_array_push(v_a_317_, v___x_486_);
v___x_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
return v___x_489_;
}
}
else
{
v_args_463_ = v_args_477_;
v___y_464_ = v_a_317_;
goto v___jp_462_;
}
v___jp_319_:
{
lean_object* v___x_322_; 
v___x_322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_322_, 0, v___y_320_);
lean_ctor_set(v___x_322_, 1, v_a_321_);
return v___x_322_;
}
v___jp_323_:
{
if (lean_obj_tag(v___y_325_) == 0)
{
lean_dec(v___y_324_);
return v___y_325_;
}
else
{
lean_object* v_a_326_; 
v_a_326_ = lean_ctor_get(v___y_325_, 1);
lean_inc(v_a_326_);
lean_dec_ref_known(v___y_325_, 2);
v___y_320_ = v___y_324_;
v_a_321_ = v_a_326_;
goto v___jp_319_;
}
}
v___jp_332_:
{
lean_object* v___x_336_; 
lean_inc_ref(v_setupFile_311_);
v___x_336_ = l_Lake_createParentDirs(v_setupFile_311_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec_ref_known(v___x_336_, 1);
v___x_337_ = l_Lean_instToJsonModuleSetup_toJson(v_setup_310_);
v___x_338_ = lean_unsigned_to_nat(80u);
v___x_339_ = l_Lean_Json_pretty(v___x_337_, v___x_338_);
v___x_340_ = l_IO_FS_writeFile(v_setupFile_311_, v___x_339_);
lean_dec_ref(v___x_339_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_406_; 
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v___x_340_, 0);
lean_dec(v_unused_407_);
v___x_342_ = v___x_340_;
v_isShared_343_ = v_isSharedCheck_406_;
goto v_resetjp_341_;
}
else
{
lean_dec(v___x_340_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_406_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_344_ = lean_obj_once(&l_Lake_compileLeanModule___closed__1, &l_Lake_compileLeanModule___closed__1_once, _init_l_Lake_compileLeanModule___closed__1);
lean_inc_ref(v_setupFile_311_);
v___x_345_ = lean_array_push(v___x_344_, v_setupFile_311_);
v___x_346_ = l_Array_append___redArg(v_args_334_, v___x_345_);
lean_dec_ref(v___x_345_);
v___x_347_ = ((lean_object*)(l_Lake_compileLeanModule___closed__2));
v___x_348_ = lean_array_push(v___x_346_, v___x_347_);
v___x_349_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_350_ = lean_box(0);
v___x_351_ = ((lean_object*)(l_Lake_compileLeanModule___closed__4));
v___x_352_ = l_System_SearchPath_toString(v_leanPath_314_);
if (v_isShared_343_ == 0)
{
lean_ctor_set_tag(v___x_342_, 1);
lean_ctor_set(v___x_342_, 0, v___x_352_);
v___x_354_ = v___x_342_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_405_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_351_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_mk_empty_array_with_capacity(v___x_356_);
v___x_358_ = lean_array_push(v___x_357_, v___x_355_);
v___x_359_ = 1;
v___x_360_ = 0;
lean_inc_ref(v___x_358_);
lean_inc_ref(v_lean_315_);
v___x_361_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_361_, 0, v___x_349_);
lean_ctor_set(v___x_361_, 1, v_lean_315_);
lean_ctor_set(v___x_361_, 2, v___x_348_);
lean_ctor_set(v___x_361_, 3, v___x_350_);
lean_ctor_set(v___x_361_, 4, v___x_358_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*5, v___x_359_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*5 + 1, v___x_360_);
v___x_362_ = lean_array_get_size(v___y_335_);
lean_inc_ref(v___x_361_);
v___x_363_ = l_Lake_mkCmdLog(v___x_361_);
v___x_364_ = 0;
v___x_365_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*1, v___x_364_);
v___x_366_ = lean_array_push(v___y_335_, v___x_365_);
v___x_367_ = l_IO_Process_output(v___x_361_, v___x_350_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; uint32_t v_exitCode_369_; lean_object* v_stdout_370_; lean_object* v_stderr_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
lean_dec_ref(v_lean_315_);
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
v_exitCode_369_ = lean_ctor_get_uint32(v_a_368_, sizeof(void*)*2);
v_stdout_370_ = lean_ctor_get(v_a_368_, 0);
lean_inc_ref(v_stdout_370_);
v_stderr_371_ = lean_ctor_get(v_a_368_, 1);
lean_inc_ref(v_stderr_371_);
lean_dec(v_a_368_);
v___x_372_ = lean_string_utf8_byte_size(v_stdout_370_);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_nat_dec_eq(v___x_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
lean_inc_ref(v_stdout_370_);
v___x_375_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_375_, 0, v_stdout_370_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
lean_ctor_set(v___x_375_, 2, v___x_372_);
v___x_376_ = ((lean_object*)(l_Lake_compileLeanModule___closed__5));
v___x_377_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0(v___x_375_);
v___x_378_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(v_relLeanFile_309_, v_stdout_370_, v___x_375_, v___x_372_, v___x_377_, v___x_376_, v___x_366_);
lean_dec_ref_known(v___x_375_, 3);
lean_dec_ref(v_stdout_370_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v_a_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
v_a_380_ = lean_ctor_get(v___x_378_, 1);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_378_, 2);
v___x_381_ = lean_string_utf8_byte_size(v_a_379_);
v___x_382_ = lean_nat_dec_eq(v___x_381_, v___x_373_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_383_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1));
v___x_384_ = lean_string_append(v___x_383_, v_a_379_);
lean_dec(v_a_379_);
v___x_385_ = 1;
v___x_386_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*1, v___x_385_);
v___x_387_ = lean_box(0);
v___x_388_ = lean_array_push(v_a_380_, v___x_386_);
v___x_389_ = l_Lake_compileLeanModule___lam__0(v_exitCode_369_, v___y_333_, v_ir_x3f_329_, v_c_x3f_330_, v_setupFile_311_, v___x_349_, v_leanir_316_, v___x_350_, v___x_358_, v___x_359_, v___x_360_, v___x_350_, v_olean_x3f_327_, v_stderr_371_, v___x_387_, v___x_388_);
lean_dec(v_olean_x3f_327_);
v___y_324_ = v___x_362_;
v___y_325_ = v___x_389_;
goto v___jp_323_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v_a_379_);
v___x_390_ = lean_box(0);
v___x_391_ = l_Lake_compileLeanModule___lam__0(v_exitCode_369_, v___y_333_, v_ir_x3f_329_, v_c_x3f_330_, v_setupFile_311_, v___x_349_, v_leanir_316_, v___x_350_, v___x_358_, v___x_359_, v___x_360_, v___x_350_, v_olean_x3f_327_, v_stderr_371_, v___x_390_, v_a_380_);
lean_dec(v_olean_x3f_327_);
v___y_324_ = v___x_362_;
v___y_325_ = v___x_391_;
goto v___jp_323_;
}
}
else
{
lean_object* v_a_392_; 
lean_dec_ref(v_stderr_371_);
lean_dec_ref(v___x_358_);
lean_dec(v_c_x3f_330_);
lean_dec(v_ir_x3f_329_);
lean_dec(v_olean_x3f_327_);
lean_dec_ref(v_leanir_316_);
lean_dec_ref(v_setupFile_311_);
v_a_392_ = lean_ctor_get(v___x_378_, 1);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_378_, 2);
v___y_320_ = v___x_362_;
v_a_321_ = v_a_392_;
goto v___jp_319_;
}
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec_ref(v_stdout_370_);
lean_dec_ref(v_relLeanFile_309_);
v___x_393_ = lean_box(0);
v___x_394_ = l_Lake_compileLeanModule___lam__0(v_exitCode_369_, v___y_333_, v_ir_x3f_329_, v_c_x3f_330_, v_setupFile_311_, v___x_349_, v_leanir_316_, v___x_350_, v___x_358_, v___x_359_, v___x_360_, v___x_350_, v_olean_x3f_327_, v_stderr_371_, v___x_393_, v___x_366_);
lean_dec(v_olean_x3f_327_);
v___y_324_ = v___x_362_;
v___y_325_ = v___x_394_;
goto v___jp_323_;
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec_ref(v___x_358_);
lean_dec(v_c_x3f_330_);
lean_dec(v_ir_x3f_329_);
lean_dec(v_olean_x3f_327_);
lean_dec_ref(v_leanir_316_);
lean_dec_ref(v_setupFile_311_);
lean_dec_ref(v_relLeanFile_309_);
v_a_395_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_367_, 1);
v___x_396_ = ((lean_object*)(l_Lake_compileLeanModule___closed__6));
v___x_397_ = lean_string_append(v___x_396_, v_lean_315_);
lean_dec_ref(v_lean_315_);
v___x_398_ = ((lean_object*)(l_Lake_compileLeanModule___closed__7));
v___x_399_ = lean_string_append(v___x_397_, v___x_398_);
v___x_400_ = lean_io_error_to_string(v_a_395_);
v___x_401_ = lean_string_append(v___x_399_, v___x_400_);
lean_dec_ref(v___x_400_);
v___x_402_ = 3;
v___x_403_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*1, v___x_402_);
v___x_404_ = lean_array_push(v___x_366_, v___x_403_);
v___y_320_ = v___x_362_;
v_a_321_ = v___x_404_;
goto v___jp_319_;
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec_ref(v_args_334_);
lean_dec(v_c_x3f_330_);
lean_dec(v_ir_x3f_329_);
lean_dec(v_olean_x3f_327_);
lean_dec_ref(v_leanir_316_);
lean_dec_ref(v_lean_315_);
lean_dec(v_leanPath_314_);
lean_dec_ref(v_setupFile_311_);
lean_dec_ref(v_relLeanFile_309_);
v_a_408_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_340_, 1);
v___x_409_ = lean_io_error_to_string(v_a_408_);
v___x_410_ = 3;
v___x_411_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_411_, 0, v___x_409_);
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*1, v___x_410_);
v___x_412_ = lean_array_get_size(v___y_335_);
v___x_413_ = lean_array_push(v___y_335_, v___x_411_);
v___x_414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_412_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
return v___x_414_;
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_416_; uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec_ref(v_args_334_);
lean_dec(v_c_x3f_330_);
lean_dec(v_ir_x3f_329_);
lean_dec(v_olean_x3f_327_);
lean_dec_ref(v_leanir_316_);
lean_dec_ref(v_lean_315_);
lean_dec(v_leanPath_314_);
lean_dec_ref(v_setupFile_311_);
lean_dec_ref(v_setup_310_);
lean_dec_ref(v_relLeanFile_309_);
v_a_415_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_336_, 1);
v___x_416_ = lean_io_error_to_string(v_a_415_);
v___x_417_ = 3;
v___x_418_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*1, v___x_417_);
v___x_419_ = lean_array_get_size(v___y_335_);
v___x_420_ = lean_array_push(v___y_335_, v___x_418_);
v___x_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_419_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
return v___x_421_;
}
}
v___jp_422_:
{
if (lean_obj_tag(v_bc_x3f_331_) == 1)
{
lean_object* v_val_426_; lean_object* v___x_427_; 
v_val_426_ = lean_ctor_get(v_bc_x3f_331_, 0);
lean_inc_n(v_val_426_, 2);
lean_dec_ref_known(v_bc_x3f_331_, 1);
v___x_427_ = l_Lake_createParentDirs(v_val_426_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec_ref_known(v___x_427_, 1);
v___x_428_ = lean_obj_once(&l_Lake_compileLeanModule___closed__9, &l_Lake_compileLeanModule___closed__9_once, _init_l_Lake_compileLeanModule___closed__9);
v___x_429_ = lean_array_push(v___x_428_, v_val_426_);
v___x_430_ = l_Array_append___redArg(v_args_425_, v___x_429_);
lean_dec_ref(v___x_429_);
v___y_333_ = v___y_424_;
v_args_334_ = v___x_430_;
v___y_335_ = v___y_423_;
goto v___jp_332_;
}
else
{
lean_object* v_a_431_; lean_object* v___x_432_; uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec(v_val_426_);
lean_dec_ref(v_args_425_);
lean_dec(v_c_x3f_330_);
lean_dec(v_ir_x3f_329_);
lean_dec(v_olean_x3f_327_);
lean_dec_ref(v_leanir_316_);
lean_dec_ref(v_lean_315_);
lean_dec(v_leanPath_314_);
lean_dec_ref(v_setupFile_311_);
lean_dec_ref(v_setup_310_);
lean_dec_ref(v_relLeanFile_309_);
v_a_431_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v___x_427_, 1);
v___x_432_ = lean_io_error_to_string(v_a_431_);
v___x_433_ = 3;
v___x_434_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*1, v___x_433_);
v___x_435_ = lean_array_get_size(v___y_423_);
v___x_436_ = lean_array_push(v___y_423_, v___x_434_);
v___x_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_435_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
return v___x_437_;
}
}
else
{
lean_dec(v_bc_x3f_331_);
v___y_333_ = v___y_424_;
v_args_334_ = v_args_425_;
v___y_335_ = v___y_423_;
goto v___jp_332_;
}
}
v___jp_438_:
{
if (lean_obj_tag(v_c_x3f_330_) == 1)
{
lean_object* v_val_442_; lean_object* v___x_443_; 
v_val_442_ = lean_ctor_get(v_c_x3f_330_, 0);
lean_inc(v_val_442_);
v___x_443_ = l_Lake_createParentDirs(v_val_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec_ref_known(v___x_443_, 1);
v___x_444_ = lean_obj_once(&l_Lake_compileLeanModule___closed__11, &l_Lake_compileLeanModule___closed__11_once, _init_l_Lake_compileLeanModule___closed__11);
lean_inc(v_val_442_);
v___x_445_ = lean_array_push(v___x_444_, v_val_442_);
v___x_446_ = l_Array_append___redArg(v___y_440_, v___x_445_);
lean_dec_ref(v___x_445_);
v___y_423_ = v___y_439_;
v___y_424_ = v___y_441_;
v_args_425_ = v___x_446_;
goto v___jp_422_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec_ref_known(v_c_x3f_330_, 1);
lean_dec_ref(v___y_440_);
lean_dec(v_bc_x3f_331_);
lean_dec(v_ir_x3f_329_);
lean_dec(v_olean_x3f_327_);
lean_dec_ref(v_leanir_316_);
lean_dec_ref(v_lean_315_);
lean_dec(v_leanPath_314_);
lean_dec_ref(v_setupFile_311_);
lean_dec_ref(v_setup_310_);
lean_dec_ref(v_relLeanFile_309_);
v_a_447_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_443_, 1);
v___x_448_ = lean_io_error_to_string(v_a_447_);
v___x_449_ = 3;
v___x_450_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*1, v___x_449_);
v___x_451_ = lean_array_get_size(v___y_439_);
v___x_452_ = lean_array_push(v___y_439_, v___x_450_);
v___x_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
return v___x_453_;
}
}
else
{
v___y_423_ = v___y_439_;
v___y_424_ = v___y_441_;
v_args_425_ = v___y_440_;
goto v___jp_422_;
}
}
v___jp_454_:
{
uint8_t v_isModule_457_; 
v_isModule_457_ = lean_ctor_get_uint8(v_setup_310_, sizeof(void*)*7);
if (v_isModule_457_ == 0)
{
v___y_439_ = v___y_456_;
v___y_440_ = v_args_455_;
v___y_441_ = v_isModule_457_;
goto v___jp_438_;
}
else
{
lean_object* v_options_458_; lean_object* v_opts_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_options_458_ = lean_ctor_get(v_setup_310_, 6);
lean_inc(v_options_458_);
v_opts_459_ = l_Lean_LeanOptions_toOptions(v_options_458_);
v___x_460_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_461_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2(v_opts_459_, v___x_460_);
lean_dec_ref(v_opts_459_);
if (v___x_461_ == 0)
{
v___y_439_ = v___y_456_;
v___y_440_ = v_args_455_;
v___y_441_ = v___x_461_;
goto v___jp_438_;
}
else
{
v___y_423_ = v___y_456_;
v___y_424_ = v___x_461_;
v_args_425_ = v_args_455_;
goto v___jp_422_;
}
}
}
v___jp_462_:
{
if (lean_obj_tag(v_ilean_x3f_328_) == 1)
{
lean_object* v_val_465_; lean_object* v___x_466_; 
v_val_465_ = lean_ctor_get(v_ilean_x3f_328_, 0);
lean_inc_n(v_val_465_, 2);
lean_dec_ref_known(v_ilean_x3f_328_, 1);
v___x_466_ = l_Lake_createParentDirs(v_val_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref_known(v___x_466_, 1);
v___x_467_ = lean_obj_once(&l_Lake_compileLeanModule___closed__13, &l_Lake_compileLeanModule___closed__13_once, _init_l_Lake_compileLeanModule___closed__13);
v___x_468_ = lean_array_push(v___x_467_, v_val_465_);
v___x_469_ = l_Array_append___redArg(v_args_463_, v___x_468_);
lean_dec_ref(v___x_468_);
v_args_455_ = v___x_469_;
v___y_456_ = v___y_464_;
goto v___jp_454_;
}
else
{
lean_object* v_a_470_; lean_object* v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_val_465_);
lean_dec_ref(v_args_463_);
lean_dec(v_bc_x3f_331_);
lean_dec(v_c_x3f_330_);
lean_dec(v_ir_x3f_329_);
lean_dec(v_olean_x3f_327_);
lean_dec_ref(v_leanir_316_);
lean_dec_ref(v_lean_315_);
lean_dec(v_leanPath_314_);
lean_dec_ref(v_setupFile_311_);
lean_dec_ref(v_setup_310_);
lean_dec_ref(v_relLeanFile_309_);
v_a_470_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_466_, 1);
v___x_471_ = lean_io_error_to_string(v_a_470_);
v___x_472_ = 3;
v___x_473_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*1, v___x_472_);
v___x_474_ = lean_array_get_size(v___y_464_);
v___x_475_ = lean_array_push(v___y_464_, v___x_473_);
v___x_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
return v___x_476_;
}
}
else
{
lean_dec(v_ilean_x3f_328_);
v_args_455_ = v_args_463_;
v___y_456_ = v___y_464_;
goto v___jp_454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object* v_leanFile_490_, lean_object* v_relLeanFile_491_, lean_object* v_setup_492_, lean_object* v_setupFile_493_, lean_object* v_arts_494_, lean_object* v_leanArgs_495_, lean_object* v_leanPath_496_, lean_object* v_lean_497_, lean_object* v_leanir_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lake_compileLeanModule(v_leanFile_490_, v_relLeanFile_491_, v_setup_492_, v_setupFile_493_, v_arts_494_, v_leanArgs_495_, v_leanPath_496_, v_lean_497_, v_leanir_498_, v_a_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1(lean_object* v_relLeanFile_502_, lean_object* v___x_503_, lean_object* v___x_504_, lean_object* v___x_505_, lean_object* v_inst_506_, lean_object* v_R_507_, lean_object* v_a_508_, lean_object* v_b_509_, lean_object* v_c_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(v_relLeanFile_502_, v___x_503_, v___x_504_, v___x_505_, v_a_508_, v_b_509_, v___y_511_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___boxed(lean_object* v_relLeanFile_514_, lean_object* v___x_515_, lean_object* v___x_516_, lean_object* v___x_517_, lean_object* v_inst_518_, lean_object* v_R_519_, lean_object* v_a_520_, lean_object* v_b_521_, lean_object* v_c_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1(v_relLeanFile_514_, v___x_515_, v___x_516_, v___x_517_, v_inst_518_, v_R_519_, v_a_520_, v_b_521_, v_c_522_, v___y_523_);
lean_dec_ref(v___x_516_);
lean_dec_ref(v___x_515_);
return v_res_525_;
}
}
static lean_object* _init_l_Lake_compileO___closed__0(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_526_ = ((lean_object*)(l_Lake_compileLeanModule___closed__10));
v___x_527_ = lean_unsigned_to_nat(4u);
v___x_528_ = lean_mk_empty_array_with_capacity(v___x_527_);
v___x_529_ = lean_array_push(v___x_528_, v___x_526_);
return v___x_529_;
}
}
static lean_object* _init_l_Lake_compileO___closed__1(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_531_ = lean_obj_once(&l_Lake_compileO___closed__0, &l_Lake_compileO___closed__0_once, _init_l_Lake_compileO___closed__0);
v___x_532_ = lean_array_push(v___x_531_, v___x_530_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object* v_oFile_535_, lean_object* v_srcFile_536_, lean_object* v_moreArgs_537_, lean_object* v_compiler_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_541_; 
lean_inc_ref(v_oFile_535_);
v___x_541_ = l_Lake_createParentDirs(v_oFile_535_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_dec_ref_known(v___x_541_, 1);
v___x_542_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_543_ = lean_obj_once(&l_Lake_compileO___closed__1, &l_Lake_compileO___closed__1_once, _init_l_Lake_compileO___closed__1);
v___x_544_ = lean_array_push(v___x_543_, v_oFile_535_);
v___x_545_ = lean_array_push(v___x_544_, v_srcFile_536_);
v___x_546_ = l_Array_append___redArg(v___x_545_, v_moreArgs_537_);
v___x_547_ = lean_box(0);
v___x_548_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_549_ = 1;
v___x_550_ = 0;
v___x_551_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_551_, 0, v___x_542_);
lean_ctor_set(v___x_551_, 1, v_compiler_538_);
lean_ctor_set(v___x_551_, 2, v___x_546_);
lean_ctor_set(v___x_551_, 3, v___x_547_);
lean_ctor_set(v___x_551_, 4, v___x_548_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*5, v___x_549_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*5 + 1, v___x_550_);
v___x_552_ = l_Lake_proc(v___x_551_, v___x_550_, v___x_547_, v_a_539_);
return v___x_552_;
}
else
{
lean_object* v_a_553_; lean_object* v___x_554_; uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec_ref(v_compiler_538_);
lean_dec_ref(v_srcFile_536_);
lean_dec_ref(v_oFile_535_);
v_a_553_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_541_, 1);
v___x_554_ = lean_io_error_to_string(v_a_553_);
v___x_555_ = 3;
v___x_556_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*1, v___x_555_);
v___x_557_ = lean_array_get_size(v_a_539_);
v___x_558_ = lean_array_push(v_a_539_, v___x_556_);
v___x_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object* v_oFile_560_, lean_object* v_srcFile_561_, lean_object* v_moreArgs_562_, lean_object* v_compiler_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lake_compileO(v_oFile_560_, v_srcFile_561_, v_moreArgs_562_, v_compiler_563_, v_a_564_);
lean_dec_ref(v_moreArgs_562_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(lean_object* v___x_567_, lean_object* v___y_568_, lean_object* v_a_569_, lean_object* v_b_570_){
_start:
{
lean_object* v_startInclusive_571_; lean_object* v_endExclusive_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_startInclusive_571_ = lean_ctor_get(v___x_567_, 1);
v_endExclusive_572_ = lean_ctor_get(v___x_567_, 2);
v___x_573_ = lean_nat_sub(v_endExclusive_572_, v_startInclusive_571_);
v___x_574_ = lean_nat_dec_eq(v_a_569_, v___x_573_);
lean_dec(v___x_573_);
if (v___x_574_ == 0)
{
uint32_t v___x_575_; lean_object* v___x_576_; uint32_t v___x_577_; uint8_t v___y_579_; uint8_t v___x_585_; 
v___x_575_ = lean_string_utf8_get_fast(v___y_568_, v_a_569_);
v___x_576_ = lean_string_utf8_next_fast(v___y_568_, v_a_569_);
lean_dec(v_a_569_);
v___x_577_ = 92;
v___x_585_ = lean_uint32_dec_eq(v___x_575_, v___x_577_);
if (v___x_585_ == 0)
{
uint32_t v___x_586_; uint8_t v___x_587_; 
v___x_586_ = 34;
v___x_587_ = lean_uint32_dec_eq(v___x_575_, v___x_586_);
v___y_579_ = v___x_587_;
goto v___jp_578_;
}
else
{
v___y_579_ = v___x_585_;
goto v___jp_578_;
}
v___jp_578_:
{
if (v___y_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_string_push(v_b_570_, v___x_575_);
v_a_569_ = v___x_576_;
v_b_570_ = v___x_580_;
goto _start;
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_string_push(v_b_570_, v___x_577_);
v___x_583_ = lean_string_push(v___x_582_, v___x_575_);
v_a_569_ = v___x_576_;
v_b_570_ = v___x_583_;
goto _start;
}
}
}
else
{
lean_dec(v_a_569_);
return v_b_570_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg___boxed(lean_object* v___x_588_, lean_object* v___y_589_, lean_object* v_a_590_, lean_object* v_b_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_588_, v___y_589_, v_a_590_, v_b_591_);
lean_dec_ref(v___y_589_);
lean_dec_ref(v___x_588_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(lean_object* v_a_595_, lean_object* v_as_596_, size_t v_i_597_, size_t v_stop_598_, lean_object* v_b_599_, lean_object* v___y_600_){
_start:
{
uint8_t v___x_602_; 
v___x_602_ = lean_usize_dec_eq(v_i_597_, v_stop_598_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_603_ = lean_array_uget_borrowed(v_as_596_, v_i_597_);
v___x_604_ = ((lean_object*)(l_Lake_compileLeanModule___closed__5));
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = lean_string_utf8_byte_size(v___x_603_);
lean_inc(v___x_603_);
v___x_607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_607_, 0, v___x_603_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
lean_ctor_set(v___x_607_, 2, v___x_606_);
v___x_608_ = l_String_Slice_positions(v___x_607_);
v___x_609_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_607_, v___x_603_, v___x_608_, v___x_604_);
lean_dec_ref_known(v___x_607_, 3);
v___x_610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0));
v___x_611_ = lean_string_append(v___x_610_, v___x_609_);
lean_dec_ref(v___x_609_);
v___x_612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1));
v___x_613_ = lean_string_append(v___x_611_, v___x_612_);
v___x_614_ = lean_io_prim_handle_put_str(v_a_595_, v___x_613_);
lean_dec_ref(v___x_613_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; size_t v___x_616_; size_t v___x_617_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v___x_616_ = ((size_t)1ULL);
v___x_617_ = lean_usize_add(v_i_597_, v___x_616_);
v_i_597_ = v___x_617_;
v_b_599_ = v_a_615_;
goto _start;
}
else
{
lean_object* v_a_619_; lean_object* v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_a_619_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_614_, 1);
v___x_620_ = lean_io_error_to_string(v_a_619_);
v___x_621_ = 3;
v___x_622_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*1, v___x_621_);
v___x_623_ = lean_array_get_size(v___y_600_);
v___x_624_ = lean_array_push(v___y_600_, v___x_622_);
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
return v___x_625_;
}
}
else
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v_b_599_);
lean_ctor_set(v___x_626_, 1, v___y_600_);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___boxed(lean_object* v_a_627_, lean_object* v_as_628_, lean_object* v_i_629_, lean_object* v_stop_630_, lean_object* v_b_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
size_t v_i_boxed_634_; size_t v_stop_boxed_635_; lean_object* v_res_636_; 
v_i_boxed_634_ = lean_unbox_usize(v_i_629_);
lean_dec(v_i_629_);
v_stop_boxed_635_ = lean_unbox_usize(v_stop_630_);
lean_dec(v_stop_630_);
v_res_636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_627_, v_as_628_, v_i_boxed_634_, v_stop_boxed_635_, v_b_631_, v___y_632_);
lean_dec_ref(v_as_628_);
lean_dec(v_a_627_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object* v_basePath_639_, lean_object* v_args_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___x_643_; lean_object* v_rspFile_644_; lean_object* v_a_646_; lean_object* v___y_654_; uint8_t v___x_665_; lean_object* v___x_666_; 
v___x_643_ = ((lean_object*)(l_Lake_mkArgs___closed__0));
v_rspFile_644_ = l_System_FilePath_addExtension(v_basePath_639_, v___x_643_);
v___x_665_ = 1;
v___x_666_ = lean_io_prim_handle_mk(v_rspFile_644_, v___x_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_array_get_size(v_args_640_);
v___x_670_ = lean_nat_dec_lt(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
lean_dec(v_a_667_);
v_a_646_ = v_a_641_;
goto v___jp_645_;
}
else
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_box(0);
v___x_672_ = lean_nat_dec_le(v___x_669_, v___x_669_);
if (v___x_672_ == 0)
{
if (v___x_670_ == 0)
{
lean_dec(v_a_667_);
v_a_646_ = v_a_641_;
goto v___jp_645_;
}
else
{
size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v___x_673_ = ((size_t)0ULL);
v___x_674_ = lean_usize_of_nat(v___x_669_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_667_, v_args_640_, v___x_673_, v___x_674_, v___x_671_, v_a_641_);
lean_dec(v_a_667_);
v___y_654_ = v___x_675_;
goto v___jp_653_;
}
}
else
{
size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; 
v___x_676_ = ((size_t)0ULL);
v___x_677_ = lean_usize_of_nat(v___x_669_);
v___x_678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_667_, v_args_640_, v___x_676_, v___x_677_, v___x_671_, v_a_641_);
lean_dec(v_a_667_);
v___y_654_ = v___x_678_;
goto v___jp_653_;
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_680_; uint8_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
lean_dec_ref(v_rspFile_644_);
v_a_679_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_666_, 1);
v___x_680_ = lean_io_error_to_string(v_a_679_);
v___x_681_ = 3;
v___x_682_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set_uint8(v___x_682_, sizeof(void*)*1, v___x_681_);
v___x_683_ = lean_array_get_size(v_a_641_);
v___x_684_ = lean_array_push(v_a_641_, v___x_682_);
v___x_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
return v___x_685_;
}
v___jp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_647_ = ((lean_object*)(l_Lake_mkArgs___closed__1));
v___x_648_ = lean_string_append(v___x_647_, v_rspFile_644_);
lean_dec_ref(v_rspFile_644_);
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_mk_empty_array_with_capacity(v___x_649_);
v___x_651_ = lean_array_push(v___x_650_, v___x_648_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v_a_646_);
return v___x_652_;
}
v___jp_653_:
{
if (lean_obj_tag(v___y_654_) == 0)
{
lean_object* v_a_655_; 
v_a_655_ = lean_ctor_get(v___y_654_, 1);
lean_inc(v_a_655_);
lean_dec_ref_known(v___y_654_, 2);
v_a_646_ = v_a_655_;
goto v___jp_645_;
}
else
{
lean_object* v_a_656_; lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec_ref(v_rspFile_644_);
v_a_656_ = lean_ctor_get(v___y_654_, 0);
v_a_657_ = lean_ctor_get(v___y_654_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v___y_654_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___y_654_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_inc(v_a_656_);
lean_dec(v___y_654_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_656_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs___boxed(lean_object* v_basePath_686_, lean_object* v_args_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lake_mkArgs(v_basePath_686_, v_args_687_, v_a_688_);
lean_dec_ref(v_args_687_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(lean_object* v___x_691_, lean_object* v___y_692_, lean_object* v_inst_693_, lean_object* v_R_694_, lean_object* v_a_695_, lean_object* v_b_696_, lean_object* v_c_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_691_, v___y_692_, v_a_695_, v_b_696_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(lean_object* v___x_699_, lean_object* v___y_700_, lean_object* v_inst_701_, lean_object* v_R_702_, lean_object* v_a_703_, lean_object* v_b_704_, lean_object* v_c_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(v___x_699_, v___y_700_, v_inst_701_, v_R_702_, v_a_703_, v_b_704_, v_c_705_);
lean_dec_ref(v___y_700_);
lean_dec_ref(v___x_699_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(size_t v_sz_707_, size_t v_i_708_, lean_object* v_bs_709_){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = lean_usize_dec_lt(v_i_708_, v_sz_707_);
if (v___x_710_ == 0)
{
return v_bs_709_;
}
else
{
lean_object* v_v_711_; lean_object* v___x_712_; lean_object* v_bs_x27_713_; size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v_v_711_ = lean_array_uget(v_bs_709_, v_i_708_);
v___x_712_ = lean_unsigned_to_nat(0u);
v_bs_x27_713_ = lean_array_uset(v_bs_709_, v_i_708_, v___x_712_);
v___x_714_ = ((size_t)1ULL);
v___x_715_ = lean_usize_add(v_i_708_, v___x_714_);
v___x_716_ = lean_array_uset(v_bs_x27_713_, v_i_708_, v_v_711_);
v_i_708_ = v___x_715_;
v_bs_709_ = v___x_716_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0___boxed(lean_object* v_sz_718_, lean_object* v_i_719_, lean_object* v_bs_720_){
_start:
{
size_t v_sz_boxed_721_; size_t v_i_boxed_722_; lean_object* v_res_723_; 
v_sz_boxed_721_ = lean_unbox_usize(v_sz_718_);
lean_dec(v_sz_718_);
v_i_boxed_722_ = lean_unbox_usize(v_i_719_);
lean_dec(v_i_719_);
v_res_723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_boxed_721_, v_i_boxed_722_, v_bs_720_);
return v_res_723_;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__3(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = ((lean_object*)(l_Lake_compileStaticLib___closed__2));
v___x_731_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_732_ = lean_array_push(v___x_731_, v___x_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object* v_libFile_733_, lean_object* v_oFiles_734_, lean_object* v_ar_735_, uint8_t v_thin_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_739_; 
lean_inc_ref(v_libFile_733_);
v___x_739_ = l_Lake_createParentDirs(v_libFile_733_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v___x_740_; 
lean_dec_ref_known(v___x_739_, 1);
v___x_740_ = l_Lake_removeFileIfExists(v_libFile_733_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v___x_741_; uint8_t v___x_742_; lean_object* v___y_744_; 
lean_dec_ref_known(v___x_740_, 1);
v___x_741_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_742_ = 1;
if (v_thin_736_ == 0)
{
v___y_744_ = v___x_741_;
goto v___jp_743_;
}
else
{
lean_object* v___x_768_; 
v___x_768_ = lean_obj_once(&l_Lake_compileStaticLib___closed__3, &l_Lake_compileStaticLib___closed__3_once, _init_l_Lake_compileStaticLib___closed__3);
v___y_744_ = v___x_768_;
goto v___jp_743_;
}
v___jp_743_:
{
size_t v_sz_745_; size_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_sz_745_ = lean_array_size(v_oFiles_734_);
v___x_746_ = ((size_t)0ULL);
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_745_, v___x_746_, v_oFiles_734_);
lean_inc_ref(v_libFile_733_);
v___x_748_ = l_Lake_mkArgs(v_libFile_733_, v___x_747_, v_a_737_);
lean_dec_ref(v___x_747_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v_a_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
v_a_750_ = lean_ctor_get(v___x_748_, 1);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_748_, 2);
lean_inc_ref(v___y_744_);
v___x_751_ = lean_array_push(v___y_744_, v_libFile_733_);
v___x_752_ = l_Array_append___redArg(v___x_751_, v_a_749_);
lean_dec(v_a_749_);
v___x_753_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_754_ = lean_box(0);
v___x_755_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_756_ = 0;
v___x_757_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_757_, 0, v___x_753_);
lean_ctor_set(v___x_757_, 1, v_ar_735_);
lean_ctor_set(v___x_757_, 2, v___x_752_);
lean_ctor_set(v___x_757_, 3, v___x_754_);
lean_ctor_set(v___x_757_, 4, v___x_755_);
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*5, v___x_742_);
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*5 + 1, v___x_756_);
v___x_758_ = l_Lake_proc(v___x_757_, v___x_756_, v___x_754_, v_a_750_);
return v___x_758_;
}
else
{
lean_object* v_a_759_; lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref(v_ar_735_);
lean_dec_ref(v_libFile_733_);
v_a_759_ = lean_ctor_get(v___x_748_, 0);
v_a_760_ = lean_ctor_get(v___x_748_, 1);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_748_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_inc(v_a_759_);
lean_dec(v___x_748_);
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
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_759_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec_ref(v_ar_735_);
lean_dec_ref(v_oFiles_734_);
lean_dec_ref(v_libFile_733_);
v_a_769_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_740_, 1);
v___x_770_ = lean_io_error_to_string(v_a_769_);
v___x_771_ = 3;
v___x_772_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*1, v___x_771_);
v___x_773_ = lean_array_get_size(v_a_737_);
v___x_774_ = lean_array_push(v_a_737_, v___x_772_);
v___x_775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
return v___x_775_;
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec_ref(v_ar_735_);
lean_dec_ref(v_oFiles_734_);
lean_dec_ref(v_libFile_733_);
v_a_776_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_739_, 1);
v___x_777_ = lean_io_error_to_string(v_a_776_);
v___x_778_ = 3;
v___x_779_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*1, v___x_778_);
v___x_780_ = lean_array_get_size(v_a_737_);
v___x_781_ = lean_array_push(v_a_737_, v___x_779_);
v___x_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object* v_libFile_783_, lean_object* v_oFiles_784_, lean_object* v_ar_785_, lean_object* v_thin_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
uint8_t v_thin_boxed_789_; lean_object* v_res_790_; 
v_thin_boxed_789_ = lean_unbox(v_thin_786_);
v_res_790_ = l_Lake_compileStaticLib(v_libFile_783_, v_oFiles_784_, v_ar_785_, v_thin_boxed_789_, v_a_787_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = l_System_Platform_isOSX;
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
v___x_804_ = ((lean_object*)(l_Lake_compileO___closed__2));
return v___x_804_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0));
v___x_806_ = lean_io_getenv(v___x_805_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v___x_807_; 
v___x_807_ = ((lean_object*)(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4));
return v___x_807_;
}
else
{
lean_object* v___x_808_; 
lean_dec_ref_known(v___x_806_, 1);
v___x_808_ = ((lean_object*)(l_Lake_compileO___closed__2));
return v___x_808_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___boxed(lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
return v_res_810_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__1(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_812_ = ((lean_object*)(l_Lake_compileSharedLib___closed__0));
v___x_813_ = lean_unsigned_to_nat(3u);
v___x_814_ = lean_mk_empty_array_with_capacity(v___x_813_);
v___x_815_ = lean_array_push(v___x_814_, v___x_812_);
return v___x_815_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__2(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_817_ = lean_obj_once(&l_Lake_compileSharedLib___closed__1, &l_Lake_compileSharedLib___closed__1_once, _init_l_Lake_compileSharedLib___closed__1);
v___x_818_ = lean_array_push(v___x_817_, v___x_816_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object* v_libFile_819_, lean_object* v_linkArgs_820_, lean_object* v_linker_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___x_824_; 
lean_inc_ref(v_libFile_819_);
v___x_824_ = l_Lake_createParentDirs(v_libFile_819_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v___x_825_; 
lean_dec_ref_known(v___x_824_, 1);
lean_inc_ref(v_libFile_819_);
v___x_825_ = l_Lake_mkArgs(v_libFile_819_, v_linkArgs_820_, v_a_822_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v_a_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
v_a_827_ = lean_ctor_get(v___x_825_, 1);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_825_, 2);
v___x_828_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
v___x_829_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_830_ = lean_obj_once(&l_Lake_compileSharedLib___closed__2, &l_Lake_compileSharedLib___closed__2_once, _init_l_Lake_compileSharedLib___closed__2);
v___x_831_ = lean_array_push(v___x_830_, v_libFile_819_);
v___x_832_ = l_Array_append___redArg(v___x_831_, v_a_826_);
lean_dec(v_a_826_);
v___x_833_ = lean_box(0);
v___x_834_ = 1;
v___x_835_ = 0;
v___x_836_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_836_, 0, v___x_829_);
lean_ctor_set(v___x_836_, 1, v_linker_821_);
lean_ctor_set(v___x_836_, 2, v___x_832_);
lean_ctor_set(v___x_836_, 3, v___x_833_);
lean_ctor_set(v___x_836_, 4, v___x_828_);
lean_ctor_set_uint8(v___x_836_, sizeof(void*)*5, v___x_834_);
lean_ctor_set_uint8(v___x_836_, sizeof(void*)*5 + 1, v___x_835_);
v___x_837_ = l_Lake_proc(v___x_836_, v___x_835_, v___x_833_, v_a_827_);
return v___x_837_;
}
else
{
lean_object* v_a_838_; lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec_ref(v_linker_821_);
lean_dec_ref(v_libFile_819_);
v_a_838_ = lean_ctor_get(v___x_825_, 0);
v_a_839_ = lean_ctor_get(v___x_825_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_825_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_inc(v_a_838_);
lean_dec(v___x_825_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_838_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_848_; uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec_ref(v_linker_821_);
lean_dec_ref(v_libFile_819_);
v_a_847_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_824_, 1);
v___x_848_ = lean_io_error_to_string(v_a_847_);
v___x_849_ = 3;
v___x_850_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set_uint8(v___x_850_, sizeof(void*)*1, v___x_849_);
v___x_851_ = lean_array_get_size(v_a_822_);
v___x_852_ = lean_array_push(v_a_822_, v___x_850_);
v___x_853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object* v_libFile_854_, lean_object* v_linkArgs_855_, lean_object* v_linker_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lake_compileSharedLib(v_libFile_854_, v_linkArgs_855_, v_linker_856_, v_a_857_);
lean_dec_ref(v_linkArgs_855_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object* v_binFile_860_, lean_object* v_linkArgs_861_, lean_object* v_linker_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; 
lean_inc_ref(v_binFile_860_);
v___x_865_ = l_Lake_createParentDirs(v_binFile_860_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v___x_866_; 
lean_dec_ref_known(v___x_865_, 1);
lean_inc_ref(v_binFile_860_);
v___x_866_ = l_Lake_mkArgs(v_binFile_860_, v_linkArgs_861_, v_a_863_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
v_a_868_ = lean_ctor_get(v___x_866_, 1);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_866_, 2);
v___x_869_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
v___x_870_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_871_ = lean_unsigned_to_nat(2u);
v___x_872_ = lean_mk_empty_array_with_capacity(v___x_871_);
lean_dec_ref(v___x_872_);
v___x_873_ = lean_obj_once(&l_Lake_compileLeanModule___closed__15, &l_Lake_compileLeanModule___closed__15_once, _init_l_Lake_compileLeanModule___closed__15);
v___x_874_ = lean_array_push(v___x_873_, v_binFile_860_);
v___x_875_ = l_Array_append___redArg(v___x_874_, v_a_867_);
lean_dec(v_a_867_);
v___x_876_ = lean_box(0);
v___x_877_ = 1;
v___x_878_ = 0;
v___x_879_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_879_, 0, v___x_870_);
lean_ctor_set(v___x_879_, 1, v_linker_862_);
lean_ctor_set(v___x_879_, 2, v___x_875_);
lean_ctor_set(v___x_879_, 3, v___x_876_);
lean_ctor_set(v___x_879_, 4, v___x_869_);
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*5, v___x_877_);
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*5 + 1, v___x_878_);
v___x_880_ = l_Lake_proc(v___x_879_, v___x_878_, v___x_876_, v_a_868_);
return v___x_880_;
}
else
{
lean_object* v_a_881_; lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec_ref(v_linker_862_);
lean_dec_ref(v_binFile_860_);
v_a_881_ = lean_ctor_get(v___x_866_, 0);
v_a_882_ = lean_ctor_get(v___x_866_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_866_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_inc(v_a_881_);
lean_dec(v___x_866_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_881_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref(v_linker_862_);
lean_dec_ref(v_binFile_860_);
v_a_890_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_865_, 1);
v___x_891_ = lean_io_error_to_string(v_a_890_);
v___x_892_ = 3;
v___x_893_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*1, v___x_892_);
v___x_894_ = lean_array_get_size(v_a_863_);
v___x_895_ = lean_array_push(v_a_863_, v___x_893_);
v___x_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object* v_binFile_897_, lean_object* v_linkArgs_898_, lean_object* v_linker_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lake_compileExe(v_binFile_897_, v_linkArgs_898_, v_linker_899_, v_a_900_);
lean_dec_ref(v_linkArgs_898_);
return v_res_902_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0));
v___x_905_ = lean_unsigned_to_nat(2u);
v___x_906_ = lean_mk_empty_array_with_capacity(v___x_905_);
v___x_907_ = lean_array_push(v___x_906_, v___x_904_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(lean_object* v_as_908_, size_t v_i_909_, size_t v_stop_910_, lean_object* v_b_911_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = lean_usize_dec_eq(v_i_909_, v_stop_910_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; size_t v___x_917_; size_t v___x_918_; 
v___x_913_ = lean_array_uget_borrowed(v_as_908_, v_i_909_);
v___x_914_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1);
lean_inc(v___x_913_);
v___x_915_ = lean_array_push(v___x_914_, v___x_913_);
v___x_916_ = l_Array_append___redArg(v_b_911_, v___x_915_);
lean_dec_ref(v___x_915_);
v___x_917_ = ((size_t)1ULL);
v___x_918_ = lean_usize_add(v_i_909_, v___x_917_);
v_i_909_ = v___x_918_;
v_b_911_ = v___x_916_;
goto _start;
}
else
{
return v_b_911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___boxed(lean_object* v_as_920_, lean_object* v_i_921_, lean_object* v_stop_922_, lean_object* v_b_923_){
_start:
{
size_t v_i_boxed_924_; size_t v_stop_boxed_925_; lean_object* v_res_926_; 
v_i_boxed_924_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_stop_boxed_925_ = lean_unbox_usize(v_stop_922_);
lean_dec(v_stop_922_);
v_res_926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_as_920_, v_i_boxed_924_, v_stop_boxed_925_, v_b_923_);
lean_dec_ref(v_as_920_);
return v_res_926_;
}
}
static lean_object* _init_l_Lake_download___closed__5(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_932_ = ((lean_object*)(l_Lake_download___closed__1));
v___x_933_ = lean_unsigned_to_nat(7u);
v___x_934_ = lean_mk_empty_array_with_capacity(v___x_933_);
v___x_935_ = lean_array_push(v___x_934_, v___x_932_);
return v___x_935_;
}
}
static lean_object* _init_l_Lake_download___closed__6(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = ((lean_object*)(l_Lake_download___closed__2));
v___x_937_ = lean_obj_once(&l_Lake_download___closed__5, &l_Lake_download___closed__5_once, _init_l_Lake_download___closed__5);
v___x_938_ = lean_array_push(v___x_937_, v___x_936_);
return v___x_938_;
}
}
static lean_object* _init_l_Lake_download___closed__7(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_940_ = lean_obj_once(&l_Lake_download___closed__6, &l_Lake_download___closed__6_once, _init_l_Lake_download___closed__6);
v___x_941_ = lean_array_push(v___x_940_, v___x_939_);
return v___x_941_;
}
}
static lean_object* _init_l_Lake_download___closed__8(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_943_ = lean_obj_once(&l_Lake_download___closed__7, &l_Lake_download___closed__7_once, _init_l_Lake_download___closed__7);
v___x_944_ = lean_array_push(v___x_943_, v___x_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_download(lean_object* v_url_945_, lean_object* v_file_946_, lean_object* v_headers_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_962_; uint8_t v___x_978_; 
v___x_978_ = l_System_FilePath_pathExists(v_file_946_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
lean_inc_ref(v_file_946_);
v___x_979_ = l_Lake_createParentDirs(v_file_946_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_dec_ref_known(v___x_979_, 1);
v___y_962_ = v_a_948_;
goto v___jp_961_;
}
else
{
lean_object* v_a_980_; lean_object* v___x_981_; uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
lean_dec_ref(v_file_946_);
lean_dec_ref(v_url_945_);
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = lean_io_error_to_string(v_a_980_);
v___x_982_ = 3;
v___x_983_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*1, v___x_982_);
v___x_984_ = lean_array_get_size(v_a_948_);
v___x_985_ = lean_array_push(v_a_948_, v___x_983_);
v___x_986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
return v___x_986_;
}
}
else
{
lean_object* v___x_987_; 
v___x_987_ = lean_io_remove_file(v_file_946_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_dec_ref_known(v___x_987_, 1);
v___y_962_ = v_a_948_;
goto v___jp_961_;
}
else
{
lean_object* v_a_988_; lean_object* v___x_989_; uint8_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec_ref(v_file_946_);
lean_dec_ref(v_url_945_);
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = lean_io_error_to_string(v_a_988_);
v___x_990_ = 3;
v___x_991_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set_uint8(v___x_991_, sizeof(void*)*1, v___x_990_);
v___x_992_ = lean_array_get_size(v_a_948_);
v___x_993_ = lean_array_push(v_a_948_, v___x_991_);
v___x_994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
return v___x_994_;
}
}
v___jp_950_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; uint8_t v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_953_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_954_ = ((lean_object*)(l_Lake_download___closed__0));
v___x_955_ = lean_box(0);
v___x_956_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_957_ = 1;
v___x_958_ = 0;
v___x_959_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_959_, 0, v___x_953_);
lean_ctor_set(v___x_959_, 1, v___x_954_);
lean_ctor_set(v___x_959_, 2, v___y_952_);
lean_ctor_set(v___x_959_, 3, v___x_955_);
lean_ctor_set(v___x_959_, 4, v___x_956_);
lean_ctor_set_uint8(v___x_959_, sizeof(void*)*5, v___x_957_);
lean_ctor_set_uint8(v___x_959_, sizeof(void*)*5 + 1, v___x_958_);
v___x_960_ = l_Lake_proc(v___x_959_, v___x_957_, v___x_955_, v___y_951_);
return v___x_960_;
}
v___jp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_963_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_964_ = lean_obj_once(&l_Lake_download___closed__8, &l_Lake_download___closed__8_once, _init_l_Lake_download___closed__8);
v___x_965_ = lean_array_push(v___x_964_, v_file_946_);
v___x_966_ = lean_array_push(v___x_965_, v___x_963_);
v___x_967_ = lean_array_push(v___x_966_, v_url_945_);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_array_get_size(v_headers_947_);
v___x_970_ = lean_nat_dec_lt(v___x_968_, v___x_969_);
if (v___x_970_ == 0)
{
v___y_951_ = v___y_962_;
v___y_952_ = v___x_967_;
goto v___jp_950_;
}
else
{
uint8_t v___x_971_; 
v___x_971_ = lean_nat_dec_le(v___x_969_, v___x_969_);
if (v___x_971_ == 0)
{
if (v___x_970_ == 0)
{
v___y_951_ = v___y_962_;
v___y_952_ = v___x_967_;
goto v___jp_950_;
}
else
{
size_t v___x_972_; size_t v___x_973_; lean_object* v___x_974_; 
v___x_972_ = ((size_t)0ULL);
v___x_973_ = lean_usize_of_nat(v___x_969_);
v___x_974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_947_, v___x_972_, v___x_973_, v___x_967_);
v___y_951_ = v___y_962_;
v___y_952_ = v___x_974_;
goto v___jp_950_;
}
}
else
{
size_t v___x_975_; size_t v___x_976_; lean_object* v___x_977_; 
v___x_975_ = ((size_t)0ULL);
v___x_976_ = lean_usize_of_nat(v___x_969_);
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_947_, v___x_975_, v___x_976_, v___x_967_);
v___y_951_ = v___y_962_;
v___y_952_ = v___x_977_;
goto v___jp_950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object* v_url_995_, lean_object* v_file_996_, lean_object* v_headers_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lake_download(v_url_995_, v_file_996_, v_headers_997_, v_a_998_);
lean_dec_ref(v_headers_997_);
return v_res_1000_;
}
}
static lean_object* _init_l_Lake_untar___closed__3(void){
_start:
{
uint32_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = 122;
v___x_1005_ = ((lean_object*)(l_Lake_untar___closed__2));
v___x_1006_ = lean_string_push(v___x_1005_, v___x_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lake_untar(lean_object* v_file_1007_, lean_object* v_dir_1008_, uint8_t v_gzip_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1012_; 
lean_inc_ref(v_dir_1008_);
v___x_1012_ = l_IO_FS_createDirAll(v_dir_1008_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_opts_1014_; lean_object* v___y_1015_; lean_object* v___x_1033_; 
lean_dec_ref_known(v___x_1012_, 1);
v___x_1033_ = ((lean_object*)(l_Lake_untar___closed__2));
if (v_gzip_1009_ == 0)
{
v_opts_1014_ = v___x_1033_;
v___y_1015_ = v_a_1010_;
goto v___jp_1013_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_obj_once(&l_Lake_untar___closed__3, &l_Lake_untar___closed__3_once, _init_l_Lake_untar___closed__3);
v_opts_1014_ = v___x_1034_;
v___y_1015_ = v_a_1010_;
goto v___jp_1013_;
}
v___jp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1016_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_1017_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_1018_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_1019_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_1020_ = lean_unsigned_to_nat(5u);
v___x_1021_ = lean_mk_empty_array_with_capacity(v___x_1020_);
lean_inc_ref(v_opts_1014_);
v___x_1022_ = lean_array_push(v___x_1021_, v_opts_1014_);
v___x_1023_ = lean_array_push(v___x_1022_, v___x_1018_);
v___x_1024_ = lean_array_push(v___x_1023_, v_file_1007_);
v___x_1025_ = lean_array_push(v___x_1024_, v___x_1019_);
v___x_1026_ = lean_array_push(v___x_1025_, v_dir_1008_);
v___x_1027_ = lean_box(0);
v___x_1028_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_1029_ = 1;
v___x_1030_ = 0;
v___x_1031_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1031_, 0, v___x_1016_);
lean_ctor_set(v___x_1031_, 1, v___x_1017_);
lean_ctor_set(v___x_1031_, 2, v___x_1026_);
lean_ctor_set(v___x_1031_, 3, v___x_1027_);
lean_ctor_set(v___x_1031_, 4, v___x_1028_);
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*5, v___x_1029_);
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*5 + 1, v___x_1030_);
v___x_1032_ = l_Lake_proc(v___x_1031_, v___x_1029_, v___x_1027_, v___y_1015_);
return v___x_1032_;
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec_ref(v_dir_1008_);
lean_dec_ref(v_file_1007_);
v_a_1035_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1036_ = lean_io_error_to_string(v_a_1035_);
v___x_1037_ = 3;
v___x_1038_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*1, v___x_1037_);
v___x_1039_ = lean_array_get_size(v_a_1010_);
v___x_1040_ = lean_array_push(v_a_1010_, v___x_1038_);
v___x_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object* v_file_1042_, lean_object* v_dir_1043_, lean_object* v_gzip_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
uint8_t v_gzip_boxed_1047_; lean_object* v_res_1048_; 
v_gzip_boxed_1047_ = lean_unbox(v_gzip_1044_);
v_res_1048_ = l_Lake_untar(v_file_1042_, v_dir_1043_, v_gzip_boxed_1047_, v_a_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(lean_object* v_as_1050_, size_t v_sz_1051_, size_t v_i_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_){
_start:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_usize_dec_lt(v_i_1052_, v_sz_1051_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_b_1053_);
lean_ctor_set(v___x_1057_, 1, v___y_1054_);
return v___x_1057_;
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; size_t v___x_1062_; size_t v___x_1063_; 
v_a_1058_ = lean_array_uget_borrowed(v_as_1050_, v_i_1052_);
v___x_1059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0));
v___x_1060_ = lean_string_append(v___x_1059_, v_a_1058_);
v___x_1061_ = lean_array_push(v_b_1053_, v___x_1060_);
v___x_1062_ = ((size_t)1ULL);
v___x_1063_ = lean_usize_add(v_i_1052_, v___x_1062_);
v_i_1052_ = v___x_1063_;
v_b_1053_ = v___x_1061_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___boxed(lean_object* v_as_1065_, lean_object* v_sz_1066_, lean_object* v_i_1067_, lean_object* v_b_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
size_t v_sz_boxed_1071_; size_t v_i_boxed_1072_; lean_object* v_res_1073_; 
v_sz_boxed_1071_ = lean_unbox_usize(v_sz_1066_);
lean_dec(v_sz_1066_);
v_i_boxed_1072_ = lean_unbox_usize(v_i_1067_);
lean_dec(v_i_1067_);
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_as_1065_, v_sz_boxed_1071_, v_i_boxed_1072_, v_b_1068_, v___y_1069_);
lean_dec_ref(v_as_1065_);
return v_res_1073_;
}
}
static lean_object* _init_l_Lake_tar___closed__1(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1075_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_1076_ = lean_unsigned_to_nat(5u);
v___x_1077_ = lean_mk_empty_array_with_capacity(v___x_1076_);
v___x_1078_ = lean_array_push(v___x_1077_, v___x_1075_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lake_tar___closed__10(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = ((lean_object*)(l_Lake_tar___closed__9));
v___x_1097_ = ((lean_object*)(l_Lake_tar___closed__8));
v___x_1098_ = lean_array_push(v___x_1097_, v___x_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lake_tar(lean_object* v_dir_1099_, lean_object* v_file_1100_, uint8_t v_gzip_1101_, lean_object* v_excludePaths_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v___y_1106_; uint8_t v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___x_1117_; 
lean_inc_ref(v_file_1100_);
v___x_1117_ = l_Lake_createParentDirs(v_file_1100_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_args_1119_; lean_object* v___y_1120_; lean_object* v___x_1150_; 
lean_dec_ref_known(v___x_1117_, 1);
v___x_1150_ = ((lean_object*)(l_Lake_tar___closed__8));
if (v_gzip_1101_ == 0)
{
v_args_1119_ = v___x_1150_;
v___y_1120_ = v_a_1103_;
goto v___jp_1118_;
}
else
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_obj_once(&l_Lake_tar___closed__10, &l_Lake_tar___closed__10_once, _init_l_Lake_tar___closed__10);
v_args_1119_ = v___x_1151_;
v___y_1120_ = v_a_1103_;
goto v___jp_1118_;
}
v___jp_1118_:
{
size_t v_sz_1121_; size_t v___x_1122_; lean_object* v___x_1123_; 
v_sz_1121_ = lean_array_size(v_excludePaths_1102_);
v___x_1122_ = ((size_t)0ULL);
lean_inc_ref(v_args_1119_);
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_excludePaths_1102_, v_sz_1121_, v___x_1122_, v_args_1119_, v___y_1120_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v_a_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; uint8_t v___x_1138_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
v_a_1125_ = lean_ctor_get(v___x_1123_, 1);
lean_inc(v_a_1125_);
lean_dec_ref_known(v___x_1123_, 2);
v___x_1126_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_1127_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_1128_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_1129_ = ((lean_object*)(l_Lake_tar___closed__0));
v___x_1130_ = lean_obj_once(&l_Lake_tar___closed__1, &l_Lake_tar___closed__1_once, _init_l_Lake_tar___closed__1);
v___x_1131_ = lean_array_push(v___x_1130_, v_file_1100_);
v___x_1132_ = lean_array_push(v___x_1131_, v___x_1128_);
v___x_1133_ = lean_array_push(v___x_1132_, v_dir_1099_);
v___x_1134_ = lean_array_push(v___x_1133_, v___x_1129_);
v___x_1135_ = l_Array_append___redArg(v_a_1124_, v___x_1134_);
lean_dec_ref(v___x_1134_);
v___x_1136_ = lean_box(0);
v___x_1137_ = l_System_Platform_isOSX;
v___x_1138_ = 1;
if (v___x_1137_ == 0)
{
lean_object* v___x_1139_; 
v___x_1139_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_1106_ = v___x_1136_;
v___y_1107_ = v___x_1138_;
v___y_1108_ = v_a_1125_;
v___y_1109_ = v___x_1135_;
v___y_1110_ = v___x_1127_;
v___y_1111_ = v___x_1126_;
v___y_1112_ = v___x_1139_;
goto v___jp_1105_;
}
else
{
lean_object* v___x_1140_; 
v___x_1140_ = ((lean_object*)(l_Lake_tar___closed__6));
v___y_1106_ = v___x_1136_;
v___y_1107_ = v___x_1138_;
v___y_1108_ = v_a_1125_;
v___y_1109_ = v___x_1135_;
v___y_1110_ = v___x_1127_;
v___y_1111_ = v___x_1126_;
v___y_1112_ = v___x_1140_;
goto v___jp_1105_;
}
}
else
{
lean_object* v_a_1141_; lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v_file_1100_);
lean_dec_ref(v_dir_1099_);
v_a_1141_ = lean_ctor_get(v___x_1123_, 0);
v_a_1142_ = lean_ctor_get(v___x_1123_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1123_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_inc(v_a_1141_);
lean_dec(v___x_1123_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1141_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec_ref(v_file_1100_);
lean_dec_ref(v_dir_1099_);
v_a_1152_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1152_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1153_ = lean_io_error_to_string(v_a_1152_);
v___x_1154_ = 3;
v___x_1155_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*1, v___x_1154_);
v___x_1156_ = lean_array_get_size(v_a_1103_);
v___x_1157_ = lean_array_push(v_a_1103_, v___x_1155_);
v___x_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
return v___x_1158_;
}
v___jp_1105_:
{
uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1113_ = 0;
lean_inc_ref(v___y_1112_);
lean_inc(v___y_1106_);
lean_inc_ref(v___y_1110_);
lean_inc_ref(v___y_1111_);
v___x_1114_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1114_, 0, v___y_1111_);
lean_ctor_set(v___x_1114_, 1, v___y_1110_);
lean_ctor_set(v___x_1114_, 2, v___y_1109_);
lean_ctor_set(v___x_1114_, 3, v___y_1106_);
lean_ctor_set(v___x_1114_, 4, v___y_1112_);
lean_ctor_set_uint8(v___x_1114_, sizeof(void*)*5, v___y_1107_);
lean_ctor_set_uint8(v___x_1114_, sizeof(void*)*5 + 1, v___x_1113_);
v___x_1115_ = lean_box(0);
v___x_1116_ = l_Lake_proc(v___x_1114_, v___y_1107_, v___x_1115_, v___y_1108_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object* v_dir_1159_, lean_object* v_file_1160_, lean_object* v_gzip_1161_, lean_object* v_excludePaths_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
uint8_t v_gzip_boxed_1165_; lean_object* v_res_1166_; 
v_gzip_boxed_1165_ = lean_unbox(v_gzip_1161_);
v_res_1166_ = l_Lake_tar(v_dir_1159_, v_file_1160_, v_gzip_boxed_1165_, v_excludePaths_1162_, v_a_1163_);
lean_dec_ref(v_excludePaths_1162_);
return v_res_1166_;
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
