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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
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
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_compileLeanModule___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean exited with code "};
static const lean_object* l_Lake_compileLeanModule___lam__0___closed__0 = (const lean_object*)&l_Lake_compileLeanModule___lam__0___closed__0_value;
static const lean_string_object l_Lake_compileLeanModule___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stderr:\n"};
static const lean_object* l_Lake_compileLeanModule___lam__0___closed__1 = (const lean_object*)&l_Lake_compileLeanModule___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stdout:\n"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1(lean_object* v_s_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0));
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___boxed(lean_object* v_s_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1(v_s_5_);
lean_dec_ref(v_s_5_);
return v_res_6_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(lean_object* v_opts_7_, lean_object* v_opt_8_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3___boxed(lean_object* v_opts_17_, lean_object* v_opt_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(v_opts_17_, v_opt_18_);
lean_dec_ref(v_opt_18_);
lean_dec_ref(v_opts_17_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(lean_object* v_as_21_, size_t v_i_22_, size_t v_stop_23_){
_start:
{
uint8_t v___x_24_; 
v___x_24_ = lean_usize_dec_eq(v_i_22_, v_stop_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; uint8_t v_level_26_; 
v___x_25_ = lean_array_uget_borrowed(v_as_21_, v_i_22_);
v_level_26_ = lean_ctor_get_uint8(v___x_25_, sizeof(void*)*1);
if (v_level_26_ == 3)
{
uint8_t v___x_27_; 
v___x_27_ = 1;
return v___x_27_;
}
else
{
size_t v___x_28_; size_t v___x_29_; 
v___x_28_ = ((size_t)1ULL);
v___x_29_ = lean_usize_add(v_i_22_, v___x_28_);
v_i_22_ = v___x_29_;
goto _start;
}
}
else
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0___boxed(lean_object* v_as_32_, lean_object* v_i_33_, lean_object* v_stop_34_){
_start:
{
size_t v_i_boxed_35_; size_t v_stop_boxed_36_; uint8_t v_res_37_; lean_object* v_r_38_; 
v_i_boxed_35_ = lean_unbox_usize(v_i_33_);
lean_dec(v_i_33_);
v_stop_boxed_36_ = lean_unbox_usize(v_stop_34_);
lean_dec(v_stop_34_);
v_res_37_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(v_as_32_, v_i_boxed_35_, v_stop_boxed_36_);
lean_dec_ref(v_as_32_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint8_t v___y_41_, lean_object* v_ir_x3f_42_, lean_object* v_c_x3f_43_, lean_object* v_setupFile_44_, lean_object* v___x_45_, lean_object* v_leanir_46_, lean_object* v___x_47_, lean_object* v___x_48_, uint8_t v___x_49_, uint8_t v___x_50_, lean_object* v___x_51_, lean_object* v_olean_x3f_52_, uint32_t v_exitCode_53_, lean_object* v___x_54_, lean_object* v_stderr_55_, lean_object* v_____r_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___y_60_; uint32_t v___y_64_; lean_object* v___y_65_; lean_object* v___y_76_; lean_object* v___y_77_; uint32_t v___y_80_; uint8_t v___y_81_; lean_object* v___y_82_; uint8_t v___y_83_; lean_object* v___y_135_; uint8_t v___y_136_; lean_object* v___y_140_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_149_ = lean_string_utf8_byte_size(v_stderr_55_);
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_nat_dec_eq(v___x_149_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_152_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__1));
v___x_153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_153_, 0, v_stderr_55_);
lean_ctor_set(v___x_153_, 1, v___x_150_);
lean_ctor_set(v___x_153_, 2, v___x_149_);
v___x_154_ = l_String_Slice_trimAscii(v___x_153_);
v___x_155_ = l_String_Slice_toString(v___x_154_);
lean_dec_ref(v___x_154_);
v___x_156_ = lean_string_append(v___x_152_, v___x_155_);
lean_dec_ref(v___x_155_);
v___x_157_ = 1;
v___x_158_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_158_, 0, v___x_156_);
lean_ctor_set_uint8(v___x_158_, sizeof(void*)*1, v___x_157_);
v___x_159_ = lean_array_push(v___y_57_, v___x_158_);
v___y_140_ = v___x_159_;
goto v___jp_139_;
}
else
{
lean_dec_ref(v_stderr_55_);
v___y_140_ = v___y_57_;
goto v___jp_139_;
}
v___jp_59_:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_box(0);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___y_60_);
return v___x_62_;
}
v___jp_63_:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_66_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__0));
v___x_67_ = lean_uint32_to_nat(v___y_64_);
v___x_68_ = l_Nat_reprFast(v___x_67_);
v___x_69_ = lean_string_append(v___x_66_, v___x_68_);
lean_dec_ref(v___x_68_);
v___x_70_ = 3;
v___x_71_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set_uint8(v___x_71_, sizeof(void*)*1, v___x_70_);
v___x_72_ = lean_array_get_size(v___y_65_);
v___x_73_ = lean_array_push(v___y_65_, v___x_71_);
v___x_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
return v___x_74_;
}
v___jp_75_:
{
lean_object* v___x_78_; 
v___x_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_78_, 0, v___y_76_);
lean_ctor_set(v___x_78_, 1, v___y_77_);
return v___x_78_;
}
v___jp_79_:
{
if (v___y_83_ == 0)
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 0;
v___x_85_ = lean_uint32_dec_eq(v___y_80_, v___x_84_);
if (v___x_85_ == 0)
{
lean_dec_ref(v___x_48_);
lean_dec(v___x_47_);
lean_dec_ref(v_leanir_46_);
lean_dec_ref(v___x_45_);
lean_dec_ref(v_setupFile_44_);
lean_dec(v_c_x3f_43_);
lean_dec(v_ir_x3f_42_);
v___y_64_ = v___y_80_;
v___y_65_ = v___y_82_;
goto v___jp_63_;
}
else
{
if (v___y_81_ == 0)
{
if (v___y_41_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec_ref(v___x_48_);
lean_dec(v___x_47_);
lean_dec_ref(v_leanir_46_);
lean_dec_ref(v___x_45_);
lean_dec_ref(v_setupFile_44_);
lean_dec(v_c_x3f_43_);
lean_dec(v_ir_x3f_42_);
v___x_86_ = lean_box(0);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___y_82_);
return v___x_87_;
}
else
{
if (lean_obj_tag(v_ir_x3f_42_) == 1)
{
if (lean_obj_tag(v_c_x3f_43_) == 1)
{
lean_object* v_val_88_; lean_object* v_val_89_; lean_object* v___x_90_; 
v_val_88_ = lean_ctor_get(v_ir_x3f_42_, 0);
lean_inc_n(v_val_88_, 2);
lean_dec_ref_known(v_ir_x3f_42_, 1);
v_val_89_ = lean_ctor_get(v_c_x3f_43_, 0);
lean_inc(v_val_89_);
lean_dec_ref_known(v_c_x3f_43_, 1);
v___x_90_ = l_Lake_createParentDirs(v_val_88_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v___x_91_; 
lean_dec_ref_known(v___x_90_, 1);
lean_inc(v_val_89_);
v___x_91_ = l_Lake_createParentDirs(v_val_89_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec_ref_known(v___x_91_, 1);
v___x_92_ = lean_unsigned_to_nat(3u);
v___x_93_ = lean_mk_empty_array_with_capacity(v___x_92_);
v___x_94_ = lean_array_push(v___x_93_, v_setupFile_44_);
v___x_95_ = lean_array_push(v___x_94_, v_val_88_);
v___x_96_ = lean_array_push(v___x_95_, v_val_89_);
v___x_97_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_97_, 0, v___x_45_);
lean_ctor_set(v___x_97_, 1, v_leanir_46_);
lean_ctor_set(v___x_97_, 2, v___x_96_);
lean_ctor_set(v___x_97_, 3, v___x_47_);
lean_ctor_set(v___x_97_, 4, v___x_48_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*5, v___x_49_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*5 + 1, v___x_50_);
v___x_98_ = l_Lake_proc(v___x_97_, v___x_50_, v___x_51_, v___y_82_);
if (lean_obj_tag(v___x_98_) == 0)
{
return v___x_98_;
}
else
{
if (lean_obj_tag(v_olean_x3f_52_) == 1)
{
lean_object* v_a_99_; lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_115_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_a_100_ = lean_ctor_get(v___x_98_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_115_ == 0)
{
v___x_102_ = v___x_98_;
v_isShared_103_ = v_isSharedCheck_115_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_115_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_val_104_; lean_object* v___x_105_; 
v_val_104_ = lean_ctor_get(v_olean_x3f_52_, 0);
v___x_105_ = l_Lake_removeFileIfExists(v_val_104_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_dec_ref_known(v___x_105_, 1);
lean_del_object(v___x_102_);
v___y_76_ = v_a_99_;
v___y_77_ = v_a_100_;
goto v___jp_75_;
}
else
{
lean_object* v_a_106_; lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
lean_dec(v_a_99_);
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v___x_107_ = lean_io_error_to_string(v_a_106_);
v___x_108_ = 3;
v___x_109_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_109_, 0, v___x_107_);
lean_ctor_set_uint8(v___x_109_, sizeof(void*)*1, v___x_108_);
v___x_110_ = lean_array_get_size(v_a_100_);
v___x_111_ = lean_array_push(v_a_100_, v___x_109_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_111_);
lean_ctor_set(v___x_102_, 0, v___x_110_);
v___x_113_ = v___x_102_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
else
{
lean_object* v_a_116_; lean_object* v_a_117_; 
v_a_116_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_116_);
v_a_117_ = lean_ctor_get(v___x_98_, 1);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_98_, 2);
v___y_76_ = v_a_116_;
v___y_77_ = v_a_117_;
goto v___jp_75_;
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec(v_val_89_);
lean_dec(v_val_88_);
lean_dec_ref(v___x_48_);
lean_dec(v___x_47_);
lean_dec_ref(v_leanir_46_);
lean_dec_ref(v___x_45_);
lean_dec_ref(v_setupFile_44_);
v_a_118_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_91_, 1);
v___x_119_ = lean_io_error_to_string(v_a_118_);
v___x_120_ = 3;
v___x_121_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*1, v___x_120_);
v___x_122_ = lean_array_get_size(v___y_82_);
v___x_123_ = lean_array_push(v___y_82_, v___x_121_);
v___x_124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
return v___x_124_;
}
}
else
{
lean_object* v_a_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_val_89_);
lean_dec(v_val_88_);
lean_dec_ref(v___x_48_);
lean_dec(v___x_47_);
lean_dec_ref(v_leanir_46_);
lean_dec_ref(v___x_45_);
lean_dec_ref(v_setupFile_44_);
v_a_125_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_125_);
lean_dec_ref_known(v___x_90_, 1);
v___x_126_ = lean_io_error_to_string(v_a_125_);
v___x_127_ = 3;
v___x_128_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*1, v___x_127_);
v___x_129_ = lean_array_get_size(v___y_82_);
v___x_130_ = lean_array_push(v___y_82_, v___x_128_);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
return v___x_131_;
}
}
else
{
lean_dec_ref_known(v_ir_x3f_42_, 1);
lean_dec_ref(v___x_48_);
lean_dec(v___x_47_);
lean_dec_ref(v_leanir_46_);
lean_dec_ref(v___x_45_);
lean_dec_ref(v_setupFile_44_);
lean_dec(v_c_x3f_43_);
v___y_60_ = v___y_82_;
goto v___jp_59_;
}
}
else
{
lean_dec_ref(v___x_48_);
lean_dec(v___x_47_);
lean_dec_ref(v_leanir_46_);
lean_dec_ref(v___x_45_);
lean_dec_ref(v_setupFile_44_);
lean_dec(v_c_x3f_43_);
lean_dec(v_ir_x3f_42_);
v___y_60_ = v___y_82_;
goto v___jp_59_;
}
}
}
else
{
lean_dec_ref(v___x_48_);
lean_dec(v___x_47_);
lean_dec_ref(v_leanir_46_);
lean_dec_ref(v___x_45_);
lean_dec_ref(v_setupFile_44_);
lean_dec(v_c_x3f_43_);
lean_dec(v_ir_x3f_42_);
v___y_64_ = v___y_80_;
v___y_65_ = v___y_82_;
goto v___jp_63_;
}
}
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec_ref(v___x_48_);
lean_dec(v___x_47_);
lean_dec_ref(v_leanir_46_);
lean_dec_ref(v___x_45_);
lean_dec_ref(v_setupFile_44_);
lean_dec(v_c_x3f_43_);
lean_dec(v_ir_x3f_42_);
v___x_132_ = lean_array_get_size(v___y_82_);
v___x_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___y_82_);
return v___x_133_;
}
}
v___jp_134_:
{
uint32_t v___x_137_; uint8_t v___x_138_; 
v___x_137_ = 1;
v___x_138_ = lean_uint32_dec_eq(v_exitCode_53_, v___x_137_);
if (v___x_138_ == 0)
{
v___y_80_ = v_exitCode_53_;
v___y_81_ = v___y_136_;
v___y_82_ = v___y_135_;
v___y_83_ = v___x_138_;
goto v___jp_79_;
}
else
{
v___y_80_ = v_exitCode_53_;
v___y_81_ = v___y_136_;
v___y_82_ = v___y_135_;
v___y_83_ = v___y_136_;
goto v___jp_79_;
}
}
v___jp_139_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_141_ = lean_array_get_size(v___y_140_);
v___x_142_ = l_Array_extract___redArg(v___y_140_, v___x_54_, v___x_141_);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_array_get_size(v___x_142_);
v___x_145_ = lean_nat_dec_lt(v___x_143_, v___x_144_);
if (v___x_145_ == 0)
{
lean_dec_ref(v___x_142_);
v___y_135_ = v___y_140_;
v___y_136_ = v___x_50_;
goto v___jp_134_;
}
else
{
if (v___x_145_ == 0)
{
lean_dec_ref(v___x_142_);
v___y_135_ = v___y_140_;
v___y_136_ = v___x_50_;
goto v___jp_134_;
}
else
{
size_t v___x_146_; size_t v___x_147_; uint8_t v___x_148_; 
v___x_146_ = ((size_t)0ULL);
v___x_147_ = lean_usize_of_nat(v___x_144_);
v___x_148_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(v___x_142_, v___x_146_, v___x_147_);
lean_dec_ref(v___x_142_);
v___y_135_ = v___y_140_;
v___y_136_ = v___x_148_;
goto v___jp_134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object** _args){
lean_object* v___y_160_ = _args[0];
lean_object* v_ir_x3f_161_ = _args[1];
lean_object* v_c_x3f_162_ = _args[2];
lean_object* v_setupFile_163_ = _args[3];
lean_object* v___x_164_ = _args[4];
lean_object* v_leanir_165_ = _args[5];
lean_object* v___x_166_ = _args[6];
lean_object* v___x_167_ = _args[7];
lean_object* v___x_168_ = _args[8];
lean_object* v___x_169_ = _args[9];
lean_object* v___x_170_ = _args[10];
lean_object* v_olean_x3f_171_ = _args[11];
lean_object* v_exitCode_172_ = _args[12];
lean_object* v___x_173_ = _args[13];
lean_object* v_stderr_174_ = _args[14];
lean_object* v_____r_175_ = _args[15];
lean_object* v___y_176_ = _args[16];
lean_object* v___y_177_ = _args[17];
_start:
{
uint8_t v___y_36639__boxed_178_; uint8_t v___x_36643__boxed_179_; uint8_t v___x_36644__boxed_180_; uint32_t v_exitCode_boxed_181_; lean_object* v_res_182_; 
v___y_36639__boxed_178_ = lean_unbox(v___y_160_);
v___x_36643__boxed_179_ = lean_unbox(v___x_168_);
v___x_36644__boxed_180_ = lean_unbox(v___x_169_);
v_exitCode_boxed_181_ = lean_unbox_uint32(v_exitCode_172_);
lean_dec(v_exitCode_172_);
v_res_182_ = l_Lake_compileLeanModule___lam__0(v___y_36639__boxed_178_, v_ir_x3f_161_, v_c_x3f_162_, v_setupFile_163_, v___x_164_, v_leanir_165_, v___x_166_, v___x_167_, v___x_36643__boxed_179_, v___x_36644__boxed_180_, v___x_170_, v_olean_x3f_171_, v_exitCode_boxed_181_, v___x_173_, v_stderr_174_, v_____r_175_, v___y_176_);
lean_dec(v_olean_x3f_171_);
lean_dec(v___x_170_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(lean_object* v_a_183_, lean_object* v_b_184_, lean_object* v_relLeanFile_185_, lean_object* v_____r_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_a_190_; lean_object* v_toBaseMessage_192_; uint8_t v_isSilent_193_; 
v_toBaseMessage_192_ = lean_ctor_get(v_a_183_, 0);
lean_inc_ref(v_toBaseMessage_192_);
v_isSilent_193_ = lean_ctor_get_uint8(v_toBaseMessage_192_, sizeof(void*)*5 + 2);
if (v_isSilent_193_ == 0)
{
lean_object* v_kind_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_218_; 
v_kind_194_ = lean_ctor_get(v_a_183_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_a_183_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_a_183_, 0);
lean_dec(v_unused_219_);
v___x_196_ = v_a_183_;
v_isShared_197_ = v_isSharedCheck_218_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_kind_194_);
lean_dec(v_a_183_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_218_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v_pos_198_; lean_object* v_endPos_199_; uint8_t v_keepFullRange_200_; uint8_t v_severity_201_; lean_object* v_caption_202_; lean_object* v_data_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_216_; 
v_pos_198_ = lean_ctor_get(v_toBaseMessage_192_, 1);
v_endPos_199_ = lean_ctor_get(v_toBaseMessage_192_, 2);
v_keepFullRange_200_ = lean_ctor_get_uint8(v_toBaseMessage_192_, sizeof(void*)*5);
v_severity_201_ = lean_ctor_get_uint8(v_toBaseMessage_192_, sizeof(void*)*5 + 1);
v_caption_202_ = lean_ctor_get(v_toBaseMessage_192_, 3);
v_data_203_ = lean_ctor_get(v_toBaseMessage_192_, 4);
v_isSharedCheck_216_ = !lean_is_exclusive(v_toBaseMessage_192_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; 
v_unused_217_ = lean_ctor_get(v_toBaseMessage_192_, 0);
lean_dec(v_unused_217_);
v___x_205_ = v_toBaseMessage_192_;
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_data_203_);
lean_inc(v_caption_202_);
lean_inc(v_endPos_199_);
lean_inc(v_pos_198_);
lean_dec(v_toBaseMessage_192_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = l_Lake_mkRelPathString(v_relLeanFile_185_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_207_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_pos_198_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_endPos_199_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_caption_202_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_data_203_);
lean_ctor_set_uint8(v_reuseFailAlloc_215_, sizeof(void*)*5, v_keepFullRange_200_);
lean_ctor_set_uint8(v_reuseFailAlloc_215_, sizeof(void*)*5 + 1, v_severity_201_);
lean_ctor_set_uint8(v_reuseFailAlloc_215_, sizeof(void*)*5 + 2, v_isSilent_193_);
v___x_209_ = v_reuseFailAlloc_215_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_211_; 
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_209_);
v___x_211_ = v___x_196_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_kind_194_);
v___x_211_ = v_reuseFailAlloc_214_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = l_Lake_LogEntry_ofSerialMessage(v___x_211_);
v___x_213_ = lean_array_push(v___y_187_, v___x_212_);
v_a_190_ = v___x_213_;
goto v___jp_189_;
}
}
}
}
}
else
{
lean_dec_ref(v_toBaseMessage_192_);
lean_dec_ref(v_relLeanFile_185_);
lean_dec_ref(v_a_183_);
v_a_190_ = v___y_187_;
goto v___jp_189_;
}
v___jp_189_:
{
lean_object* v___x_191_; 
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v_b_184_);
lean_ctor_set(v___x_191_, 1, v_a_190_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0___boxed(lean_object* v_a_220_, lean_object* v_b_221_, lean_object* v_relLeanFile_222_, lean_object* v_____r_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_220_, v_b_221_, v_relLeanFile_222_, v_____r_223_, v___y_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(lean_object* v_relLeanFile_229_, lean_object* v___x_230_, lean_object* v___x_231_, lean_object* v___x_232_, lean_object* v_a_233_, lean_object* v_b_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___y_238_; lean_object* v___y_239_; uint8_t v___y_240_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v_it_261_; lean_object* v_startInclusive_262_; lean_object* v_endExclusive_263_; 
if (lean_obj_tag(v_a_233_) == 0)
{
lean_object* v_currPos_281_; lean_object* v_searcher_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_308_; 
v_currPos_281_ = lean_ctor_get(v_a_233_, 0);
v_searcher_282_ = lean_ctor_get(v_a_233_, 1);
v_isSharedCheck_308_ = !lean_is_exclusive(v_a_233_);
if (v_isSharedCheck_308_ == 0)
{
v___x_284_ = v_a_233_;
v_isShared_285_ = v_isSharedCheck_308_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_searcher_282_);
lean_inc(v_currPos_281_);
lean_dec(v_a_233_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_308_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_startInclusive_286_; lean_object* v_endExclusive_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_startInclusive_286_ = lean_ctor_get(v___x_231_, 1);
v_endExclusive_287_ = lean_ctor_get(v___x_231_, 2);
v___x_288_ = lean_nat_sub(v_endExclusive_287_, v_startInclusive_286_);
v___x_289_ = lean_nat_dec_eq(v_searcher_282_, v___x_288_);
lean_dec(v___x_288_);
if (v___x_289_ == 0)
{
uint32_t v___x_290_; uint32_t v___x_291_; uint8_t v___x_292_; 
v___x_290_ = 10;
v___x_291_ = lean_string_utf8_get_fast(v___x_230_, v_searcher_282_);
v___x_292_ = lean_uint32_dec_eq(v___x_291_, v___x_290_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_string_utf8_next_fast(v___x_230_, v_searcher_282_);
lean_dec(v_searcher_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v___x_293_);
v___x_295_ = v___x_284_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_currPos_281_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_297_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
v_a_233_ = v___x_295_;
goto _start;
}
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_slice_301_; lean_object* v_nextIt_303_; 
v___x_298_ = lean_string_utf8_next_fast(v___x_230_, v_searcher_282_);
v___x_299_ = lean_nat_sub(v___x_298_, v_searcher_282_);
v___x_300_ = lean_nat_add(v_searcher_282_, v___x_299_);
lean_dec(v___x_299_);
v_slice_301_ = l_String_Slice_subslice_x21(v___x_231_, v_currPos_281_, v_searcher_282_);
lean_inc(v___x_300_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v___x_300_);
lean_ctor_set(v___x_284_, 0, v___x_300_);
v_nextIt_303_ = v___x_284_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v___x_300_);
v_nextIt_303_ = v_reuseFailAlloc_306_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v_startInclusive_304_; lean_object* v_endExclusive_305_; 
v_startInclusive_304_ = lean_ctor_get(v_slice_301_, 0);
lean_inc(v_startInclusive_304_);
v_endExclusive_305_ = lean_ctor_get(v_slice_301_, 1);
lean_inc(v_endExclusive_305_);
lean_dec_ref(v_slice_301_);
v_it_261_ = v_nextIt_303_;
v_startInclusive_262_ = v_startInclusive_304_;
v_endExclusive_263_ = v_endExclusive_305_;
goto v___jp_260_;
}
}
}
else
{
lean_object* v___x_307_; 
lean_del_object(v___x_284_);
lean_dec(v_searcher_282_);
v___x_307_ = lean_box(1);
lean_inc(v___x_232_);
v_it_261_ = v___x_307_;
v_startInclusive_262_ = v_currPos_281_;
v_endExclusive_263_ = v___x_232_;
goto v___jp_260_;
}
}
}
else
{
lean_object* v___x_309_; 
lean_dec(v___x_232_);
lean_dec_ref(v_relLeanFile_229_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_b_234_);
lean_ctor_set(v___x_309_, 1, v___y_235_);
return v___x_309_;
}
v___jp_237_:
{
if (v___y_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_string_append(v_b_234_, v___y_239_);
lean_dec_ref(v___y_239_);
v___x_242_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__0));
v___x_243_ = lean_string_append(v___x_241_, v___x_242_);
v_a_233_ = v___y_238_;
v_b_234_ = v___x_243_;
goto _start;
}
else
{
lean_dec_ref(v___y_239_);
v_a_233_ = v___y_238_;
goto _start;
}
}
v___jp_246_:
{
lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_249_ = lean_string_utf8_byte_size(v_b_234_);
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = lean_nat_dec_eq(v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
v___y_238_ = v___y_248_;
v___y_239_ = v___y_247_;
v___y_240_ = v___x_251_;
goto v___jp_237_;
}
else
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = lean_string_utf8_byte_size(v___y_247_);
v___x_253_ = lean_nat_dec_eq(v___x_252_, v___x_250_);
v___y_238_ = v___y_248_;
v___y_239_ = v___y_247_;
v___y_240_ = v___x_253_;
goto v___jp_237_;
}
}
v___jp_254_:
{
if (lean_obj_tag(v___y_256_) == 0)
{
lean_object* v_a_257_; lean_object* v_a_258_; 
v_a_257_ = lean_ctor_get(v___y_256_, 0);
lean_inc(v_a_257_);
v_a_258_ = lean_ctor_get(v___y_256_, 1);
lean_inc(v_a_258_);
lean_dec_ref_known(v___y_256_, 2);
v_a_233_ = v___y_255_;
v_b_234_ = v_a_257_;
v___y_235_ = v_a_258_;
goto _start;
}
else
{
lean_dec(v___y_255_);
lean_dec(v___x_232_);
lean_dec_ref(v_relLeanFile_229_);
return v___y_256_;
}
}
v___jp_260_:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_string_utf8_extract(v___x_230_, v_startInclusive_262_, v_endExclusive_263_);
lean_dec(v_endExclusive_263_);
lean_dec(v_startInclusive_262_);
lean_inc_ref(v___x_264_);
v___x_265_ = l_Lean_Json_parse(v___x_264_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_dec_ref_known(v___x_265_, 1);
v___y_247_ = v___x_264_;
v___y_248_ = v_it_261_;
goto v___jp_246_;
}
else
{
lean_object* v_a_266_; lean_object* v___x_267_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_265_, 1);
v___x_267_ = l_Lean_instFromJsonSerialMessage_fromJson(v_a_266_);
if (lean_obj_tag(v___x_267_) == 1)
{
lean_object* v_a_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
lean_dec_ref(v___x_264_);
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v___x_267_, 1);
v___x_269_ = lean_string_utf8_byte_size(v_b_234_);
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_nat_dec_eq(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_272_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__1));
v___x_273_ = lean_string_append(v___x_272_, v_b_234_);
v___x_274_ = 1;
v___x_275_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set_uint8(v___x_275_, sizeof(void*)*1, v___x_274_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_array_push(v___y_235_, v___x_275_);
lean_inc_ref(v_relLeanFile_229_);
v___x_278_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_268_, v_b_234_, v_relLeanFile_229_, v___x_276_, v___x_277_);
v___y_255_ = v_it_261_;
v___y_256_ = v___x_278_;
goto v___jp_254_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_box(0);
lean_inc_ref(v_relLeanFile_229_);
v___x_280_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_268_, v_b_234_, v_relLeanFile_229_, v___x_279_, v___y_235_);
v___y_255_ = v_it_261_;
v___y_256_ = v___x_280_;
goto v___jp_254_;
}
}
else
{
lean_dec_ref(v___x_267_);
v___y_247_ = v___x_264_;
v___y_248_ = v_it_261_;
goto v___jp_246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___boxed(lean_object* v_relLeanFile_310_, lean_object* v___x_311_, lean_object* v___x_312_, lean_object* v___x_313_, lean_object* v_a_314_, lean_object* v_b_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(v_relLeanFile_310_, v___x_311_, v___x_312_, v___x_313_, v_a_314_, v_b_315_, v___y_316_);
lean_dec_ref(v___x_312_);
lean_dec_ref(v___x_311_);
return v_res_318_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__1(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_320_ = ((lean_object*)(l_Lake_compileLeanModule___closed__0));
v___x_321_ = lean_unsigned_to_nat(2u);
v___x_322_ = lean_mk_empty_array_with_capacity(v___x_321_);
v___x_323_ = lean_array_push(v___x_322_, v___x_320_);
return v___x_323_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__9(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_332_ = ((lean_object*)(l_Lake_compileLeanModule___closed__8));
v___x_333_ = lean_unsigned_to_nat(2u);
v___x_334_ = lean_mk_empty_array_with_capacity(v___x_333_);
v___x_335_ = lean_array_push(v___x_334_, v___x_332_);
return v___x_335_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__11(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_337_ = ((lean_object*)(l_Lake_compileLeanModule___closed__10));
v___x_338_ = lean_unsigned_to_nat(2u);
v___x_339_ = lean_mk_empty_array_with_capacity(v___x_338_);
v___x_340_ = lean_array_push(v___x_339_, v___x_337_);
return v___x_340_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__13(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_342_ = ((lean_object*)(l_Lake_compileLeanModule___closed__12));
v___x_343_ = lean_unsigned_to_nat(2u);
v___x_344_ = lean_mk_empty_array_with_capacity(v___x_343_);
v___x_345_ = lean_array_push(v___x_344_, v___x_342_);
return v___x_345_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__15(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_348_ = lean_unsigned_to_nat(2u);
v___x_349_ = lean_mk_empty_array_with_capacity(v___x_348_);
v___x_350_ = lean_array_push(v___x_349_, v___x_347_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object* v_leanFile_351_, lean_object* v_relLeanFile_352_, lean_object* v_setup_353_, lean_object* v_setupFile_354_, lean_object* v_arts_355_, lean_object* v_leanArgs_356_, lean_object* v_leanPath_357_, lean_object* v_lean_358_, lean_object* v_leanir_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___y_363_; lean_object* v_a_364_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v_olean_x3f_370_; lean_object* v_ilean_x3f_371_; lean_object* v_ir_x3f_372_; lean_object* v_c_x3f_373_; lean_object* v_bc_x3f_374_; uint8_t v___y_376_; lean_object* v_args_377_; lean_object* v___y_378_; lean_object* v___y_467_; uint8_t v___y_468_; lean_object* v_args_469_; lean_object* v___y_483_; lean_object* v___y_484_; uint8_t v___y_485_; lean_object* v_args_499_; lean_object* v___y_500_; lean_object* v_args_507_; lean_object* v___y_508_; lean_object* v_args_521_; 
v_olean_x3f_370_ = lean_ctor_get(v_arts_355_, 1);
lean_inc(v_olean_x3f_370_);
v_ilean_x3f_371_ = lean_ctor_get(v_arts_355_, 4);
lean_inc(v_ilean_x3f_371_);
v_ir_x3f_372_ = lean_ctor_get(v_arts_355_, 6);
lean_inc(v_ir_x3f_372_);
v_c_x3f_373_ = lean_ctor_get(v_arts_355_, 7);
lean_inc(v_c_x3f_373_);
v_bc_x3f_374_ = lean_ctor_get(v_arts_355_, 8);
lean_inc(v_bc_x3f_374_);
lean_dec_ref(v_arts_355_);
v_args_521_ = lean_array_push(v_leanArgs_356_, v_leanFile_351_);
if (lean_obj_tag(v_olean_x3f_370_) == 1)
{
lean_object* v_val_522_; lean_object* v___x_523_; 
v_val_522_ = lean_ctor_get(v_olean_x3f_370_, 0);
lean_inc(v_val_522_);
v___x_523_ = l_Lake_createParentDirs(v_val_522_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
lean_dec_ref_known(v___x_523_, 1);
v___x_524_ = lean_obj_once(&l_Lake_compileLeanModule___closed__15, &l_Lake_compileLeanModule___closed__15_once, _init_l_Lake_compileLeanModule___closed__15);
lean_inc(v_val_522_);
v___x_525_ = lean_array_push(v___x_524_, v_val_522_);
v___x_526_ = l_Array_append___redArg(v_args_521_, v___x_525_);
lean_dec_ref(v___x_525_);
v_args_507_ = v___x_526_;
v___y_508_ = v_a_360_;
goto v___jp_506_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec_ref_known(v_olean_x3f_370_, 1);
lean_dec_ref(v_args_521_);
lean_dec(v_bc_x3f_374_);
lean_dec(v_c_x3f_373_);
lean_dec(v_ir_x3f_372_);
lean_dec(v_ilean_x3f_371_);
lean_dec_ref(v_leanir_359_);
lean_dec_ref(v_lean_358_);
lean_dec(v_leanPath_357_);
lean_dec_ref(v_setupFile_354_);
lean_dec_ref(v_setup_353_);
lean_dec_ref(v_relLeanFile_352_);
v_a_527_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_523_, 1);
v___x_528_ = lean_io_error_to_string(v_a_527_);
v___x_529_ = 3;
v___x_530_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*1, v___x_529_);
v___x_531_ = lean_array_get_size(v_a_360_);
v___x_532_ = lean_array_push(v_a_360_, v___x_530_);
v___x_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
return v___x_533_;
}
}
else
{
v_args_507_ = v_args_521_;
v___y_508_ = v_a_360_;
goto v___jp_506_;
}
v___jp_362_:
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_365_, 0, v___y_363_);
lean_ctor_set(v___x_365_, 1, v_a_364_);
return v___x_365_;
}
v___jp_366_:
{
if (lean_obj_tag(v___y_368_) == 0)
{
lean_dec(v___y_367_);
return v___y_368_;
}
else
{
lean_object* v_a_369_; 
v_a_369_ = lean_ctor_get(v___y_368_, 1);
lean_inc(v_a_369_);
lean_dec_ref_known(v___y_368_, 2);
v___y_363_ = v___y_367_;
v_a_364_ = v_a_369_;
goto v___jp_362_;
}
}
v___jp_375_:
{
lean_object* v___x_379_; 
lean_inc_ref(v_setupFile_354_);
v___x_379_ = l_Lake_createParentDirs(v_setupFile_354_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
lean_dec_ref_known(v___x_379_, 1);
v___x_380_ = l_Lean_instToJsonModuleSetup_toJson(v_setup_353_);
v___x_381_ = lean_unsigned_to_nat(80u);
v___x_382_ = l_Lean_Json_pretty(v___x_380_, v___x_381_);
v___x_383_ = l_IO_FS_writeFile(v_setupFile_354_, v___x_382_);
lean_dec_ref(v___x_382_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_450_; 
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; 
v_unused_451_ = lean_ctor_get(v___x_383_, 0);
lean_dec(v_unused_451_);
v___x_385_ = v___x_383_;
v_isShared_386_ = v_isSharedCheck_450_;
goto v_resetjp_384_;
}
else
{
lean_dec(v___x_383_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_450_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_387_ = lean_obj_once(&l_Lake_compileLeanModule___closed__1, &l_Lake_compileLeanModule___closed__1_once, _init_l_Lake_compileLeanModule___closed__1);
lean_inc_ref(v_setupFile_354_);
v___x_388_ = lean_array_push(v___x_387_, v_setupFile_354_);
v___x_389_ = l_Array_append___redArg(v_args_377_, v___x_388_);
lean_dec_ref(v___x_388_);
v___x_390_ = ((lean_object*)(l_Lake_compileLeanModule___closed__2));
v___x_391_ = lean_array_push(v___x_389_, v___x_390_);
v___x_392_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_393_ = lean_box(0);
v___x_394_ = ((lean_object*)(l_Lake_compileLeanModule___closed__4));
v___x_395_ = l_System_SearchPath_toString(v_leanPath_357_);
if (v_isShared_386_ == 0)
{
lean_ctor_set_tag(v___x_385_, 1);
lean_ctor_set(v___x_385_, 0, v___x_395_);
v___x_397_ = v___x_385_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_449_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_394_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = lean_mk_empty_array_with_capacity(v___x_399_);
v___x_401_ = lean_array_push(v___x_400_, v___x_398_);
v___x_402_ = 1;
v___x_403_ = 0;
lean_inc_ref(v___x_401_);
lean_inc_ref(v_lean_358_);
v___x_404_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_404_, 0, v___x_392_);
lean_ctor_set(v___x_404_, 1, v_lean_358_);
lean_ctor_set(v___x_404_, 2, v___x_391_);
lean_ctor_set(v___x_404_, 3, v___x_393_);
lean_ctor_set(v___x_404_, 4, v___x_401_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*5, v___x_402_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*5 + 1, v___x_403_);
v___x_405_ = lean_array_get_size(v___y_378_);
lean_inc_ref(v___x_404_);
v___x_406_ = l_Lake_mkCmdLog(v___x_404_);
v___x_407_ = 0;
v___x_408_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_408_, 0, v___x_406_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*1, v___x_407_);
v___x_409_ = lean_array_push(v___y_378_, v___x_408_);
v___x_410_ = l_IO_Process_output(v___x_404_, v___x_393_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; uint32_t v_exitCode_412_; lean_object* v_stdout_413_; lean_object* v_stderr_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
lean_dec_ref(v_lean_358_);
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v_exitCode_412_ = lean_ctor_get_uint32(v_a_411_, sizeof(void*)*2);
v_stdout_413_ = lean_ctor_get(v_a_411_, 0);
lean_inc_ref(v_stdout_413_);
v_stderr_414_ = lean_ctor_get(v_a_411_, 1);
lean_inc_ref(v_stderr_414_);
lean_dec(v_a_411_);
v___x_415_ = lean_array_get_size(v___x_409_);
v___x_416_ = lean_string_utf8_byte_size(v_stdout_413_);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_nat_dec_eq(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
lean_inc_ref(v_stdout_413_);
v___x_419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_419_, 0, v_stdout_413_);
lean_ctor_set(v___x_419_, 1, v___x_417_);
lean_ctor_set(v___x_419_, 2, v___x_416_);
v___x_420_ = ((lean_object*)(l_Lake_compileLeanModule___closed__5));
v___x_421_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1(v___x_419_);
v___x_422_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(v_relLeanFile_352_, v_stdout_413_, v___x_419_, v___x_416_, v___x_421_, v___x_420_, v___x_409_);
lean_dec_ref_known(v___x_419_, 3);
lean_dec_ref(v_stdout_413_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v_a_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
v_a_424_ = lean_ctor_get(v___x_422_, 1);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_422_, 2);
v___x_425_ = lean_string_utf8_byte_size(v_a_423_);
v___x_426_ = lean_nat_dec_eq(v___x_425_, v___x_417_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_427_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__1));
v___x_428_ = lean_string_append(v___x_427_, v_a_423_);
lean_dec(v_a_423_);
v___x_429_ = 1;
v___x_430_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*1, v___x_429_);
v___x_431_ = lean_box(0);
v___x_432_ = lean_array_push(v_a_424_, v___x_430_);
v___x_433_ = l_Lake_compileLeanModule___lam__0(v___y_376_, v_ir_x3f_372_, v_c_x3f_373_, v_setupFile_354_, v___x_392_, v_leanir_359_, v___x_393_, v___x_401_, v___x_402_, v___x_403_, v___x_393_, v_olean_x3f_370_, v_exitCode_412_, v___x_415_, v_stderr_414_, v___x_431_, v___x_432_);
lean_dec(v_olean_x3f_370_);
v___y_367_ = v___x_405_;
v___y_368_ = v___x_433_;
goto v___jp_366_;
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v_a_423_);
v___x_434_ = lean_box(0);
v___x_435_ = l_Lake_compileLeanModule___lam__0(v___y_376_, v_ir_x3f_372_, v_c_x3f_373_, v_setupFile_354_, v___x_392_, v_leanir_359_, v___x_393_, v___x_401_, v___x_402_, v___x_403_, v___x_393_, v_olean_x3f_370_, v_exitCode_412_, v___x_415_, v_stderr_414_, v___x_434_, v_a_424_);
lean_dec(v_olean_x3f_370_);
v___y_367_ = v___x_405_;
v___y_368_ = v___x_435_;
goto v___jp_366_;
}
}
else
{
lean_object* v_a_436_; 
lean_dec_ref(v_stderr_414_);
lean_dec_ref(v___x_401_);
lean_dec(v_c_x3f_373_);
lean_dec(v_ir_x3f_372_);
lean_dec(v_olean_x3f_370_);
lean_dec_ref(v_leanir_359_);
lean_dec_ref(v_setupFile_354_);
v_a_436_ = lean_ctor_get(v___x_422_, 1);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_422_, 2);
v___y_363_ = v___x_405_;
v_a_364_ = v_a_436_;
goto v___jp_362_;
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec_ref(v_stdout_413_);
lean_dec_ref(v_relLeanFile_352_);
v___x_437_ = lean_box(0);
v___x_438_ = l_Lake_compileLeanModule___lam__0(v___y_376_, v_ir_x3f_372_, v_c_x3f_373_, v_setupFile_354_, v___x_392_, v_leanir_359_, v___x_393_, v___x_401_, v___x_402_, v___x_403_, v___x_393_, v_olean_x3f_370_, v_exitCode_412_, v___x_415_, v_stderr_414_, v___x_437_, v___x_409_);
lean_dec(v_olean_x3f_370_);
v___y_367_ = v___x_405_;
v___y_368_ = v___x_438_;
goto v___jp_366_;
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec_ref(v___x_401_);
lean_dec(v_c_x3f_373_);
lean_dec(v_ir_x3f_372_);
lean_dec(v_olean_x3f_370_);
lean_dec_ref(v_leanir_359_);
lean_dec_ref(v_setupFile_354_);
lean_dec_ref(v_relLeanFile_352_);
v_a_439_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_410_, 1);
v___x_440_ = ((lean_object*)(l_Lake_compileLeanModule___closed__6));
v___x_441_ = lean_string_append(v___x_440_, v_lean_358_);
lean_dec_ref(v_lean_358_);
v___x_442_ = ((lean_object*)(l_Lake_compileLeanModule___closed__7));
v___x_443_ = lean_string_append(v___x_441_, v___x_442_);
v___x_444_ = lean_io_error_to_string(v_a_439_);
v___x_445_ = lean_string_append(v___x_443_, v___x_444_);
lean_dec_ref(v___x_444_);
v___x_446_ = 3;
v___x_447_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*1, v___x_446_);
v___x_448_ = lean_array_push(v___x_409_, v___x_447_);
v___y_363_ = v___x_405_;
v_a_364_ = v___x_448_;
goto v___jp_362_;
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec_ref(v_args_377_);
lean_dec(v_c_x3f_373_);
lean_dec(v_ir_x3f_372_);
lean_dec(v_olean_x3f_370_);
lean_dec_ref(v_leanir_359_);
lean_dec_ref(v_lean_358_);
lean_dec(v_leanPath_357_);
lean_dec_ref(v_setupFile_354_);
lean_dec_ref(v_relLeanFile_352_);
v_a_452_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_383_, 1);
v___x_453_ = lean_io_error_to_string(v_a_452_);
v___x_454_ = 3;
v___x_455_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*1, v___x_454_);
v___x_456_ = lean_array_get_size(v___y_378_);
v___x_457_ = lean_array_push(v___y_378_, v___x_455_);
v___x_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
return v___x_458_;
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec_ref(v_args_377_);
lean_dec(v_c_x3f_373_);
lean_dec(v_ir_x3f_372_);
lean_dec(v_olean_x3f_370_);
lean_dec_ref(v_leanir_359_);
lean_dec_ref(v_lean_358_);
lean_dec(v_leanPath_357_);
lean_dec_ref(v_setupFile_354_);
lean_dec_ref(v_setup_353_);
lean_dec_ref(v_relLeanFile_352_);
v_a_459_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_379_, 1);
v___x_460_ = lean_io_error_to_string(v_a_459_);
v___x_461_ = 3;
v___x_462_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*1, v___x_461_);
v___x_463_ = lean_array_get_size(v___y_378_);
v___x_464_ = lean_array_push(v___y_378_, v___x_462_);
v___x_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
return v___x_465_;
}
}
v___jp_466_:
{
if (lean_obj_tag(v_bc_x3f_374_) == 1)
{
lean_object* v_val_470_; lean_object* v___x_471_; 
v_val_470_ = lean_ctor_get(v_bc_x3f_374_, 0);
lean_inc_n(v_val_470_, 2);
lean_dec_ref_known(v_bc_x3f_374_, 1);
v___x_471_ = l_Lake_createParentDirs(v_val_470_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec_ref_known(v___x_471_, 1);
v___x_472_ = lean_obj_once(&l_Lake_compileLeanModule___closed__9, &l_Lake_compileLeanModule___closed__9_once, _init_l_Lake_compileLeanModule___closed__9);
v___x_473_ = lean_array_push(v___x_472_, v_val_470_);
v___x_474_ = l_Array_append___redArg(v_args_469_, v___x_473_);
lean_dec_ref(v___x_473_);
v___y_376_ = v___y_468_;
v_args_377_ = v___x_474_;
v___y_378_ = v___y_467_;
goto v___jp_375_;
}
else
{
lean_object* v_a_475_; lean_object* v___x_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_val_470_);
lean_dec_ref(v_args_469_);
lean_dec(v_c_x3f_373_);
lean_dec(v_ir_x3f_372_);
lean_dec(v_olean_x3f_370_);
lean_dec_ref(v_leanir_359_);
lean_dec_ref(v_lean_358_);
lean_dec(v_leanPath_357_);
lean_dec_ref(v_setupFile_354_);
lean_dec_ref(v_setup_353_);
lean_dec_ref(v_relLeanFile_352_);
v_a_475_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_471_, 1);
v___x_476_ = lean_io_error_to_string(v_a_475_);
v___x_477_ = 3;
v___x_478_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_478_, 0, v___x_476_);
lean_ctor_set_uint8(v___x_478_, sizeof(void*)*1, v___x_477_);
v___x_479_ = lean_array_get_size(v___y_467_);
v___x_480_ = lean_array_push(v___y_467_, v___x_478_);
v___x_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
return v___x_481_;
}
}
else
{
lean_dec(v_bc_x3f_374_);
v___y_376_ = v___y_468_;
v_args_377_ = v_args_469_;
v___y_378_ = v___y_467_;
goto v___jp_375_;
}
}
v___jp_482_:
{
if (lean_obj_tag(v_c_x3f_373_) == 1)
{
lean_object* v_val_486_; lean_object* v___x_487_; 
v_val_486_ = lean_ctor_get(v_c_x3f_373_, 0);
lean_inc(v_val_486_);
v___x_487_ = l_Lake_createParentDirs(v_val_486_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec_ref_known(v___x_487_, 1);
v___x_488_ = lean_obj_once(&l_Lake_compileLeanModule___closed__11, &l_Lake_compileLeanModule___closed__11_once, _init_l_Lake_compileLeanModule___closed__11);
lean_inc(v_val_486_);
v___x_489_ = lean_array_push(v___x_488_, v_val_486_);
v___x_490_ = l_Array_append___redArg(v___y_483_, v___x_489_);
lean_dec_ref(v___x_489_);
v___y_467_ = v___y_484_;
v___y_468_ = v___y_485_;
v_args_469_ = v___x_490_;
goto v___jp_466_;
}
else
{
lean_object* v_a_491_; lean_object* v___x_492_; uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec_ref_known(v_c_x3f_373_, 1);
lean_dec_ref(v___y_483_);
lean_dec(v_bc_x3f_374_);
lean_dec(v_ir_x3f_372_);
lean_dec(v_olean_x3f_370_);
lean_dec_ref(v_leanir_359_);
lean_dec_ref(v_lean_358_);
lean_dec(v_leanPath_357_);
lean_dec_ref(v_setupFile_354_);
lean_dec_ref(v_setup_353_);
lean_dec_ref(v_relLeanFile_352_);
v_a_491_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_487_, 1);
v___x_492_ = lean_io_error_to_string(v_a_491_);
v___x_493_ = 3;
v___x_494_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set_uint8(v___x_494_, sizeof(void*)*1, v___x_493_);
v___x_495_ = lean_array_get_size(v___y_484_);
v___x_496_ = lean_array_push(v___y_484_, v___x_494_);
v___x_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_495_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
return v___x_497_;
}
}
else
{
v___y_467_ = v___y_484_;
v___y_468_ = v___y_485_;
v_args_469_ = v___y_483_;
goto v___jp_466_;
}
}
v___jp_498_:
{
uint8_t v_isModule_501_; 
v_isModule_501_ = lean_ctor_get_uint8(v_setup_353_, sizeof(void*)*7);
if (v_isModule_501_ == 0)
{
v___y_483_ = v_args_499_;
v___y_484_ = v___y_500_;
v___y_485_ = v_isModule_501_;
goto v___jp_482_;
}
else
{
lean_object* v_options_502_; lean_object* v_opts_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v_options_502_ = lean_ctor_get(v_setup_353_, 6);
lean_inc(v_options_502_);
v_opts_503_ = l_Lean_LeanOptions_toOptions(v_options_502_);
v___x_504_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_505_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(v_opts_503_, v___x_504_);
lean_dec_ref(v_opts_503_);
if (v___x_505_ == 0)
{
v___y_483_ = v_args_499_;
v___y_484_ = v___y_500_;
v___y_485_ = v___x_505_;
goto v___jp_482_;
}
else
{
v___y_467_ = v___y_500_;
v___y_468_ = v___x_505_;
v_args_469_ = v_args_499_;
goto v___jp_466_;
}
}
}
v___jp_506_:
{
if (lean_obj_tag(v_ilean_x3f_371_) == 1)
{
lean_object* v_val_509_; lean_object* v___x_510_; 
v_val_509_ = lean_ctor_get(v_ilean_x3f_371_, 0);
lean_inc_n(v_val_509_, 2);
lean_dec_ref_known(v_ilean_x3f_371_, 1);
v___x_510_ = l_Lake_createParentDirs(v_val_509_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec_ref_known(v___x_510_, 1);
v___x_511_ = lean_obj_once(&l_Lake_compileLeanModule___closed__13, &l_Lake_compileLeanModule___closed__13_once, _init_l_Lake_compileLeanModule___closed__13);
v___x_512_ = lean_array_push(v___x_511_, v_val_509_);
v___x_513_ = l_Array_append___redArg(v_args_507_, v___x_512_);
lean_dec_ref(v___x_512_);
v_args_499_ = v___x_513_;
v___y_500_ = v___y_508_;
goto v___jp_498_;
}
else
{
lean_object* v_a_514_; lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec(v_val_509_);
lean_dec_ref(v_args_507_);
lean_dec(v_bc_x3f_374_);
lean_dec(v_c_x3f_373_);
lean_dec(v_ir_x3f_372_);
lean_dec(v_olean_x3f_370_);
lean_dec_ref(v_leanir_359_);
lean_dec_ref(v_lean_358_);
lean_dec(v_leanPath_357_);
lean_dec_ref(v_setupFile_354_);
lean_dec_ref(v_setup_353_);
lean_dec_ref(v_relLeanFile_352_);
v_a_514_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_510_, 1);
v___x_515_ = lean_io_error_to_string(v_a_514_);
v___x_516_ = 3;
v___x_517_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*1, v___x_516_);
v___x_518_ = lean_array_get_size(v___y_508_);
v___x_519_ = lean_array_push(v___y_508_, v___x_517_);
v___x_520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
return v___x_520_;
}
}
else
{
lean_dec(v_ilean_x3f_371_);
v_args_499_ = v_args_507_;
v___y_500_ = v___y_508_;
goto v___jp_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object* v_leanFile_534_, lean_object* v_relLeanFile_535_, lean_object* v_setup_536_, lean_object* v_setupFile_537_, lean_object* v_arts_538_, lean_object* v_leanArgs_539_, lean_object* v_leanPath_540_, lean_object* v_lean_541_, lean_object* v_leanir_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lake_compileLeanModule(v_leanFile_534_, v_relLeanFile_535_, v_setup_536_, v_setupFile_537_, v_arts_538_, v_leanArgs_539_, v_leanPath_540_, v_lean_541_, v_leanir_542_, v_a_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2(lean_object* v_relLeanFile_546_, lean_object* v___x_547_, lean_object* v___x_548_, lean_object* v___x_549_, lean_object* v_inst_550_, lean_object* v_R_551_, lean_object* v_a_552_, lean_object* v_b_553_, lean_object* v_c_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(v_relLeanFile_546_, v___x_547_, v___x_548_, v___x_549_, v_a_552_, v_b_553_, v___y_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___boxed(lean_object* v_relLeanFile_558_, lean_object* v___x_559_, lean_object* v___x_560_, lean_object* v___x_561_, lean_object* v_inst_562_, lean_object* v_R_563_, lean_object* v_a_564_, lean_object* v_b_565_, lean_object* v_c_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2(v_relLeanFile_558_, v___x_559_, v___x_560_, v___x_561_, v_inst_562_, v_R_563_, v_a_564_, v_b_565_, v_c_566_, v___y_567_);
lean_dec_ref(v___x_560_);
lean_dec_ref(v___x_559_);
return v_res_569_;
}
}
static lean_object* _init_l_Lake_compileO___closed__0(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_570_ = ((lean_object*)(l_Lake_compileLeanModule___closed__10));
v___x_571_ = lean_unsigned_to_nat(4u);
v___x_572_ = lean_mk_empty_array_with_capacity(v___x_571_);
v___x_573_ = lean_array_push(v___x_572_, v___x_570_);
return v___x_573_;
}
}
static lean_object* _init_l_Lake_compileO___closed__1(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_575_ = lean_obj_once(&l_Lake_compileO___closed__0, &l_Lake_compileO___closed__0_once, _init_l_Lake_compileO___closed__0);
v___x_576_ = lean_array_push(v___x_575_, v___x_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object* v_oFile_579_, lean_object* v_srcFile_580_, lean_object* v_moreArgs_581_, lean_object* v_compiler_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; 
lean_inc_ref(v_oFile_579_);
v___x_585_ = l_Lake_createParentDirs(v_oFile_579_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; uint8_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec_ref_known(v___x_585_, 1);
v___x_586_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_587_ = lean_obj_once(&l_Lake_compileO___closed__1, &l_Lake_compileO___closed__1_once, _init_l_Lake_compileO___closed__1);
v___x_588_ = lean_array_push(v___x_587_, v_oFile_579_);
v___x_589_ = lean_array_push(v___x_588_, v_srcFile_580_);
v___x_590_ = l_Array_append___redArg(v___x_589_, v_moreArgs_581_);
v___x_591_ = lean_box(0);
v___x_592_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_593_ = 1;
v___x_594_ = 0;
v___x_595_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_595_, 0, v___x_586_);
lean_ctor_set(v___x_595_, 1, v_compiler_582_);
lean_ctor_set(v___x_595_, 2, v___x_590_);
lean_ctor_set(v___x_595_, 3, v___x_591_);
lean_ctor_set(v___x_595_, 4, v___x_592_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*5, v___x_593_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*5 + 1, v___x_594_);
v___x_596_ = l_Lake_proc(v___x_595_, v___x_594_, v___x_591_, v_a_583_);
return v___x_596_;
}
else
{
lean_object* v_a_597_; lean_object* v___x_598_; uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec_ref(v_compiler_582_);
lean_dec_ref(v_srcFile_580_);
lean_dec_ref(v_oFile_579_);
v_a_597_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_585_, 1);
v___x_598_ = lean_io_error_to_string(v_a_597_);
v___x_599_ = 3;
v___x_600_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set_uint8(v___x_600_, sizeof(void*)*1, v___x_599_);
v___x_601_ = lean_array_get_size(v_a_583_);
v___x_602_ = lean_array_push(v_a_583_, v___x_600_);
v___x_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object* v_oFile_604_, lean_object* v_srcFile_605_, lean_object* v_moreArgs_606_, lean_object* v_compiler_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lake_compileO(v_oFile_604_, v_srcFile_605_, v_moreArgs_606_, v_compiler_607_, v_a_608_);
lean_dec_ref(v_moreArgs_606_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(lean_object* v___x_611_, lean_object* v___y_612_, lean_object* v_a_613_, lean_object* v_b_614_){
_start:
{
lean_object* v_startInclusive_615_; lean_object* v_endExclusive_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_startInclusive_615_ = lean_ctor_get(v___x_611_, 1);
v_endExclusive_616_ = lean_ctor_get(v___x_611_, 2);
v___x_617_ = lean_nat_sub(v_endExclusive_616_, v_startInclusive_615_);
v___x_618_ = lean_nat_dec_eq(v_a_613_, v___x_617_);
lean_dec(v___x_617_);
if (v___x_618_ == 0)
{
uint32_t v___x_619_; lean_object* v___x_620_; uint32_t v___x_621_; uint8_t v___y_623_; uint8_t v___x_629_; 
v___x_619_ = lean_string_utf8_get_fast(v___y_612_, v_a_613_);
v___x_620_ = lean_string_utf8_next_fast(v___y_612_, v_a_613_);
lean_dec(v_a_613_);
v___x_621_ = 92;
v___x_629_ = lean_uint32_dec_eq(v___x_619_, v___x_621_);
if (v___x_629_ == 0)
{
uint32_t v___x_630_; uint8_t v___x_631_; 
v___x_630_ = 34;
v___x_631_ = lean_uint32_dec_eq(v___x_619_, v___x_630_);
v___y_623_ = v___x_631_;
goto v___jp_622_;
}
else
{
v___y_623_ = v___x_629_;
goto v___jp_622_;
}
v___jp_622_:
{
if (v___y_623_ == 0)
{
lean_object* v___x_624_; 
v___x_624_ = lean_string_push(v_b_614_, v___x_619_);
v_a_613_ = v___x_620_;
v_b_614_ = v___x_624_;
goto _start;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_string_push(v_b_614_, v___x_621_);
v___x_627_ = lean_string_push(v___x_626_, v___x_619_);
v_a_613_ = v___x_620_;
v_b_614_ = v___x_627_;
goto _start;
}
}
}
else
{
lean_dec(v_a_613_);
return v_b_614_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg___boxed(lean_object* v___x_632_, lean_object* v___y_633_, lean_object* v_a_634_, lean_object* v_b_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_632_, v___y_633_, v_a_634_, v_b_635_);
lean_dec_ref(v___y_633_);
lean_dec_ref(v___x_632_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(lean_object* v_a_639_, lean_object* v_as_640_, size_t v_i_641_, size_t v_stop_642_, lean_object* v_b_643_, lean_object* v___y_644_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = lean_usize_dec_eq(v_i_641_, v_stop_642_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_647_ = lean_array_uget_borrowed(v_as_640_, v_i_641_);
v___x_648_ = ((lean_object*)(l_Lake_compileLeanModule___closed__5));
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_string_utf8_byte_size(v___x_647_);
lean_inc(v___x_647_);
v___x_651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_651_, 0, v___x_647_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
lean_ctor_set(v___x_651_, 2, v___x_650_);
v___x_652_ = l_String_Slice_positions(v___x_651_);
v___x_653_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_651_, v___x_647_, v___x_652_, v___x_648_);
lean_dec_ref_known(v___x_651_, 3);
v___x_654_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0));
v___x_655_ = lean_string_append(v___x_654_, v___x_653_);
lean_dec_ref(v___x_653_);
v___x_656_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1));
v___x_657_ = lean_string_append(v___x_655_, v___x_656_);
v___x_658_ = lean_io_prim_handle_put_str(v_a_639_, v___x_657_);
lean_dec_ref(v___x_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; size_t v___x_660_; size_t v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = ((size_t)1ULL);
v___x_661_ = lean_usize_add(v_i_641_, v___x_660_);
v_i_641_ = v___x_661_;
v_b_643_ = v_a_659_;
goto _start;
}
else
{
lean_object* v_a_663_; lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_a_663_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_658_, 1);
v___x_664_ = lean_io_error_to_string(v_a_663_);
v___x_665_ = 3;
v___x_666_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*1, v___x_665_);
v___x_667_ = lean_array_get_size(v___y_644_);
v___x_668_ = lean_array_push(v___y_644_, v___x_666_);
v___x_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
return v___x_669_;
}
}
else
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_b_643_);
lean_ctor_set(v___x_670_, 1, v___y_644_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___boxed(lean_object* v_a_671_, lean_object* v_as_672_, lean_object* v_i_673_, lean_object* v_stop_674_, lean_object* v_b_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
size_t v_i_boxed_678_; size_t v_stop_boxed_679_; lean_object* v_res_680_; 
v_i_boxed_678_ = lean_unbox_usize(v_i_673_);
lean_dec(v_i_673_);
v_stop_boxed_679_ = lean_unbox_usize(v_stop_674_);
lean_dec(v_stop_674_);
v_res_680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_671_, v_as_672_, v_i_boxed_678_, v_stop_boxed_679_, v_b_675_, v___y_676_);
lean_dec_ref(v_as_672_);
lean_dec(v_a_671_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object* v_basePath_683_, lean_object* v_args_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_687_; lean_object* v_rspFile_688_; lean_object* v_a_690_; lean_object* v___y_698_; uint8_t v___x_709_; lean_object* v___x_710_; 
v___x_687_ = ((lean_object*)(l_Lake_mkArgs___closed__0));
v_rspFile_688_ = l_System_FilePath_addExtension(v_basePath_683_, v___x_687_);
v___x_709_ = 1;
v___x_710_ = lean_io_prim_handle_mk(v_rspFile_688_, v___x_709_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = lean_array_get_size(v_args_684_);
v___x_714_ = lean_nat_dec_lt(v___x_712_, v___x_713_);
if (v___x_714_ == 0)
{
lean_dec(v_a_711_);
v_a_690_ = v_a_685_;
goto v___jp_689_;
}
else
{
lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_715_ = lean_box(0);
v___x_716_ = lean_nat_dec_le(v___x_713_, v___x_713_);
if (v___x_716_ == 0)
{
if (v___x_714_ == 0)
{
lean_dec(v_a_711_);
v_a_690_ = v_a_685_;
goto v___jp_689_;
}
else
{
size_t v___x_717_; size_t v___x_718_; lean_object* v___x_719_; 
v___x_717_ = ((size_t)0ULL);
v___x_718_ = lean_usize_of_nat(v___x_713_);
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_711_, v_args_684_, v___x_717_, v___x_718_, v___x_715_, v_a_685_);
lean_dec(v_a_711_);
v___y_698_ = v___x_719_;
goto v___jp_697_;
}
}
else
{
size_t v___x_720_; size_t v___x_721_; lean_object* v___x_722_; 
v___x_720_ = ((size_t)0ULL);
v___x_721_ = lean_usize_of_nat(v___x_713_);
v___x_722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_711_, v_args_684_, v___x_720_, v___x_721_, v___x_715_, v_a_685_);
lean_dec(v_a_711_);
v___y_698_ = v___x_722_;
goto v___jp_697_;
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec_ref(v_rspFile_688_);
v_a_723_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_710_, 1);
v___x_724_ = lean_io_error_to_string(v_a_723_);
v___x_725_ = 3;
v___x_726_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*1, v___x_725_);
v___x_727_ = lean_array_get_size(v_a_685_);
v___x_728_ = lean_array_push(v_a_685_, v___x_726_);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
return v___x_729_;
}
v___jp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_691_ = ((lean_object*)(l_Lake_mkArgs___closed__1));
v___x_692_ = lean_string_append(v___x_691_, v_rspFile_688_);
lean_dec_ref(v_rspFile_688_);
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = lean_mk_empty_array_with_capacity(v___x_693_);
v___x_695_ = lean_array_push(v___x_694_, v___x_692_);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v_a_690_);
return v___x_696_;
}
v___jp_697_:
{
if (lean_obj_tag(v___y_698_) == 0)
{
lean_object* v_a_699_; 
v_a_699_ = lean_ctor_get(v___y_698_, 1);
lean_inc(v_a_699_);
lean_dec_ref_known(v___y_698_, 2);
v_a_690_ = v_a_699_;
goto v___jp_689_;
}
else
{
lean_object* v_a_700_; lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec_ref(v_rspFile_688_);
v_a_700_ = lean_ctor_get(v___y_698_, 0);
v_a_701_ = lean_ctor_get(v___y_698_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v___y_698_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___y_698_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_inc(v_a_700_);
lean_dec(v___y_698_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_700_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_a_701_);
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
}
LEAN_EXPORT lean_object* l_Lake_mkArgs___boxed(lean_object* v_basePath_730_, lean_object* v_args_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lake_mkArgs(v_basePath_730_, v_args_731_, v_a_732_);
lean_dec_ref(v_args_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(lean_object* v___x_735_, lean_object* v___y_736_, lean_object* v_inst_737_, lean_object* v_R_738_, lean_object* v_a_739_, lean_object* v_b_740_, lean_object* v_c_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_735_, v___y_736_, v_a_739_, v_b_740_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(lean_object* v___x_743_, lean_object* v___y_744_, lean_object* v_inst_745_, lean_object* v_R_746_, lean_object* v_a_747_, lean_object* v_b_748_, lean_object* v_c_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(v___x_743_, v___y_744_, v_inst_745_, v_R_746_, v_a_747_, v_b_748_, v_c_749_);
lean_dec_ref(v___y_744_);
lean_dec_ref(v___x_743_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(size_t v_sz_751_, size_t v_i_752_, lean_object* v_bs_753_){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = lean_usize_dec_lt(v_i_752_, v_sz_751_);
if (v___x_754_ == 0)
{
return v_bs_753_;
}
else
{
lean_object* v_v_755_; lean_object* v___x_756_; lean_object* v_bs_x27_757_; size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; 
v_v_755_ = lean_array_uget(v_bs_753_, v_i_752_);
v___x_756_ = lean_unsigned_to_nat(0u);
v_bs_x27_757_ = lean_array_uset(v_bs_753_, v_i_752_, v___x_756_);
v___x_758_ = ((size_t)1ULL);
v___x_759_ = lean_usize_add(v_i_752_, v___x_758_);
v___x_760_ = lean_array_uset(v_bs_x27_757_, v_i_752_, v_v_755_);
v_i_752_ = v___x_759_;
v_bs_753_ = v___x_760_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0___boxed(lean_object* v_sz_762_, lean_object* v_i_763_, lean_object* v_bs_764_){
_start:
{
size_t v_sz_boxed_765_; size_t v_i_boxed_766_; lean_object* v_res_767_; 
v_sz_boxed_765_ = lean_unbox_usize(v_sz_762_);
lean_dec(v_sz_762_);
v_i_boxed_766_ = lean_unbox_usize(v_i_763_);
lean_dec(v_i_763_);
v_res_767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_boxed_765_, v_i_boxed_766_, v_bs_764_);
return v_res_767_;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__3(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = ((lean_object*)(l_Lake_compileStaticLib___closed__2));
v___x_775_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_776_ = lean_array_push(v___x_775_, v___x_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object* v_libFile_777_, lean_object* v_oFiles_778_, lean_object* v_ar_779_, uint8_t v_thin_780_, lean_object* v_a_781_){
_start:
{
lean_object* v___x_783_; 
lean_inc_ref(v_libFile_777_);
v___x_783_ = l_Lake_createParentDirs(v_libFile_777_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v___x_784_; 
lean_dec_ref_known(v___x_783_, 1);
v___x_784_ = l_Lake_removeFileIfExists(v_libFile_777_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v___x_785_; uint8_t v___x_786_; lean_object* v___y_788_; 
lean_dec_ref_known(v___x_784_, 1);
v___x_785_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_786_ = 1;
if (v_thin_780_ == 0)
{
v___y_788_ = v___x_785_;
goto v___jp_787_;
}
else
{
lean_object* v___x_812_; 
v___x_812_ = lean_obj_once(&l_Lake_compileStaticLib___closed__3, &l_Lake_compileStaticLib___closed__3_once, _init_l_Lake_compileStaticLib___closed__3);
v___y_788_ = v___x_812_;
goto v___jp_787_;
}
v___jp_787_:
{
size_t v_sz_789_; size_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_sz_789_ = lean_array_size(v_oFiles_778_);
v___x_790_ = ((size_t)0ULL);
v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_789_, v___x_790_, v_oFiles_778_);
lean_inc_ref(v_libFile_777_);
v___x_792_ = l_Lake_mkArgs(v_libFile_777_, v___x_791_, v_a_781_);
lean_dec_ref(v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v_a_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
v_a_794_ = lean_ctor_get(v___x_792_, 1);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_792_, 2);
lean_inc_ref(v___y_788_);
v___x_795_ = lean_array_push(v___y_788_, v_libFile_777_);
v___x_796_ = l_Array_append___redArg(v___x_795_, v_a_793_);
lean_dec(v_a_793_);
v___x_797_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_798_ = lean_box(0);
v___x_799_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_800_ = 0;
v___x_801_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_801_, 0, v___x_797_);
lean_ctor_set(v___x_801_, 1, v_ar_779_);
lean_ctor_set(v___x_801_, 2, v___x_796_);
lean_ctor_set(v___x_801_, 3, v___x_798_);
lean_ctor_set(v___x_801_, 4, v___x_799_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*5, v___x_786_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*5 + 1, v___x_800_);
v___x_802_ = l_Lake_proc(v___x_801_, v___x_800_, v___x_798_, v_a_794_);
return v___x_802_;
}
else
{
lean_object* v_a_803_; lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v_ar_779_);
lean_dec_ref(v_libFile_777_);
v_a_803_ = lean_ctor_get(v___x_792_, 0);
v_a_804_ = lean_ctor_get(v___x_792_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_792_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_inc(v_a_803_);
lean_dec(v___x_792_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_803_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_814_; uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref(v_ar_779_);
lean_dec_ref(v_oFiles_778_);
lean_dec_ref(v_libFile_777_);
v_a_813_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_784_, 1);
v___x_814_ = lean_io_error_to_string(v_a_813_);
v___x_815_ = 3;
v___x_816_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*1, v___x_815_);
v___x_817_ = lean_array_get_size(v_a_781_);
v___x_818_ = lean_array_push(v_a_781_, v___x_816_);
v___x_819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
return v___x_819_;
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec_ref(v_ar_779_);
lean_dec_ref(v_oFiles_778_);
lean_dec_ref(v_libFile_777_);
v_a_820_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_783_, 1);
v___x_821_ = lean_io_error_to_string(v_a_820_);
v___x_822_ = 3;
v___x_823_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*1, v___x_822_);
v___x_824_ = lean_array_get_size(v_a_781_);
v___x_825_ = lean_array_push(v_a_781_, v___x_823_);
v___x_826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object* v_libFile_827_, lean_object* v_oFiles_828_, lean_object* v_ar_829_, lean_object* v_thin_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
uint8_t v_thin_boxed_833_; lean_object* v_res_834_; 
v_thin_boxed_833_ = lean_unbox(v_thin_830_);
v_res_834_ = l_Lake_compileStaticLib(v_libFile_827_, v_oFiles_828_, v_ar_829_, v_thin_boxed_833_, v_a_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = l_System_Platform_isOSX;
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
v___x_848_ = ((lean_object*)(l_Lake_compileO___closed__2));
return v___x_848_;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0));
v___x_850_ = lean_io_getenv(v___x_849_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v___x_851_; 
v___x_851_ = ((lean_object*)(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4));
return v___x_851_;
}
else
{
lean_object* v___x_852_; 
lean_dec_ref_known(v___x_850_, 1);
v___x_852_ = ((lean_object*)(l_Lake_compileO___closed__2));
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___boxed(lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
return v_res_854_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__1(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_856_ = ((lean_object*)(l_Lake_compileSharedLib___closed__0));
v___x_857_ = lean_unsigned_to_nat(3u);
v___x_858_ = lean_mk_empty_array_with_capacity(v___x_857_);
v___x_859_ = lean_array_push(v___x_858_, v___x_856_);
return v___x_859_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__2(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_861_ = lean_obj_once(&l_Lake_compileSharedLib___closed__1, &l_Lake_compileSharedLib___closed__1_once, _init_l_Lake_compileSharedLib___closed__1);
v___x_862_ = lean_array_push(v___x_861_, v___x_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object* v_libFile_863_, lean_object* v_linkArgs_864_, lean_object* v_linker_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; 
lean_inc_ref(v_libFile_863_);
v___x_868_ = l_Lake_createParentDirs(v_libFile_863_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v___x_869_; 
lean_dec_ref_known(v___x_868_, 1);
lean_inc_ref(v_libFile_863_);
v___x_869_ = l_Lake_mkArgs(v_libFile_863_, v_linkArgs_864_, v_a_866_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v_a_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
v_a_871_ = lean_ctor_get(v___x_869_, 1);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_869_, 2);
v___x_872_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
v___x_873_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_874_ = lean_obj_once(&l_Lake_compileSharedLib___closed__2, &l_Lake_compileSharedLib___closed__2_once, _init_l_Lake_compileSharedLib___closed__2);
v___x_875_ = lean_array_push(v___x_874_, v_libFile_863_);
v___x_876_ = l_Array_append___redArg(v___x_875_, v_a_870_);
lean_dec(v_a_870_);
v___x_877_ = lean_box(0);
v___x_878_ = 1;
v___x_879_ = 0;
v___x_880_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_880_, 0, v___x_873_);
lean_ctor_set(v___x_880_, 1, v_linker_865_);
lean_ctor_set(v___x_880_, 2, v___x_876_);
lean_ctor_set(v___x_880_, 3, v___x_877_);
lean_ctor_set(v___x_880_, 4, v___x_872_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*5, v___x_878_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*5 + 1, v___x_879_);
v___x_881_ = l_Lake_proc(v___x_880_, v___x_879_, v___x_877_, v_a_871_);
return v___x_881_;
}
else
{
lean_object* v_a_882_; lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec_ref(v_linker_865_);
lean_dec_ref(v_libFile_863_);
v_a_882_ = lean_ctor_get(v___x_869_, 0);
v_a_883_ = lean_ctor_get(v___x_869_, 1);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_869_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_inc(v_a_882_);
lean_dec(v___x_869_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_882_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec_ref(v_linker_865_);
lean_dec_ref(v_libFile_863_);
v_a_891_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_868_, 1);
v___x_892_ = lean_io_error_to_string(v_a_891_);
v___x_893_ = 3;
v___x_894_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set_uint8(v___x_894_, sizeof(void*)*1, v___x_893_);
v___x_895_ = lean_array_get_size(v_a_866_);
v___x_896_ = lean_array_push(v_a_866_, v___x_894_);
v___x_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object* v_libFile_898_, lean_object* v_linkArgs_899_, lean_object* v_linker_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lake_compileSharedLib(v_libFile_898_, v_linkArgs_899_, v_linker_900_, v_a_901_);
lean_dec_ref(v_linkArgs_899_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object* v_binFile_904_, lean_object* v_linkArgs_905_, lean_object* v_linker_906_, lean_object* v_a_907_){
_start:
{
lean_object* v___x_909_; 
lean_inc_ref(v_binFile_904_);
v___x_909_ = l_Lake_createParentDirs(v_binFile_904_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v___x_910_; 
lean_dec_ref_known(v___x_909_, 1);
lean_inc_ref(v_binFile_904_);
v___x_910_ = l_Lake_mkArgs(v_binFile_904_, v_linkArgs_905_, v_a_907_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
v_a_912_ = lean_ctor_get(v___x_910_, 1);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_910_, 2);
v___x_913_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
v___x_914_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_915_ = lean_unsigned_to_nat(2u);
v___x_916_ = lean_mk_empty_array_with_capacity(v___x_915_);
lean_dec_ref(v___x_916_);
v___x_917_ = lean_obj_once(&l_Lake_compileLeanModule___closed__15, &l_Lake_compileLeanModule___closed__15_once, _init_l_Lake_compileLeanModule___closed__15);
v___x_918_ = lean_array_push(v___x_917_, v_binFile_904_);
v___x_919_ = l_Array_append___redArg(v___x_918_, v_a_911_);
lean_dec(v_a_911_);
v___x_920_ = lean_box(0);
v___x_921_ = 1;
v___x_922_ = 0;
v___x_923_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_923_, 0, v___x_914_);
lean_ctor_set(v___x_923_, 1, v_linker_906_);
lean_ctor_set(v___x_923_, 2, v___x_919_);
lean_ctor_set(v___x_923_, 3, v___x_920_);
lean_ctor_set(v___x_923_, 4, v___x_913_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*5, v___x_921_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*5 + 1, v___x_922_);
v___x_924_ = l_Lake_proc(v___x_923_, v___x_922_, v___x_920_, v_a_912_);
return v___x_924_;
}
else
{
lean_object* v_a_925_; lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v_linker_906_);
lean_dec_ref(v_binFile_904_);
v_a_925_ = lean_ctor_get(v___x_910_, 0);
v_a_926_ = lean_ctor_get(v___x_910_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_910_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_inc(v_a_925_);
lean_dec(v___x_910_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_925_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec_ref(v_linker_906_);
lean_dec_ref(v_binFile_904_);
v_a_934_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_909_, 1);
v___x_935_ = lean_io_error_to_string(v_a_934_);
v___x_936_ = 3;
v___x_937_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set_uint8(v___x_937_, sizeof(void*)*1, v___x_936_);
v___x_938_ = lean_array_get_size(v_a_907_);
v___x_939_ = lean_array_push(v_a_907_, v___x_937_);
v___x_940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object* v_binFile_941_, lean_object* v_linkArgs_942_, lean_object* v_linker_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lake_compileExe(v_binFile_941_, v_linkArgs_942_, v_linker_943_, v_a_944_);
lean_dec_ref(v_linkArgs_942_);
return v_res_946_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_948_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0));
v___x_949_ = lean_unsigned_to_nat(2u);
v___x_950_ = lean_mk_empty_array_with_capacity(v___x_949_);
v___x_951_ = lean_array_push(v___x_950_, v___x_948_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(lean_object* v_as_952_, size_t v_i_953_, size_t v_stop_954_, lean_object* v_b_955_){
_start:
{
uint8_t v___x_956_; 
v___x_956_ = lean_usize_dec_eq(v_i_953_, v_stop_954_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; size_t v___x_961_; size_t v___x_962_; 
v___x_957_ = lean_array_uget_borrowed(v_as_952_, v_i_953_);
v___x_958_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1);
lean_inc(v___x_957_);
v___x_959_ = lean_array_push(v___x_958_, v___x_957_);
v___x_960_ = l_Array_append___redArg(v_b_955_, v___x_959_);
lean_dec_ref(v___x_959_);
v___x_961_ = ((size_t)1ULL);
v___x_962_ = lean_usize_add(v_i_953_, v___x_961_);
v_i_953_ = v___x_962_;
v_b_955_ = v___x_960_;
goto _start;
}
else
{
return v_b_955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___boxed(lean_object* v_as_964_, lean_object* v_i_965_, lean_object* v_stop_966_, lean_object* v_b_967_){
_start:
{
size_t v_i_boxed_968_; size_t v_stop_boxed_969_; lean_object* v_res_970_; 
v_i_boxed_968_ = lean_unbox_usize(v_i_965_);
lean_dec(v_i_965_);
v_stop_boxed_969_ = lean_unbox_usize(v_stop_966_);
lean_dec(v_stop_966_);
v_res_970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_as_964_, v_i_boxed_968_, v_stop_boxed_969_, v_b_967_);
lean_dec_ref(v_as_964_);
return v_res_970_;
}
}
static lean_object* _init_l_Lake_download___closed__5(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_976_ = ((lean_object*)(l_Lake_download___closed__1));
v___x_977_ = lean_unsigned_to_nat(7u);
v___x_978_ = lean_mk_empty_array_with_capacity(v___x_977_);
v___x_979_ = lean_array_push(v___x_978_, v___x_976_);
return v___x_979_;
}
}
static lean_object* _init_l_Lake_download___closed__6(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = ((lean_object*)(l_Lake_download___closed__2));
v___x_981_ = lean_obj_once(&l_Lake_download___closed__5, &l_Lake_download___closed__5_once, _init_l_Lake_download___closed__5);
v___x_982_ = lean_array_push(v___x_981_, v___x_980_);
return v___x_982_;
}
}
static lean_object* _init_l_Lake_download___closed__7(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_984_ = lean_obj_once(&l_Lake_download___closed__6, &l_Lake_download___closed__6_once, _init_l_Lake_download___closed__6);
v___x_985_ = lean_array_push(v___x_984_, v___x_983_);
return v___x_985_;
}
}
static lean_object* _init_l_Lake_download___closed__8(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_987_ = lean_obj_once(&l_Lake_download___closed__7, &l_Lake_download___closed__7_once, _init_l_Lake_download___closed__7);
v___x_988_ = lean_array_push(v___x_987_, v___x_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lake_download(lean_object* v_url_989_, lean_object* v_file_990_, lean_object* v_headers_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_1006_; uint8_t v___x_1022_; 
v___x_1022_ = l_System_FilePath_pathExists(v_file_990_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; 
lean_inc_ref(v_file_990_);
v___x_1023_ = l_Lake_createParentDirs(v_file_990_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_dec_ref_known(v___x_1023_, 1);
v___y_1006_ = v_a_992_;
goto v___jp_1005_;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec_ref(v_file_990_);
lean_dec_ref(v_url_989_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = lean_io_error_to_string(v_a_1024_);
v___x_1026_ = 3;
v___x_1027_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set_uint8(v___x_1027_, sizeof(void*)*1, v___x_1026_);
v___x_1028_ = lean_array_get_size(v_a_992_);
v___x_1029_ = lean_array_push(v_a_992_, v___x_1027_);
v___x_1030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
return v___x_1030_;
}
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_io_remove_file(v_file_990_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_dec_ref_known(v___x_1031_, 1);
v___y_1006_ = v_a_992_;
goto v___jp_1005_;
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec_ref(v_file_990_);
lean_dec_ref(v_url_989_);
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = lean_io_error_to_string(v_a_1032_);
v___x_1034_ = 3;
v___x_1035_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*1, v___x_1034_);
v___x_1036_ = lean_array_get_size(v_a_992_);
v___x_1037_ = lean_array_push(v_a_992_, v___x_1035_);
v___x_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
return v___x_1038_;
}
}
v___jp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; uint8_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_997_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_998_ = ((lean_object*)(l_Lake_download___closed__0));
v___x_999_ = lean_box(0);
v___x_1000_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_1001_ = 1;
v___x_1002_ = 0;
v___x_1003_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1003_, 0, v___x_997_);
lean_ctor_set(v___x_1003_, 1, v___x_998_);
lean_ctor_set(v___x_1003_, 2, v___y_996_);
lean_ctor_set(v___x_1003_, 3, v___x_999_);
lean_ctor_set(v___x_1003_, 4, v___x_1000_);
lean_ctor_set_uint8(v___x_1003_, sizeof(void*)*5, v___x_1001_);
lean_ctor_set_uint8(v___x_1003_, sizeof(void*)*5 + 1, v___x_1002_);
v___x_1004_ = l_Lake_proc(v___x_1003_, v___x_1001_, v___x_999_, v___y_995_);
return v___x_1004_;
}
v___jp_1005_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1007_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_1008_ = lean_obj_once(&l_Lake_download___closed__8, &l_Lake_download___closed__8_once, _init_l_Lake_download___closed__8);
v___x_1009_ = lean_array_push(v___x_1008_, v_file_990_);
v___x_1010_ = lean_array_push(v___x_1009_, v___x_1007_);
v___x_1011_ = lean_array_push(v___x_1010_, v_url_989_);
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = lean_array_get_size(v_headers_991_);
v___x_1014_ = lean_nat_dec_lt(v___x_1012_, v___x_1013_);
if (v___x_1014_ == 0)
{
v___y_995_ = v___y_1006_;
v___y_996_ = v___x_1011_;
goto v___jp_994_;
}
else
{
uint8_t v___x_1015_; 
v___x_1015_ = lean_nat_dec_le(v___x_1013_, v___x_1013_);
if (v___x_1015_ == 0)
{
if (v___x_1014_ == 0)
{
v___y_995_ = v___y_1006_;
v___y_996_ = v___x_1011_;
goto v___jp_994_;
}
else
{
size_t v___x_1016_; size_t v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = ((size_t)0ULL);
v___x_1017_ = lean_usize_of_nat(v___x_1013_);
v___x_1018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_991_, v___x_1016_, v___x_1017_, v___x_1011_);
v___y_995_ = v___y_1006_;
v___y_996_ = v___x_1018_;
goto v___jp_994_;
}
}
else
{
size_t v___x_1019_; size_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = ((size_t)0ULL);
v___x_1020_ = lean_usize_of_nat(v___x_1013_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_991_, v___x_1019_, v___x_1020_, v___x_1011_);
v___y_995_ = v___y_1006_;
v___y_996_ = v___x_1021_;
goto v___jp_994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object* v_url_1039_, lean_object* v_file_1040_, lean_object* v_headers_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lake_download(v_url_1039_, v_file_1040_, v_headers_1041_, v_a_1042_);
lean_dec_ref(v_headers_1041_);
return v_res_1044_;
}
}
static lean_object* _init_l_Lake_untar___closed__3(void){
_start:
{
uint32_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = 122;
v___x_1049_ = ((lean_object*)(l_Lake_untar___closed__2));
v___x_1050_ = lean_string_push(v___x_1049_, v___x_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lake_untar(lean_object* v_file_1051_, lean_object* v_dir_1052_, uint8_t v_gzip_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1056_; 
lean_inc_ref(v_dir_1052_);
v___x_1056_ = l_IO_FS_createDirAll(v_dir_1052_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_opts_1058_; lean_object* v___y_1059_; lean_object* v___x_1077_; 
lean_dec_ref_known(v___x_1056_, 1);
v___x_1077_ = ((lean_object*)(l_Lake_untar___closed__2));
if (v_gzip_1053_ == 0)
{
v_opts_1058_ = v___x_1077_;
v___y_1059_ = v_a_1054_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_obj_once(&l_Lake_untar___closed__3, &l_Lake_untar___closed__3_once, _init_l_Lake_untar___closed__3);
v_opts_1058_ = v___x_1078_;
v___y_1059_ = v_a_1054_;
goto v___jp_1057_;
}
v___jp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1060_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_1061_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_1062_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_1063_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_1064_ = lean_unsigned_to_nat(5u);
v___x_1065_ = lean_mk_empty_array_with_capacity(v___x_1064_);
lean_inc_ref(v_opts_1058_);
v___x_1066_ = lean_array_push(v___x_1065_, v_opts_1058_);
v___x_1067_ = lean_array_push(v___x_1066_, v___x_1062_);
v___x_1068_ = lean_array_push(v___x_1067_, v_file_1051_);
v___x_1069_ = lean_array_push(v___x_1068_, v___x_1063_);
v___x_1070_ = lean_array_push(v___x_1069_, v_dir_1052_);
v___x_1071_ = lean_box(0);
v___x_1072_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_1073_ = 1;
v___x_1074_ = 0;
v___x_1075_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1075_, 0, v___x_1060_);
lean_ctor_set(v___x_1075_, 1, v___x_1061_);
lean_ctor_set(v___x_1075_, 2, v___x_1070_);
lean_ctor_set(v___x_1075_, 3, v___x_1071_);
lean_ctor_set(v___x_1075_, 4, v___x_1072_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*5, v___x_1073_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*5 + 1, v___x_1074_);
v___x_1076_ = l_Lake_proc(v___x_1075_, v___x_1073_, v___x_1071_, v___y_1059_);
return v___x_1076_;
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec_ref(v_dir_1052_);
lean_dec_ref(v_file_1051_);
v_a_1079_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1056_, 1);
v___x_1080_ = lean_io_error_to_string(v_a_1079_);
v___x_1081_ = 3;
v___x_1082_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*1, v___x_1081_);
v___x_1083_ = lean_array_get_size(v_a_1054_);
v___x_1084_ = lean_array_push(v_a_1054_, v___x_1082_);
v___x_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object* v_file_1086_, lean_object* v_dir_1087_, lean_object* v_gzip_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
uint8_t v_gzip_boxed_1091_; lean_object* v_res_1092_; 
v_gzip_boxed_1091_ = lean_unbox(v_gzip_1088_);
v_res_1092_ = l_Lake_untar(v_file_1086_, v_dir_1087_, v_gzip_boxed_1091_, v_a_1089_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(lean_object* v_as_1094_, size_t v_sz_1095_, size_t v_i_1096_, lean_object* v_b_1097_, lean_object* v___y_1098_){
_start:
{
uint8_t v___x_1100_; 
v___x_1100_ = lean_usize_dec_lt(v_i_1096_, v_sz_1095_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v_b_1097_);
lean_ctor_set(v___x_1101_, 1, v___y_1098_);
return v___x_1101_;
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; 
v_a_1102_ = lean_array_uget_borrowed(v_as_1094_, v_i_1096_);
v___x_1103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0));
v___x_1104_ = lean_string_append(v___x_1103_, v_a_1102_);
v___x_1105_ = lean_array_push(v_b_1097_, v___x_1104_);
v___x_1106_ = ((size_t)1ULL);
v___x_1107_ = lean_usize_add(v_i_1096_, v___x_1106_);
v_i_1096_ = v___x_1107_;
v_b_1097_ = v___x_1105_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___boxed(lean_object* v_as_1109_, lean_object* v_sz_1110_, lean_object* v_i_1111_, lean_object* v_b_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
size_t v_sz_boxed_1115_; size_t v_i_boxed_1116_; lean_object* v_res_1117_; 
v_sz_boxed_1115_ = lean_unbox_usize(v_sz_1110_);
lean_dec(v_sz_1110_);
v_i_boxed_1116_ = lean_unbox_usize(v_i_1111_);
lean_dec(v_i_1111_);
v_res_1117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_as_1109_, v_sz_boxed_1115_, v_i_boxed_1116_, v_b_1112_, v___y_1113_);
lean_dec_ref(v_as_1109_);
return v_res_1117_;
}
}
static lean_object* _init_l_Lake_tar___closed__1(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1119_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_1120_ = lean_unsigned_to_nat(5u);
v___x_1121_ = lean_mk_empty_array_with_capacity(v___x_1120_);
v___x_1122_ = lean_array_push(v___x_1121_, v___x_1119_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lake_tar___closed__10(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = ((lean_object*)(l_Lake_tar___closed__9));
v___x_1141_ = ((lean_object*)(l_Lake_tar___closed__8));
v___x_1142_ = lean_array_push(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lake_tar(lean_object* v_dir_1143_, lean_object* v_file_1144_, uint8_t v_gzip_1145_, lean_object* v_excludePaths_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; uint8_t v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___x_1161_; 
lean_inc_ref(v_file_1144_);
v___x_1161_ = l_Lake_createParentDirs(v_file_1144_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_args_1163_; lean_object* v___y_1164_; lean_object* v___x_1194_; 
lean_dec_ref_known(v___x_1161_, 1);
v___x_1194_ = ((lean_object*)(l_Lake_tar___closed__8));
if (v_gzip_1145_ == 0)
{
v_args_1163_ = v___x_1194_;
v___y_1164_ = v_a_1147_;
goto v___jp_1162_;
}
else
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_obj_once(&l_Lake_tar___closed__10, &l_Lake_tar___closed__10_once, _init_l_Lake_tar___closed__10);
v_args_1163_ = v___x_1195_;
v___y_1164_ = v_a_1147_;
goto v___jp_1162_;
}
v___jp_1162_:
{
size_t v_sz_1165_; size_t v___x_1166_; lean_object* v___x_1167_; 
v_sz_1165_ = lean_array_size(v_excludePaths_1146_);
v___x_1166_ = ((size_t)0ULL);
lean_inc_ref(v_args_1163_);
v___x_1167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_excludePaths_1146_, v_sz_1165_, v___x_1166_, v_args_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v_a_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; uint8_t v___x_1182_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
v_a_1169_ = lean_ctor_get(v___x_1167_, 1);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1167_, 2);
v___x_1170_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_1171_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_1172_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_1173_ = ((lean_object*)(l_Lake_tar___closed__0));
v___x_1174_ = lean_obj_once(&l_Lake_tar___closed__1, &l_Lake_tar___closed__1_once, _init_l_Lake_tar___closed__1);
v___x_1175_ = lean_array_push(v___x_1174_, v_file_1144_);
v___x_1176_ = lean_array_push(v___x_1175_, v___x_1172_);
v___x_1177_ = lean_array_push(v___x_1176_, v_dir_1143_);
v___x_1178_ = lean_array_push(v___x_1177_, v___x_1173_);
v___x_1179_ = l_Array_append___redArg(v_a_1168_, v___x_1178_);
lean_dec_ref(v___x_1178_);
v___x_1180_ = lean_box(0);
v___x_1181_ = l_System_Platform_isOSX;
v___x_1182_ = 1;
if (v___x_1181_ == 0)
{
lean_object* v___x_1183_; 
v___x_1183_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_1150_ = v_a_1169_;
v___y_1151_ = v___x_1180_;
v___y_1152_ = v___x_1170_;
v___y_1153_ = v___x_1182_;
v___y_1154_ = v___x_1179_;
v___y_1155_ = v___x_1171_;
v___y_1156_ = v___x_1183_;
goto v___jp_1149_;
}
else
{
lean_object* v___x_1184_; 
v___x_1184_ = ((lean_object*)(l_Lake_tar___closed__6));
v___y_1150_ = v_a_1169_;
v___y_1151_ = v___x_1180_;
v___y_1152_ = v___x_1170_;
v___y_1153_ = v___x_1182_;
v___y_1154_ = v___x_1179_;
v___y_1155_ = v___x_1171_;
v___y_1156_ = v___x_1184_;
goto v___jp_1149_;
}
}
else
{
lean_object* v_a_1185_; lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec_ref(v_file_1144_);
lean_dec_ref(v_dir_1143_);
v_a_1185_ = lean_ctor_get(v___x_1167_, 0);
v_a_1186_ = lean_ctor_get(v___x_1167_, 1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1167_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_inc(v_a_1185_);
lean_dec(v___x_1167_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1185_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec_ref(v_file_1144_);
lean_dec_ref(v_dir_1143_);
v_a_1196_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1161_, 1);
v___x_1197_ = lean_io_error_to_string(v_a_1196_);
v___x_1198_ = 3;
v___x_1199_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set_uint8(v___x_1199_, sizeof(void*)*1, v___x_1198_);
v___x_1200_ = lean_array_get_size(v_a_1147_);
v___x_1201_ = lean_array_push(v_a_1147_, v___x_1199_);
v___x_1202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
return v___x_1202_;
}
v___jp_1149_:
{
uint8_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1157_ = 0;
lean_inc_ref(v___y_1156_);
lean_inc(v___y_1151_);
lean_inc_ref(v___y_1155_);
lean_inc_ref(v___y_1152_);
v___x_1158_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1158_, 0, v___y_1152_);
lean_ctor_set(v___x_1158_, 1, v___y_1155_);
lean_ctor_set(v___x_1158_, 2, v___y_1154_);
lean_ctor_set(v___x_1158_, 3, v___y_1151_);
lean_ctor_set(v___x_1158_, 4, v___y_1156_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*5, v___y_1153_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*5 + 1, v___x_1157_);
v___x_1159_ = lean_box(0);
v___x_1160_ = l_Lake_proc(v___x_1158_, v___y_1153_, v___x_1159_, v___y_1150_);
return v___x_1160_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object* v_dir_1203_, lean_object* v_file_1204_, lean_object* v_gzip_1205_, lean_object* v_excludePaths_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
uint8_t v_gzip_boxed_1209_; lean_object* v_res_1210_; 
v_gzip_boxed_1209_ = lean_unbox(v_gzip_1205_);
v_res_1210_ = l_Lake_tar(v_dir_1203_, v_file_1204_, v_gzip_boxed_1209_, v_excludePaths_1206_, v_a_1207_);
lean_dec_ref(v_excludePaths_1206_);
return v_res_1210_;
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
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Actions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
