// Lean compiler output
// Module: Lake.Build.Actions
// Imports: public import Lake.Util.Log import Lake.Util.Proc import Lake.Util.FilePath import Lake.Util.IO import Lake.Util.Url import Init.Data.String.Search import Init.Data.String.TakeDrop import Init.System.Platform import Lean.CoreM import Lean.Compiler.Options
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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
extern uint8_t l_System_Platform_isOSX;
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
lean_object* lean_io_getenv(lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake_compileSharedLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "-shared"};
static const lean_object* l_Lake_compileSharedLib___closed__0 = (const lean_object*)&l_Lake_compileSharedLib___closed__0_value;
static lean_once_cell_t l_Lake_compileSharedLib___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileSharedLib___closed__1;
static lean_once_cell_t l_Lake_compileSharedLib___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileSharedLib___closed__2;
static const lean_string_object l_Lake_compileSharedLib___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "MACOSX_DEPLOYMENT_TARGET"};
static const lean_object* l_Lake_compileSharedLib___closed__3 = (const lean_object*)&l_Lake_compileSharedLib___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-H"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_download___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "CURL"};
static const lean_object* l_Lake_download___closed__0 = (const lean_object*)&l_Lake_download___closed__0_value;
static const lean_string_object l_Lake_download___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "curl"};
static const lean_object* l_Lake_download___closed__1 = (const lean_object*)&l_Lake_download___closed__1_value;
static const lean_string_object l_Lake_download___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-s"};
static const lean_object* l_Lake_download___closed__2 = (const lean_object*)&l_Lake_download___closed__2_value;
static const lean_string_object l_Lake_download___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-S"};
static const lean_object* l_Lake_download___closed__3 = (const lean_object*)&l_Lake_download___closed__3_value;
static const lean_string_object l_Lake_download___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-f"};
static const lean_object* l_Lake_download___closed__4 = (const lean_object*)&l_Lake_download___closed__4_value;
static const lean_string_object l_Lake_download___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-L"};
static const lean_object* l_Lake_download___closed__5 = (const lean_object*)&l_Lake_download___closed__5_value;
static lean_once_cell_t l_Lake_download___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_download___closed__6;
static lean_once_cell_t l_Lake_download___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_download___closed__7;
static lean_once_cell_t l_Lake_download___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_download___closed__8;
static lean_once_cell_t l_Lake_download___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_download___closed__9;
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
lean_object* v___y_60_; lean_object* v___y_64_; uint32_t v___y_65_; lean_object* v___y_76_; lean_object* v___y_77_; lean_object* v___y_80_; uint8_t v___y_81_; uint32_t v___y_82_; lean_object* v___y_132_; uint8_t v___y_133_; lean_object* v___y_139_; lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = lean_string_utf8_byte_size(v_stderr_55_);
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = lean_nat_dec_eq(v___x_148_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_151_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__1));
v___x_152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_152_, 0, v_stderr_55_);
lean_ctor_set(v___x_152_, 1, v___x_149_);
lean_ctor_set(v___x_152_, 2, v___x_148_);
v___x_153_ = l_String_Slice_trimAscii(v___x_152_);
v___x_154_ = l_String_Slice_toString(v___x_153_);
lean_dec_ref(v___x_153_);
v___x_155_ = lean_string_append(v___x_151_, v___x_154_);
lean_dec_ref(v___x_154_);
v___x_156_ = 1;
v___x_157_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*1, v___x_156_);
v___x_158_ = lean_array_push(v___y_57_, v___x_157_);
v___y_139_ = v___x_158_;
goto v___jp_138_;
}
else
{
lean_dec_ref(v_stderr_55_);
v___y_139_ = v___y_57_;
goto v___jp_138_;
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
v___x_67_ = lean_uint32_to_nat(v___y_65_);
v___x_68_ = l_Nat_reprFast(v___x_67_);
v___x_69_ = lean_string_append(v___x_66_, v___x_68_);
lean_dec_ref(v___x_68_);
v___x_70_ = 3;
v___x_71_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set_uint8(v___x_71_, sizeof(void*)*1, v___x_70_);
v___x_72_ = lean_array_get_size(v___y_64_);
v___x_73_ = lean_array_push(v___y_64_, v___x_71_);
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
uint32_t v___x_83_; uint8_t v___x_84_; 
v___x_83_ = 0;
v___x_84_ = lean_uint32_dec_eq(v___y_82_, v___x_83_);
if (v___x_84_ == 0)
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
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec_ref(v___x_48_);
lean_dec(v___x_47_);
lean_dec_ref(v_leanir_46_);
lean_dec_ref(v___x_45_);
lean_dec_ref(v_setupFile_44_);
lean_dec(v_c_x3f_43_);
lean_dec(v_ir_x3f_42_);
v___x_85_ = lean_box(0);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___y_80_);
return v___x_86_;
}
else
{
if (lean_obj_tag(v_ir_x3f_42_) == 1)
{
if (lean_obj_tag(v_c_x3f_43_) == 1)
{
lean_object* v_val_87_; lean_object* v_val_88_; lean_object* v___x_89_; 
v_val_87_ = lean_ctor_get(v_ir_x3f_42_, 0);
lean_inc_n(v_val_87_, 2);
lean_dec_ref_known(v_ir_x3f_42_, 1);
v_val_88_ = lean_ctor_get(v_c_x3f_43_, 0);
lean_inc(v_val_88_);
lean_dec_ref_known(v_c_x3f_43_, 1);
v___x_89_ = l_Lake_createParentDirs(v_val_87_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v___x_90_; 
lean_dec_ref_known(v___x_89_, 1);
lean_inc(v_val_88_);
v___x_90_ = l_Lake_createParentDirs(v_val_88_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec_ref_known(v___x_90_, 1);
v___x_91_ = lean_unsigned_to_nat(3u);
v___x_92_ = lean_mk_empty_array_with_capacity(v___x_91_);
v___x_93_ = lean_array_push(v___x_92_, v_setupFile_44_);
v___x_94_ = lean_array_push(v___x_93_, v_val_87_);
v___x_95_ = lean_array_push(v___x_94_, v_val_88_);
v___x_96_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_96_, 0, v___x_45_);
lean_ctor_set(v___x_96_, 1, v_leanir_46_);
lean_ctor_set(v___x_96_, 2, v___x_95_);
lean_ctor_set(v___x_96_, 3, v___x_47_);
lean_ctor_set(v___x_96_, 4, v___x_48_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*5, v___x_49_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*5 + 1, v___x_50_);
v___x_97_ = l_Lake_proc(v___x_96_, v___x_50_, v___x_51_, v___y_80_);
if (lean_obj_tag(v___x_97_) == 0)
{
return v___x_97_;
}
else
{
if (lean_obj_tag(v_olean_x3f_52_) == 1)
{
lean_object* v_a_98_; lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_114_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_a_99_ = lean_ctor_get(v___x_97_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_114_ == 0)
{
v___x_101_ = v___x_97_;
v_isShared_102_ = v_isSharedCheck_114_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_114_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_val_103_; lean_object* v___x_104_; 
v_val_103_ = lean_ctor_get(v_olean_x3f_52_, 0);
v___x_104_ = l_Lake_removeFileIfExists(v_val_103_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_dec_ref_known(v___x_104_, 1);
lean_del_object(v___x_101_);
v___y_76_ = v_a_98_;
v___y_77_ = v_a_99_;
goto v___jp_75_;
}
else
{
lean_object* v_a_105_; lean_object* v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
lean_dec(v_a_98_);
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
v___x_106_ = lean_io_error_to_string(v_a_105_);
v___x_107_ = 3;
v___x_108_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*1, v___x_107_);
v___x_109_ = lean_array_get_size(v_a_99_);
v___x_110_ = lean_array_push(v_a_99_, v___x_108_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_110_);
lean_ctor_set(v___x_101_, 0, v___x_109_);
v___x_112_ = v___x_101_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
else
{
lean_object* v_a_115_; lean_object* v_a_116_; 
v_a_115_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_a_115_);
v_a_116_ = lean_ctor_get(v___x_97_, 1);
lean_inc(v_a_116_);
lean_dec_ref_known(v___x_97_, 2);
v___y_76_ = v_a_115_;
v___y_77_ = v_a_116_;
goto v___jp_75_;
}
}
}
else
{
lean_object* v_a_117_; lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_val_88_);
lean_dec(v_val_87_);
lean_dec_ref(v___x_48_);
lean_dec(v___x_47_);
lean_dec_ref(v_leanir_46_);
lean_dec_ref(v___x_45_);
lean_dec_ref(v_setupFile_44_);
v_a_117_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_90_, 1);
v___x_118_ = lean_io_error_to_string(v_a_117_);
v___x_119_ = 3;
v___x_120_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_119_);
v___x_121_ = lean_array_get_size(v___y_80_);
v___x_122_ = lean_array_push(v___y_80_, v___x_120_);
v___x_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
return v___x_123_;
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v_val_88_);
lean_dec(v_val_87_);
lean_dec_ref(v___x_48_);
lean_dec(v___x_47_);
lean_dec_ref(v_leanir_46_);
lean_dec_ref(v___x_45_);
lean_dec_ref(v_setupFile_44_);
v_a_124_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_a_124_);
lean_dec_ref_known(v___x_89_, 1);
v___x_125_ = lean_io_error_to_string(v_a_124_);
v___x_126_ = 3;
v___x_127_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_127_, 0, v___x_125_);
lean_ctor_set_uint8(v___x_127_, sizeof(void*)*1, v___x_126_);
v___x_128_ = lean_array_get_size(v___y_80_);
v___x_129_ = lean_array_push(v___y_80_, v___x_127_);
v___x_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
return v___x_130_;
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
v___y_60_ = v___y_80_;
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
v___y_60_ = v___y_80_;
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
v___jp_131_:
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 1;
v___x_135_ = lean_uint32_dec_eq(v_exitCode_53_, v___x_134_);
if (v___x_135_ == 0)
{
v___y_80_ = v___y_132_;
v___y_81_ = v___y_133_;
v___y_82_ = v_exitCode_53_;
goto v___jp_79_;
}
else
{
if (v___y_133_ == 0)
{
v___y_80_ = v___y_132_;
v___y_81_ = v___y_133_;
v___y_82_ = v_exitCode_53_;
goto v___jp_79_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec_ref(v___x_48_);
lean_dec(v___x_47_);
lean_dec_ref(v_leanir_46_);
lean_dec_ref(v___x_45_);
lean_dec_ref(v_setupFile_44_);
lean_dec(v_c_x3f_43_);
lean_dec(v_ir_x3f_42_);
v___x_136_ = lean_array_get_size(v___y_132_);
v___x_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___y_132_);
return v___x_137_;
}
}
}
v___jp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_140_ = lean_array_get_size(v___y_139_);
v___x_141_ = l_Array_extract___redArg(v___y_139_, v___x_54_, v___x_140_);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_array_get_size(v___x_141_);
v___x_144_ = lean_nat_dec_lt(v___x_142_, v___x_143_);
if (v___x_144_ == 0)
{
lean_dec_ref(v___x_141_);
v___y_132_ = v___y_139_;
v___y_133_ = v___x_144_;
goto v___jp_131_;
}
else
{
if (v___x_144_ == 0)
{
lean_dec_ref(v___x_141_);
v___y_132_ = v___y_139_;
v___y_133_ = v___x_144_;
goto v___jp_131_;
}
else
{
size_t v___x_145_; size_t v___x_146_; uint8_t v___x_147_; 
v___x_145_ = ((size_t)0ULL);
v___x_146_ = lean_usize_of_nat(v___x_143_);
v___x_147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(v___x_141_, v___x_145_, v___x_146_);
lean_dec_ref(v___x_141_);
v___y_132_ = v___y_139_;
v___y_133_ = v___x_147_;
goto v___jp_131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object** _args){
lean_object* v___y_159_ = _args[0];
lean_object* v_ir_x3f_160_ = _args[1];
lean_object* v_c_x3f_161_ = _args[2];
lean_object* v_setupFile_162_ = _args[3];
lean_object* v___x_163_ = _args[4];
lean_object* v_leanir_164_ = _args[5];
lean_object* v___x_165_ = _args[6];
lean_object* v___x_166_ = _args[7];
lean_object* v___x_167_ = _args[8];
lean_object* v___x_168_ = _args[9];
lean_object* v___x_169_ = _args[10];
lean_object* v_olean_x3f_170_ = _args[11];
lean_object* v_exitCode_171_ = _args[12];
lean_object* v___x_172_ = _args[13];
lean_object* v_stderr_173_ = _args[14];
lean_object* v_____r_174_ = _args[15];
lean_object* v___y_175_ = _args[16];
lean_object* v___y_176_ = _args[17];
_start:
{
uint8_t v___y_33969__boxed_177_; uint8_t v___x_33973__boxed_178_; uint8_t v___x_33974__boxed_179_; uint32_t v_exitCode_boxed_180_; lean_object* v_res_181_; 
v___y_33969__boxed_177_ = lean_unbox(v___y_159_);
v___x_33973__boxed_178_ = lean_unbox(v___x_167_);
v___x_33974__boxed_179_ = lean_unbox(v___x_168_);
v_exitCode_boxed_180_ = lean_unbox_uint32(v_exitCode_171_);
lean_dec(v_exitCode_171_);
v_res_181_ = l_Lake_compileLeanModule___lam__0(v___y_33969__boxed_177_, v_ir_x3f_160_, v_c_x3f_161_, v_setupFile_162_, v___x_163_, v_leanir_164_, v___x_165_, v___x_166_, v___x_33973__boxed_178_, v___x_33974__boxed_179_, v___x_169_, v_olean_x3f_170_, v_exitCode_boxed_180_, v___x_172_, v_stderr_173_, v_____r_174_, v___y_175_);
lean_dec(v_olean_x3f_170_);
lean_dec(v___x_169_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(lean_object* v_a_182_, lean_object* v_b_183_, lean_object* v_relLeanFile_184_, lean_object* v_____r_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_a_189_; lean_object* v_toBaseMessage_191_; uint8_t v_isSilent_192_; 
v_toBaseMessage_191_ = lean_ctor_get(v_a_182_, 0);
lean_inc_ref(v_toBaseMessage_191_);
v_isSilent_192_ = lean_ctor_get_uint8(v_toBaseMessage_191_, sizeof(void*)*5 + 2);
if (v_isSilent_192_ == 0)
{
lean_object* v_kind_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_217_; 
v_kind_193_ = lean_ctor_get(v_a_182_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_a_182_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; 
v_unused_218_ = lean_ctor_get(v_a_182_, 0);
lean_dec(v_unused_218_);
v___x_195_ = v_a_182_;
v_isShared_196_ = v_isSharedCheck_217_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_kind_193_);
lean_dec(v_a_182_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_217_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v_pos_197_; lean_object* v_endPos_198_; uint8_t v_keepFullRange_199_; uint8_t v_severity_200_; lean_object* v_caption_201_; lean_object* v_data_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_215_; 
v_pos_197_ = lean_ctor_get(v_toBaseMessage_191_, 1);
v_endPos_198_ = lean_ctor_get(v_toBaseMessage_191_, 2);
v_keepFullRange_199_ = lean_ctor_get_uint8(v_toBaseMessage_191_, sizeof(void*)*5);
v_severity_200_ = lean_ctor_get_uint8(v_toBaseMessage_191_, sizeof(void*)*5 + 1);
v_caption_201_ = lean_ctor_get(v_toBaseMessage_191_, 3);
v_data_202_ = lean_ctor_get(v_toBaseMessage_191_, 4);
v_isSharedCheck_215_ = !lean_is_exclusive(v_toBaseMessage_191_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; 
v_unused_216_ = lean_ctor_get(v_toBaseMessage_191_, 0);
lean_dec(v_unused_216_);
v___x_204_ = v_toBaseMessage_191_;
v_isShared_205_ = v_isSharedCheck_215_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_data_202_);
lean_inc(v_caption_201_);
lean_inc(v_endPos_198_);
lean_inc(v_pos_197_);
lean_dec(v_toBaseMessage_191_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_215_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_206_ = l_Lake_mkRelPathString(v_relLeanFile_184_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_206_);
v___x_208_ = v___x_204_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_pos_197_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_endPos_198_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v_caption_201_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v_data_202_);
lean_ctor_set_uint8(v_reuseFailAlloc_214_, sizeof(void*)*5, v_keepFullRange_199_);
lean_ctor_set_uint8(v_reuseFailAlloc_214_, sizeof(void*)*5 + 1, v_severity_200_);
lean_ctor_set_uint8(v_reuseFailAlloc_214_, sizeof(void*)*5 + 2, v_isSilent_192_);
v___x_208_ = v_reuseFailAlloc_214_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_210_; 
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_208_);
v___x_210_ = v___x_195_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_kind_193_);
v___x_210_ = v_reuseFailAlloc_213_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = l_Lake_LogEntry_ofSerialMessage(v___x_210_);
v___x_212_ = lean_array_push(v___y_186_, v___x_211_);
v_a_189_ = v___x_212_;
goto v___jp_188_;
}
}
}
}
}
else
{
lean_dec_ref(v_toBaseMessage_191_);
lean_dec_ref(v_relLeanFile_184_);
lean_dec_ref(v_a_182_);
v_a_189_ = v___y_186_;
goto v___jp_188_;
}
v___jp_188_:
{
lean_object* v___x_190_; 
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_b_183_);
lean_ctor_set(v___x_190_, 1, v_a_189_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0___boxed(lean_object* v_a_219_, lean_object* v_b_220_, lean_object* v_relLeanFile_221_, lean_object* v_____r_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_219_, v_b_220_, v_relLeanFile_221_, v_____r_222_, v___y_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(lean_object* v_relLeanFile_228_, lean_object* v___x_229_, lean_object* v___x_230_, lean_object* v___x_231_, lean_object* v_a_232_, lean_object* v_b_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v_it_259_; lean_object* v_startInclusive_260_; lean_object* v_endExclusive_261_; 
if (lean_obj_tag(v_a_232_) == 0)
{
lean_object* v_currPos_279_; lean_object* v_searcher_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_303_; 
v_currPos_279_ = lean_ctor_get(v_a_232_, 0);
v_searcher_280_ = lean_ctor_get(v_a_232_, 1);
v_isSharedCheck_303_ = !lean_is_exclusive(v_a_232_);
if (v_isSharedCheck_303_ == 0)
{
v___x_282_ = v_a_232_;
v_isShared_283_ = v_isSharedCheck_303_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_searcher_280_);
lean_inc(v_currPos_279_);
lean_dec(v_a_232_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_303_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
uint8_t v_decide_284_; 
v_decide_284_ = lean_nat_dec_eq(v_searcher_280_, v___x_231_);
if (v_decide_284_ == 0)
{
uint32_t v___x_285_; uint32_t v___x_286_; uint8_t v___x_287_; 
v___x_285_ = 10;
v___x_286_ = lean_string_utf8_get_fast(v___x_229_, v_searcher_280_);
v___x_287_ = lean_uint32_dec_eq(v___x_286_, v___x_285_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = lean_string_utf8_next_fast(v___x_229_, v_searcher_280_);
lean_dec(v_searcher_280_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v___x_288_);
v___x_290_ = v___x_282_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_currPos_279_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_288_);
v___x_290_ = v_reuseFailAlloc_292_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
v_a_232_ = v___x_290_;
goto _start;
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_slice_296_; lean_object* v_nextIt_298_; 
v___x_293_ = lean_string_utf8_next_fast(v___x_229_, v_searcher_280_);
v___x_294_ = lean_nat_sub(v___x_293_, v_searcher_280_);
v___x_295_ = lean_nat_add(v_searcher_280_, v___x_294_);
lean_dec(v___x_294_);
v_slice_296_ = l_String_Slice_subslice_x21(v___x_230_, v_currPos_279_, v_searcher_280_);
lean_inc(v___x_295_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v___x_295_);
lean_ctor_set(v___x_282_, 0, v___x_295_);
v_nextIt_298_ = v___x_282_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v___x_295_);
v_nextIt_298_ = v_reuseFailAlloc_301_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v_startInclusive_299_; lean_object* v_endExclusive_300_; 
v_startInclusive_299_ = lean_ctor_get(v_slice_296_, 0);
lean_inc(v_startInclusive_299_);
v_endExclusive_300_ = lean_ctor_get(v_slice_296_, 1);
lean_inc(v_endExclusive_300_);
lean_dec_ref(v_slice_296_);
v_it_259_ = v_nextIt_298_;
v_startInclusive_260_ = v_startInclusive_299_;
v_endExclusive_261_ = v_endExclusive_300_;
goto v___jp_258_;
}
}
}
else
{
lean_object* v___x_302_; 
lean_del_object(v___x_282_);
lean_dec(v_searcher_280_);
v___x_302_ = lean_box(1);
lean_inc(v___x_231_);
v_it_259_ = v___x_302_;
v_startInclusive_260_ = v_currPos_279_;
v_endExclusive_261_ = v___x_231_;
goto v___jp_258_;
}
}
}
else
{
lean_object* v___x_304_; 
lean_dec(v___x_231_);
lean_dec_ref(v_relLeanFile_228_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_b_233_);
lean_ctor_set(v___x_304_, 1, v___y_234_);
return v___x_304_;
}
v___jp_236_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_string_append(v_b_233_, v___y_237_);
lean_dec_ref(v___y_237_);
v___x_240_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__0));
v___x_241_ = lean_string_append(v___x_239_, v___x_240_);
v_a_232_ = v___y_238_;
v_b_233_ = v___x_241_;
goto _start;
}
v___jp_243_:
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = lean_string_utf8_byte_size(v_b_233_);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_nat_dec_eq(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
v___y_237_ = v___y_244_;
v___y_238_ = v___y_245_;
goto v___jp_236_;
}
else
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_string_utf8_byte_size(v___y_244_);
v___x_250_ = lean_nat_dec_eq(v___x_249_, v___x_247_);
if (v___x_250_ == 0)
{
v___y_237_ = v___y_244_;
v___y_238_ = v___y_245_;
goto v___jp_236_;
}
else
{
lean_dec_ref(v___y_244_);
v_a_232_ = v___y_245_;
goto _start;
}
}
}
v___jp_252_:
{
if (lean_obj_tag(v___y_254_) == 0)
{
lean_object* v_a_255_; lean_object* v_a_256_; 
v_a_255_ = lean_ctor_get(v___y_254_, 0);
lean_inc(v_a_255_);
v_a_256_ = lean_ctor_get(v___y_254_, 1);
lean_inc(v_a_256_);
lean_dec_ref_known(v___y_254_, 2);
v_a_232_ = v___y_253_;
v_b_233_ = v_a_255_;
v___y_234_ = v_a_256_;
goto _start;
}
else
{
lean_dec(v___y_253_);
lean_dec(v___x_231_);
lean_dec_ref(v_relLeanFile_228_);
return v___y_254_;
}
}
v___jp_258_:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_string_utf8_extract_fast(v___x_229_, v_startInclusive_260_, v_endExclusive_261_);
lean_dec(v_endExclusive_261_);
lean_dec(v_startInclusive_260_);
lean_inc_ref(v___x_262_);
v___x_263_ = l_Lean_Json_parse(v___x_262_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_dec_ref_known(v___x_263_, 1);
v___y_244_ = v___x_262_;
v___y_245_ = v_it_259_;
goto v___jp_243_;
}
else
{
lean_object* v_a_264_; lean_object* v___x_265_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_263_, 1);
v___x_265_ = l_Lean_instFromJsonSerialMessage_fromJson(v_a_264_);
if (lean_obj_tag(v___x_265_) == 1)
{
lean_object* v_a_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
lean_dec_ref(v___x_262_);
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_265_, 1);
v___x_267_ = lean_string_utf8_byte_size(v_b_233_);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_nat_dec_eq(v___x_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_270_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__1));
v___x_271_ = lean_string_append(v___x_270_, v_b_233_);
v___x_272_ = 1;
v___x_273_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*1, v___x_272_);
v___x_274_ = lean_box(0);
v___x_275_ = lean_array_push(v___y_234_, v___x_273_);
lean_inc_ref(v_relLeanFile_228_);
v___x_276_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_266_, v_b_233_, v_relLeanFile_228_, v___x_274_, v___x_275_);
v___y_253_ = v_it_259_;
v___y_254_ = v___x_276_;
goto v___jp_252_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_box(0);
lean_inc_ref(v_relLeanFile_228_);
v___x_278_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_266_, v_b_233_, v_relLeanFile_228_, v___x_277_, v___y_234_);
v___y_253_ = v_it_259_;
v___y_254_ = v___x_278_;
goto v___jp_252_;
}
}
else
{
lean_dec_ref(v___x_265_);
v___y_244_ = v___x_262_;
v___y_245_ = v_it_259_;
goto v___jp_243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___boxed(lean_object* v_relLeanFile_305_, lean_object* v___x_306_, lean_object* v___x_307_, lean_object* v___x_308_, lean_object* v_a_309_, lean_object* v_b_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(v_relLeanFile_305_, v___x_306_, v___x_307_, v___x_308_, v_a_309_, v_b_310_, v___y_311_);
lean_dec_ref(v___x_307_);
lean_dec_ref(v___x_306_);
return v_res_313_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__1(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_315_ = ((lean_object*)(l_Lake_compileLeanModule___closed__0));
v___x_316_ = lean_unsigned_to_nat(2u);
v___x_317_ = lean_mk_empty_array_with_capacity(v___x_316_);
v___x_318_ = lean_array_push(v___x_317_, v___x_315_);
return v___x_318_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__9(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_327_ = ((lean_object*)(l_Lake_compileLeanModule___closed__8));
v___x_328_ = lean_unsigned_to_nat(2u);
v___x_329_ = lean_mk_empty_array_with_capacity(v___x_328_);
v___x_330_ = lean_array_push(v___x_329_, v___x_327_);
return v___x_330_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__11(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_332_ = ((lean_object*)(l_Lake_compileLeanModule___closed__10));
v___x_333_ = lean_unsigned_to_nat(2u);
v___x_334_ = lean_mk_empty_array_with_capacity(v___x_333_);
v___x_335_ = lean_array_push(v___x_334_, v___x_332_);
return v___x_335_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__13(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_337_ = ((lean_object*)(l_Lake_compileLeanModule___closed__12));
v___x_338_ = lean_unsigned_to_nat(2u);
v___x_339_ = lean_mk_empty_array_with_capacity(v___x_338_);
v___x_340_ = lean_array_push(v___x_339_, v___x_337_);
return v___x_340_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__15(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_342_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_343_ = lean_unsigned_to_nat(2u);
v___x_344_ = lean_mk_empty_array_with_capacity(v___x_343_);
v___x_345_ = lean_array_push(v___x_344_, v___x_342_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object* v_leanFile_346_, lean_object* v_relLeanFile_347_, lean_object* v_setup_348_, lean_object* v_setupFile_349_, lean_object* v_arts_350_, lean_object* v_leanArgs_351_, lean_object* v_leanPath_352_, lean_object* v_lean_353_, lean_object* v_leanir_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___y_358_; lean_object* v_a_359_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v_olean_x3f_365_; lean_object* v_ilean_x3f_366_; lean_object* v_ir_x3f_367_; lean_object* v_c_x3f_368_; lean_object* v_bc_x3f_369_; uint8_t v___y_371_; lean_object* v_args_372_; lean_object* v___y_373_; uint8_t v___y_462_; lean_object* v___y_463_; lean_object* v_args_464_; lean_object* v___y_478_; lean_object* v___y_479_; uint8_t v___y_480_; lean_object* v_args_494_; lean_object* v___y_495_; lean_object* v_args_502_; lean_object* v___y_503_; lean_object* v_args_516_; 
v_olean_x3f_365_ = lean_ctor_get(v_arts_350_, 1);
lean_inc(v_olean_x3f_365_);
v_ilean_x3f_366_ = lean_ctor_get(v_arts_350_, 4);
lean_inc(v_ilean_x3f_366_);
v_ir_x3f_367_ = lean_ctor_get(v_arts_350_, 6);
lean_inc(v_ir_x3f_367_);
v_c_x3f_368_ = lean_ctor_get(v_arts_350_, 7);
lean_inc(v_c_x3f_368_);
v_bc_x3f_369_ = lean_ctor_get(v_arts_350_, 8);
lean_inc(v_bc_x3f_369_);
lean_dec_ref(v_arts_350_);
v_args_516_ = lean_array_push(v_leanArgs_351_, v_leanFile_346_);
if (lean_obj_tag(v_olean_x3f_365_) == 1)
{
lean_object* v_val_517_; lean_object* v___x_518_; 
v_val_517_ = lean_ctor_get(v_olean_x3f_365_, 0);
lean_inc(v_val_517_);
v___x_518_ = l_Lake_createParentDirs(v_val_517_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec_ref_known(v___x_518_, 1);
v___x_519_ = lean_obj_once(&l_Lake_compileLeanModule___closed__15, &l_Lake_compileLeanModule___closed__15_once, _init_l_Lake_compileLeanModule___closed__15);
lean_inc(v_val_517_);
v___x_520_ = lean_array_push(v___x_519_, v_val_517_);
v___x_521_ = l_Array_append___redArg(v_args_516_, v___x_520_);
lean_dec_ref(v___x_520_);
v_args_502_ = v___x_521_;
v___y_503_ = v_a_355_;
goto v___jp_501_;
}
else
{
lean_object* v_a_522_; lean_object* v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec_ref_known(v_olean_x3f_365_, 1);
lean_dec_ref(v_args_516_);
lean_dec(v_bc_x3f_369_);
lean_dec(v_c_x3f_368_);
lean_dec(v_ir_x3f_367_);
lean_dec(v_ilean_x3f_366_);
lean_dec_ref(v_leanir_354_);
lean_dec_ref(v_lean_353_);
lean_dec(v_leanPath_352_);
lean_dec_ref(v_setupFile_349_);
lean_dec_ref(v_setup_348_);
lean_dec_ref(v_relLeanFile_347_);
v_a_522_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_518_, 1);
v___x_523_ = lean_io_error_to_string(v_a_522_);
v___x_524_ = 3;
v___x_525_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*1, v___x_524_);
v___x_526_ = lean_array_get_size(v_a_355_);
v___x_527_ = lean_array_push(v_a_355_, v___x_525_);
v___x_528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
return v___x_528_;
}
}
else
{
v_args_502_ = v_args_516_;
v___y_503_ = v_a_355_;
goto v___jp_501_;
}
v___jp_357_:
{
lean_object* v___x_360_; 
v___x_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_360_, 0, v___y_358_);
lean_ctor_set(v___x_360_, 1, v_a_359_);
return v___x_360_;
}
v___jp_361_:
{
if (lean_obj_tag(v___y_363_) == 0)
{
lean_dec(v___y_362_);
return v___y_363_;
}
else
{
lean_object* v_a_364_; 
v_a_364_ = lean_ctor_get(v___y_363_, 1);
lean_inc(v_a_364_);
lean_dec_ref_known(v___y_363_, 2);
v___y_358_ = v___y_362_;
v_a_359_ = v_a_364_;
goto v___jp_357_;
}
}
v___jp_370_:
{
lean_object* v___x_374_; 
lean_inc_ref(v_setupFile_349_);
v___x_374_ = l_Lake_createParentDirs(v_setupFile_349_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec_ref_known(v___x_374_, 1);
v___x_375_ = l_Lean_instToJsonModuleSetup_toJson(v_setup_348_);
v___x_376_ = lean_unsigned_to_nat(80u);
v___x_377_ = l_Lean_Json_pretty(v___x_375_, v___x_376_);
v___x_378_ = l_IO_FS_writeFile(v_setupFile_349_, v___x_377_);
lean_dec_ref(v___x_377_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_445_; 
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v___x_378_, 0);
lean_dec(v_unused_446_);
v___x_380_ = v___x_378_;
v_isShared_381_ = v_isSharedCheck_445_;
goto v_resetjp_379_;
}
else
{
lean_dec(v___x_378_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_445_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_382_ = lean_obj_once(&l_Lake_compileLeanModule___closed__1, &l_Lake_compileLeanModule___closed__1_once, _init_l_Lake_compileLeanModule___closed__1);
lean_inc_ref(v_setupFile_349_);
v___x_383_ = lean_array_push(v___x_382_, v_setupFile_349_);
v___x_384_ = l_Array_append___redArg(v_args_372_, v___x_383_);
lean_dec_ref(v___x_383_);
v___x_385_ = ((lean_object*)(l_Lake_compileLeanModule___closed__2));
v___x_386_ = lean_array_push(v___x_384_, v___x_385_);
v___x_387_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_388_ = lean_box(0);
v___x_389_ = ((lean_object*)(l_Lake_compileLeanModule___closed__4));
v___x_390_ = l_System_SearchPath_toString(v_leanPath_352_);
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 1);
lean_ctor_set(v___x_380_, 0, v___x_390_);
v___x_392_ = v___x_380_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_444_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; uint8_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_389_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_mk_empty_array_with_capacity(v___x_394_);
v___x_396_ = lean_array_push(v___x_395_, v___x_393_);
v___x_397_ = 1;
v___x_398_ = 0;
lean_inc_ref(v___x_396_);
lean_inc_ref(v_lean_353_);
v___x_399_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_399_, 0, v___x_387_);
lean_ctor_set(v___x_399_, 1, v_lean_353_);
lean_ctor_set(v___x_399_, 2, v___x_386_);
lean_ctor_set(v___x_399_, 3, v___x_388_);
lean_ctor_set(v___x_399_, 4, v___x_396_);
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*5, v___x_397_);
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*5 + 1, v___x_398_);
v___x_400_ = lean_array_get_size(v___y_373_);
lean_inc_ref(v___x_399_);
v___x_401_ = l_Lake_mkCmdLog(v___x_399_);
v___x_402_ = 0;
v___x_403_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*1, v___x_402_);
v___x_404_ = lean_array_push(v___y_373_, v___x_403_);
v___x_405_ = l_IO_Process_output(v___x_399_, v___x_388_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; uint32_t v_exitCode_407_; lean_object* v_stdout_408_; lean_object* v_stderr_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
lean_dec_ref(v_lean_353_);
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 1);
v_exitCode_407_ = lean_ctor_get_uint32(v_a_406_, sizeof(void*)*2);
v_stdout_408_ = lean_ctor_get(v_a_406_, 0);
lean_inc_ref(v_stdout_408_);
v_stderr_409_ = lean_ctor_get(v_a_406_, 1);
lean_inc_ref(v_stderr_409_);
lean_dec(v_a_406_);
v___x_410_ = lean_array_get_size(v___x_404_);
v___x_411_ = lean_string_utf8_byte_size(v_stdout_408_);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_nat_dec_eq(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_inc_ref(v_stdout_408_);
v___x_414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_414_, 0, v_stdout_408_);
lean_ctor_set(v___x_414_, 1, v___x_412_);
lean_ctor_set(v___x_414_, 2, v___x_411_);
v___x_415_ = ((lean_object*)(l_Lake_compileLeanModule___closed__5));
v___x_416_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1(v___x_414_);
v___x_417_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(v_relLeanFile_347_, v_stdout_408_, v___x_414_, v___x_411_, v___x_416_, v___x_415_, v___x_404_);
lean_dec_ref_known(v___x_414_, 3);
lean_dec_ref(v_stdout_408_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v_a_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
v_a_419_ = lean_ctor_get(v___x_417_, 1);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_417_, 2);
v___x_420_ = lean_string_utf8_byte_size(v_a_418_);
v___x_421_ = lean_nat_dec_eq(v___x_420_, v___x_412_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_422_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__1));
v___x_423_ = lean_string_append(v___x_422_, v_a_418_);
lean_dec(v_a_418_);
v___x_424_ = 1;
v___x_425_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*1, v___x_424_);
v___x_426_ = lean_box(0);
v___x_427_ = lean_array_push(v_a_419_, v___x_425_);
v___x_428_ = l_Lake_compileLeanModule___lam__0(v___y_371_, v_ir_x3f_367_, v_c_x3f_368_, v_setupFile_349_, v___x_387_, v_leanir_354_, v___x_388_, v___x_396_, v___x_397_, v___x_398_, v___x_388_, v_olean_x3f_365_, v_exitCode_407_, v___x_410_, v_stderr_409_, v___x_426_, v___x_427_);
lean_dec(v_olean_x3f_365_);
v___y_362_ = v___x_400_;
v___y_363_ = v___x_428_;
goto v___jp_361_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v_a_418_);
v___x_429_ = lean_box(0);
v___x_430_ = l_Lake_compileLeanModule___lam__0(v___y_371_, v_ir_x3f_367_, v_c_x3f_368_, v_setupFile_349_, v___x_387_, v_leanir_354_, v___x_388_, v___x_396_, v___x_397_, v___x_398_, v___x_388_, v_olean_x3f_365_, v_exitCode_407_, v___x_410_, v_stderr_409_, v___x_429_, v_a_419_);
lean_dec(v_olean_x3f_365_);
v___y_362_ = v___x_400_;
v___y_363_ = v___x_430_;
goto v___jp_361_;
}
}
else
{
lean_object* v_a_431_; 
lean_dec_ref(v_stderr_409_);
lean_dec_ref(v___x_396_);
lean_dec(v_c_x3f_368_);
lean_dec(v_ir_x3f_367_);
lean_dec(v_olean_x3f_365_);
lean_dec_ref(v_leanir_354_);
lean_dec_ref(v_setupFile_349_);
v_a_431_ = lean_ctor_get(v___x_417_, 1);
lean_inc(v_a_431_);
lean_dec_ref_known(v___x_417_, 2);
v___y_358_ = v___x_400_;
v_a_359_ = v_a_431_;
goto v___jp_357_;
}
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref(v_stdout_408_);
lean_dec_ref(v_relLeanFile_347_);
v___x_432_ = lean_box(0);
v___x_433_ = l_Lake_compileLeanModule___lam__0(v___y_371_, v_ir_x3f_367_, v_c_x3f_368_, v_setupFile_349_, v___x_387_, v_leanir_354_, v___x_388_, v___x_396_, v___x_397_, v___x_398_, v___x_388_, v_olean_x3f_365_, v_exitCode_407_, v___x_410_, v_stderr_409_, v___x_432_, v___x_404_);
lean_dec(v_olean_x3f_365_);
v___y_362_ = v___x_400_;
v___y_363_ = v___x_433_;
goto v___jp_361_;
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec_ref(v___x_396_);
lean_dec(v_c_x3f_368_);
lean_dec(v_ir_x3f_367_);
lean_dec(v_olean_x3f_365_);
lean_dec_ref(v_leanir_354_);
lean_dec_ref(v_setupFile_349_);
lean_dec_ref(v_relLeanFile_347_);
v_a_434_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_405_, 1);
v___x_435_ = ((lean_object*)(l_Lake_compileLeanModule___closed__6));
v___x_436_ = lean_string_append(v___x_435_, v_lean_353_);
lean_dec_ref(v_lean_353_);
v___x_437_ = ((lean_object*)(l_Lake_compileLeanModule___closed__7));
v___x_438_ = lean_string_append(v___x_436_, v___x_437_);
v___x_439_ = lean_io_error_to_string(v_a_434_);
v___x_440_ = lean_string_append(v___x_438_, v___x_439_);
lean_dec_ref(v___x_439_);
v___x_441_ = 3;
v___x_442_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*1, v___x_441_);
v___x_443_ = lean_array_push(v___x_404_, v___x_442_);
v___y_358_ = v___x_400_;
v_a_359_ = v___x_443_;
goto v___jp_357_;
}
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec_ref(v_args_372_);
lean_dec(v_c_x3f_368_);
lean_dec(v_ir_x3f_367_);
lean_dec(v_olean_x3f_365_);
lean_dec_ref(v_leanir_354_);
lean_dec_ref(v_lean_353_);
lean_dec(v_leanPath_352_);
lean_dec_ref(v_setupFile_349_);
lean_dec_ref(v_relLeanFile_347_);
v_a_447_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_378_, 1);
v___x_448_ = lean_io_error_to_string(v_a_447_);
v___x_449_ = 3;
v___x_450_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*1, v___x_449_);
v___x_451_ = lean_array_get_size(v___y_373_);
v___x_452_ = lean_array_push(v___y_373_, v___x_450_);
v___x_453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
return v___x_453_;
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_455_; uint8_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec_ref(v_args_372_);
lean_dec(v_c_x3f_368_);
lean_dec(v_ir_x3f_367_);
lean_dec(v_olean_x3f_365_);
lean_dec_ref(v_leanir_354_);
lean_dec_ref(v_lean_353_);
lean_dec(v_leanPath_352_);
lean_dec_ref(v_setupFile_349_);
lean_dec_ref(v_setup_348_);
lean_dec_ref(v_relLeanFile_347_);
v_a_454_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_374_, 1);
v___x_455_ = lean_io_error_to_string(v_a_454_);
v___x_456_ = 3;
v___x_457_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*1, v___x_456_);
v___x_458_ = lean_array_get_size(v___y_373_);
v___x_459_ = lean_array_push(v___y_373_, v___x_457_);
v___x_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
return v___x_460_;
}
}
v___jp_461_:
{
if (lean_obj_tag(v_bc_x3f_369_) == 1)
{
lean_object* v_val_465_; lean_object* v___x_466_; 
v_val_465_ = lean_ctor_get(v_bc_x3f_369_, 0);
lean_inc_n(v_val_465_, 2);
lean_dec_ref_known(v_bc_x3f_369_, 1);
v___x_466_ = l_Lake_createParentDirs(v_val_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref_known(v___x_466_, 1);
v___x_467_ = lean_obj_once(&l_Lake_compileLeanModule___closed__9, &l_Lake_compileLeanModule___closed__9_once, _init_l_Lake_compileLeanModule___closed__9);
v___x_468_ = lean_array_push(v___x_467_, v_val_465_);
v___x_469_ = l_Array_append___redArg(v_args_464_, v___x_468_);
lean_dec_ref(v___x_468_);
v___y_371_ = v___y_462_;
v_args_372_ = v___x_469_;
v___y_373_ = v___y_463_;
goto v___jp_370_;
}
else
{
lean_object* v_a_470_; lean_object* v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_val_465_);
lean_dec_ref(v_args_464_);
lean_dec(v_c_x3f_368_);
lean_dec(v_ir_x3f_367_);
lean_dec(v_olean_x3f_365_);
lean_dec_ref(v_leanir_354_);
lean_dec_ref(v_lean_353_);
lean_dec(v_leanPath_352_);
lean_dec_ref(v_setupFile_349_);
lean_dec_ref(v_setup_348_);
lean_dec_ref(v_relLeanFile_347_);
v_a_470_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_466_, 1);
v___x_471_ = lean_io_error_to_string(v_a_470_);
v___x_472_ = 3;
v___x_473_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*1, v___x_472_);
v___x_474_ = lean_array_get_size(v___y_463_);
v___x_475_ = lean_array_push(v___y_463_, v___x_473_);
v___x_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
return v___x_476_;
}
}
else
{
lean_dec(v_bc_x3f_369_);
v___y_371_ = v___y_462_;
v_args_372_ = v_args_464_;
v___y_373_ = v___y_463_;
goto v___jp_370_;
}
}
v___jp_477_:
{
if (lean_obj_tag(v_c_x3f_368_) == 1)
{
lean_object* v_val_481_; lean_object* v___x_482_; 
v_val_481_ = lean_ctor_get(v_c_x3f_368_, 0);
lean_inc(v_val_481_);
v___x_482_ = l_Lake_createParentDirs(v_val_481_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec_ref_known(v___x_482_, 1);
v___x_483_ = lean_obj_once(&l_Lake_compileLeanModule___closed__11, &l_Lake_compileLeanModule___closed__11_once, _init_l_Lake_compileLeanModule___closed__11);
lean_inc(v_val_481_);
v___x_484_ = lean_array_push(v___x_483_, v_val_481_);
v___x_485_ = l_Array_append___redArg(v___y_478_, v___x_484_);
lean_dec_ref(v___x_484_);
v___y_462_ = v___y_480_;
v___y_463_ = v___y_479_;
v_args_464_ = v___x_485_;
goto v___jp_461_;
}
else
{
lean_object* v_a_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec_ref_known(v_c_x3f_368_, 1);
lean_dec_ref(v___y_478_);
lean_dec(v_bc_x3f_369_);
lean_dec(v_ir_x3f_367_);
lean_dec(v_olean_x3f_365_);
lean_dec_ref(v_leanir_354_);
lean_dec_ref(v_lean_353_);
lean_dec(v_leanPath_352_);
lean_dec_ref(v_setupFile_349_);
lean_dec_ref(v_setup_348_);
lean_dec_ref(v_relLeanFile_347_);
v_a_486_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_482_, 1);
v___x_487_ = lean_io_error_to_string(v_a_486_);
v___x_488_ = 3;
v___x_489_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*1, v___x_488_);
v___x_490_ = lean_array_get_size(v___y_479_);
v___x_491_ = lean_array_push(v___y_479_, v___x_489_);
v___x_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
return v___x_492_;
}
}
else
{
v___y_462_ = v___y_480_;
v___y_463_ = v___y_479_;
v_args_464_ = v___y_478_;
goto v___jp_461_;
}
}
v___jp_493_:
{
uint8_t v_isModule_496_; 
v_isModule_496_ = lean_ctor_get_uint8(v_setup_348_, sizeof(void*)*7);
if (v_isModule_496_ == 0)
{
v___y_478_ = v_args_494_;
v___y_479_ = v___y_495_;
v___y_480_ = v_isModule_496_;
goto v___jp_477_;
}
else
{
lean_object* v_options_497_; lean_object* v_opts_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_options_497_ = lean_ctor_get(v_setup_348_, 6);
lean_inc(v_options_497_);
v_opts_498_ = l_Lean_LeanOptions_toOptions(v_options_497_);
v___x_499_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_500_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(v_opts_498_, v___x_499_);
lean_dec_ref(v_opts_498_);
if (v___x_500_ == 0)
{
v___y_478_ = v_args_494_;
v___y_479_ = v___y_495_;
v___y_480_ = v___x_500_;
goto v___jp_477_;
}
else
{
v___y_462_ = v___x_500_;
v___y_463_ = v___y_495_;
v_args_464_ = v_args_494_;
goto v___jp_461_;
}
}
}
v___jp_501_:
{
if (lean_obj_tag(v_ilean_x3f_366_) == 1)
{
lean_object* v_val_504_; lean_object* v___x_505_; 
v_val_504_ = lean_ctor_get(v_ilean_x3f_366_, 0);
lean_inc_n(v_val_504_, 2);
lean_dec_ref_known(v_ilean_x3f_366_, 1);
v___x_505_ = l_Lake_createParentDirs(v_val_504_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec_ref_known(v___x_505_, 1);
v___x_506_ = lean_obj_once(&l_Lake_compileLeanModule___closed__13, &l_Lake_compileLeanModule___closed__13_once, _init_l_Lake_compileLeanModule___closed__13);
v___x_507_ = lean_array_push(v___x_506_, v_val_504_);
v___x_508_ = l_Array_append___redArg(v_args_502_, v___x_507_);
lean_dec_ref(v___x_507_);
v_args_494_ = v___x_508_;
v___y_495_ = v___y_503_;
goto v___jp_493_;
}
else
{
lean_object* v_a_509_; lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v_val_504_);
lean_dec_ref(v_args_502_);
lean_dec(v_bc_x3f_369_);
lean_dec(v_c_x3f_368_);
lean_dec(v_ir_x3f_367_);
lean_dec(v_olean_x3f_365_);
lean_dec_ref(v_leanir_354_);
lean_dec_ref(v_lean_353_);
lean_dec(v_leanPath_352_);
lean_dec_ref(v_setupFile_349_);
lean_dec_ref(v_setup_348_);
lean_dec_ref(v_relLeanFile_347_);
v_a_509_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_505_, 1);
v___x_510_ = lean_io_error_to_string(v_a_509_);
v___x_511_ = 3;
v___x_512_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*1, v___x_511_);
v___x_513_ = lean_array_get_size(v___y_503_);
v___x_514_ = lean_array_push(v___y_503_, v___x_512_);
v___x_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
return v___x_515_;
}
}
else
{
lean_dec(v_ilean_x3f_366_);
v_args_494_ = v_args_502_;
v___y_495_ = v___y_503_;
goto v___jp_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object* v_leanFile_529_, lean_object* v_relLeanFile_530_, lean_object* v_setup_531_, lean_object* v_setupFile_532_, lean_object* v_arts_533_, lean_object* v_leanArgs_534_, lean_object* v_leanPath_535_, lean_object* v_lean_536_, lean_object* v_leanir_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lake_compileLeanModule(v_leanFile_529_, v_relLeanFile_530_, v_setup_531_, v_setupFile_532_, v_arts_533_, v_leanArgs_534_, v_leanPath_535_, v_lean_536_, v_leanir_537_, v_a_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2(lean_object* v_relLeanFile_541_, lean_object* v___x_542_, lean_object* v___x_543_, lean_object* v___x_544_, lean_object* v_inst_545_, lean_object* v_R_546_, lean_object* v_a_547_, lean_object* v_b_548_, lean_object* v_c_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(v_relLeanFile_541_, v___x_542_, v___x_543_, v___x_544_, v_a_547_, v_b_548_, v___y_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___boxed(lean_object* v_relLeanFile_553_, lean_object* v___x_554_, lean_object* v___x_555_, lean_object* v___x_556_, lean_object* v_inst_557_, lean_object* v_R_558_, lean_object* v_a_559_, lean_object* v_b_560_, lean_object* v_c_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2(v_relLeanFile_553_, v___x_554_, v___x_555_, v___x_556_, v_inst_557_, v_R_558_, v_a_559_, v_b_560_, v_c_561_, v___y_562_);
lean_dec_ref(v___x_555_);
lean_dec_ref(v___x_554_);
return v_res_564_;
}
}
static lean_object* _init_l_Lake_compileO___closed__0(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_565_ = ((lean_object*)(l_Lake_compileLeanModule___closed__10));
v___x_566_ = lean_unsigned_to_nat(4u);
v___x_567_ = lean_mk_empty_array_with_capacity(v___x_566_);
v___x_568_ = lean_array_push(v___x_567_, v___x_565_);
return v___x_568_;
}
}
static lean_object* _init_l_Lake_compileO___closed__1(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_570_ = lean_obj_once(&l_Lake_compileO___closed__0, &l_Lake_compileO___closed__0_once, _init_l_Lake_compileO___closed__0);
v___x_571_ = lean_array_push(v___x_570_, v___x_569_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object* v_oFile_574_, lean_object* v_srcFile_575_, lean_object* v_moreArgs_576_, lean_object* v_compiler_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_580_; 
lean_inc_ref(v_oFile_574_);
v___x_580_ = l_Lake_createParentDirs(v_oFile_574_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec_ref_known(v___x_580_, 1);
v___x_581_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_582_ = lean_obj_once(&l_Lake_compileO___closed__1, &l_Lake_compileO___closed__1_once, _init_l_Lake_compileO___closed__1);
v___x_583_ = lean_array_push(v___x_582_, v_oFile_574_);
v___x_584_ = lean_array_push(v___x_583_, v_srcFile_575_);
v___x_585_ = l_Array_append___redArg(v___x_584_, v_moreArgs_576_);
v___x_586_ = lean_box(0);
v___x_587_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_588_ = 1;
v___x_589_ = 0;
v___x_590_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_590_, 0, v___x_581_);
lean_ctor_set(v___x_590_, 1, v_compiler_577_);
lean_ctor_set(v___x_590_, 2, v___x_585_);
lean_ctor_set(v___x_590_, 3, v___x_586_);
lean_ctor_set(v___x_590_, 4, v___x_587_);
lean_ctor_set_uint8(v___x_590_, sizeof(void*)*5, v___x_588_);
lean_ctor_set_uint8(v___x_590_, sizeof(void*)*5 + 1, v___x_589_);
v___x_591_ = l_Lake_proc(v___x_590_, v___x_589_, v___x_586_, v_a_578_);
return v___x_591_;
}
else
{
lean_object* v_a_592_; lean_object* v___x_593_; uint8_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec_ref(v_compiler_577_);
lean_dec_ref(v_srcFile_575_);
lean_dec_ref(v_oFile_574_);
v_a_592_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_580_, 1);
v___x_593_ = lean_io_error_to_string(v_a_592_);
v___x_594_ = 3;
v___x_595_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*1, v___x_594_);
v___x_596_ = lean_array_get_size(v_a_578_);
v___x_597_ = lean_array_push(v_a_578_, v___x_595_);
v___x_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object* v_oFile_599_, lean_object* v_srcFile_600_, lean_object* v_moreArgs_601_, lean_object* v_compiler_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lake_compileO(v_oFile_599_, v_srcFile_600_, v_moreArgs_601_, v_compiler_602_, v_a_603_);
lean_dec_ref(v_moreArgs_601_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(lean_object* v___x_606_, lean_object* v___y_607_, lean_object* v_a_608_, lean_object* v_b_609_){
_start:
{
uint8_t v_decide_610_; 
v_decide_610_ = lean_nat_dec_eq(v_a_608_, v___x_606_);
if (v_decide_610_ == 0)
{
uint32_t v___x_611_; lean_object* v___x_612_; uint32_t v___x_613_; uint8_t v___x_618_; 
v___x_611_ = lean_string_utf8_get_fast(v___y_607_, v_a_608_);
v___x_612_ = lean_string_utf8_next_fast(v___y_607_, v_a_608_);
lean_dec(v_a_608_);
v___x_613_ = 92;
v___x_618_ = lean_uint32_dec_eq(v___x_611_, v___x_613_);
if (v___x_618_ == 0)
{
uint32_t v___x_619_; uint8_t v___x_620_; 
v___x_619_ = 34;
v___x_620_ = lean_uint32_dec_eq(v___x_611_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
v___x_621_ = lean_string_push(v_b_609_, v___x_611_);
v_a_608_ = v___x_612_;
v_b_609_ = v___x_621_;
goto _start;
}
else
{
goto v___jp_614_;
}
}
else
{
goto v___jp_614_;
}
v___jp_614_:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_string_push(v_b_609_, v___x_613_);
v___x_616_ = lean_string_push(v___x_615_, v___x_611_);
v_a_608_ = v___x_612_;
v_b_609_ = v___x_616_;
goto _start;
}
}
else
{
lean_dec(v_a_608_);
return v_b_609_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg___boxed(lean_object* v___x_623_, lean_object* v___y_624_, lean_object* v_a_625_, lean_object* v_b_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_623_, v___y_624_, v_a_625_, v_b_626_);
lean_dec_ref(v___y_624_);
lean_dec(v___x_623_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(lean_object* v_a_630_, lean_object* v_as_631_, size_t v_i_632_, size_t v_stop_633_, lean_object* v_b_634_, lean_object* v___y_635_){
_start:
{
uint8_t v___x_637_; 
v___x_637_ = lean_usize_dec_eq(v_i_632_, v_stop_633_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_638_ = lean_array_uget_borrowed(v_as_631_, v_i_632_);
v___x_639_ = ((lean_object*)(l_Lake_compileLeanModule___closed__5));
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_string_utf8_byte_size(v___x_638_);
lean_inc(v___x_638_);
v___x_642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_642_, 0, v___x_638_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
lean_ctor_set(v___x_642_, 2, v___x_641_);
v___x_643_ = l_String_Slice_positions(v___x_642_);
lean_dec_ref_known(v___x_642_, 3);
v___x_644_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_641_, v___x_638_, v___x_643_, v___x_639_);
v___x_645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0));
v___x_646_ = lean_string_append(v___x_645_, v___x_644_);
lean_dec_ref(v___x_644_);
v___x_647_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1));
v___x_648_ = lean_string_append(v___x_646_, v___x_647_);
v___x_649_ = lean_io_prim_handle_put_str(v_a_630_, v___x_648_);
lean_dec_ref(v___x_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; size_t v___x_651_; size_t v___x_652_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_add(v_i_632_, v___x_651_);
v_i_632_ = v___x_652_;
v_b_634_ = v_a_650_;
goto _start;
}
else
{
lean_object* v_a_654_; lean_object* v___x_655_; uint8_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_a_654_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_649_, 1);
v___x_655_ = lean_io_error_to_string(v_a_654_);
v___x_656_ = 3;
v___x_657_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set_uint8(v___x_657_, sizeof(void*)*1, v___x_656_);
v___x_658_ = lean_array_get_size(v___y_635_);
v___x_659_ = lean_array_push(v___y_635_, v___x_657_);
v___x_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
return v___x_660_;
}
}
else
{
lean_object* v___x_661_; 
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v_b_634_);
lean_ctor_set(v___x_661_, 1, v___y_635_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___boxed(lean_object* v_a_662_, lean_object* v_as_663_, lean_object* v_i_664_, lean_object* v_stop_665_, lean_object* v_b_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
size_t v_i_boxed_669_; size_t v_stop_boxed_670_; lean_object* v_res_671_; 
v_i_boxed_669_ = lean_unbox_usize(v_i_664_);
lean_dec(v_i_664_);
v_stop_boxed_670_ = lean_unbox_usize(v_stop_665_);
lean_dec(v_stop_665_);
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_662_, v_as_663_, v_i_boxed_669_, v_stop_boxed_670_, v_b_666_, v___y_667_);
lean_dec_ref(v_as_663_);
lean_dec(v_a_662_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object* v_basePath_674_, lean_object* v_args_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___x_678_; lean_object* v_rspFile_679_; lean_object* v_a_681_; lean_object* v___y_689_; uint8_t v___x_700_; lean_object* v___x_701_; 
v___x_678_ = ((lean_object*)(l_Lake_mkArgs___closed__0));
v_rspFile_679_ = l_System_FilePath_addExtension(v_basePath_674_, v___x_678_);
v___x_700_ = 1;
v___x_701_ = lean_io_prim_handle_mk(v_rspFile_679_, v___x_700_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_array_get_size(v_args_675_);
v___x_705_ = lean_nat_dec_lt(v___x_703_, v___x_704_);
if (v___x_705_ == 0)
{
lean_dec(v_a_702_);
v_a_681_ = v_a_676_;
goto v___jp_680_;
}
else
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_box(0);
v___x_707_ = lean_nat_dec_le(v___x_704_, v___x_704_);
if (v___x_707_ == 0)
{
if (v___x_705_ == 0)
{
lean_dec(v_a_702_);
v_a_681_ = v_a_676_;
goto v___jp_680_;
}
else
{
size_t v___x_708_; size_t v___x_709_; lean_object* v___x_710_; 
v___x_708_ = ((size_t)0ULL);
v___x_709_ = lean_usize_of_nat(v___x_704_);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_702_, v_args_675_, v___x_708_, v___x_709_, v___x_706_, v_a_676_);
lean_dec(v_a_702_);
v___y_689_ = v___x_710_;
goto v___jp_688_;
}
}
else
{
size_t v___x_711_; size_t v___x_712_; lean_object* v___x_713_; 
v___x_711_ = ((size_t)0ULL);
v___x_712_ = lean_usize_of_nat(v___x_704_);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_702_, v_args_675_, v___x_711_, v___x_712_, v___x_706_, v_a_676_);
lean_dec(v_a_702_);
v___y_689_ = v___x_713_;
goto v___jp_688_;
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_715_; uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec_ref(v_rspFile_679_);
v_a_714_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v___x_701_, 1);
v___x_715_ = lean_io_error_to_string(v_a_714_);
v___x_716_ = 3;
v___x_717_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*1, v___x_716_);
v___x_718_ = lean_array_get_size(v_a_676_);
v___x_719_ = lean_array_push(v_a_676_, v___x_717_);
v___x_720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
return v___x_720_;
}
v___jp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_682_ = ((lean_object*)(l_Lake_mkArgs___closed__1));
v___x_683_ = lean_string_append(v___x_682_, v_rspFile_679_);
lean_dec_ref(v_rspFile_679_);
v___x_684_ = lean_unsigned_to_nat(1u);
v___x_685_ = lean_mk_empty_array_with_capacity(v___x_684_);
v___x_686_ = lean_array_push(v___x_685_, v___x_683_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v_a_681_);
return v___x_687_;
}
v___jp_688_:
{
if (lean_obj_tag(v___y_689_) == 0)
{
lean_object* v_a_690_; 
v_a_690_ = lean_ctor_get(v___y_689_, 1);
lean_inc(v_a_690_);
lean_dec_ref_known(v___y_689_, 2);
v_a_681_ = v_a_690_;
goto v___jp_680_;
}
else
{
lean_object* v_a_691_; lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec_ref(v_rspFile_679_);
v_a_691_ = lean_ctor_get(v___y_689_, 0);
v_a_692_ = lean_ctor_get(v___y_689_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v___y_689_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___y_689_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_inc(v_a_691_);
lean_dec(v___y_689_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_691_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs___boxed(lean_object* v_basePath_721_, lean_object* v_args_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lake_mkArgs(v_basePath_721_, v_args_722_, v_a_723_);
lean_dec_ref(v_args_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(lean_object* v___x_726_, lean_object* v___x_727_, lean_object* v___y_728_, lean_object* v_inst_729_, lean_object* v_R_730_, lean_object* v_a_731_, lean_object* v_b_732_, lean_object* v_c_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_727_, v___y_728_, v_a_731_, v_b_732_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(lean_object* v___x_735_, lean_object* v___x_736_, lean_object* v___y_737_, lean_object* v_inst_738_, lean_object* v_R_739_, lean_object* v_a_740_, lean_object* v_b_741_, lean_object* v_c_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(v___x_735_, v___x_736_, v___y_737_, v_inst_738_, v_R_739_, v_a_740_, v_b_741_, v_c_742_);
lean_dec_ref(v___y_737_);
lean_dec(v___x_736_);
lean_dec_ref(v___x_735_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(size_t v_sz_744_, size_t v_i_745_, lean_object* v_bs_746_){
_start:
{
uint8_t v___x_747_; 
v___x_747_ = lean_usize_dec_lt(v_i_745_, v_sz_744_);
if (v___x_747_ == 0)
{
return v_bs_746_;
}
else
{
lean_object* v_v_748_; lean_object* v___x_749_; lean_object* v_bs_x27_750_; size_t v___x_751_; size_t v___x_752_; lean_object* v___x_753_; 
v_v_748_ = lean_array_uget(v_bs_746_, v_i_745_);
v___x_749_ = lean_unsigned_to_nat(0u);
v_bs_x27_750_ = lean_array_uset(v_bs_746_, v_i_745_, v___x_749_);
v___x_751_ = ((size_t)1ULL);
v___x_752_ = lean_usize_add(v_i_745_, v___x_751_);
v___x_753_ = lean_array_uset(v_bs_x27_750_, v_i_745_, v_v_748_);
v_i_745_ = v___x_752_;
v_bs_746_ = v___x_753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0___boxed(lean_object* v_sz_755_, lean_object* v_i_756_, lean_object* v_bs_757_){
_start:
{
size_t v_sz_boxed_758_; size_t v_i_boxed_759_; lean_object* v_res_760_; 
v_sz_boxed_758_ = lean_unbox_usize(v_sz_755_);
lean_dec(v_sz_755_);
v_i_boxed_759_ = lean_unbox_usize(v_i_756_);
lean_dec(v_i_756_);
v_res_760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_boxed_758_, v_i_boxed_759_, v_bs_757_);
return v_res_760_;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__3(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((lean_object*)(l_Lake_compileStaticLib___closed__2));
v___x_768_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_769_ = lean_array_push(v___x_768_, v___x_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object* v_libFile_770_, lean_object* v_oFiles_771_, lean_object* v_ar_772_, uint8_t v_thin_773_, lean_object* v_a_774_){
_start:
{
lean_object* v___x_776_; 
lean_inc_ref(v_libFile_770_);
v___x_776_ = l_Lake_createParentDirs(v_libFile_770_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_777_; 
lean_dec_ref_known(v___x_776_, 1);
v___x_777_ = l_Lake_removeFileIfExists(v_libFile_770_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v___x_778_; uint8_t v___x_779_; lean_object* v___y_781_; 
lean_dec_ref_known(v___x_777_, 1);
v___x_778_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_779_ = 1;
if (v_thin_773_ == 0)
{
v___y_781_ = v___x_778_;
goto v___jp_780_;
}
else
{
lean_object* v___x_805_; 
v___x_805_ = lean_obj_once(&l_Lake_compileStaticLib___closed__3, &l_Lake_compileStaticLib___closed__3_once, _init_l_Lake_compileStaticLib___closed__3);
v___y_781_ = v___x_805_;
goto v___jp_780_;
}
v___jp_780_:
{
size_t v_sz_782_; size_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_sz_782_ = lean_array_size(v_oFiles_771_);
v___x_783_ = ((size_t)0ULL);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_782_, v___x_783_, v_oFiles_771_);
lean_inc_ref(v_libFile_770_);
v___x_785_ = l_Lake_mkArgs(v_libFile_770_, v___x_784_, v_a_774_);
lean_dec_ref(v___x_784_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
v_a_787_ = lean_ctor_get(v___x_785_, 1);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_785_, 2);
lean_inc_ref(v___y_781_);
v___x_788_ = lean_array_push(v___y_781_, v_libFile_770_);
v___x_789_ = l_Array_append___redArg(v___x_788_, v_a_786_);
lean_dec(v_a_786_);
v___x_790_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_791_ = lean_box(0);
v___x_792_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_793_ = 0;
v___x_794_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_794_, 0, v___x_790_);
lean_ctor_set(v___x_794_, 1, v_ar_772_);
lean_ctor_set(v___x_794_, 2, v___x_789_);
lean_ctor_set(v___x_794_, 3, v___x_791_);
lean_ctor_set(v___x_794_, 4, v___x_792_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*5, v___x_779_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*5 + 1, v___x_793_);
v___x_795_ = l_Lake_proc(v___x_794_, v___x_793_, v___x_791_, v_a_787_);
return v___x_795_;
}
else
{
lean_object* v_a_796_; lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref(v_ar_772_);
lean_dec_ref(v_libFile_770_);
v_a_796_ = lean_ctor_get(v___x_785_, 0);
v_a_797_ = lean_ctor_get(v___x_785_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_785_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_inc(v_a_796_);
lean_dec(v___x_785_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_796_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_807_; uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec_ref(v_ar_772_);
lean_dec_ref(v_oFiles_771_);
lean_dec_ref(v_libFile_770_);
v_a_806_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_777_, 1);
v___x_807_ = lean_io_error_to_string(v_a_806_);
v___x_808_ = 3;
v___x_809_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*1, v___x_808_);
v___x_810_ = lean_array_get_size(v_a_774_);
v___x_811_ = lean_array_push(v_a_774_, v___x_809_);
v___x_812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
return v___x_812_;
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_814_; uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref(v_ar_772_);
lean_dec_ref(v_oFiles_771_);
lean_dec_ref(v_libFile_770_);
v_a_813_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_776_, 1);
v___x_814_ = lean_io_error_to_string(v_a_813_);
v___x_815_ = 3;
v___x_816_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*1, v___x_815_);
v___x_817_ = lean_array_get_size(v_a_774_);
v___x_818_ = lean_array_push(v_a_774_, v___x_816_);
v___x_819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object* v_libFile_820_, lean_object* v_oFiles_821_, lean_object* v_ar_822_, lean_object* v_thin_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
uint8_t v_thin_boxed_826_; lean_object* v_res_827_; 
v_thin_boxed_826_ = lean_unbox(v_thin_823_);
v_res_827_ = l_Lake_compileStaticLib(v_libFile_820_, v_oFiles_821_, v_ar_822_, v_thin_boxed_826_, v_a_824_);
return v_res_827_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__1(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = ((lean_object*)(l_Lake_compileSharedLib___closed__0));
v___x_830_ = lean_unsigned_to_nat(3u);
v___x_831_ = lean_mk_empty_array_with_capacity(v___x_830_);
v___x_832_ = lean_array_push(v___x_831_, v___x_829_);
return v___x_832_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__2(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_834_ = lean_obj_once(&l_Lake_compileSharedLib___closed__1, &l_Lake_compileSharedLib___closed__1_once, _init_l_Lake_compileSharedLib___closed__1);
v___x_835_ = lean_array_push(v___x_834_, v___x_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object* v_libFile_837_, lean_object* v_linkArgs_838_, lean_object* v_linker_839_, lean_object* v_macosxDeploymentTarget_x3f_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_843_; 
lean_inc_ref(v_libFile_837_);
v___x_843_ = l_Lake_createParentDirs(v_libFile_837_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v___x_844_; 
lean_dec_ref_known(v___x_843_, 1);
lean_inc_ref(v_libFile_837_);
v___x_844_ = l_Lake_mkArgs(v_libFile_837_, v_linkArgs_838_, v_a_841_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v_a_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___y_853_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
v_a_846_ = lean_ctor_get(v___x_844_, 1);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_844_, 2);
v___x_847_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_848_ = lean_obj_once(&l_Lake_compileSharedLib___closed__2, &l_Lake_compileSharedLib___closed__2_once, _init_l_Lake_compileSharedLib___closed__2);
v___x_849_ = lean_array_push(v___x_848_, v_libFile_837_);
v___x_850_ = l_Array_append___redArg(v___x_849_, v_a_845_);
lean_dec(v_a_845_);
v___x_851_ = lean_box(0);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_840_) == 0)
{
lean_object* v___x_858_; 
v___x_858_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_853_ = v___x_858_;
goto v___jp_852_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_859_ = ((lean_object*)(l_Lake_compileSharedLib___closed__3));
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v_macosxDeploymentTarget_x3f_840_);
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_mk_empty_array_with_capacity(v___x_861_);
v___x_863_ = lean_array_push(v___x_862_, v___x_860_);
v___y_853_ = v___x_863_;
goto v___jp_852_;
}
v___jp_852_:
{
uint8_t v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_854_ = 1;
v___x_855_ = 0;
v___x_856_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_856_, 0, v___x_847_);
lean_ctor_set(v___x_856_, 1, v_linker_839_);
lean_ctor_set(v___x_856_, 2, v___x_850_);
lean_ctor_set(v___x_856_, 3, v___x_851_);
lean_ctor_set(v___x_856_, 4, v___y_853_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*5, v___x_854_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*5 + 1, v___x_855_);
v___x_857_ = l_Lake_proc(v___x_856_, v___x_855_, v___x_851_, v_a_846_);
return v___x_857_;
}
}
else
{
lean_object* v_a_864_; lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec(v_macosxDeploymentTarget_x3f_840_);
lean_dec_ref(v_linker_839_);
lean_dec_ref(v_libFile_837_);
v_a_864_ = lean_ctor_get(v___x_844_, 0);
v_a_865_ = lean_ctor_get(v___x_844_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_844_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_inc(v_a_864_);
lean_dec(v___x_844_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_864_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec(v_macosxDeploymentTarget_x3f_840_);
lean_dec_ref(v_linker_839_);
lean_dec_ref(v_libFile_837_);
v_a_873_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_843_, 1);
v___x_874_ = lean_io_error_to_string(v_a_873_);
v___x_875_ = 3;
v___x_876_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*1, v___x_875_);
v___x_877_ = lean_array_get_size(v_a_841_);
v___x_878_ = lean_array_push(v_a_841_, v___x_876_);
v___x_879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object* v_libFile_880_, lean_object* v_linkArgs_881_, lean_object* v_linker_882_, lean_object* v_macosxDeploymentTarget_x3f_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lake_compileSharedLib(v_libFile_880_, v_linkArgs_881_, v_linker_882_, v_macosxDeploymentTarget_x3f_883_, v_a_884_);
lean_dec_ref(v_linkArgs_881_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object* v_binFile_887_, lean_object* v_linkArgs_888_, lean_object* v_linker_889_, lean_object* v_macosxDeploymentTarget_x3f_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___x_893_; 
lean_inc_ref(v_binFile_887_);
v___x_893_ = l_Lake_createParentDirs(v_binFile_887_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v___x_894_; 
lean_dec_ref_known(v___x_893_, 1);
lean_inc_ref(v_binFile_887_);
v___x_894_ = l_Lake_mkArgs(v_binFile_887_, v_linkArgs_888_, v_a_891_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___y_905_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
v_a_896_ = lean_ctor_get(v___x_894_, 1);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_894_, 2);
v___x_897_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_898_ = lean_unsigned_to_nat(2u);
v___x_899_ = lean_mk_empty_array_with_capacity(v___x_898_);
lean_dec_ref(v___x_899_);
v___x_900_ = lean_obj_once(&l_Lake_compileLeanModule___closed__15, &l_Lake_compileLeanModule___closed__15_once, _init_l_Lake_compileLeanModule___closed__15);
v___x_901_ = lean_array_push(v___x_900_, v_binFile_887_);
v___x_902_ = l_Array_append___redArg(v___x_901_, v_a_895_);
lean_dec(v_a_895_);
v___x_903_ = lean_box(0);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_890_) == 0)
{
lean_object* v___x_910_; 
v___x_910_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_905_ = v___x_910_;
goto v___jp_904_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_911_ = ((lean_object*)(l_Lake_compileSharedLib___closed__3));
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v_macosxDeploymentTarget_x3f_890_);
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = lean_mk_empty_array_with_capacity(v___x_913_);
v___x_915_ = lean_array_push(v___x_914_, v___x_912_);
v___y_905_ = v___x_915_;
goto v___jp_904_;
}
v___jp_904_:
{
uint8_t v___x_906_; uint8_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_906_ = 1;
v___x_907_ = 0;
v___x_908_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_908_, 0, v___x_897_);
lean_ctor_set(v___x_908_, 1, v_linker_889_);
lean_ctor_set(v___x_908_, 2, v___x_902_);
lean_ctor_set(v___x_908_, 3, v___x_903_);
lean_ctor_set(v___x_908_, 4, v___y_905_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*5, v___x_906_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*5 + 1, v___x_907_);
v___x_909_ = l_Lake_proc(v___x_908_, v___x_907_, v___x_903_, v_a_896_);
return v___x_909_;
}
}
else
{
lean_object* v_a_916_; lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_macosxDeploymentTarget_x3f_890_);
lean_dec_ref(v_linker_889_);
lean_dec_ref(v_binFile_887_);
v_a_916_ = lean_ctor_get(v___x_894_, 0);
v_a_917_ = lean_ctor_get(v___x_894_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_894_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_inc(v_a_916_);
lean_dec(v___x_894_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_916_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_926_; uint8_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec(v_macosxDeploymentTarget_x3f_890_);
lean_dec_ref(v_linker_889_);
lean_dec_ref(v_binFile_887_);
v_a_925_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_893_, 1);
v___x_926_ = lean_io_error_to_string(v_a_925_);
v___x_927_ = 3;
v___x_928_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*1, v___x_927_);
v___x_929_ = lean_array_get_size(v_a_891_);
v___x_930_ = lean_array_push(v_a_891_, v___x_928_);
v___x_931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object* v_binFile_932_, lean_object* v_linkArgs_933_, lean_object* v_linker_934_, lean_object* v_macosxDeploymentTarget_x3f_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lake_compileExe(v_binFile_932_, v_linkArgs_933_, v_linker_934_, v_macosxDeploymentTarget_x3f_935_, v_a_936_);
lean_dec_ref(v_linkArgs_933_);
return v_res_938_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0));
v___x_941_ = lean_unsigned_to_nat(2u);
v___x_942_ = lean_mk_empty_array_with_capacity(v___x_941_);
v___x_943_ = lean_array_push(v___x_942_, v___x_940_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(lean_object* v_as_944_, size_t v_i_945_, size_t v_stop_946_, lean_object* v_b_947_){
_start:
{
uint8_t v___x_948_; 
v___x_948_ = lean_usize_dec_eq(v_i_945_, v_stop_946_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; size_t v___x_953_; size_t v___x_954_; 
v___x_949_ = lean_array_uget_borrowed(v_as_944_, v_i_945_);
v___x_950_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1);
lean_inc(v___x_949_);
v___x_951_ = lean_array_push(v___x_950_, v___x_949_);
v___x_952_ = l_Array_append___redArg(v_b_947_, v___x_951_);
lean_dec_ref(v___x_951_);
v___x_953_ = ((size_t)1ULL);
v___x_954_ = lean_usize_add(v_i_945_, v___x_953_);
v_i_945_ = v___x_954_;
v_b_947_ = v___x_952_;
goto _start;
}
else
{
return v_b_947_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___boxed(lean_object* v_as_956_, lean_object* v_i_957_, lean_object* v_stop_958_, lean_object* v_b_959_){
_start:
{
size_t v_i_boxed_960_; size_t v_stop_boxed_961_; lean_object* v_res_962_; 
v_i_boxed_960_ = lean_unbox_usize(v_i_957_);
lean_dec(v_i_957_);
v_stop_boxed_961_ = lean_unbox_usize(v_stop_958_);
lean_dec(v_stop_958_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_as_956_, v_i_boxed_960_, v_stop_boxed_961_, v_b_959_);
lean_dec_ref(v_as_956_);
return v_res_962_;
}
}
static lean_object* _init_l_Lake_download___closed__6(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_969_ = ((lean_object*)(l_Lake_download___closed__2));
v___x_970_ = lean_unsigned_to_nat(7u);
v___x_971_ = lean_mk_empty_array_with_capacity(v___x_970_);
v___x_972_ = lean_array_push(v___x_971_, v___x_969_);
return v___x_972_;
}
}
static lean_object* _init_l_Lake_download___closed__7(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_974_ = lean_obj_once(&l_Lake_download___closed__6, &l_Lake_download___closed__6_once, _init_l_Lake_download___closed__6);
v___x_975_ = lean_array_push(v___x_974_, v___x_973_);
return v___x_975_;
}
}
static lean_object* _init_l_Lake_download___closed__8(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_977_ = lean_obj_once(&l_Lake_download___closed__7, &l_Lake_download___closed__7_once, _init_l_Lake_download___closed__7);
v___x_978_ = lean_array_push(v___x_977_, v___x_976_);
return v___x_978_;
}
}
static lean_object* _init_l_Lake_download___closed__9(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_980_ = lean_obj_once(&l_Lake_download___closed__8, &l_Lake_download___closed__8_once, _init_l_Lake_download___closed__8);
v___x_981_ = lean_array_push(v___x_980_, v___x_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lake_download(lean_object* v_url_982_, lean_object* v_file_983_, lean_object* v_headers_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v_val_990_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1006_; uint8_t v___x_1022_; 
v___x_1022_ = l_System_FilePath_pathExists(v_file_983_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; 
lean_inc_ref(v_file_983_);
v___x_1023_ = l_Lake_createParentDirs(v_file_983_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_dec_ref_known(v___x_1023_, 1);
v___y_1006_ = v_a_985_;
goto v___jp_1005_;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec_ref(v_file_983_);
lean_dec_ref(v_url_982_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = lean_io_error_to_string(v_a_1024_);
v___x_1026_ = 3;
v___x_1027_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set_uint8(v___x_1027_, sizeof(void*)*1, v___x_1026_);
v___x_1028_ = lean_array_get_size(v_a_985_);
v___x_1029_ = lean_array_push(v_a_985_, v___x_1027_);
v___x_1030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
return v___x_1030_;
}
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_io_remove_file(v_file_983_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_dec_ref_known(v___x_1031_, 1);
v___y_1006_ = v_a_985_;
goto v___jp_1005_;
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec_ref(v_file_983_);
lean_dec_ref(v_url_982_);
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = lean_io_error_to_string(v_a_1032_);
v___x_1034_ = 3;
v___x_1035_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*1, v___x_1034_);
v___x_1036_ = lean_array_get_size(v_a_985_);
v___x_1037_ = lean_array_push(v_a_985_, v___x_1035_);
v___x_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
return v___x_1038_;
}
}
v___jp_987_:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; uint8_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_991_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_992_ = lean_box(0);
v___x_993_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_994_ = 1;
v___x_995_ = 0;
v___x_996_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_996_, 0, v___x_991_);
lean_ctor_set(v___x_996_, 1, v_val_990_);
lean_ctor_set(v___x_996_, 2, v___y_988_);
lean_ctor_set(v___x_996_, 3, v___x_992_);
lean_ctor_set(v___x_996_, 4, v___x_993_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*5, v___x_994_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*5 + 1, v___x_995_);
v___x_997_ = l_Lake_proc(v___x_996_, v___x_994_, v___x_992_, v___y_989_);
return v___x_997_;
}
v___jp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lake_download___closed__0));
v___x_1002_ = lean_io_getenv(v___x_1001_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v___x_1003_; 
v___x_1003_ = ((lean_object*)(l_Lake_download___closed__1));
v___y_988_ = v___y_1000_;
v___y_989_ = v___y_999_;
v_val_990_ = v___x_1003_;
goto v___jp_987_;
}
else
{
lean_object* v_val_1004_; 
v_val_1004_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_val_1004_);
lean_dec_ref_known(v___x_1002_, 1);
v___y_988_ = v___y_1000_;
v___y_989_ = v___y_999_;
v_val_990_ = v_val_1004_;
goto v___jp_987_;
}
}
v___jp_1005_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1007_ = ((lean_object*)(l_Lake_download___closed__5));
v___x_1008_ = lean_obj_once(&l_Lake_download___closed__9, &l_Lake_download___closed__9_once, _init_l_Lake_download___closed__9);
v___x_1009_ = lean_array_push(v___x_1008_, v_file_983_);
v___x_1010_ = lean_array_push(v___x_1009_, v___x_1007_);
v___x_1011_ = lean_array_push(v___x_1010_, v_url_982_);
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = lean_array_get_size(v_headers_984_);
v___x_1014_ = lean_nat_dec_lt(v___x_1012_, v___x_1013_);
if (v___x_1014_ == 0)
{
v___y_999_ = v___y_1006_;
v___y_1000_ = v___x_1011_;
goto v___jp_998_;
}
else
{
uint8_t v___x_1015_; 
v___x_1015_ = lean_nat_dec_le(v___x_1013_, v___x_1013_);
if (v___x_1015_ == 0)
{
if (v___x_1014_ == 0)
{
v___y_999_ = v___y_1006_;
v___y_1000_ = v___x_1011_;
goto v___jp_998_;
}
else
{
size_t v___x_1016_; size_t v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = ((size_t)0ULL);
v___x_1017_ = lean_usize_of_nat(v___x_1013_);
v___x_1018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_984_, v___x_1016_, v___x_1017_, v___x_1011_);
v___y_999_ = v___y_1006_;
v___y_1000_ = v___x_1018_;
goto v___jp_998_;
}
}
else
{
size_t v___x_1019_; size_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = ((size_t)0ULL);
v___x_1020_ = lean_usize_of_nat(v___x_1013_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_984_, v___x_1019_, v___x_1020_, v___x_1011_);
v___y_999_ = v___y_1006_;
v___y_1000_ = v___x_1021_;
goto v___jp_998_;
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
v___x_1062_ = ((lean_object*)(l_Lake_download___closed__4));
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
v___x_1119_ = ((lean_object*)(l_Lake_download___closed__4));
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
lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; uint8_t v___y_1155_; lean_object* v___y_1156_; lean_object* v___x_1161_; 
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
v___y_1150_ = v___x_1171_;
v___y_1151_ = v___x_1180_;
v___y_1152_ = v_a_1169_;
v___y_1153_ = v___x_1170_;
v___y_1154_ = v___x_1179_;
v___y_1155_ = v___x_1182_;
v___y_1156_ = v___x_1183_;
goto v___jp_1149_;
}
else
{
lean_object* v___x_1184_; 
v___x_1184_ = ((lean_object*)(l_Lake_tar___closed__6));
v___y_1150_ = v___x_1171_;
v___y_1151_ = v___x_1180_;
v___y_1152_ = v_a_1169_;
v___y_1153_ = v___x_1170_;
v___y_1154_ = v___x_1179_;
v___y_1155_ = v___x_1182_;
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
lean_inc_ref(v___y_1150_);
lean_inc_ref(v___y_1153_);
v___x_1158_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1158_, 0, v___y_1153_);
lean_ctor_set(v___x_1158_, 1, v___y_1150_);
lean_ctor_set(v___x_1158_, 2, v___y_1154_);
lean_ctor_set(v___x_1158_, 3, v___y_1151_);
lean_ctor_set(v___x_1158_, 4, v___y_1156_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*5, v___y_1155_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*5 + 1, v___x_1157_);
v___x_1159_ = lean_box(0);
v___x_1160_ = l_Lake_proc(v___x_1158_, v___y_1155_, v___x_1159_, v___y_1152_);
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
lean_object* runtime_initialize_Lake_Util_Url(uint8_t builtin);
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
res = runtime_initialize_Lake_Util_Url(builtin);
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
lean_object* initialize_Lake_Util_Url(uint8_t builtin);
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
res = initialize_Lake_Util_Url(builtin);
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
