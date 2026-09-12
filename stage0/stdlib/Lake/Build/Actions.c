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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0;
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg(){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg___closed__0));
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg___boxed(lean_object* v___dummy_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg();
return v_res_6_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg();
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1(lean_object* v_s_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___boxed(lean_object* v_s_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1(v_s_10_);
lean_dec_ref(v_s_10_);
return v_res_11_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(lean_object* v_opts_12_, lean_object* v_opt_13_){
_start:
{
lean_object* v_name_14_; lean_object* v_defValue_15_; lean_object* v_map_16_; lean_object* v___x_17_; 
v_name_14_ = lean_ctor_get(v_opt_13_, 0);
v_defValue_15_ = lean_ctor_get(v_opt_13_, 1);
v_map_16_ = lean_ctor_get(v_opts_12_, 0);
v___x_17_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_16_, v_name_14_);
if (lean_obj_tag(v___x_17_) == 0)
{
uint8_t v___x_18_; 
v___x_18_ = lean_unbox(v_defValue_15_);
return v___x_18_;
}
else
{
lean_object* v_val_19_; 
v_val_19_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_val_19_);
lean_dec_ref_known(v___x_17_, 1);
if (lean_obj_tag(v_val_19_) == 1)
{
uint8_t v_v_20_; 
v_v_20_ = lean_ctor_get_uint8(v_val_19_, 0);
lean_dec_ref_known(v_val_19_, 0);
return v_v_20_;
}
else
{
uint8_t v___x_21_; 
lean_dec(v_val_19_);
v___x_21_ = lean_unbox(v_defValue_15_);
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3___boxed(lean_object* v_opts_22_, lean_object* v_opt_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(v_opts_22_, v_opt_23_);
lean_dec_ref(v_opt_23_);
lean_dec_ref(v_opts_22_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(lean_object* v_as_26_, size_t v_i_27_, size_t v_stop_28_){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = lean_usize_dec_eq(v_i_27_, v_stop_28_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; uint8_t v_level_31_; 
v___x_30_ = lean_array_uget_borrowed(v_as_26_, v_i_27_);
v_level_31_ = lean_ctor_get_uint8(v___x_30_, sizeof(void*)*1);
if (v_level_31_ == 3)
{
uint8_t v___x_32_; 
v___x_32_ = 1;
return v___x_32_;
}
else
{
size_t v___x_33_; size_t v___x_34_; 
v___x_33_ = ((size_t)1ULL);
v___x_34_ = lean_usize_add(v_i_27_, v___x_33_);
v_i_27_ = v___x_34_;
goto _start;
}
}
else
{
uint8_t v___x_36_; 
v___x_36_ = 0;
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0___boxed(lean_object* v_as_37_, lean_object* v_i_38_, lean_object* v_stop_39_){
_start:
{
size_t v_i_boxed_40_; size_t v_stop_boxed_41_; uint8_t v_res_42_; lean_object* v_r_43_; 
v_i_boxed_40_ = lean_unbox_usize(v_i_38_);
lean_dec(v_i_38_);
v_stop_boxed_41_ = lean_unbox_usize(v_stop_39_);
lean_dec(v_stop_39_);
v_res_42_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(v_as_37_, v_i_boxed_40_, v_stop_boxed_41_);
lean_dec_ref(v_as_37_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint8_t v___y_46_, lean_object* v_ir_x3f_47_, lean_object* v_c_x3f_48_, lean_object* v_setupFile_49_, lean_object* v___x_50_, lean_object* v_leanir_51_, lean_object* v___x_52_, lean_object* v___x_53_, uint8_t v___x_54_, uint8_t v___x_55_, lean_object* v___x_56_, lean_object* v_olean_x3f_57_, uint32_t v_exitCode_58_, lean_object* v___x_59_, lean_object* v_stderr_60_, lean_object* v_____r_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___y_65_; lean_object* v___y_69_; uint32_t v___y_70_; lean_object* v___y_81_; lean_object* v___y_82_; lean_object* v___y_85_; uint32_t v___y_86_; uint8_t v___y_87_; lean_object* v___y_137_; uint8_t v___y_138_; lean_object* v___y_144_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = lean_string_utf8_byte_size(v_stderr_60_);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_nat_dec_eq(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_156_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__1));
v___x_157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_157_, 0, v_stderr_60_);
lean_ctor_set(v___x_157_, 1, v___x_154_);
lean_ctor_set(v___x_157_, 2, v___x_153_);
v___x_158_ = l_String_Slice_trimAscii(v___x_157_);
v___x_159_ = l_String_Slice_toString(v___x_158_);
lean_dec_ref(v___x_158_);
v___x_160_ = lean_string_append(v___x_156_, v___x_159_);
lean_dec_ref(v___x_159_);
v___x_161_ = 1;
v___x_162_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*1, v___x_161_);
v___x_163_ = lean_array_push(v___y_62_, v___x_162_);
v___y_144_ = v___x_163_;
goto v___jp_143_;
}
else
{
lean_dec_ref(v_stderr_60_);
v___y_144_ = v___y_62_;
goto v___jp_143_;
}
v___jp_64_:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_box(0);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___y_65_);
return v___x_67_;
}
v___jp_68_:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_71_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__0));
v___x_72_ = lean_uint32_to_nat(v___y_70_);
v___x_73_ = l_Nat_reprFast(v___x_72_);
v___x_74_ = lean_string_append(v___x_71_, v___x_73_);
lean_dec_ref(v___x_73_);
v___x_75_ = 3;
v___x_76_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*1, v___x_75_);
v___x_77_ = lean_array_get_size(v___y_69_);
v___x_78_ = lean_array_push(v___y_69_, v___x_76_);
v___x_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
return v___x_79_;
}
v___jp_80_:
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v___y_81_);
lean_ctor_set(v___x_83_, 1, v___y_82_);
return v___x_83_;
}
v___jp_84_:
{
uint32_t v___x_88_; uint8_t v___x_89_; 
v___x_88_ = 0;
v___x_89_ = lean_uint32_dec_eq(v___y_86_, v___x_88_);
if (v___x_89_ == 0)
{
lean_dec_ref(v___x_53_);
lean_dec(v___x_52_);
lean_dec_ref(v_leanir_51_);
lean_dec_ref(v___x_50_);
lean_dec_ref(v_setupFile_49_);
lean_dec(v_c_x3f_48_);
lean_dec(v_ir_x3f_47_);
v___y_69_ = v___y_85_;
v___y_70_ = v___y_86_;
goto v___jp_68_;
}
else
{
if (v___y_87_ == 0)
{
if (v___y_46_ == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec_ref(v___x_53_);
lean_dec(v___x_52_);
lean_dec_ref(v_leanir_51_);
lean_dec_ref(v___x_50_);
lean_dec_ref(v_setupFile_49_);
lean_dec(v_c_x3f_48_);
lean_dec(v_ir_x3f_47_);
v___x_90_ = lean_box(0);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___y_85_);
return v___x_91_;
}
else
{
if (lean_obj_tag(v_ir_x3f_47_) == 1)
{
if (lean_obj_tag(v_c_x3f_48_) == 1)
{
lean_object* v_val_92_; lean_object* v_val_93_; lean_object* v___x_94_; 
v_val_92_ = lean_ctor_get(v_ir_x3f_47_, 0);
lean_inc_n(v_val_92_, 2);
lean_dec_ref_known(v_ir_x3f_47_, 1);
v_val_93_ = lean_ctor_get(v_c_x3f_48_, 0);
lean_inc(v_val_93_);
lean_dec_ref_known(v_c_x3f_48_, 1);
v___x_94_ = l_Lake_createParentDirs(v_val_92_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v___x_95_; 
lean_dec_ref_known(v___x_94_, 1);
lean_inc(v_val_93_);
v___x_95_ = l_Lake_createParentDirs(v_val_93_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec_ref_known(v___x_95_, 1);
v___x_96_ = lean_unsigned_to_nat(3u);
v___x_97_ = lean_mk_empty_array_with_capacity(v___x_96_);
v___x_98_ = lean_array_push(v___x_97_, v_setupFile_49_);
v___x_99_ = lean_array_push(v___x_98_, v_val_92_);
v___x_100_ = lean_array_push(v___x_99_, v_val_93_);
v___x_101_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_101_, 0, v___x_50_);
lean_ctor_set(v___x_101_, 1, v_leanir_51_);
lean_ctor_set(v___x_101_, 2, v___x_100_);
lean_ctor_set(v___x_101_, 3, v___x_52_);
lean_ctor_set(v___x_101_, 4, v___x_53_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*5, v___x_54_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*5 + 1, v___x_55_);
v___x_102_ = l_Lake_proc(v___x_101_, v___x_55_, v___x_56_, v___y_85_);
if (lean_obj_tag(v___x_102_) == 0)
{
return v___x_102_;
}
else
{
if (lean_obj_tag(v_olean_x3f_57_) == 1)
{
lean_object* v_a_103_; lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_119_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
v_a_104_ = lean_ctor_get(v___x_102_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_119_ == 0)
{
v___x_106_ = v___x_102_;
v_isShared_107_ = v_isSharedCheck_119_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_inc(v_a_103_);
lean_dec(v___x_102_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_119_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v_val_108_; lean_object* v___x_109_; 
v_val_108_ = lean_ctor_get(v_olean_x3f_57_, 0);
v___x_109_ = l_Lake_removeFileIfExists(v_val_108_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_dec_ref_known(v___x_109_, 1);
lean_del_object(v___x_106_);
v___y_81_ = v_a_103_;
v___y_82_ = v_a_104_;
goto v___jp_80_;
}
else
{
lean_object* v_a_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
lean_dec(v_a_103_);
v_a_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_a_110_);
lean_dec_ref_known(v___x_109_, 1);
v___x_111_ = lean_io_error_to_string(v_a_110_);
v___x_112_ = 3;
v___x_113_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_112_);
v___x_114_ = lean_array_get_size(v_a_104_);
v___x_115_ = lean_array_push(v_a_104_, v___x_113_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v___x_115_);
lean_ctor_set(v___x_106_, 0, v___x_114_);
v___x_117_ = v___x_106_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_114_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
else
{
lean_object* v_a_120_; lean_object* v_a_121_; 
v_a_120_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_120_);
v_a_121_ = lean_ctor_get(v___x_102_, 1);
lean_inc(v_a_121_);
lean_dec_ref_known(v___x_102_, 2);
v___y_81_ = v_a_120_;
v___y_82_ = v_a_121_;
goto v___jp_80_;
}
}
}
else
{
lean_object* v_a_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v_val_93_);
lean_dec(v_val_92_);
lean_dec_ref(v___x_53_);
lean_dec(v___x_52_);
lean_dec_ref(v_leanir_51_);
lean_dec_ref(v___x_50_);
lean_dec_ref(v_setupFile_49_);
v_a_122_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_122_);
lean_dec_ref_known(v___x_95_, 1);
v___x_123_ = lean_io_error_to_string(v_a_122_);
v___x_124_ = 3;
v___x_125_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_124_);
v___x_126_ = lean_array_get_size(v___y_85_);
v___x_127_ = lean_array_push(v___y_85_, v___x_125_);
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
return v___x_128_;
}
}
else
{
lean_object* v_a_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v_val_93_);
lean_dec(v_val_92_);
lean_dec_ref(v___x_53_);
lean_dec(v___x_52_);
lean_dec_ref(v_leanir_51_);
lean_dec_ref(v___x_50_);
lean_dec_ref(v_setupFile_49_);
v_a_129_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_a_129_);
lean_dec_ref_known(v___x_94_, 1);
v___x_130_ = lean_io_error_to_string(v_a_129_);
v___x_131_ = 3;
v___x_132_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*1, v___x_131_);
v___x_133_ = lean_array_get_size(v___y_85_);
v___x_134_ = lean_array_push(v___y_85_, v___x_132_);
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
return v___x_135_;
}
}
else
{
lean_dec_ref_known(v_ir_x3f_47_, 1);
lean_dec_ref(v___x_53_);
lean_dec(v___x_52_);
lean_dec_ref(v_leanir_51_);
lean_dec_ref(v___x_50_);
lean_dec_ref(v_setupFile_49_);
lean_dec(v_c_x3f_48_);
v___y_65_ = v___y_85_;
goto v___jp_64_;
}
}
else
{
lean_dec_ref(v___x_53_);
lean_dec(v___x_52_);
lean_dec_ref(v_leanir_51_);
lean_dec_ref(v___x_50_);
lean_dec_ref(v_setupFile_49_);
lean_dec(v_c_x3f_48_);
lean_dec(v_ir_x3f_47_);
v___y_65_ = v___y_85_;
goto v___jp_64_;
}
}
}
else
{
lean_dec_ref(v___x_53_);
lean_dec(v___x_52_);
lean_dec_ref(v_leanir_51_);
lean_dec_ref(v___x_50_);
lean_dec_ref(v_setupFile_49_);
lean_dec(v_c_x3f_48_);
lean_dec(v_ir_x3f_47_);
v___y_69_ = v___y_85_;
v___y_70_ = v___y_86_;
goto v___jp_68_;
}
}
}
v___jp_136_:
{
uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 1;
v___x_140_ = lean_uint32_dec_eq(v_exitCode_58_, v___x_139_);
if (v___x_140_ == 0)
{
v___y_85_ = v___y_137_;
v___y_86_ = v_exitCode_58_;
v___y_87_ = v___y_138_;
goto v___jp_84_;
}
else
{
if (v___y_138_ == 0)
{
v___y_85_ = v___y_137_;
v___y_86_ = v_exitCode_58_;
v___y_87_ = v___y_138_;
goto v___jp_84_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec_ref(v___x_53_);
lean_dec(v___x_52_);
lean_dec_ref(v_leanir_51_);
lean_dec_ref(v___x_50_);
lean_dec_ref(v_setupFile_49_);
lean_dec(v_c_x3f_48_);
lean_dec(v_ir_x3f_47_);
v___x_141_ = lean_array_get_size(v___y_137_);
v___x_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___y_137_);
return v___x_142_;
}
}
}
v___jp_143_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_145_ = lean_array_get_size(v___y_144_);
v___x_146_ = l_Array_extract___redArg(v___y_144_, v___x_59_, v___x_145_);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_array_get_size(v___x_146_);
v___x_149_ = lean_nat_dec_lt(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_dec_ref(v___x_146_);
v___y_137_ = v___y_144_;
v___y_138_ = v___x_149_;
goto v___jp_136_;
}
else
{
if (v___x_149_ == 0)
{
lean_dec_ref(v___x_146_);
v___y_137_ = v___y_144_;
v___y_138_ = v___x_149_;
goto v___jp_136_;
}
else
{
size_t v___x_150_; size_t v___x_151_; uint8_t v___x_152_; 
v___x_150_ = ((size_t)0ULL);
v___x_151_ = lean_usize_of_nat(v___x_148_);
v___x_152_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(v___x_146_, v___x_150_, v___x_151_);
lean_dec_ref(v___x_146_);
v___y_137_ = v___y_144_;
v___y_138_ = v___x_152_;
goto v___jp_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object** _args){
lean_object* v___y_164_ = _args[0];
lean_object* v_ir_x3f_165_ = _args[1];
lean_object* v_c_x3f_166_ = _args[2];
lean_object* v_setupFile_167_ = _args[3];
lean_object* v___x_168_ = _args[4];
lean_object* v_leanir_169_ = _args[5];
lean_object* v___x_170_ = _args[6];
lean_object* v___x_171_ = _args[7];
lean_object* v___x_172_ = _args[8];
lean_object* v___x_173_ = _args[9];
lean_object* v___x_174_ = _args[10];
lean_object* v_olean_x3f_175_ = _args[11];
lean_object* v_exitCode_176_ = _args[12];
lean_object* v___x_177_ = _args[13];
lean_object* v_stderr_178_ = _args[14];
lean_object* v_____r_179_ = _args[15];
lean_object* v___y_180_ = _args[16];
lean_object* v___y_181_ = _args[17];
_start:
{
uint8_t v___y_33982__boxed_182_; uint8_t v___x_33986__boxed_183_; uint8_t v___x_33987__boxed_184_; uint32_t v_exitCode_boxed_185_; lean_object* v_res_186_; 
v___y_33982__boxed_182_ = lean_unbox(v___y_164_);
v___x_33986__boxed_183_ = lean_unbox(v___x_172_);
v___x_33987__boxed_184_ = lean_unbox(v___x_173_);
v_exitCode_boxed_185_ = lean_unbox_uint32(v_exitCode_176_);
lean_dec(v_exitCode_176_);
v_res_186_ = l_Lake_compileLeanModule___lam__0(v___y_33982__boxed_182_, v_ir_x3f_165_, v_c_x3f_166_, v_setupFile_167_, v___x_168_, v_leanir_169_, v___x_170_, v___x_171_, v___x_33986__boxed_183_, v___x_33987__boxed_184_, v___x_174_, v_olean_x3f_175_, v_exitCode_boxed_185_, v___x_177_, v_stderr_178_, v_____r_179_, v___y_180_);
lean_dec(v_olean_x3f_175_);
lean_dec(v___x_174_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(lean_object* v_a_187_, lean_object* v_b_188_, lean_object* v_relLeanFile_189_, lean_object* v_____r_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_a_194_; lean_object* v_toBaseMessage_196_; uint8_t v_isSilent_197_; 
v_toBaseMessage_196_ = lean_ctor_get(v_a_187_, 0);
lean_inc_ref(v_toBaseMessage_196_);
v_isSilent_197_ = lean_ctor_get_uint8(v_toBaseMessage_196_, sizeof(void*)*5 + 2);
if (v_isSilent_197_ == 0)
{
lean_object* v_kind_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_222_; 
v_kind_198_ = lean_ctor_get(v_a_187_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v_a_187_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; 
v_unused_223_ = lean_ctor_get(v_a_187_, 0);
lean_dec(v_unused_223_);
v___x_200_ = v_a_187_;
v_isShared_201_ = v_isSharedCheck_222_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_kind_198_);
lean_dec(v_a_187_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_222_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v_pos_202_; lean_object* v_endPos_203_; uint8_t v_keepFullRange_204_; uint8_t v_severity_205_; lean_object* v_caption_206_; lean_object* v_data_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_220_; 
v_pos_202_ = lean_ctor_get(v_toBaseMessage_196_, 1);
v_endPos_203_ = lean_ctor_get(v_toBaseMessage_196_, 2);
v_keepFullRange_204_ = lean_ctor_get_uint8(v_toBaseMessage_196_, sizeof(void*)*5);
v_severity_205_ = lean_ctor_get_uint8(v_toBaseMessage_196_, sizeof(void*)*5 + 1);
v_caption_206_ = lean_ctor_get(v_toBaseMessage_196_, 3);
v_data_207_ = lean_ctor_get(v_toBaseMessage_196_, 4);
v_isSharedCheck_220_ = !lean_is_exclusive(v_toBaseMessage_196_);
if (v_isSharedCheck_220_ == 0)
{
lean_object* v_unused_221_; 
v_unused_221_ = lean_ctor_get(v_toBaseMessage_196_, 0);
lean_dec(v_unused_221_);
v___x_209_ = v_toBaseMessage_196_;
v_isShared_210_ = v_isSharedCheck_220_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_data_207_);
lean_inc(v_caption_206_);
lean_inc(v_endPos_203_);
lean_inc(v_pos_202_);
lean_dec(v_toBaseMessage_196_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_220_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = l_Lake_mkRelPathString(v_relLeanFile_189_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_211_);
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_pos_202_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_endPos_203_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v_caption_206_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v_data_207_);
lean_ctor_set_uint8(v_reuseFailAlloc_219_, sizeof(void*)*5, v_keepFullRange_204_);
lean_ctor_set_uint8(v_reuseFailAlloc_219_, sizeof(void*)*5 + 1, v_severity_205_);
lean_ctor_set_uint8(v_reuseFailAlloc_219_, sizeof(void*)*5 + 2, v_isSilent_197_);
v___x_213_ = v_reuseFailAlloc_219_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_215_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_213_);
v___x_215_ = v___x_200_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_kind_198_);
v___x_215_ = v_reuseFailAlloc_218_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = l_Lake_LogEntry_ofSerialMessage(v___x_215_);
v___x_217_ = lean_array_push(v___y_191_, v___x_216_);
v_a_194_ = v___x_217_;
goto v___jp_193_;
}
}
}
}
}
else
{
lean_dec_ref(v_toBaseMessage_196_);
lean_dec_ref(v_relLeanFile_189_);
lean_dec_ref(v_a_187_);
v_a_194_ = v___y_191_;
goto v___jp_193_;
}
v___jp_193_:
{
lean_object* v___x_195_; 
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v_b_188_);
lean_ctor_set(v___x_195_, 1, v_a_194_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0___boxed(lean_object* v_a_224_, lean_object* v_b_225_, lean_object* v_relLeanFile_226_, lean_object* v_____r_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_224_, v_b_225_, v_relLeanFile_226_, v_____r_227_, v___y_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(lean_object* v_relLeanFile_233_, lean_object* v___x_234_, lean_object* v___x_235_, lean_object* v___x_236_, lean_object* v_a_237_, lean_object* v_b_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v_it_264_; lean_object* v_startInclusive_265_; lean_object* v_endExclusive_266_; 
if (lean_obj_tag(v_a_237_) == 0)
{
lean_object* v_currPos_284_; lean_object* v_searcher_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_308_; 
v_currPos_284_ = lean_ctor_get(v_a_237_, 0);
v_searcher_285_ = lean_ctor_get(v_a_237_, 1);
v_isSharedCheck_308_ = !lean_is_exclusive(v_a_237_);
if (v_isSharedCheck_308_ == 0)
{
v___x_287_ = v_a_237_;
v_isShared_288_ = v_isSharedCheck_308_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_searcher_285_);
lean_inc(v_currPos_284_);
lean_dec(v_a_237_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_308_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
uint8_t v_decide_289_; 
v_decide_289_ = lean_nat_dec_eq(v_searcher_285_, v___x_236_);
if (v_decide_289_ == 0)
{
uint32_t v___x_290_; uint32_t v___x_291_; uint8_t v___x_292_; 
v___x_290_ = 10;
v___x_291_ = lean_string_utf8_get_fast(v___x_234_, v_searcher_285_);
v___x_292_ = lean_uint32_dec_eq(v___x_291_, v___x_290_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_string_utf8_next_fast(v___x_234_, v_searcher_285_);
lean_dec(v_searcher_285_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___x_293_);
v___x_295_ = v___x_287_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_currPos_284_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_297_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
v_a_237_ = v___x_295_;
goto _start;
}
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_slice_301_; lean_object* v_nextIt_303_; 
v___x_298_ = lean_string_utf8_next_fast(v___x_234_, v_searcher_285_);
v___x_299_ = lean_nat_sub(v___x_298_, v_searcher_285_);
v___x_300_ = lean_nat_add(v_searcher_285_, v___x_299_);
lean_dec(v___x_299_);
v_slice_301_ = l_String_Slice_subslice_x21(v___x_235_, v_currPos_284_, v_searcher_285_);
lean_inc(v___x_300_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___x_300_);
lean_ctor_set(v___x_287_, 0, v___x_300_);
v_nextIt_303_ = v___x_287_;
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
v_it_264_ = v_nextIt_303_;
v_startInclusive_265_ = v_startInclusive_304_;
v_endExclusive_266_ = v_endExclusive_305_;
goto v___jp_263_;
}
}
}
else
{
lean_object* v___x_307_; 
lean_del_object(v___x_287_);
lean_dec(v_searcher_285_);
v___x_307_ = lean_box(1);
lean_inc(v___x_236_);
v_it_264_ = v___x_307_;
v_startInclusive_265_ = v_currPos_284_;
v_endExclusive_266_ = v___x_236_;
goto v___jp_263_;
}
}
}
else
{
lean_object* v___x_309_; 
lean_dec(v___x_236_);
lean_dec_ref(v_relLeanFile_233_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_b_238_);
lean_ctor_set(v___x_309_, 1, v___y_239_);
return v___x_309_;
}
v___jp_241_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_string_append(v_b_238_, v___y_242_);
lean_dec_ref(v___y_242_);
v___x_245_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__0));
v___x_246_ = lean_string_append(v___x_244_, v___x_245_);
v_a_237_ = v___y_243_;
v_b_238_ = v___x_246_;
goto _start;
}
v___jp_248_:
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_251_ = lean_string_utf8_byte_size(v_b_238_);
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_nat_dec_eq(v___x_251_, v___x_252_);
if (v___x_253_ == 0)
{
v___y_242_ = v___y_249_;
v___y_243_ = v___y_250_;
goto v___jp_241_;
}
else
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_string_utf8_byte_size(v___y_249_);
v___x_255_ = lean_nat_dec_eq(v___x_254_, v___x_252_);
if (v___x_255_ == 0)
{
v___y_242_ = v___y_249_;
v___y_243_ = v___y_250_;
goto v___jp_241_;
}
else
{
lean_dec_ref(v___y_249_);
v_a_237_ = v___y_250_;
goto _start;
}
}
}
v___jp_257_:
{
if (lean_obj_tag(v___y_259_) == 0)
{
lean_object* v_a_260_; lean_object* v_a_261_; 
v_a_260_ = lean_ctor_get(v___y_259_, 0);
lean_inc(v_a_260_);
v_a_261_ = lean_ctor_get(v___y_259_, 1);
lean_inc(v_a_261_);
lean_dec_ref_known(v___y_259_, 2);
v_a_237_ = v___y_258_;
v_b_238_ = v_a_260_;
v___y_239_ = v_a_261_;
goto _start;
}
else
{
lean_dec(v___y_258_);
lean_dec(v___x_236_);
lean_dec_ref(v_relLeanFile_233_);
return v___y_259_;
}
}
v___jp_263_:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_string_utf8_extract_fast(v___x_234_, v_startInclusive_265_, v_endExclusive_266_);
lean_dec(v_endExclusive_266_);
lean_dec(v_startInclusive_265_);
lean_inc_ref(v___x_267_);
v___x_268_ = l_Lean_Json_parse(v___x_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_dec_ref_known(v___x_268_, 1);
v___y_249_ = v___x_267_;
v___y_250_ = v_it_264_;
goto v___jp_248_;
}
else
{
lean_object* v_a_269_; lean_object* v___x_270_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v___x_268_, 1);
v___x_270_ = l_Lean_instFromJsonSerialMessage_fromJson(v_a_269_);
if (lean_obj_tag(v___x_270_) == 1)
{
lean_object* v_a_271_; lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
lean_dec_ref(v___x_267_);
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_270_, 1);
v___x_272_ = lean_string_utf8_byte_size(v_b_238_);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_nat_dec_eq(v___x_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_275_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__1));
v___x_276_ = lean_string_append(v___x_275_, v_b_238_);
v___x_277_ = 1;
v___x_278_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set_uint8(v___x_278_, sizeof(void*)*1, v___x_277_);
v___x_279_ = lean_box(0);
v___x_280_ = lean_array_push(v___y_239_, v___x_278_);
lean_inc_ref(v_relLeanFile_233_);
v___x_281_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_271_, v_b_238_, v_relLeanFile_233_, v___x_279_, v___x_280_);
v___y_258_ = v_it_264_;
v___y_259_ = v___x_281_;
goto v___jp_257_;
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_box(0);
lean_inc_ref(v_relLeanFile_233_);
v___x_283_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_271_, v_b_238_, v_relLeanFile_233_, v___x_282_, v___y_239_);
v___y_258_ = v_it_264_;
v___y_259_ = v___x_283_;
goto v___jp_257_;
}
}
else
{
lean_dec_ref(v___x_270_);
v___y_249_ = v___x_267_;
v___y_250_ = v_it_264_;
goto v___jp_248_;
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
lean_object* v___y_363_; lean_object* v_a_364_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v_olean_x3f_370_; lean_object* v_ilean_x3f_371_; lean_object* v_ir_x3f_372_; lean_object* v_c_x3f_373_; lean_object* v_bc_x3f_374_; uint8_t v___y_376_; lean_object* v_args_377_; lean_object* v___y_378_; uint8_t v___y_467_; lean_object* v___y_468_; lean_object* v_args_469_; lean_object* v___y_483_; lean_object* v___y_484_; uint8_t v___y_485_; lean_object* v_args_499_; lean_object* v___y_500_; lean_object* v_args_507_; lean_object* v___y_508_; lean_object* v_args_521_; 
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
v___x_421_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0);
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
v___y_376_ = v___y_467_;
v_args_377_ = v___x_474_;
v___y_378_ = v___y_468_;
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
v___x_479_ = lean_array_get_size(v___y_468_);
v___x_480_ = lean_array_push(v___y_468_, v___x_478_);
v___x_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
return v___x_481_;
}
}
else
{
lean_dec(v_bc_x3f_374_);
v___y_376_ = v___y_467_;
v_args_377_ = v_args_469_;
v___y_378_ = v___y_468_;
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
v___y_467_ = v___y_485_;
v___y_468_ = v___y_484_;
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
v___y_467_ = v___y_485_;
v___y_468_ = v___y_484_;
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
v___y_467_ = v___x_505_;
v___y_468_ = v___y_500_;
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
uint8_t v_decide_615_; 
v_decide_615_ = lean_nat_dec_eq(v_a_613_, v___x_611_);
if (v_decide_615_ == 0)
{
uint32_t v___x_616_; lean_object* v___x_617_; uint32_t v___x_618_; uint8_t v___x_623_; 
v___x_616_ = lean_string_utf8_get_fast(v___y_612_, v_a_613_);
v___x_617_ = lean_string_utf8_next_fast(v___y_612_, v_a_613_);
lean_dec(v_a_613_);
v___x_618_ = 92;
v___x_623_ = lean_uint32_dec_eq(v___x_616_, v___x_618_);
if (v___x_623_ == 0)
{
uint32_t v___x_624_; uint8_t v___x_625_; 
v___x_624_ = 34;
v___x_625_ = lean_uint32_dec_eq(v___x_616_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
v___x_626_ = lean_string_push(v_b_614_, v___x_616_);
v_a_613_ = v___x_617_;
v_b_614_ = v___x_626_;
goto _start;
}
else
{
goto v___jp_619_;
}
}
else
{
goto v___jp_619_;
}
v___jp_619_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_string_push(v_b_614_, v___x_618_);
v___x_621_ = lean_string_push(v___x_620_, v___x_616_);
v_a_613_ = v___x_617_;
v_b_614_ = v___x_621_;
goto _start;
}
}
else
{
lean_dec(v_a_613_);
return v_b_614_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg___boxed(lean_object* v___x_628_, lean_object* v___y_629_, lean_object* v_a_630_, lean_object* v_b_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_628_, v___y_629_, v_a_630_, v_b_631_);
lean_dec_ref(v___y_629_);
lean_dec(v___x_628_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(lean_object* v_a_635_, lean_object* v_as_636_, size_t v_i_637_, size_t v_stop_638_, lean_object* v_b_639_, lean_object* v___y_640_){
_start:
{
uint8_t v___x_642_; 
v___x_642_ = lean_usize_dec_eq(v_i_637_, v_stop_638_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_643_ = lean_array_uget_borrowed(v_as_636_, v_i_637_);
v___x_644_ = ((lean_object*)(l_Lake_compileLeanModule___closed__5));
v___x_645_ = lean_string_utf8_byte_size(v___x_643_);
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_645_, v___x_643_, v___x_646_, v___x_644_);
v___x_648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0));
v___x_649_ = lean_string_append(v___x_648_, v___x_647_);
lean_dec_ref(v___x_647_);
v___x_650_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1));
v___x_651_ = lean_string_append(v___x_649_, v___x_650_);
v___x_652_ = lean_io_prim_handle_put_str(v_a_635_, v___x_651_);
lean_dec_ref(v___x_651_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; size_t v___x_654_; size_t v___x_655_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_add(v_i_637_, v___x_654_);
v_i_637_ = v___x_655_;
v_b_639_ = v_a_653_;
goto _start;
}
else
{
lean_object* v_a_657_; lean_object* v___x_658_; uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_a_657_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_652_, 1);
v___x_658_ = lean_io_error_to_string(v_a_657_);
v___x_659_ = 3;
v___x_660_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set_uint8(v___x_660_, sizeof(void*)*1, v___x_659_);
v___x_661_ = lean_array_get_size(v___y_640_);
v___x_662_ = lean_array_push(v___y_640_, v___x_660_);
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
return v___x_663_;
}
}
else
{
lean_object* v___x_664_; 
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v_b_639_);
lean_ctor_set(v___x_664_, 1, v___y_640_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___boxed(lean_object* v_a_665_, lean_object* v_as_666_, lean_object* v_i_667_, lean_object* v_stop_668_, lean_object* v_b_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
size_t v_i_boxed_672_; size_t v_stop_boxed_673_; lean_object* v_res_674_; 
v_i_boxed_672_ = lean_unbox_usize(v_i_667_);
lean_dec(v_i_667_);
v_stop_boxed_673_ = lean_unbox_usize(v_stop_668_);
lean_dec(v_stop_668_);
v_res_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_665_, v_as_666_, v_i_boxed_672_, v_stop_boxed_673_, v_b_669_, v___y_670_);
lean_dec_ref(v_as_666_);
lean_dec(v_a_665_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object* v_basePath_677_, lean_object* v_args_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_681_; lean_object* v_rspFile_682_; lean_object* v_a_684_; lean_object* v___y_692_; uint8_t v___x_703_; lean_object* v___x_704_; 
v___x_681_ = ((lean_object*)(l_Lake_mkArgs___closed__0));
v_rspFile_682_ = l_System_FilePath_addExtension(v_basePath_677_, v___x_681_);
v___x_703_ = 1;
v___x_704_ = lean_io_prim_handle_mk(v_rspFile_682_, v___x_703_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_array_get_size(v_args_678_);
v___x_708_ = lean_nat_dec_lt(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_dec(v_a_705_);
v_a_684_ = v_a_679_;
goto v___jp_683_;
}
else
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = lean_box(0);
v___x_710_ = lean_nat_dec_le(v___x_707_, v___x_707_);
if (v___x_710_ == 0)
{
if (v___x_708_ == 0)
{
lean_dec(v_a_705_);
v_a_684_ = v_a_679_;
goto v___jp_683_;
}
else
{
size_t v___x_711_; size_t v___x_712_; lean_object* v___x_713_; 
v___x_711_ = ((size_t)0ULL);
v___x_712_ = lean_usize_of_nat(v___x_707_);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_705_, v_args_678_, v___x_711_, v___x_712_, v___x_709_, v_a_679_);
lean_dec(v_a_705_);
v___y_692_ = v___x_713_;
goto v___jp_691_;
}
}
else
{
size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v___x_714_ = ((size_t)0ULL);
v___x_715_ = lean_usize_of_nat(v___x_707_);
v___x_716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_705_, v_args_678_, v___x_714_, v___x_715_, v___x_709_, v_a_679_);
lean_dec(v_a_705_);
v___y_692_ = v___x_716_;
goto v___jp_691_;
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_718_; uint8_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
lean_dec_ref(v_rspFile_682_);
v_a_717_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_704_, 1);
v___x_718_ = lean_io_error_to_string(v_a_717_);
v___x_719_ = 3;
v___x_720_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set_uint8(v___x_720_, sizeof(void*)*1, v___x_719_);
v___x_721_ = lean_array_get_size(v_a_679_);
v___x_722_ = lean_array_push(v_a_679_, v___x_720_);
v___x_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
return v___x_723_;
}
v___jp_683_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_685_ = ((lean_object*)(l_Lake_mkArgs___closed__1));
v___x_686_ = lean_string_append(v___x_685_, v_rspFile_682_);
lean_dec_ref(v_rspFile_682_);
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_mk_empty_array_with_capacity(v___x_687_);
v___x_689_ = lean_array_push(v___x_688_, v___x_686_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_a_684_);
return v___x_690_;
}
v___jp_691_:
{
if (lean_obj_tag(v___y_692_) == 0)
{
lean_object* v_a_693_; 
v_a_693_ = lean_ctor_get(v___y_692_, 1);
lean_inc(v_a_693_);
lean_dec_ref_known(v___y_692_, 2);
v_a_684_ = v_a_693_;
goto v___jp_683_;
}
else
{
lean_object* v_a_694_; lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec_ref(v_rspFile_682_);
v_a_694_ = lean_ctor_get(v___y_692_, 0);
v_a_695_ = lean_ctor_get(v___y_692_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v___y_692_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___y_692_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_inc(v_a_694_);
lean_dec(v___y_692_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_694_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs___boxed(lean_object* v_basePath_724_, lean_object* v_args_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lake_mkArgs(v_basePath_724_, v_args_725_, v_a_726_);
lean_dec_ref(v_args_725_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(lean_object* v___x_729_, lean_object* v___x_730_, lean_object* v___y_731_, lean_object* v_inst_732_, lean_object* v_R_733_, lean_object* v_a_734_, lean_object* v_b_735_, lean_object* v_c_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_730_, v___y_731_, v_a_734_, v_b_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(lean_object* v___x_738_, lean_object* v___x_739_, lean_object* v___y_740_, lean_object* v_inst_741_, lean_object* v_R_742_, lean_object* v_a_743_, lean_object* v_b_744_, lean_object* v_c_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(v___x_738_, v___x_739_, v___y_740_, v_inst_741_, v_R_742_, v_a_743_, v_b_744_, v_c_745_);
lean_dec_ref(v___y_740_);
lean_dec(v___x_739_);
lean_dec_ref(v___x_738_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(size_t v_sz_747_, size_t v_i_748_, lean_object* v_bs_749_){
_start:
{
uint8_t v___x_750_; 
v___x_750_ = lean_usize_dec_lt(v_i_748_, v_sz_747_);
if (v___x_750_ == 0)
{
return v_bs_749_;
}
else
{
lean_object* v_v_751_; lean_object* v___x_752_; lean_object* v_bs_x27_753_; size_t v___x_754_; size_t v___x_755_; lean_object* v___x_756_; 
v_v_751_ = lean_array_uget(v_bs_749_, v_i_748_);
v___x_752_ = lean_unsigned_to_nat(0u);
v_bs_x27_753_ = lean_array_uset(v_bs_749_, v_i_748_, v___x_752_);
v___x_754_ = ((size_t)1ULL);
v___x_755_ = lean_usize_add(v_i_748_, v___x_754_);
v___x_756_ = lean_array_uset(v_bs_x27_753_, v_i_748_, v_v_751_);
v_i_748_ = v___x_755_;
v_bs_749_ = v___x_756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0___boxed(lean_object* v_sz_758_, lean_object* v_i_759_, lean_object* v_bs_760_){
_start:
{
size_t v_sz_boxed_761_; size_t v_i_boxed_762_; lean_object* v_res_763_; 
v_sz_boxed_761_ = lean_unbox_usize(v_sz_758_);
lean_dec(v_sz_758_);
v_i_boxed_762_ = lean_unbox_usize(v_i_759_);
lean_dec(v_i_759_);
v_res_763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_boxed_761_, v_i_boxed_762_, v_bs_760_);
return v_res_763_;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__3(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = ((lean_object*)(l_Lake_compileStaticLib___closed__2));
v___x_771_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_772_ = lean_array_push(v___x_771_, v___x_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object* v_libFile_773_, lean_object* v_oFiles_774_, lean_object* v_ar_775_, uint8_t v_thin_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___x_779_; 
lean_inc_ref(v_libFile_773_);
v___x_779_ = l_Lake_createParentDirs(v_libFile_773_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; 
lean_dec_ref_known(v___x_779_, 1);
v___x_780_ = l_Lake_removeFileIfExists(v_libFile_773_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v___x_781_; uint8_t v___x_782_; lean_object* v___y_784_; 
lean_dec_ref_known(v___x_780_, 1);
v___x_781_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_782_ = 1;
if (v_thin_776_ == 0)
{
v___y_784_ = v___x_781_;
goto v___jp_783_;
}
else
{
lean_object* v___x_808_; 
v___x_808_ = lean_obj_once(&l_Lake_compileStaticLib___closed__3, &l_Lake_compileStaticLib___closed__3_once, _init_l_Lake_compileStaticLib___closed__3);
v___y_784_ = v___x_808_;
goto v___jp_783_;
}
v___jp_783_:
{
size_t v_sz_785_; size_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_sz_785_ = lean_array_size(v_oFiles_774_);
v___x_786_ = ((size_t)0ULL);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_785_, v___x_786_, v_oFiles_774_);
lean_inc_ref(v_libFile_773_);
v___x_788_ = l_Lake_mkArgs(v_libFile_773_, v___x_787_, v_a_777_);
lean_dec_ref(v___x_787_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v_a_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
v_a_790_ = lean_ctor_get(v___x_788_, 1);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_788_, 2);
lean_inc_ref(v___y_784_);
v___x_791_ = lean_array_push(v___y_784_, v_libFile_773_);
v___x_792_ = l_Array_append___redArg(v___x_791_, v_a_789_);
lean_dec(v_a_789_);
v___x_793_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_794_ = lean_box(0);
v___x_795_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_796_ = 0;
v___x_797_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_797_, 0, v___x_793_);
lean_ctor_set(v___x_797_, 1, v_ar_775_);
lean_ctor_set(v___x_797_, 2, v___x_792_);
lean_ctor_set(v___x_797_, 3, v___x_794_);
lean_ctor_set(v___x_797_, 4, v___x_795_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*5, v___x_782_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*5 + 1, v___x_796_);
v___x_798_ = l_Lake_proc(v___x_797_, v___x_796_, v___x_794_, v_a_790_);
return v___x_798_;
}
else
{
lean_object* v_a_799_; lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v_ar_775_);
lean_dec_ref(v_libFile_773_);
v_a_799_ = lean_ctor_get(v___x_788_, 0);
v_a_800_ = lean_ctor_get(v___x_788_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_788_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_inc(v_a_799_);
lean_dec(v___x_788_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_799_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_810_; uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec_ref(v_ar_775_);
lean_dec_ref(v_oFiles_774_);
lean_dec_ref(v_libFile_773_);
v_a_809_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_780_, 1);
v___x_810_ = lean_io_error_to_string(v_a_809_);
v___x_811_ = 3;
v___x_812_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set_uint8(v___x_812_, sizeof(void*)*1, v___x_811_);
v___x_813_ = lean_array_get_size(v_a_777_);
v___x_814_ = lean_array_push(v_a_777_, v___x_812_);
v___x_815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
return v___x_815_;
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_817_; uint8_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec_ref(v_ar_775_);
lean_dec_ref(v_oFiles_774_);
lean_dec_ref(v_libFile_773_);
v_a_816_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_816_);
lean_dec_ref_known(v___x_779_, 1);
v___x_817_ = lean_io_error_to_string(v_a_816_);
v___x_818_ = 3;
v___x_819_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*1, v___x_818_);
v___x_820_ = lean_array_get_size(v_a_777_);
v___x_821_ = lean_array_push(v_a_777_, v___x_819_);
v___x_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object* v_libFile_823_, lean_object* v_oFiles_824_, lean_object* v_ar_825_, lean_object* v_thin_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
uint8_t v_thin_boxed_829_; lean_object* v_res_830_; 
v_thin_boxed_829_ = lean_unbox(v_thin_826_);
v_res_830_ = l_Lake_compileStaticLib(v_libFile_823_, v_oFiles_824_, v_ar_825_, v_thin_boxed_829_, v_a_827_);
return v_res_830_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__1(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_832_ = ((lean_object*)(l_Lake_compileSharedLib___closed__0));
v___x_833_ = lean_unsigned_to_nat(3u);
v___x_834_ = lean_mk_empty_array_with_capacity(v___x_833_);
v___x_835_ = lean_array_push(v___x_834_, v___x_832_);
return v___x_835_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__2(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_837_ = lean_obj_once(&l_Lake_compileSharedLib___closed__1, &l_Lake_compileSharedLib___closed__1_once, _init_l_Lake_compileSharedLib___closed__1);
v___x_838_ = lean_array_push(v___x_837_, v___x_836_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object* v_libFile_840_, lean_object* v_linkArgs_841_, lean_object* v_linker_842_, lean_object* v_macosxDeploymentTarget_x3f_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_846_; 
lean_inc_ref(v_libFile_840_);
v___x_846_ = l_Lake_createParentDirs(v_libFile_840_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v___x_847_; 
lean_dec_ref_known(v___x_846_, 1);
lean_inc_ref(v_libFile_840_);
v___x_847_ = l_Lake_mkArgs(v_libFile_840_, v_linkArgs_841_, v_a_844_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v_a_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___y_856_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
v_a_849_ = lean_ctor_get(v___x_847_, 1);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_847_, 2);
v___x_850_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_851_ = lean_obj_once(&l_Lake_compileSharedLib___closed__2, &l_Lake_compileSharedLib___closed__2_once, _init_l_Lake_compileSharedLib___closed__2);
v___x_852_ = lean_array_push(v___x_851_, v_libFile_840_);
v___x_853_ = l_Array_append___redArg(v___x_852_, v_a_848_);
lean_dec(v_a_848_);
v___x_854_ = lean_box(0);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_843_) == 0)
{
lean_object* v___x_861_; 
v___x_861_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_856_ = v___x_861_;
goto v___jp_855_;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_862_ = ((lean_object*)(l_Lake_compileSharedLib___closed__3));
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v_macosxDeploymentTarget_x3f_843_);
v___x_864_ = lean_unsigned_to_nat(1u);
v___x_865_ = lean_mk_empty_array_with_capacity(v___x_864_);
v___x_866_ = lean_array_push(v___x_865_, v___x_863_);
v___y_856_ = v___x_866_;
goto v___jp_855_;
}
v___jp_855_:
{
uint8_t v___x_857_; uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_857_ = 1;
v___x_858_ = 0;
v___x_859_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_859_, 0, v___x_850_);
lean_ctor_set(v___x_859_, 1, v_linker_842_);
lean_ctor_set(v___x_859_, 2, v___x_853_);
lean_ctor_set(v___x_859_, 3, v___x_854_);
lean_ctor_set(v___x_859_, 4, v___y_856_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*5, v___x_857_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*5 + 1, v___x_858_);
v___x_860_ = l_Lake_proc(v___x_859_, v___x_858_, v___x_854_, v_a_849_);
return v___x_860_;
}
}
else
{
lean_object* v_a_867_; lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_macosxDeploymentTarget_x3f_843_);
lean_dec_ref(v_linker_842_);
lean_dec_ref(v_libFile_840_);
v_a_867_ = lean_ctor_get(v___x_847_, 0);
v_a_868_ = lean_ctor_get(v___x_847_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_847_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_inc(v_a_867_);
lean_dec(v___x_847_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_867_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_877_; uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec(v_macosxDeploymentTarget_x3f_843_);
lean_dec_ref(v_linker_842_);
lean_dec_ref(v_libFile_840_);
v_a_876_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_846_, 1);
v___x_877_ = lean_io_error_to_string(v_a_876_);
v___x_878_ = 3;
v___x_879_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*1, v___x_878_);
v___x_880_ = lean_array_get_size(v_a_844_);
v___x_881_ = lean_array_push(v_a_844_, v___x_879_);
v___x_882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
return v___x_882_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object* v_libFile_883_, lean_object* v_linkArgs_884_, lean_object* v_linker_885_, lean_object* v_macosxDeploymentTarget_x3f_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lake_compileSharedLib(v_libFile_883_, v_linkArgs_884_, v_linker_885_, v_macosxDeploymentTarget_x3f_886_, v_a_887_);
lean_dec_ref(v_linkArgs_884_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object* v_binFile_890_, lean_object* v_linkArgs_891_, lean_object* v_linker_892_, lean_object* v_macosxDeploymentTarget_x3f_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_896_; 
lean_inc_ref(v_binFile_890_);
v___x_896_ = l_Lake_createParentDirs(v_binFile_890_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v___x_897_; 
lean_dec_ref_known(v___x_896_, 1);
lean_inc_ref(v_binFile_890_);
v___x_897_ = l_Lake_mkArgs(v_binFile_890_, v_linkArgs_891_, v_a_894_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v_a_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___y_908_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
v_a_899_ = lean_ctor_get(v___x_897_, 1);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_897_, 2);
v___x_900_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_901_ = lean_unsigned_to_nat(2u);
v___x_902_ = lean_mk_empty_array_with_capacity(v___x_901_);
lean_dec_ref(v___x_902_);
v___x_903_ = lean_obj_once(&l_Lake_compileLeanModule___closed__15, &l_Lake_compileLeanModule___closed__15_once, _init_l_Lake_compileLeanModule___closed__15);
v___x_904_ = lean_array_push(v___x_903_, v_binFile_890_);
v___x_905_ = l_Array_append___redArg(v___x_904_, v_a_898_);
lean_dec(v_a_898_);
v___x_906_ = lean_box(0);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_893_) == 0)
{
lean_object* v___x_913_; 
v___x_913_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_908_ = v___x_913_;
goto v___jp_907_;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_914_ = ((lean_object*)(l_Lake_compileSharedLib___closed__3));
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v_macosxDeploymentTarget_x3f_893_);
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_mk_empty_array_with_capacity(v___x_916_);
v___x_918_ = lean_array_push(v___x_917_, v___x_915_);
v___y_908_ = v___x_918_;
goto v___jp_907_;
}
v___jp_907_:
{
uint8_t v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_909_ = 1;
v___x_910_ = 0;
v___x_911_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_911_, 0, v___x_900_);
lean_ctor_set(v___x_911_, 1, v_linker_892_);
lean_ctor_set(v___x_911_, 2, v___x_905_);
lean_ctor_set(v___x_911_, 3, v___x_906_);
lean_ctor_set(v___x_911_, 4, v___y_908_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*5, v___x_909_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*5 + 1, v___x_910_);
v___x_912_ = l_Lake_proc(v___x_911_, v___x_910_, v___x_906_, v_a_899_);
return v___x_912_;
}
}
else
{
lean_object* v_a_919_; lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec(v_macosxDeploymentTarget_x3f_893_);
lean_dec_ref(v_linker_892_);
lean_dec_ref(v_binFile_890_);
v_a_919_ = lean_ctor_get(v___x_897_, 0);
v_a_920_ = lean_ctor_get(v___x_897_, 1);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_897_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_inc(v_a_919_);
lean_dec(v___x_897_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_919_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_929_; uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec(v_macosxDeploymentTarget_x3f_893_);
lean_dec_ref(v_linker_892_);
lean_dec_ref(v_binFile_890_);
v_a_928_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_896_, 1);
v___x_929_ = lean_io_error_to_string(v_a_928_);
v___x_930_ = 3;
v___x_931_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*1, v___x_930_);
v___x_932_ = lean_array_get_size(v_a_894_);
v___x_933_ = lean_array_push(v_a_894_, v___x_931_);
v___x_934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object* v_binFile_935_, lean_object* v_linkArgs_936_, lean_object* v_linker_937_, lean_object* v_macosxDeploymentTarget_x3f_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lake_compileExe(v_binFile_935_, v_linkArgs_936_, v_linker_937_, v_macosxDeploymentTarget_x3f_938_, v_a_939_);
lean_dec_ref(v_linkArgs_936_);
return v_res_941_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_943_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0));
v___x_944_ = lean_unsigned_to_nat(2u);
v___x_945_ = lean_mk_empty_array_with_capacity(v___x_944_);
v___x_946_ = lean_array_push(v___x_945_, v___x_943_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(lean_object* v_as_947_, size_t v_i_948_, size_t v_stop_949_, lean_object* v_b_950_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = lean_usize_dec_eq(v_i_948_, v_stop_949_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; size_t v___x_956_; size_t v___x_957_; 
v___x_952_ = lean_array_uget_borrowed(v_as_947_, v_i_948_);
v___x_953_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1);
lean_inc(v___x_952_);
v___x_954_ = lean_array_push(v___x_953_, v___x_952_);
v___x_955_ = l_Array_append___redArg(v_b_950_, v___x_954_);
lean_dec_ref(v___x_954_);
v___x_956_ = ((size_t)1ULL);
v___x_957_ = lean_usize_add(v_i_948_, v___x_956_);
v_i_948_ = v___x_957_;
v_b_950_ = v___x_955_;
goto _start;
}
else
{
return v_b_950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___boxed(lean_object* v_as_959_, lean_object* v_i_960_, lean_object* v_stop_961_, lean_object* v_b_962_){
_start:
{
size_t v_i_boxed_963_; size_t v_stop_boxed_964_; lean_object* v_res_965_; 
v_i_boxed_963_ = lean_unbox_usize(v_i_960_);
lean_dec(v_i_960_);
v_stop_boxed_964_ = lean_unbox_usize(v_stop_961_);
lean_dec(v_stop_961_);
v_res_965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_as_959_, v_i_boxed_963_, v_stop_boxed_964_, v_b_962_);
lean_dec_ref(v_as_959_);
return v_res_965_;
}
}
static lean_object* _init_l_Lake_download___closed__6(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_972_ = ((lean_object*)(l_Lake_download___closed__2));
v___x_973_ = lean_unsigned_to_nat(7u);
v___x_974_ = lean_mk_empty_array_with_capacity(v___x_973_);
v___x_975_ = lean_array_push(v___x_974_, v___x_972_);
return v___x_975_;
}
}
static lean_object* _init_l_Lake_download___closed__7(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_977_ = lean_obj_once(&l_Lake_download___closed__6, &l_Lake_download___closed__6_once, _init_l_Lake_download___closed__6);
v___x_978_ = lean_array_push(v___x_977_, v___x_976_);
return v___x_978_;
}
}
static lean_object* _init_l_Lake_download___closed__8(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_980_ = lean_obj_once(&l_Lake_download___closed__7, &l_Lake_download___closed__7_once, _init_l_Lake_download___closed__7);
v___x_981_ = lean_array_push(v___x_980_, v___x_979_);
return v___x_981_;
}
}
static lean_object* _init_l_Lake_download___closed__9(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = ((lean_object*)(l_Lake_compileLeanModule___closed__14));
v___x_983_ = lean_obj_once(&l_Lake_download___closed__8, &l_Lake_download___closed__8_once, _init_l_Lake_download___closed__8);
v___x_984_ = lean_array_push(v___x_983_, v___x_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lake_download(lean_object* v_url_985_, lean_object* v_file_986_, lean_object* v_headers_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v_val_993_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1009_; uint8_t v___x_1025_; 
v___x_1025_ = l_System_FilePath_pathExists(v_file_986_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
lean_inc_ref(v_file_986_);
v___x_1026_ = l_Lake_createParentDirs(v_file_986_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_dec_ref_known(v___x_1026_, 1);
v___y_1009_ = v_a_988_;
goto v___jp_1008_;
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec_ref(v_file_986_);
lean_dec_ref(v_url_985_);
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = lean_io_error_to_string(v_a_1027_);
v___x_1029_ = 3;
v___x_1030_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*1, v___x_1029_);
v___x_1031_ = lean_array_get_size(v_a_988_);
v___x_1032_ = lean_array_push(v_a_988_, v___x_1030_);
v___x_1033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
return v___x_1033_;
}
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_io_remove_file(v_file_986_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_dec_ref_known(v___x_1034_, 1);
v___y_1009_ = v_a_988_;
goto v___jp_1008_;
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec_ref(v_file_986_);
lean_dec_ref(v_url_985_);
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = lean_io_error_to_string(v_a_1035_);
v___x_1037_ = 3;
v___x_1038_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*1, v___x_1037_);
v___x_1039_ = lean_array_get_size(v_a_988_);
v___x_1040_ = lean_array_push(v_a_988_, v___x_1038_);
v___x_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
return v___x_1041_;
}
}
v___jp_990_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_994_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_995_ = lean_box(0);
v___x_996_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_997_ = 1;
v___x_998_ = 0;
v___x_999_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_999_, 0, v___x_994_);
lean_ctor_set(v___x_999_, 1, v_val_993_);
lean_ctor_set(v___x_999_, 2, v___y_991_);
lean_ctor_set(v___x_999_, 3, v___x_995_);
lean_ctor_set(v___x_999_, 4, v___x_996_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*5, v___x_997_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*5 + 1, v___x_998_);
v___x_1000_ = l_Lake_proc(v___x_999_, v___x_997_, v___x_995_, v___y_992_);
return v___x_1000_;
}
v___jp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l_Lake_download___closed__0));
v___x_1005_ = lean_io_getenv(v___x_1004_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = ((lean_object*)(l_Lake_download___closed__1));
v___y_991_ = v___y_1003_;
v___y_992_ = v___y_1002_;
v_val_993_ = v___x_1006_;
goto v___jp_990_;
}
else
{
lean_object* v_val_1007_; 
v_val_1007_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v___x_1005_, 1);
v___y_991_ = v___y_1003_;
v___y_992_ = v___y_1002_;
v_val_993_ = v_val_1007_;
goto v___jp_990_;
}
}
v___jp_1008_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1010_ = ((lean_object*)(l_Lake_download___closed__5));
v___x_1011_ = lean_obj_once(&l_Lake_download___closed__9, &l_Lake_download___closed__9_once, _init_l_Lake_download___closed__9);
v___x_1012_ = lean_array_push(v___x_1011_, v_file_986_);
v___x_1013_ = lean_array_push(v___x_1012_, v___x_1010_);
v___x_1014_ = lean_array_push(v___x_1013_, v_url_985_);
v___x_1015_ = lean_unsigned_to_nat(0u);
v___x_1016_ = lean_array_get_size(v_headers_987_);
v___x_1017_ = lean_nat_dec_lt(v___x_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
v___y_1002_ = v___y_1009_;
v___y_1003_ = v___x_1014_;
goto v___jp_1001_;
}
else
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_nat_dec_le(v___x_1016_, v___x_1016_);
if (v___x_1018_ == 0)
{
if (v___x_1017_ == 0)
{
v___y_1002_ = v___y_1009_;
v___y_1003_ = v___x_1014_;
goto v___jp_1001_;
}
else
{
size_t v___x_1019_; size_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = ((size_t)0ULL);
v___x_1020_ = lean_usize_of_nat(v___x_1016_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_987_, v___x_1019_, v___x_1020_, v___x_1014_);
v___y_1002_ = v___y_1009_;
v___y_1003_ = v___x_1021_;
goto v___jp_1001_;
}
}
else
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = ((size_t)0ULL);
v___x_1023_ = lean_usize_of_nat(v___x_1016_);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_987_, v___x_1022_, v___x_1023_, v___x_1014_);
v___y_1002_ = v___y_1009_;
v___y_1003_ = v___x_1024_;
goto v___jp_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object* v_url_1042_, lean_object* v_file_1043_, lean_object* v_headers_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lake_download(v_url_1042_, v_file_1043_, v_headers_1044_, v_a_1045_);
lean_dec_ref(v_headers_1044_);
return v_res_1047_;
}
}
static lean_object* _init_l_Lake_untar___closed__3(void){
_start:
{
uint32_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = 122;
v___x_1052_ = ((lean_object*)(l_Lake_untar___closed__2));
v___x_1053_ = lean_string_push(v___x_1052_, v___x_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lake_untar(lean_object* v_file_1054_, lean_object* v_dir_1055_, uint8_t v_gzip_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_opts_1060_; lean_object* v___y_1061_; lean_object* v___x_1079_; 
lean_inc_ref(v_dir_1055_);
v___x_1079_ = l_IO_FS_createDirAll(v_dir_1055_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v___x_1080_; 
lean_dec_ref_known(v___x_1079_, 1);
v___x_1080_ = ((lean_object*)(l_Lake_untar___closed__2));
if (v_gzip_1056_ == 0)
{
v_opts_1060_ = v___x_1080_;
v___y_1061_ = v_a_1057_;
goto v___jp_1059_;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_obj_once(&l_Lake_untar___closed__3, &l_Lake_untar___closed__3_once, _init_l_Lake_untar___closed__3);
v_opts_1060_ = v___x_1081_;
v___y_1061_ = v_a_1057_;
goto v___jp_1059_;
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_dec_ref(v_dir_1055_);
lean_dec_ref(v_file_1054_);
v_a_1082_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1083_ = lean_io_error_to_string(v_a_1082_);
v___x_1084_ = 3;
v___x_1085_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*1, v___x_1084_);
v___x_1086_ = lean_array_get_size(v_a_1057_);
v___x_1087_ = lean_array_push(v_a_1057_, v___x_1085_);
v___x_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
return v___x_1088_;
}
v___jp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1062_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_1063_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_1064_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_1065_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_1066_ = lean_unsigned_to_nat(5u);
v___x_1067_ = lean_mk_empty_array_with_capacity(v___x_1066_);
lean_inc_ref(v_opts_1060_);
v___x_1068_ = lean_array_push(v___x_1067_, v_opts_1060_);
v___x_1069_ = lean_array_push(v___x_1068_, v___x_1064_);
v___x_1070_ = lean_array_push(v___x_1069_, v_file_1054_);
v___x_1071_ = lean_array_push(v___x_1070_, v___x_1065_);
v___x_1072_ = lean_array_push(v___x_1071_, v_dir_1055_);
v___x_1073_ = lean_box(0);
v___x_1074_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_1075_ = 1;
v___x_1076_ = 0;
v___x_1077_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1077_, 0, v___x_1062_);
lean_ctor_set(v___x_1077_, 1, v___x_1063_);
lean_ctor_set(v___x_1077_, 2, v___x_1072_);
lean_ctor_set(v___x_1077_, 3, v___x_1073_);
lean_ctor_set(v___x_1077_, 4, v___x_1074_);
lean_ctor_set_uint8(v___x_1077_, sizeof(void*)*5, v___x_1075_);
lean_ctor_set_uint8(v___x_1077_, sizeof(void*)*5 + 1, v___x_1076_);
v___x_1078_ = l_Lake_proc(v___x_1077_, v___x_1075_, v___x_1073_, v___y_1061_);
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object* v_file_1089_, lean_object* v_dir_1090_, lean_object* v_gzip_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
uint8_t v_gzip_boxed_1094_; lean_object* v_res_1095_; 
v_gzip_boxed_1094_ = lean_unbox(v_gzip_1091_);
v_res_1095_ = l_Lake_untar(v_file_1089_, v_dir_1090_, v_gzip_boxed_1094_, v_a_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(lean_object* v_as_1097_, size_t v_sz_1098_, size_t v_i_1099_, lean_object* v_b_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_usize_dec_lt(v_i_1099_, v_sz_1098_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v_b_1100_);
lean_ctor_set(v___x_1104_, 1, v___y_1101_);
return v___x_1104_;
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; 
v_a_1105_ = lean_array_uget_borrowed(v_as_1097_, v_i_1099_);
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0));
v___x_1107_ = lean_string_append(v___x_1106_, v_a_1105_);
v___x_1108_ = lean_array_push(v_b_1100_, v___x_1107_);
v___x_1109_ = ((size_t)1ULL);
v___x_1110_ = lean_usize_add(v_i_1099_, v___x_1109_);
v_i_1099_ = v___x_1110_;
v_b_1100_ = v___x_1108_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___boxed(lean_object* v_as_1112_, lean_object* v_sz_1113_, lean_object* v_i_1114_, lean_object* v_b_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
size_t v_sz_boxed_1118_; size_t v_i_boxed_1119_; lean_object* v_res_1120_; 
v_sz_boxed_1118_ = lean_unbox_usize(v_sz_1113_);
lean_dec(v_sz_1113_);
v_i_boxed_1119_ = lean_unbox_usize(v_i_1114_);
lean_dec(v_i_1114_);
v_res_1120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_as_1112_, v_sz_boxed_1118_, v_i_boxed_1119_, v_b_1115_, v___y_1116_);
lean_dec_ref(v_as_1112_);
return v_res_1120_;
}
}
static lean_object* _init_l_Lake_tar___closed__1(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1122_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_1123_ = lean_unsigned_to_nat(5u);
v___x_1124_ = lean_mk_empty_array_with_capacity(v___x_1123_);
v___x_1125_ = lean_array_push(v___x_1124_, v___x_1122_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lake_tar___closed__10(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = ((lean_object*)(l_Lake_tar___closed__9));
v___x_1144_ = ((lean_object*)(l_Lake_tar___closed__8));
v___x_1145_ = lean_array_push(v___x_1144_, v___x_1143_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lake_tar(lean_object* v_dir_1146_, lean_object* v_file_1147_, uint8_t v_gzip_1148_, lean_object* v_excludePaths_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; uint8_t v___y_1158_; lean_object* v___y_1159_; lean_object* v_args_1165_; lean_object* v___y_1166_; lean_object* v___x_1196_; 
lean_inc_ref(v_file_1147_);
v___x_1196_ = l_Lake_createParentDirs(v_file_1147_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref_known(v___x_1196_, 1);
v___x_1197_ = ((lean_object*)(l_Lake_tar___closed__8));
if (v_gzip_1148_ == 0)
{
v_args_1165_ = v___x_1197_;
v___y_1166_ = v_a_1150_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_obj_once(&l_Lake_tar___closed__10, &l_Lake_tar___closed__10_once, _init_l_Lake_tar___closed__10);
v_args_1165_ = v___x_1198_;
v___y_1166_ = v_a_1150_;
goto v___jp_1164_;
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec_ref(v_file_1147_);
lean_dec_ref(v_dir_1146_);
v_a_1199_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1196_, 1);
v___x_1200_ = lean_io_error_to_string(v_a_1199_);
v___x_1201_ = 3;
v___x_1202_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set_uint8(v___x_1202_, sizeof(void*)*1, v___x_1201_);
v___x_1203_ = lean_array_get_size(v_a_1150_);
v___x_1204_ = lean_array_push(v_a_1150_, v___x_1202_);
v___x_1205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
return v___x_1205_;
}
v___jp_1152_:
{
uint8_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1160_ = 0;
lean_inc_ref(v___y_1159_);
lean_inc(v___y_1155_);
lean_inc_ref(v___y_1154_);
lean_inc_ref(v___y_1157_);
v___x_1161_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1161_, 0, v___y_1157_);
lean_ctor_set(v___x_1161_, 1, v___y_1154_);
lean_ctor_set(v___x_1161_, 2, v___y_1153_);
lean_ctor_set(v___x_1161_, 3, v___y_1155_);
lean_ctor_set(v___x_1161_, 4, v___y_1159_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*5, v___y_1158_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*5 + 1, v___x_1160_);
v___x_1162_ = lean_box(0);
v___x_1163_ = l_Lake_proc(v___x_1161_, v___y_1158_, v___x_1162_, v___y_1156_);
return v___x_1163_;
}
v___jp_1164_:
{
size_t v_sz_1167_; size_t v___x_1168_; lean_object* v___x_1169_; 
v_sz_1167_ = lean_array_size(v_excludePaths_1149_);
v___x_1168_ = ((size_t)0ULL);
lean_inc_ref(v_args_1165_);
v___x_1169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_excludePaths_1149_, v_sz_1167_, v___x_1168_, v_args_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v_a_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; uint8_t v___x_1184_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
v_a_1171_ = lean_ctor_get(v___x_1169_, 1);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1169_, 2);
v___x_1172_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_1173_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_1174_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_1175_ = ((lean_object*)(l_Lake_tar___closed__0));
v___x_1176_ = lean_obj_once(&l_Lake_tar___closed__1, &l_Lake_tar___closed__1_once, _init_l_Lake_tar___closed__1);
v___x_1177_ = lean_array_push(v___x_1176_, v_file_1147_);
v___x_1178_ = lean_array_push(v___x_1177_, v___x_1174_);
v___x_1179_ = lean_array_push(v___x_1178_, v_dir_1146_);
v___x_1180_ = lean_array_push(v___x_1179_, v___x_1175_);
v___x_1181_ = l_Array_append___redArg(v_a_1170_, v___x_1180_);
lean_dec_ref(v___x_1180_);
v___x_1182_ = lean_box(0);
v___x_1183_ = l_System_Platform_isOSX;
v___x_1184_ = 1;
if (v___x_1183_ == 0)
{
lean_object* v___x_1185_; 
v___x_1185_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_1153_ = v___x_1181_;
v___y_1154_ = v___x_1173_;
v___y_1155_ = v___x_1182_;
v___y_1156_ = v_a_1171_;
v___y_1157_ = v___x_1172_;
v___y_1158_ = v___x_1184_;
v___y_1159_ = v___x_1185_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1186_; 
v___x_1186_ = ((lean_object*)(l_Lake_tar___closed__6));
v___y_1153_ = v___x_1181_;
v___y_1154_ = v___x_1173_;
v___y_1155_ = v___x_1182_;
v___y_1156_ = v_a_1171_;
v___y_1157_ = v___x_1172_;
v___y_1158_ = v___x_1184_;
v___y_1159_ = v___x_1186_;
goto v___jp_1152_;
}
}
else
{
lean_object* v_a_1187_; lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec_ref(v_file_1147_);
lean_dec_ref(v_dir_1146_);
v_a_1187_ = lean_ctor_get(v___x_1169_, 0);
v_a_1188_ = lean_ctor_get(v___x_1169_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1169_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_inc(v_a_1187_);
lean_dec(v___x_1169_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1187_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object* v_dir_1206_, lean_object* v_file_1207_, lean_object* v_gzip_1208_, lean_object* v_excludePaths_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
uint8_t v_gzip_boxed_1212_; lean_object* v_res_1213_; 
v_gzip_boxed_1212_ = lean_unbox(v_gzip_1208_);
v_res_1213_ = l_Lake_tar(v_dir_1206_, v_file_1207_, v_gzip_boxed_1212_, v_excludePaths_1209_, v_a_1210_);
lean_dec_ref(v_excludePaths_1209_);
return v_res_1213_;
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
