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
lean_object* l_Lake_removeFileIfExists(lean_object*);
static const lean_ctor_object l_Lake_compileLeanIR___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_compileLeanIR___closed__0 = (const lean_object*)&l_Lake_compileLeanIR___closed__0_value;
static const lean_string_object l_Lake_compileLeanIR___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LEAN_PATH"};
static const lean_object* l_Lake_compileLeanIR___closed__1 = (const lean_object*)&l_Lake_compileLeanIR___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_compileLeanIR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanIR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake_compileLeanModule___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_compileLeanModule___closed__3 = (const lean_object*)&l_Lake_compileLeanModule___closed__3_value;
static const lean_string_object l_Lake_compileLeanModule___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "failed to execute '"};
static const lean_object* l_Lake_compileLeanModule___closed__4 = (const lean_object*)&l_Lake_compileLeanModule___closed__4_value;
static const lean_string_object l_Lake_compileLeanModule___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "': "};
static const lean_object* l_Lake_compileLeanModule___closed__5 = (const lean_object*)&l_Lake_compileLeanModule___closed__5_value;
static const lean_string_object l_Lake_compileLeanModule___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-b"};
static const lean_object* l_Lake_compileLeanModule___closed__6 = (const lean_object*)&l_Lake_compileLeanModule___closed__6_value;
static lean_once_cell_t l_Lake_compileLeanModule___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileLeanModule___closed__7;
static const lean_string_object l_Lake_compileLeanModule___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-c"};
static const lean_object* l_Lake_compileLeanModule___closed__8 = (const lean_object*)&l_Lake_compileLeanModule___closed__8_value;
static lean_once_cell_t l_Lake_compileLeanModule___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileLeanModule___closed__9;
static const lean_string_object l_Lake_compileLeanModule___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-i"};
static const lean_object* l_Lake_compileLeanModule___closed__10 = (const lean_object*)&l_Lake_compileLeanModule___closed__10_value;
static lean_once_cell_t l_Lake_compileLeanModule___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileLeanModule___closed__11;
static const lean_string_object l_Lake_compileLeanModule___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-o"};
static const lean_object* l_Lake_compileLeanModule___closed__12 = (const lean_object*)&l_Lake_compileLeanModule___closed__12_value;
static lean_once_cell_t l_Lake_compileLeanModule___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_compileLeanModule___closed__13;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake_untar___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "-xvvz"};
static const lean_object* l_Lake_untar___closed__3 = (const lean_object*)&l_Lake_untar___closed__3_value;
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
LEAN_EXPORT lean_object* l_Lake_compileLeanIR(lean_object* v_setupFile_4_, lean_object* v_irFile_5_, lean_object* v_cFile_6_, lean_object* v_leanPath_7_, lean_object* v_leanir_8_, lean_object* v_a_9_){
_start:
{
lean_object* v___x_11_; 
lean_inc_ref(v_irFile_5_);
v___x_11_ = l_Lake_createParentDirs(v_irFile_5_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_12_; 
lean_dec_ref_known(v___x_11_, 1);
lean_inc_ref(v_cFile_6_);
v___x_12_ = l_Lake_createParentDirs(v_cFile_6_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_36_; 
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_36_ == 0)
{
lean_object* v_unused_37_; 
v_unused_37_ = lean_ctor_get(v___x_12_, 0);
lean_dec(v_unused_37_);
v___x_14_ = v___x_12_;
v_isShared_15_ = v_isSharedCheck_36_;
goto v_resetjp_13_;
}
else
{
lean_dec(v___x_12_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_36_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_26_; 
v___x_16_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_17_ = lean_unsigned_to_nat(3u);
v___x_18_ = lean_mk_empty_array_with_capacity(v___x_17_);
v___x_19_ = lean_array_push(v___x_18_, v_setupFile_4_);
v___x_20_ = lean_array_push(v___x_19_, v_irFile_5_);
v___x_21_ = lean_array_push(v___x_20_, v_cFile_6_);
v___x_22_ = lean_box(0);
v___x_23_ = ((lean_object*)(l_Lake_compileLeanIR___closed__1));
v___x_24_ = l_System_SearchPath_toString(v_leanPath_7_);
if (v_isShared_15_ == 0)
{
lean_ctor_set_tag(v___x_14_, 1);
lean_ctor_set(v___x_14_, 0, v___x_24_);
v___x_26_ = v___x_14_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v___x_24_);
v___x_26_ = v_reuseFailAlloc_35_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_23_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
v___x_28_ = lean_unsigned_to_nat(1u);
v___x_29_ = lean_mk_empty_array_with_capacity(v___x_28_);
v___x_30_ = lean_array_push(v___x_29_, v___x_27_);
v___x_31_ = 1;
v___x_32_ = 0;
v___x_33_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_33_, 0, v___x_16_);
lean_ctor_set(v___x_33_, 1, v_leanir_8_);
lean_ctor_set(v___x_33_, 2, v___x_21_);
lean_ctor_set(v___x_33_, 3, v___x_22_);
lean_ctor_set(v___x_33_, 4, v___x_30_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*5, v___x_31_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*5 + 1, v___x_32_);
v___x_34_ = l_Lake_proc(v___x_33_, v___x_32_, v___x_22_, v_a_9_);
return v___x_34_;
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_39_; uint8_t v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
lean_dec_ref(v_leanir_8_);
lean_dec(v_leanPath_7_);
lean_dec_ref(v_cFile_6_);
lean_dec_ref(v_irFile_5_);
lean_dec_ref(v_setupFile_4_);
v_a_38_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_a_38_);
lean_dec_ref_known(v___x_12_, 1);
v___x_39_ = lean_io_error_to_string(v_a_38_);
v___x_40_ = 3;
v___x_41_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_41_, 0, v___x_39_);
lean_ctor_set_uint8(v___x_41_, sizeof(void*)*1, v___x_40_);
v___x_42_ = lean_array_get_size(v_a_9_);
v___x_43_ = lean_array_push(v_a_9_, v___x_41_);
v___x_44_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
return v___x_44_;
}
}
else
{
lean_object* v_a_45_; lean_object* v___x_46_; uint8_t v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec_ref(v_leanir_8_);
lean_dec(v_leanPath_7_);
lean_dec_ref(v_cFile_6_);
lean_dec_ref(v_irFile_5_);
lean_dec_ref(v_setupFile_4_);
v_a_45_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_a_45_);
lean_dec_ref_known(v___x_11_, 1);
v___x_46_ = lean_io_error_to_string(v_a_45_);
v___x_47_ = 3;
v___x_48_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_48_, 0, v___x_46_);
lean_ctor_set_uint8(v___x_48_, sizeof(void*)*1, v___x_47_);
v___x_49_ = lean_array_get_size(v_a_9_);
v___x_50_ = lean_array_push(v_a_9_, v___x_48_);
v___x_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_49_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanIR___boxed(lean_object* v_setupFile_52_, lean_object* v_irFile_53_, lean_object* v_cFile_54_, lean_object* v_leanPath_55_, lean_object* v_leanir_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lake_compileLeanIR(v_setupFile_52_, v_irFile_53_, v_cFile_54_, v_leanPath_55_, v_leanir_56_, v_a_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg(){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg___closed__0));
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg___boxed(lean_object* v___dummy_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg();
return v_res_65_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg();
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1(lean_object* v_s_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___boxed(lean_object* v_s_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1(v_s_69_);
lean_dec_ref(v_s_69_);
return v_res_70_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(lean_object* v_opts_71_, lean_object* v_opt_72_){
_start:
{
lean_object* v_name_73_; lean_object* v_defValue_74_; lean_object* v_map_75_; lean_object* v___x_76_; 
v_name_73_ = lean_ctor_get(v_opt_72_, 0);
v_defValue_74_ = lean_ctor_get(v_opt_72_, 1);
v_map_75_ = lean_ctor_get(v_opts_71_, 0);
v___x_76_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_75_, v_name_73_);
if (lean_obj_tag(v___x_76_) == 0)
{
uint8_t v___x_77_; 
v___x_77_ = lean_unbox(v_defValue_74_);
return v___x_77_;
}
else
{
lean_object* v_val_78_; 
v_val_78_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_val_78_);
lean_dec_ref_known(v___x_76_, 1);
if (lean_obj_tag(v_val_78_) == 1)
{
uint8_t v_v_79_; 
v_v_79_ = lean_ctor_get_uint8(v_val_78_, 0);
lean_dec_ref_known(v_val_78_, 0);
return v_v_79_;
}
else
{
uint8_t v___x_80_; 
lean_dec(v_val_78_);
v___x_80_ = lean_unbox(v_defValue_74_);
return v___x_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3___boxed(lean_object* v_opts_81_, lean_object* v_opt_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(v_opts_81_, v_opt_82_);
lean_dec_ref(v_opt_82_);
lean_dec_ref(v_opts_81_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(lean_object* v_as_85_, size_t v_i_86_, size_t v_stop_87_){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = lean_usize_dec_eq(v_i_86_, v_stop_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; uint8_t v_level_90_; 
v___x_89_ = lean_array_uget_borrowed(v_as_85_, v_i_86_);
v_level_90_ = lean_ctor_get_uint8(v___x_89_, sizeof(void*)*1);
if (v_level_90_ == 3)
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
else
{
size_t v___x_92_; size_t v___x_93_; 
v___x_92_ = ((size_t)1ULL);
v___x_93_ = lean_usize_add(v_i_86_, v___x_92_);
v_i_86_ = v___x_93_;
goto _start;
}
}
else
{
uint8_t v___x_95_; 
v___x_95_ = 0;
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0___boxed(lean_object* v_as_96_, lean_object* v_i_97_, lean_object* v_stop_98_){
_start:
{
size_t v_i_boxed_99_; size_t v_stop_boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v_i_boxed_99_ = lean_unbox_usize(v_i_97_);
lean_dec(v_i_97_);
v_stop_boxed_100_ = lean_unbox_usize(v_stop_98_);
lean_dec(v_stop_98_);
v_res_101_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(v_as_96_, v_i_boxed_99_, v_stop_boxed_100_);
lean_dec_ref(v_as_96_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint32_t v_exitCode_105_, lean_object* v___x_106_, lean_object* v_stderr_107_, lean_object* v_____r_108_, lean_object* v___y_109_){
_start:
{
uint32_t v___y_112_; lean_object* v___y_113_; uint32_t v___y_124_; uint8_t v___y_125_; lean_object* v___y_126_; lean_object* v___y_132_; uint8_t v___y_133_; lean_object* v___y_139_; lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = lean_string_utf8_byte_size(v_stderr_107_);
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = lean_nat_dec_eq(v___x_148_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_151_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__1));
v___x_152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_152_, 0, v_stderr_107_);
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
v___x_158_ = lean_array_push(v___y_109_, v___x_157_);
v___y_139_ = v___x_158_;
goto v___jp_138_;
}
else
{
lean_dec_ref(v_stderr_107_);
v___y_139_ = v___y_109_;
goto v___jp_138_;
}
v___jp_111_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_114_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__0));
v___x_115_ = lean_uint32_to_nat(v___y_112_);
v___x_116_ = l_Nat_reprFast(v___x_115_);
v___x_117_ = lean_string_append(v___x_114_, v___x_116_);
lean_dec_ref(v___x_116_);
v___x_118_ = 3;
v___x_119_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*1, v___x_118_);
v___x_120_ = lean_array_get_size(v___y_113_);
v___x_121_ = lean_array_push(v___y_113_, v___x_119_);
v___x_122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
return v___x_122_;
}
v___jp_123_:
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 0;
v___x_128_ = lean_uint32_dec_eq(v___y_124_, v___x_127_);
if (v___x_128_ == 0)
{
v___y_112_ = v___y_124_;
v___y_113_ = v___y_126_;
goto v___jp_111_;
}
else
{
if (v___y_125_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_box(0);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___y_126_);
return v___x_130_;
}
else
{
v___y_112_ = v___y_124_;
v___y_113_ = v___y_126_;
goto v___jp_111_;
}
}
}
v___jp_131_:
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 1;
v___x_135_ = lean_uint32_dec_eq(v_exitCode_105_, v___x_134_);
if (v___x_135_ == 0)
{
v___y_124_ = v_exitCode_105_;
v___y_125_ = v___y_133_;
v___y_126_ = v___y_132_;
goto v___jp_123_;
}
else
{
if (v___y_133_ == 0)
{
v___y_124_ = v_exitCode_105_;
v___y_125_ = v___y_133_;
v___y_126_ = v___y_132_;
goto v___jp_123_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; 
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
v___x_141_ = l_Array_extract___redArg(v___y_139_, v___x_106_, v___x_140_);
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
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object* v_exitCode_159_, lean_object* v___x_160_, lean_object* v_stderr_161_, lean_object* v_____r_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
uint32_t v_exitCode_boxed_165_; lean_object* v_res_166_; 
v_exitCode_boxed_165_ = lean_unbox_uint32(v_exitCode_159_);
lean_dec(v_exitCode_159_);
v_res_166_ = l_Lake_compileLeanModule___lam__0(v_exitCode_boxed_165_, v___x_160_, v_stderr_161_, v_____r_162_, v___y_163_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(lean_object* v_a_167_, lean_object* v_b_168_, lean_object* v_relLeanFile_169_, lean_object* v_____r_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_a_174_; lean_object* v_toBaseMessage_176_; uint8_t v_isSilent_177_; 
v_toBaseMessage_176_ = lean_ctor_get(v_a_167_, 0);
lean_inc_ref(v_toBaseMessage_176_);
v_isSilent_177_ = lean_ctor_get_uint8(v_toBaseMessage_176_, sizeof(void*)*5 + 2);
if (v_isSilent_177_ == 0)
{
lean_object* v_kind_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_202_; 
v_kind_178_ = lean_ctor_get(v_a_167_, 1);
v_isSharedCheck_202_ = !lean_is_exclusive(v_a_167_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v_a_167_, 0);
lean_dec(v_unused_203_);
v___x_180_ = v_a_167_;
v_isShared_181_ = v_isSharedCheck_202_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_kind_178_);
lean_dec(v_a_167_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_202_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_pos_182_; lean_object* v_endPos_183_; uint8_t v_keepFullRange_184_; uint8_t v_severity_185_; lean_object* v_caption_186_; lean_object* v_data_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_200_; 
v_pos_182_ = lean_ctor_get(v_toBaseMessage_176_, 1);
v_endPos_183_ = lean_ctor_get(v_toBaseMessage_176_, 2);
v_keepFullRange_184_ = lean_ctor_get_uint8(v_toBaseMessage_176_, sizeof(void*)*5);
v_severity_185_ = lean_ctor_get_uint8(v_toBaseMessage_176_, sizeof(void*)*5 + 1);
v_caption_186_ = lean_ctor_get(v_toBaseMessage_176_, 3);
v_data_187_ = lean_ctor_get(v_toBaseMessage_176_, 4);
v_isSharedCheck_200_ = !lean_is_exclusive(v_toBaseMessage_176_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v_toBaseMessage_176_, 0);
lean_dec(v_unused_201_);
v___x_189_ = v_toBaseMessage_176_;
v_isShared_190_ = v_isSharedCheck_200_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_data_187_);
lean_inc(v_caption_186_);
lean_inc(v_endPos_183_);
lean_inc(v_pos_182_);
lean_dec(v_toBaseMessage_176_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_200_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = l_Lake_mkRelPathString(v_relLeanFile_169_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_191_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_pos_182_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_endPos_183_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v_caption_186_);
lean_ctor_set(v_reuseFailAlloc_199_, 4, v_data_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_199_, sizeof(void*)*5, v_keepFullRange_184_);
lean_ctor_set_uint8(v_reuseFailAlloc_199_, sizeof(void*)*5 + 1, v_severity_185_);
lean_ctor_set_uint8(v_reuseFailAlloc_199_, sizeof(void*)*5 + 2, v_isSilent_177_);
v___x_193_ = v_reuseFailAlloc_199_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_193_);
v___x_195_ = v___x_180_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_kind_178_);
v___x_195_ = v_reuseFailAlloc_198_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = l_Lake_LogEntry_ofSerialMessage(v___x_195_);
v___x_197_ = lean_array_push(v___y_171_, v___x_196_);
v_a_174_ = v___x_197_;
goto v___jp_173_;
}
}
}
}
}
else
{
lean_dec_ref(v_toBaseMessage_176_);
lean_dec_ref(v_relLeanFile_169_);
lean_dec_ref(v_a_167_);
v_a_174_ = v___y_171_;
goto v___jp_173_;
}
v___jp_173_:
{
lean_object* v___x_175_; 
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_b_168_);
lean_ctor_set(v___x_175_, 1, v_a_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0___boxed(lean_object* v_a_204_, lean_object* v_b_205_, lean_object* v_relLeanFile_206_, lean_object* v_____r_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_204_, v_b_205_, v_relLeanFile_206_, v_____r_207_, v___y_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(lean_object* v_relLeanFile_213_, lean_object* v___x_214_, lean_object* v___x_215_, lean_object* v___x_216_, lean_object* v_a_217_, lean_object* v_b_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v_it_244_; lean_object* v_startInclusive_245_; lean_object* v_endExclusive_246_; 
if (lean_obj_tag(v_a_217_) == 0)
{
lean_object* v_currPos_264_; lean_object* v_searcher_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_288_; 
v_currPos_264_ = lean_ctor_get(v_a_217_, 0);
v_searcher_265_ = lean_ctor_get(v_a_217_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v_a_217_);
if (v_isSharedCheck_288_ == 0)
{
v___x_267_ = v_a_217_;
v_isShared_268_ = v_isSharedCheck_288_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_searcher_265_);
lean_inc(v_currPos_264_);
lean_dec(v_a_217_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_288_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
uint8_t v_decide_269_; 
v_decide_269_ = lean_nat_dec_eq(v_searcher_265_, v___x_216_);
if (v_decide_269_ == 0)
{
uint32_t v___x_270_; uint32_t v___x_271_; uint8_t v___x_272_; 
v___x_270_ = 10;
v___x_271_ = lean_string_utf8_get_fast(v___x_214_, v_searcher_265_);
v___x_272_ = lean_uint32_dec_eq(v___x_271_, v___x_270_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = lean_string_utf8_next_fast(v___x_214_, v_searcher_265_);
lean_dec(v_searcher_265_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v___x_273_);
v___x_275_ = v___x_267_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_currPos_264_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_273_);
v___x_275_ = v_reuseFailAlloc_277_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
v_a_217_ = v___x_275_;
goto _start;
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_slice_281_; lean_object* v_nextIt_283_; 
v___x_278_ = lean_string_utf8_next_fast(v___x_214_, v_searcher_265_);
v___x_279_ = lean_nat_sub(v___x_278_, v_searcher_265_);
v___x_280_ = lean_nat_add(v_searcher_265_, v___x_279_);
lean_dec(v___x_279_);
v_slice_281_ = l_String_Slice_subslice_x21(v___x_215_, v_currPos_264_, v_searcher_265_);
lean_inc(v___x_280_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v___x_280_);
lean_ctor_set(v___x_267_, 0, v___x_280_);
v_nextIt_283_ = v___x_267_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v___x_280_);
v_nextIt_283_ = v_reuseFailAlloc_286_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v_startInclusive_284_; lean_object* v_endExclusive_285_; 
v_startInclusive_284_ = lean_ctor_get(v_slice_281_, 0);
lean_inc(v_startInclusive_284_);
v_endExclusive_285_ = lean_ctor_get(v_slice_281_, 1);
lean_inc(v_endExclusive_285_);
lean_dec_ref(v_slice_281_);
v_it_244_ = v_nextIt_283_;
v_startInclusive_245_ = v_startInclusive_284_;
v_endExclusive_246_ = v_endExclusive_285_;
goto v___jp_243_;
}
}
}
else
{
lean_object* v___x_287_; 
lean_del_object(v___x_267_);
lean_dec(v_searcher_265_);
v___x_287_ = lean_box(1);
lean_inc(v___x_216_);
v_it_244_ = v___x_287_;
v_startInclusive_245_ = v_currPos_264_;
v_endExclusive_246_ = v___x_216_;
goto v___jp_243_;
}
}
}
else
{
lean_object* v___x_289_; 
lean_dec(v___x_216_);
lean_dec_ref(v_relLeanFile_213_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_b_218_);
lean_ctor_set(v___x_289_, 1, v___y_219_);
return v___x_289_;
}
v___jp_221_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_string_append(v_b_218_, v___y_222_);
lean_dec_ref(v___y_222_);
v___x_225_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__0));
v___x_226_ = lean_string_append(v___x_224_, v___x_225_);
v_a_217_ = v___y_223_;
v_b_218_ = v___x_226_;
goto _start;
}
v___jp_228_:
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_231_ = lean_string_utf8_byte_size(v_b_218_);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_nat_dec_eq(v___x_231_, v___x_232_);
if (v___x_233_ == 0)
{
v___y_222_ = v___y_229_;
v___y_223_ = v___y_230_;
goto v___jp_221_;
}
else
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = lean_string_utf8_byte_size(v___y_229_);
v___x_235_ = lean_nat_dec_eq(v___x_234_, v___x_232_);
if (v___x_235_ == 0)
{
v___y_222_ = v___y_229_;
v___y_223_ = v___y_230_;
goto v___jp_221_;
}
else
{
lean_dec_ref(v___y_229_);
v_a_217_ = v___y_230_;
goto _start;
}
}
}
v___jp_237_:
{
if (lean_obj_tag(v___y_239_) == 0)
{
lean_object* v_a_240_; lean_object* v_a_241_; 
v_a_240_ = lean_ctor_get(v___y_239_, 0);
lean_inc(v_a_240_);
v_a_241_ = lean_ctor_get(v___y_239_, 1);
lean_inc(v_a_241_);
lean_dec_ref_known(v___y_239_, 2);
v_a_217_ = v___y_238_;
v_b_218_ = v_a_240_;
v___y_219_ = v_a_241_;
goto _start;
}
else
{
lean_dec(v___y_238_);
lean_dec(v___x_216_);
lean_dec_ref(v_relLeanFile_213_);
return v___y_239_;
}
}
v___jp_243_:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_string_utf8_extract_fast(v___x_214_, v_startInclusive_245_, v_endExclusive_246_);
lean_dec(v_endExclusive_246_);
lean_dec(v_startInclusive_245_);
lean_inc_ref(v___x_247_);
v___x_248_ = l_Lean_Json_parse(v___x_247_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_dec_ref_known(v___x_248_, 1);
v___y_229_ = v___x_247_;
v___y_230_ = v_it_244_;
goto v___jp_228_;
}
else
{
lean_object* v_a_249_; lean_object* v___x_250_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
v___x_250_ = l_Lean_instFromJsonSerialMessage_fromJson(v_a_249_);
if (lean_obj_tag(v___x_250_) == 1)
{
lean_object* v_a_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
lean_dec_ref(v___x_247_);
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_250_, 1);
v___x_252_ = lean_string_utf8_byte_size(v_b_218_);
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_nat_dec_eq(v___x_252_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_255_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__1));
v___x_256_ = lean_string_append(v___x_255_, v_b_218_);
v___x_257_ = 1;
v___x_258_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*1, v___x_257_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_array_push(v___y_219_, v___x_258_);
lean_inc_ref(v_relLeanFile_213_);
v___x_261_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_251_, v_b_218_, v_relLeanFile_213_, v___x_259_, v___x_260_);
v___y_238_ = v_it_244_;
v___y_239_ = v___x_261_;
goto v___jp_237_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_box(0);
lean_inc_ref(v_relLeanFile_213_);
v___x_263_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_251_, v_b_218_, v_relLeanFile_213_, v___x_262_, v___y_219_);
v___y_238_ = v_it_244_;
v___y_239_ = v___x_263_;
goto v___jp_237_;
}
}
else
{
lean_dec_ref(v___x_250_);
v___y_229_ = v___x_247_;
v___y_230_ = v_it_244_;
goto v___jp_228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___boxed(lean_object* v_relLeanFile_290_, lean_object* v___x_291_, lean_object* v___x_292_, lean_object* v___x_293_, lean_object* v_a_294_, lean_object* v_b_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(v_relLeanFile_290_, v___x_291_, v___x_292_, v___x_293_, v_a_294_, v_b_295_, v___y_296_);
lean_dec_ref(v___x_292_);
lean_dec_ref(v___x_291_);
return v_res_298_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__1(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_300_ = ((lean_object*)(l_Lake_compileLeanModule___closed__0));
v___x_301_ = lean_unsigned_to_nat(2u);
v___x_302_ = lean_mk_empty_array_with_capacity(v___x_301_);
v___x_303_ = lean_array_push(v___x_302_, v___x_300_);
return v___x_303_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__7(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_309_ = ((lean_object*)(l_Lake_compileLeanModule___closed__6));
v___x_310_ = lean_unsigned_to_nat(2u);
v___x_311_ = lean_mk_empty_array_with_capacity(v___x_310_);
v___x_312_ = lean_array_push(v___x_311_, v___x_309_);
return v___x_312_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__9(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = ((lean_object*)(l_Lake_compileLeanModule___closed__8));
v___x_315_ = lean_unsigned_to_nat(2u);
v___x_316_ = lean_mk_empty_array_with_capacity(v___x_315_);
v___x_317_ = lean_array_push(v___x_316_, v___x_314_);
return v___x_317_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__11(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_319_ = ((lean_object*)(l_Lake_compileLeanModule___closed__10));
v___x_320_ = lean_unsigned_to_nat(2u);
v___x_321_ = lean_mk_empty_array_with_capacity(v___x_320_);
v___x_322_ = lean_array_push(v___x_321_, v___x_319_);
return v___x_322_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__13(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_324_ = ((lean_object*)(l_Lake_compileLeanModule___closed__12));
v___x_325_ = lean_unsigned_to_nat(2u);
v___x_326_ = lean_mk_empty_array_with_capacity(v___x_325_);
v___x_327_ = lean_array_push(v___x_326_, v___x_324_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object* v_leanFile_328_, lean_object* v_relLeanFile_329_, lean_object* v_setup_330_, lean_object* v_setupFile_331_, lean_object* v_arts_332_, lean_object* v_leanArgs_333_, lean_object* v_leanPath_334_, lean_object* v_lean_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___y_339_; lean_object* v_a_340_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v_args_347_; lean_object* v___y_348_; lean_object* v_olean_x3f_436_; lean_object* v_ilean_x3f_437_; lean_object* v_c_x3f_438_; lean_object* v_bc_x3f_439_; lean_object* v_args_441_; lean_object* v___y_442_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v_args_471_; lean_object* v___y_472_; lean_object* v_args_479_; lean_object* v___y_480_; lean_object* v_args_493_; 
v_olean_x3f_436_ = lean_ctor_get(v_arts_332_, 1);
lean_inc(v_olean_x3f_436_);
v_ilean_x3f_437_ = lean_ctor_get(v_arts_332_, 4);
lean_inc(v_ilean_x3f_437_);
v_c_x3f_438_ = lean_ctor_get(v_arts_332_, 7);
lean_inc(v_c_x3f_438_);
v_bc_x3f_439_ = lean_ctor_get(v_arts_332_, 8);
lean_inc(v_bc_x3f_439_);
lean_dec_ref(v_arts_332_);
v_args_493_ = lean_array_push(v_leanArgs_333_, v_leanFile_328_);
if (lean_obj_tag(v_olean_x3f_436_) == 1)
{
lean_object* v_val_494_; lean_object* v___x_495_; 
v_val_494_ = lean_ctor_get(v_olean_x3f_436_, 0);
lean_inc_n(v_val_494_, 2);
lean_dec_ref_known(v_olean_x3f_436_, 1);
v___x_495_ = l_Lake_createParentDirs(v_val_494_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec_ref_known(v___x_495_, 1);
v___x_496_ = lean_obj_once(&l_Lake_compileLeanModule___closed__13, &l_Lake_compileLeanModule___closed__13_once, _init_l_Lake_compileLeanModule___closed__13);
v___x_497_ = lean_array_push(v___x_496_, v_val_494_);
v___x_498_ = l_Array_append___redArg(v_args_493_, v___x_497_);
lean_dec_ref(v___x_497_);
v_args_479_ = v___x_498_;
v___y_480_ = v_a_336_;
goto v___jp_478_;
}
else
{
lean_object* v_a_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v_val_494_);
lean_dec_ref(v_args_493_);
lean_dec(v_bc_x3f_439_);
lean_dec(v_c_x3f_438_);
lean_dec(v_ilean_x3f_437_);
lean_dec_ref(v_lean_335_);
lean_dec(v_leanPath_334_);
lean_dec_ref(v_setupFile_331_);
lean_dec_ref(v_setup_330_);
lean_dec_ref(v_relLeanFile_329_);
v_a_499_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_495_, 1);
v___x_500_ = lean_io_error_to_string(v_a_499_);
v___x_501_ = 3;
v___x_502_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*1, v___x_501_);
v___x_503_ = lean_array_get_size(v_a_336_);
v___x_504_ = lean_array_push(v_a_336_, v___x_502_);
v___x_505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_503_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
return v___x_505_;
}
}
else
{
lean_dec(v_olean_x3f_436_);
v_args_479_ = v_args_493_;
v___y_480_ = v_a_336_;
goto v___jp_478_;
}
v___jp_338_:
{
lean_object* v___x_341_; 
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v___y_339_);
lean_ctor_set(v___x_341_, 1, v_a_340_);
return v___x_341_;
}
v___jp_342_:
{
if (lean_obj_tag(v___y_344_) == 0)
{
lean_dec(v___y_343_);
return v___y_344_;
}
else
{
lean_object* v_a_345_; 
v_a_345_ = lean_ctor_get(v___y_344_, 1);
lean_inc(v_a_345_);
lean_dec_ref_known(v___y_344_, 2);
v___y_339_ = v___y_343_;
v_a_340_ = v_a_345_;
goto v___jp_338_;
}
}
v___jp_346_:
{
lean_object* v___x_349_; 
lean_inc_ref(v_setupFile_331_);
v___x_349_ = l_Lake_createParentDirs(v_setupFile_331_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec_ref_known(v___x_349_, 1);
v___x_350_ = l_Lean_instToJsonModuleSetup_toJson(v_setup_330_);
v___x_351_ = lean_unsigned_to_nat(80u);
v___x_352_ = l_Lean_Json_pretty(v___x_350_, v___x_351_);
v___x_353_ = l_IO_FS_writeFile(v_setupFile_331_, v___x_352_);
lean_dec_ref(v___x_352_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_420_; 
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v___x_353_, 0);
lean_dec(v_unused_421_);
v___x_355_ = v___x_353_;
v_isShared_356_ = v_isSharedCheck_420_;
goto v_resetjp_354_;
}
else
{
lean_dec(v___x_353_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_420_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_357_ = lean_obj_once(&l_Lake_compileLeanModule___closed__1, &l_Lake_compileLeanModule___closed__1_once, _init_l_Lake_compileLeanModule___closed__1);
v___x_358_ = lean_array_push(v___x_357_, v_setupFile_331_);
v___x_359_ = l_Array_append___redArg(v_args_347_, v___x_358_);
lean_dec_ref(v___x_358_);
v___x_360_ = ((lean_object*)(l_Lake_compileLeanModule___closed__2));
v___x_361_ = lean_array_push(v___x_359_, v___x_360_);
v___x_362_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_363_ = lean_box(0);
v___x_364_ = ((lean_object*)(l_Lake_compileLeanIR___closed__1));
v___x_365_ = l_System_SearchPath_toString(v_leanPath_334_);
if (v_isShared_356_ == 0)
{
lean_ctor_set_tag(v___x_355_, 1);
lean_ctor_set(v___x_355_, 0, v___x_365_);
v___x_367_ = v___x_355_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_419_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_364_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_mk_empty_array_with_capacity(v___x_369_);
v___x_371_ = lean_array_push(v___x_370_, v___x_368_);
v___x_372_ = 1;
v___x_373_ = 0;
lean_inc_ref(v_lean_335_);
v___x_374_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_374_, 0, v___x_362_);
lean_ctor_set(v___x_374_, 1, v_lean_335_);
lean_ctor_set(v___x_374_, 2, v___x_361_);
lean_ctor_set(v___x_374_, 3, v___x_363_);
lean_ctor_set(v___x_374_, 4, v___x_371_);
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*5, v___x_372_);
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*5 + 1, v___x_373_);
v___x_375_ = lean_array_get_size(v___y_348_);
lean_inc_ref(v___x_374_);
v___x_376_ = l_Lake_mkCmdLog(v___x_374_);
v___x_377_ = 0;
v___x_378_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*1, v___x_377_);
v___x_379_ = lean_array_push(v___y_348_, v___x_378_);
v___x_380_ = l_IO_Process_output(v___x_374_, v___x_363_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; uint32_t v_exitCode_382_; lean_object* v_stdout_383_; lean_object* v_stderr_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
lean_dec_ref(v_lean_335_);
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
v_exitCode_382_ = lean_ctor_get_uint32(v_a_381_, sizeof(void*)*2);
v_stdout_383_ = lean_ctor_get(v_a_381_, 0);
lean_inc_ref(v_stdout_383_);
v_stderr_384_ = lean_ctor_get(v_a_381_, 1);
lean_inc_ref(v_stderr_384_);
lean_dec(v_a_381_);
v___x_385_ = lean_array_get_size(v___x_379_);
v___x_386_ = lean_string_utf8_byte_size(v_stdout_383_);
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = lean_nat_dec_eq(v___x_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
lean_inc_ref(v_stdout_383_);
v___x_389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_389_, 0, v_stdout_383_);
lean_ctor_set(v___x_389_, 1, v___x_387_);
lean_ctor_set(v___x_389_, 2, v___x_386_);
v___x_390_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_391_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0);
v___x_392_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(v_relLeanFile_329_, v_stdout_383_, v___x_389_, v___x_386_, v___x_391_, v___x_390_, v___x_379_);
lean_dec_ref_known(v___x_389_, 3);
lean_dec_ref(v_stdout_383_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v_a_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
v_a_394_ = lean_ctor_get(v___x_392_, 1);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_392_, 2);
v___x_395_ = lean_string_utf8_byte_size(v_a_393_);
v___x_396_ = lean_nat_dec_eq(v___x_395_, v___x_387_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_397_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__1));
v___x_398_ = lean_string_append(v___x_397_, v_a_393_);
lean_dec(v_a_393_);
v___x_399_ = 1;
v___x_400_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*1, v___x_399_);
v___x_401_ = lean_box(0);
v___x_402_ = lean_array_push(v_a_394_, v___x_400_);
v___x_403_ = l_Lake_compileLeanModule___lam__0(v_exitCode_382_, v___x_385_, v_stderr_384_, v___x_401_, v___x_402_);
v___y_343_ = v___x_375_;
v___y_344_ = v___x_403_;
goto v___jp_342_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec(v_a_393_);
v___x_404_ = lean_box(0);
v___x_405_ = l_Lake_compileLeanModule___lam__0(v_exitCode_382_, v___x_385_, v_stderr_384_, v___x_404_, v_a_394_);
v___y_343_ = v___x_375_;
v___y_344_ = v___x_405_;
goto v___jp_342_;
}
}
else
{
lean_object* v_a_406_; 
lean_dec_ref(v_stderr_384_);
v_a_406_ = lean_ctor_get(v___x_392_, 1);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_392_, 2);
v___y_339_ = v___x_375_;
v_a_340_ = v_a_406_;
goto v___jp_338_;
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec_ref(v_stdout_383_);
lean_dec_ref(v_relLeanFile_329_);
v___x_407_ = lean_box(0);
v___x_408_ = l_Lake_compileLeanModule___lam__0(v_exitCode_382_, v___x_385_, v_stderr_384_, v___x_407_, v___x_379_);
v___y_343_ = v___x_375_;
v___y_344_ = v___x_408_;
goto v___jp_342_;
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec_ref(v_relLeanFile_329_);
v_a_409_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_380_, 1);
v___x_410_ = ((lean_object*)(l_Lake_compileLeanModule___closed__4));
v___x_411_ = lean_string_append(v___x_410_, v_lean_335_);
lean_dec_ref(v_lean_335_);
v___x_412_ = ((lean_object*)(l_Lake_compileLeanModule___closed__5));
v___x_413_ = lean_string_append(v___x_411_, v___x_412_);
v___x_414_ = lean_io_error_to_string(v_a_409_);
v___x_415_ = lean_string_append(v___x_413_, v___x_414_);
lean_dec_ref(v___x_414_);
v___x_416_ = 3;
v___x_417_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*1, v___x_416_);
v___x_418_ = lean_array_push(v___x_379_, v___x_417_);
v___y_339_ = v___x_375_;
v_a_340_ = v___x_418_;
goto v___jp_338_;
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec_ref(v_args_347_);
lean_dec_ref(v_lean_335_);
lean_dec(v_leanPath_334_);
lean_dec_ref(v_setupFile_331_);
lean_dec_ref(v_relLeanFile_329_);
v_a_422_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_353_, 1);
v___x_423_ = lean_io_error_to_string(v_a_422_);
v___x_424_ = 3;
v___x_425_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*1, v___x_424_);
v___x_426_ = lean_array_get_size(v___y_348_);
v___x_427_ = lean_array_push(v___y_348_, v___x_425_);
v___x_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
return v___x_428_;
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_430_; uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref(v_args_347_);
lean_dec_ref(v_lean_335_);
lean_dec(v_leanPath_334_);
lean_dec_ref(v_setupFile_331_);
lean_dec_ref(v_setup_330_);
lean_dec_ref(v_relLeanFile_329_);
v_a_429_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_349_, 1);
v___x_430_ = lean_io_error_to_string(v_a_429_);
v___x_431_ = 3;
v___x_432_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*1, v___x_431_);
v___x_433_ = lean_array_get_size(v___y_348_);
v___x_434_ = lean_array_push(v___y_348_, v___x_432_);
v___x_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
return v___x_435_;
}
}
v___jp_440_:
{
if (lean_obj_tag(v_bc_x3f_439_) == 1)
{
lean_object* v_val_443_; lean_object* v___x_444_; 
v_val_443_ = lean_ctor_get(v_bc_x3f_439_, 0);
lean_inc_n(v_val_443_, 2);
lean_dec_ref_known(v_bc_x3f_439_, 1);
v___x_444_ = l_Lake_createParentDirs(v_val_443_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec_ref_known(v___x_444_, 1);
v___x_445_ = lean_obj_once(&l_Lake_compileLeanModule___closed__7, &l_Lake_compileLeanModule___closed__7_once, _init_l_Lake_compileLeanModule___closed__7);
v___x_446_ = lean_array_push(v___x_445_, v_val_443_);
v___x_447_ = l_Array_append___redArg(v_args_441_, v___x_446_);
lean_dec_ref(v___x_446_);
v_args_347_ = v___x_447_;
v___y_348_ = v___y_442_;
goto v___jp_346_;
}
else
{
lean_object* v_a_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec(v_val_443_);
lean_dec_ref(v_args_441_);
lean_dec_ref(v_lean_335_);
lean_dec(v_leanPath_334_);
lean_dec_ref(v_setupFile_331_);
lean_dec_ref(v_setup_330_);
lean_dec_ref(v_relLeanFile_329_);
v_a_448_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_444_, 1);
v___x_449_ = lean_io_error_to_string(v_a_448_);
v___x_450_ = 3;
v___x_451_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1, v___x_450_);
v___x_452_ = lean_array_get_size(v___y_442_);
v___x_453_ = lean_array_push(v___y_442_, v___x_451_);
v___x_454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
return v___x_454_;
}
}
else
{
lean_dec(v_bc_x3f_439_);
v_args_347_ = v_args_441_;
v___y_348_ = v___y_442_;
goto v___jp_346_;
}
}
v___jp_455_:
{
if (lean_obj_tag(v_c_x3f_438_) == 1)
{
lean_object* v_val_458_; lean_object* v___x_459_; 
v_val_458_ = lean_ctor_get(v_c_x3f_438_, 0);
lean_inc_n(v_val_458_, 2);
lean_dec_ref_known(v_c_x3f_438_, 1);
v___x_459_ = l_Lake_createParentDirs(v_val_458_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
lean_dec_ref_known(v___x_459_, 1);
v___x_460_ = lean_obj_once(&l_Lake_compileLeanModule___closed__9, &l_Lake_compileLeanModule___closed__9_once, _init_l_Lake_compileLeanModule___closed__9);
v___x_461_ = lean_array_push(v___x_460_, v_val_458_);
v___x_462_ = l_Array_append___redArg(v___y_457_, v___x_461_);
lean_dec_ref(v___x_461_);
v_args_441_ = v___x_462_;
v___y_442_ = v___y_456_;
goto v___jp_440_;
}
else
{
lean_object* v_a_463_; lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v_val_458_);
lean_dec_ref(v___y_457_);
lean_dec(v_bc_x3f_439_);
lean_dec_ref(v_lean_335_);
lean_dec(v_leanPath_334_);
lean_dec_ref(v_setupFile_331_);
lean_dec_ref(v_setup_330_);
lean_dec_ref(v_relLeanFile_329_);
v_a_463_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_459_, 1);
v___x_464_ = lean_io_error_to_string(v_a_463_);
v___x_465_ = 3;
v___x_466_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*1, v___x_465_);
v___x_467_ = lean_array_get_size(v___y_456_);
v___x_468_ = lean_array_push(v___y_456_, v___x_466_);
v___x_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
return v___x_469_;
}
}
else
{
lean_dec(v_c_x3f_438_);
v_args_441_ = v___y_457_;
v___y_442_ = v___y_456_;
goto v___jp_440_;
}
}
v___jp_470_:
{
uint8_t v_isModule_473_; 
v_isModule_473_ = lean_ctor_get_uint8(v_setup_330_, sizeof(void*)*7);
if (v_isModule_473_ == 0)
{
v___y_456_ = v___y_472_;
v___y_457_ = v_args_471_;
goto v___jp_455_;
}
else
{
lean_object* v_options_474_; lean_object* v_opts_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_options_474_ = lean_ctor_get(v_setup_330_, 6);
lean_inc(v_options_474_);
v_opts_475_ = l_Lean_LeanOptions_toOptions(v_options_474_);
v___x_476_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_477_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(v_opts_475_, v___x_476_);
lean_dec_ref(v_opts_475_);
if (v___x_477_ == 0)
{
v___y_456_ = v___y_472_;
v___y_457_ = v_args_471_;
goto v___jp_455_;
}
else
{
lean_dec(v_c_x3f_438_);
v_args_441_ = v_args_471_;
v___y_442_ = v___y_472_;
goto v___jp_440_;
}
}
}
v___jp_478_:
{
if (lean_obj_tag(v_ilean_x3f_437_) == 1)
{
lean_object* v_val_481_; lean_object* v___x_482_; 
v_val_481_ = lean_ctor_get(v_ilean_x3f_437_, 0);
lean_inc_n(v_val_481_, 2);
lean_dec_ref_known(v_ilean_x3f_437_, 1);
v___x_482_ = l_Lake_createParentDirs(v_val_481_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec_ref_known(v___x_482_, 1);
v___x_483_ = lean_obj_once(&l_Lake_compileLeanModule___closed__11, &l_Lake_compileLeanModule___closed__11_once, _init_l_Lake_compileLeanModule___closed__11);
v___x_484_ = lean_array_push(v___x_483_, v_val_481_);
v___x_485_ = l_Array_append___redArg(v_args_479_, v___x_484_);
lean_dec_ref(v___x_484_);
v_args_471_ = v___x_485_;
v___y_472_ = v___y_480_;
goto v___jp_470_;
}
else
{
lean_object* v_a_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_val_481_);
lean_dec_ref(v_args_479_);
lean_dec(v_bc_x3f_439_);
lean_dec(v_c_x3f_438_);
lean_dec_ref(v_lean_335_);
lean_dec(v_leanPath_334_);
lean_dec_ref(v_setupFile_331_);
lean_dec_ref(v_setup_330_);
lean_dec_ref(v_relLeanFile_329_);
v_a_486_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_482_, 1);
v___x_487_ = lean_io_error_to_string(v_a_486_);
v___x_488_ = 3;
v___x_489_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*1, v___x_488_);
v___x_490_ = lean_array_get_size(v___y_480_);
v___x_491_ = lean_array_push(v___y_480_, v___x_489_);
v___x_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
return v___x_492_;
}
}
else
{
lean_dec(v_ilean_x3f_437_);
v_args_471_ = v_args_479_;
v___y_472_ = v___y_480_;
goto v___jp_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object* v_leanFile_506_, lean_object* v_relLeanFile_507_, lean_object* v_setup_508_, lean_object* v_setupFile_509_, lean_object* v_arts_510_, lean_object* v_leanArgs_511_, lean_object* v_leanPath_512_, lean_object* v_lean_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lake_compileLeanModule(v_leanFile_506_, v_relLeanFile_507_, v_setup_508_, v_setupFile_509_, v_arts_510_, v_leanArgs_511_, v_leanPath_512_, v_lean_513_, v_a_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2(lean_object* v_relLeanFile_517_, lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v___x_520_, lean_object* v_inst_521_, lean_object* v_R_522_, lean_object* v_a_523_, lean_object* v_b_524_, lean_object* v_c_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(v_relLeanFile_517_, v___x_518_, v___x_519_, v___x_520_, v_a_523_, v_b_524_, v___y_526_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___boxed(lean_object* v_relLeanFile_529_, lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v_inst_533_, lean_object* v_R_534_, lean_object* v_a_535_, lean_object* v_b_536_, lean_object* v_c_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2(v_relLeanFile_529_, v___x_530_, v___x_531_, v___x_532_, v_inst_533_, v_R_534_, v_a_535_, v_b_536_, v_c_537_, v___y_538_);
lean_dec_ref(v___x_531_);
lean_dec_ref(v___x_530_);
return v_res_540_;
}
}
static lean_object* _init_l_Lake_compileO___closed__0(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_541_ = ((lean_object*)(l_Lake_compileLeanModule___closed__8));
v___x_542_ = lean_unsigned_to_nat(4u);
v___x_543_ = lean_mk_empty_array_with_capacity(v___x_542_);
v___x_544_ = lean_array_push(v___x_543_, v___x_541_);
return v___x_544_;
}
}
static lean_object* _init_l_Lake_compileO___closed__1(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = ((lean_object*)(l_Lake_compileLeanModule___closed__12));
v___x_546_ = lean_obj_once(&l_Lake_compileO___closed__0, &l_Lake_compileO___closed__0_once, _init_l_Lake_compileO___closed__0);
v___x_547_ = lean_array_push(v___x_546_, v___x_545_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object* v_oFile_550_, lean_object* v_srcFile_551_, lean_object* v_moreArgs_552_, lean_object* v_compiler_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_556_; 
lean_inc_ref(v_oFile_550_);
v___x_556_ = l_Lake_createParentDirs(v_oFile_550_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref_known(v___x_556_, 1);
v___x_557_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_558_ = lean_obj_once(&l_Lake_compileO___closed__1, &l_Lake_compileO___closed__1_once, _init_l_Lake_compileO___closed__1);
v___x_559_ = lean_array_push(v___x_558_, v_oFile_550_);
v___x_560_ = lean_array_push(v___x_559_, v_srcFile_551_);
v___x_561_ = l_Array_append___redArg(v___x_560_, v_moreArgs_552_);
v___x_562_ = lean_box(0);
v___x_563_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_564_ = 1;
v___x_565_ = 0;
v___x_566_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_566_, 0, v___x_557_);
lean_ctor_set(v___x_566_, 1, v_compiler_553_);
lean_ctor_set(v___x_566_, 2, v___x_561_);
lean_ctor_set(v___x_566_, 3, v___x_562_);
lean_ctor_set(v___x_566_, 4, v___x_563_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*5, v___x_564_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*5 + 1, v___x_565_);
v___x_567_ = l_Lake_proc(v___x_566_, v___x_565_, v___x_562_, v_a_554_);
return v___x_567_;
}
else
{
lean_object* v_a_568_; lean_object* v___x_569_; uint8_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref(v_compiler_553_);
lean_dec_ref(v_srcFile_551_);
lean_dec_ref(v_oFile_550_);
v_a_568_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_556_, 1);
v___x_569_ = lean_io_error_to_string(v_a_568_);
v___x_570_ = 3;
v___x_571_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*1, v___x_570_);
v___x_572_ = lean_array_get_size(v_a_554_);
v___x_573_ = lean_array_push(v_a_554_, v___x_571_);
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object* v_oFile_575_, lean_object* v_srcFile_576_, lean_object* v_moreArgs_577_, lean_object* v_compiler_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lake_compileO(v_oFile_575_, v_srcFile_576_, v_moreArgs_577_, v_compiler_578_, v_a_579_);
lean_dec_ref(v_moreArgs_577_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(lean_object* v___x_582_, lean_object* v___y_583_, lean_object* v_a_584_, lean_object* v_b_585_){
_start:
{
uint8_t v_decide_586_; 
v_decide_586_ = lean_nat_dec_eq(v_a_584_, v___x_582_);
if (v_decide_586_ == 0)
{
uint32_t v___x_587_; lean_object* v___x_588_; uint32_t v___x_589_; uint8_t v___x_594_; 
v___x_587_ = lean_string_utf8_get_fast(v___y_583_, v_a_584_);
v___x_588_ = lean_string_utf8_next_fast(v___y_583_, v_a_584_);
lean_dec(v_a_584_);
v___x_589_ = 92;
v___x_594_ = lean_uint32_dec_eq(v___x_587_, v___x_589_);
if (v___x_594_ == 0)
{
uint32_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = 34;
v___x_596_ = lean_uint32_dec_eq(v___x_587_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
v___x_597_ = lean_string_push(v_b_585_, v___x_587_);
v_a_584_ = v___x_588_;
v_b_585_ = v___x_597_;
goto _start;
}
else
{
goto v___jp_590_;
}
}
else
{
goto v___jp_590_;
}
v___jp_590_:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_string_push(v_b_585_, v___x_589_);
v___x_592_ = lean_string_push(v___x_591_, v___x_587_);
v_a_584_ = v___x_588_;
v_b_585_ = v___x_592_;
goto _start;
}
}
else
{
lean_dec(v_a_584_);
return v_b_585_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg___boxed(lean_object* v___x_599_, lean_object* v___y_600_, lean_object* v_a_601_, lean_object* v_b_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_599_, v___y_600_, v_a_601_, v_b_602_);
lean_dec_ref(v___y_600_);
lean_dec(v___x_599_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(lean_object* v_a_606_, lean_object* v_as_607_, size_t v_i_608_, size_t v_stop_609_, lean_object* v_b_610_, lean_object* v___y_611_){
_start:
{
uint8_t v___x_613_; 
v___x_613_ = lean_usize_dec_eq(v_i_608_, v_stop_609_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_614_ = lean_array_uget_borrowed(v_as_607_, v_i_608_);
v___x_615_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_616_ = lean_string_utf8_byte_size(v___x_614_);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_616_, v___x_614_, v___x_617_, v___x_615_);
v___x_619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0));
v___x_620_ = lean_string_append(v___x_619_, v___x_618_);
lean_dec_ref(v___x_618_);
v___x_621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1));
v___x_622_ = lean_string_append(v___x_620_, v___x_621_);
v___x_623_ = lean_io_prim_handle_put_str(v_a_606_, v___x_622_);
lean_dec_ref(v___x_622_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; size_t v___x_625_; size_t v___x_626_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_add(v_i_608_, v___x_625_);
v_i_608_ = v___x_626_;
v_b_610_ = v_a_624_;
goto _start;
}
else
{
lean_object* v_a_628_; lean_object* v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_a_628_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_628_);
lean_dec_ref_known(v___x_623_, 1);
v___x_629_ = lean_io_error_to_string(v_a_628_);
v___x_630_ = 3;
v___x_631_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*1, v___x_630_);
v___x_632_ = lean_array_get_size(v___y_611_);
v___x_633_ = lean_array_push(v___y_611_, v___x_631_);
v___x_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
return v___x_634_;
}
}
else
{
lean_object* v___x_635_; 
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v_b_610_);
lean_ctor_set(v___x_635_, 1, v___y_611_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___boxed(lean_object* v_a_636_, lean_object* v_as_637_, lean_object* v_i_638_, lean_object* v_stop_639_, lean_object* v_b_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
size_t v_i_boxed_643_; size_t v_stop_boxed_644_; lean_object* v_res_645_; 
v_i_boxed_643_ = lean_unbox_usize(v_i_638_);
lean_dec(v_i_638_);
v_stop_boxed_644_ = lean_unbox_usize(v_stop_639_);
lean_dec(v_stop_639_);
v_res_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_636_, v_as_637_, v_i_boxed_643_, v_stop_boxed_644_, v_b_640_, v___y_641_);
lean_dec_ref(v_as_637_);
lean_dec(v_a_636_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object* v_basePath_648_, lean_object* v_args_649_, lean_object* v_a_650_){
_start:
{
lean_object* v___x_652_; lean_object* v_rspFile_653_; lean_object* v_a_655_; uint8_t v___x_662_; lean_object* v___x_663_; 
v___x_652_ = ((lean_object*)(l_Lake_mkArgs___closed__0));
v_rspFile_653_ = l_System_FilePath_addExtension(v_basePath_648_, v___x_652_);
v___x_662_ = 1;
v___x_663_ = lean_io_prim_handle_mk(v_rspFile_653_, v___x_662_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___x_663_, 1);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_array_get_size(v_args_649_);
v___x_667_ = lean_nat_dec_lt(v___x_665_, v___x_666_);
if (v___x_667_ == 0)
{
lean_dec(v_a_664_);
v_a_655_ = v_a_650_;
goto v___jp_654_;
}
else
{
lean_object* v___x_668_; size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; 
v___x_668_ = lean_box(0);
v___x_669_ = ((size_t)0ULL);
v___x_670_ = lean_usize_of_nat(v___x_666_);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_664_, v_args_649_, v___x_669_, v___x_670_, v___x_668_, v_a_650_);
lean_dec(v_a_664_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; 
v_a_672_ = lean_ctor_get(v___x_671_, 1);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 2);
v_a_655_ = v_a_672_;
goto v___jp_654_;
}
else
{
lean_object* v_a_673_; lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v_rspFile_653_);
v_a_673_ = lean_ctor_get(v___x_671_, 0);
v_a_674_ = lean_ctor_get(v___x_671_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_671_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_inc(v_a_673_);
lean_dec(v___x_671_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_673_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_683_; uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec_ref(v_rspFile_653_);
v_a_682_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_663_, 1);
v___x_683_ = lean_io_error_to_string(v_a_682_);
v___x_684_ = 3;
v___x_685_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set_uint8(v___x_685_, sizeof(void*)*1, v___x_684_);
v___x_686_ = lean_array_get_size(v_a_650_);
v___x_687_ = lean_array_push(v_a_650_, v___x_685_);
v___x_688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
return v___x_688_;
}
v___jp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = ((lean_object*)(l_Lake_mkArgs___closed__1));
v___x_657_ = lean_string_append(v___x_656_, v_rspFile_653_);
lean_dec_ref(v_rspFile_653_);
v___x_658_ = lean_unsigned_to_nat(1u);
v___x_659_ = lean_mk_empty_array_with_capacity(v___x_658_);
v___x_660_ = lean_array_push(v___x_659_, v___x_657_);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v_a_655_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs___boxed(lean_object* v_basePath_689_, lean_object* v_args_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lake_mkArgs(v_basePath_689_, v_args_690_, v_a_691_);
lean_dec_ref(v_args_690_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(lean_object* v___x_694_, lean_object* v___x_695_, lean_object* v___y_696_, lean_object* v_inst_697_, lean_object* v_R_698_, lean_object* v_a_699_, lean_object* v_b_700_, lean_object* v_c_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_695_, v___y_696_, v_a_699_, v_b_700_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(lean_object* v___x_703_, lean_object* v___x_704_, lean_object* v___y_705_, lean_object* v_inst_706_, lean_object* v_R_707_, lean_object* v_a_708_, lean_object* v_b_709_, lean_object* v_c_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(v___x_703_, v___x_704_, v___y_705_, v_inst_706_, v_R_707_, v_a_708_, v_b_709_, v_c_710_);
lean_dec_ref(v___y_705_);
lean_dec(v___x_704_);
lean_dec_ref(v___x_703_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(size_t v_sz_712_, size_t v_i_713_, lean_object* v_bs_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = lean_usize_dec_lt(v_i_713_, v_sz_712_);
if (v___x_715_ == 0)
{
return v_bs_714_;
}
else
{
lean_object* v_v_716_; lean_object* v___x_717_; lean_object* v_bs_x27_718_; size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; 
v_v_716_ = lean_array_uget(v_bs_714_, v_i_713_);
v___x_717_ = lean_unsigned_to_nat(0u);
v_bs_x27_718_ = lean_array_uset(v_bs_714_, v_i_713_, v___x_717_);
v___x_719_ = ((size_t)1ULL);
v___x_720_ = lean_usize_add(v_i_713_, v___x_719_);
v___x_721_ = lean_array_uset(v_bs_x27_718_, v_i_713_, v_v_716_);
v_i_713_ = v___x_720_;
v_bs_714_ = v___x_721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0___boxed(lean_object* v_sz_723_, lean_object* v_i_724_, lean_object* v_bs_725_){
_start:
{
size_t v_sz_boxed_726_; size_t v_i_boxed_727_; lean_object* v_res_728_; 
v_sz_boxed_726_ = lean_unbox_usize(v_sz_723_);
lean_dec(v_sz_723_);
v_i_boxed_727_ = lean_unbox_usize(v_i_724_);
lean_dec(v_i_724_);
v_res_728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_boxed_726_, v_i_boxed_727_, v_bs_725_);
return v_res_728_;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__3(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = ((lean_object*)(l_Lake_compileStaticLib___closed__2));
v___x_736_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_737_ = lean_array_push(v___x_736_, v___x_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object* v_libFile_738_, lean_object* v_oFiles_739_, lean_object* v_ar_740_, uint8_t v_thin_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_744_; 
lean_inc_ref(v_libFile_738_);
v___x_744_ = l_Lake_createParentDirs(v_libFile_738_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v___x_745_; 
lean_dec_ref_known(v___x_744_, 1);
v___x_745_ = l_Lake_removeFileIfExists(v_libFile_738_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v___x_746_; uint8_t v___x_747_; lean_object* v___y_749_; 
lean_dec_ref_known(v___x_745_, 1);
v___x_746_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_747_ = 1;
if (v_thin_741_ == 0)
{
v___y_749_ = v___x_746_;
goto v___jp_748_;
}
else
{
lean_object* v___x_773_; 
v___x_773_ = lean_obj_once(&l_Lake_compileStaticLib___closed__3, &l_Lake_compileStaticLib___closed__3_once, _init_l_Lake_compileStaticLib___closed__3);
v___y_749_ = v___x_773_;
goto v___jp_748_;
}
v___jp_748_:
{
size_t v_sz_750_; size_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_sz_750_ = lean_array_size(v_oFiles_739_);
v___x_751_ = ((size_t)0ULL);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_750_, v___x_751_, v_oFiles_739_);
lean_inc_ref(v_libFile_738_);
v___x_753_ = l_Lake_mkArgs(v_libFile_738_, v___x_752_, v_a_742_);
lean_dec_ref(v___x_752_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v_a_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
v_a_755_ = lean_ctor_get(v___x_753_, 1);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_753_, 2);
lean_inc_ref(v___y_749_);
v___x_756_ = lean_array_push(v___y_749_, v_libFile_738_);
v___x_757_ = l_Array_append___redArg(v___x_756_, v_a_754_);
lean_dec(v_a_754_);
v___x_758_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_759_ = lean_box(0);
v___x_760_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_761_ = 0;
v___x_762_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_762_, 0, v___x_758_);
lean_ctor_set(v___x_762_, 1, v_ar_740_);
lean_ctor_set(v___x_762_, 2, v___x_757_);
lean_ctor_set(v___x_762_, 3, v___x_759_);
lean_ctor_set(v___x_762_, 4, v___x_760_);
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*5, v___x_747_);
lean_ctor_set_uint8(v___x_762_, sizeof(void*)*5 + 1, v___x_761_);
v___x_763_ = l_Lake_proc(v___x_762_, v___x_761_, v___x_759_, v_a_755_);
return v___x_763_;
}
else
{
lean_object* v_a_764_; lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v_ar_740_);
lean_dec_ref(v_libFile_738_);
v_a_764_ = lean_ctor_get(v___x_753_, 0);
v_a_765_ = lean_ctor_get(v___x_753_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_753_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_inc(v_a_764_);
lean_dec(v___x_753_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_764_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_775_; uint8_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec_ref(v_ar_740_);
lean_dec_ref(v_oFiles_739_);
lean_dec_ref(v_libFile_738_);
v_a_774_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_745_, 1);
v___x_775_ = lean_io_error_to_string(v_a_774_);
v___x_776_ = 3;
v___x_777_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_777_, 0, v___x_775_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*1, v___x_776_);
v___x_778_ = lean_array_get_size(v_a_742_);
v___x_779_ = lean_array_push(v_a_742_, v___x_777_);
v___x_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
return v___x_780_;
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_782_; uint8_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
lean_dec_ref(v_ar_740_);
lean_dec_ref(v_oFiles_739_);
lean_dec_ref(v_libFile_738_);
v_a_781_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_744_, 1);
v___x_782_ = lean_io_error_to_string(v_a_781_);
v___x_783_ = 3;
v___x_784_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set_uint8(v___x_784_, sizeof(void*)*1, v___x_783_);
v___x_785_ = lean_array_get_size(v_a_742_);
v___x_786_ = lean_array_push(v_a_742_, v___x_784_);
v___x_787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object* v_libFile_788_, lean_object* v_oFiles_789_, lean_object* v_ar_790_, lean_object* v_thin_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
uint8_t v_thin_boxed_794_; lean_object* v_res_795_; 
v_thin_boxed_794_ = lean_unbox(v_thin_791_);
v_res_795_ = l_Lake_compileStaticLib(v_libFile_788_, v_oFiles_789_, v_ar_790_, v_thin_boxed_794_, v_a_792_);
return v_res_795_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__1(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_797_ = ((lean_object*)(l_Lake_compileSharedLib___closed__0));
v___x_798_ = lean_unsigned_to_nat(3u);
v___x_799_ = lean_mk_empty_array_with_capacity(v___x_798_);
v___x_800_ = lean_array_push(v___x_799_, v___x_797_);
return v___x_800_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__2(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = ((lean_object*)(l_Lake_compileLeanModule___closed__12));
v___x_802_ = lean_obj_once(&l_Lake_compileSharedLib___closed__1, &l_Lake_compileSharedLib___closed__1_once, _init_l_Lake_compileSharedLib___closed__1);
v___x_803_ = lean_array_push(v___x_802_, v___x_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object* v_libFile_805_, lean_object* v_linkArgs_806_, lean_object* v_linker_807_, lean_object* v_macosxDeploymentTarget_x3f_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_811_; 
lean_inc_ref(v_libFile_805_);
v___x_811_ = l_Lake_createParentDirs(v_libFile_805_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v___x_812_; 
lean_dec_ref_known(v___x_811_, 1);
lean_inc_ref(v_libFile_805_);
v___x_812_ = l_Lake_mkArgs(v_libFile_805_, v_linkArgs_806_, v_a_809_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v_a_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___y_821_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
v_a_814_ = lean_ctor_get(v___x_812_, 1);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_812_, 2);
v___x_815_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_816_ = lean_obj_once(&l_Lake_compileSharedLib___closed__2, &l_Lake_compileSharedLib___closed__2_once, _init_l_Lake_compileSharedLib___closed__2);
v___x_817_ = lean_array_push(v___x_816_, v_libFile_805_);
v___x_818_ = l_Array_append___redArg(v___x_817_, v_a_813_);
lean_dec(v_a_813_);
v___x_819_ = lean_box(0);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_808_) == 0)
{
lean_object* v___x_826_; 
v___x_826_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_821_ = v___x_826_;
goto v___jp_820_;
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_827_ = ((lean_object*)(l_Lake_compileSharedLib___closed__3));
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_macosxDeploymentTarget_x3f_808_);
v___x_829_ = lean_unsigned_to_nat(1u);
v___x_830_ = lean_mk_empty_array_with_capacity(v___x_829_);
v___x_831_ = lean_array_push(v___x_830_, v___x_828_);
v___y_821_ = v___x_831_;
goto v___jp_820_;
}
v___jp_820_:
{
uint8_t v___x_822_; uint8_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_822_ = 1;
v___x_823_ = 0;
v___x_824_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_824_, 0, v___x_815_);
lean_ctor_set(v___x_824_, 1, v_linker_807_);
lean_ctor_set(v___x_824_, 2, v___x_818_);
lean_ctor_set(v___x_824_, 3, v___x_819_);
lean_ctor_set(v___x_824_, 4, v___y_821_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*5, v___x_822_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*5 + 1, v___x_823_);
v___x_825_ = l_Lake_proc(v___x_824_, v___x_823_, v___x_819_, v_a_814_);
return v___x_825_;
}
}
else
{
lean_object* v_a_832_; lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_macosxDeploymentTarget_x3f_808_);
lean_dec_ref(v_linker_807_);
lean_dec_ref(v_libFile_805_);
v_a_832_ = lean_ctor_get(v___x_812_, 0);
v_a_833_ = lean_ctor_get(v___x_812_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_812_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_inc(v_a_832_);
lean_dec(v___x_812_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_832_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_842_; uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v_macosxDeploymentTarget_x3f_808_);
lean_dec_ref(v_linker_807_);
lean_dec_ref(v_libFile_805_);
v_a_841_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_811_, 1);
v___x_842_ = lean_io_error_to_string(v_a_841_);
v___x_843_ = 3;
v___x_844_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*1, v___x_843_);
v___x_845_ = lean_array_get_size(v_a_809_);
v___x_846_ = lean_array_push(v_a_809_, v___x_844_);
v___x_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object* v_libFile_848_, lean_object* v_linkArgs_849_, lean_object* v_linker_850_, lean_object* v_macosxDeploymentTarget_x3f_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lake_compileSharedLib(v_libFile_848_, v_linkArgs_849_, v_linker_850_, v_macosxDeploymentTarget_x3f_851_, v_a_852_);
lean_dec_ref(v_linkArgs_849_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object* v_binFile_855_, lean_object* v_linkArgs_856_, lean_object* v_linker_857_, lean_object* v_macosxDeploymentTarget_x3f_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___x_861_; 
lean_inc_ref(v_binFile_855_);
v___x_861_ = l_Lake_createParentDirs(v_binFile_855_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v___x_862_; 
lean_dec_ref_known(v___x_861_, 1);
lean_inc_ref(v_binFile_855_);
v___x_862_ = l_Lake_mkArgs(v_binFile_855_, v_linkArgs_856_, v_a_859_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___y_873_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
v_a_864_ = lean_ctor_get(v___x_862_, 1);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_862_, 2);
v___x_865_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_866_ = lean_unsigned_to_nat(2u);
v___x_867_ = lean_mk_empty_array_with_capacity(v___x_866_);
lean_dec_ref(v___x_867_);
v___x_868_ = lean_obj_once(&l_Lake_compileLeanModule___closed__13, &l_Lake_compileLeanModule___closed__13_once, _init_l_Lake_compileLeanModule___closed__13);
v___x_869_ = lean_array_push(v___x_868_, v_binFile_855_);
v___x_870_ = l_Array_append___redArg(v___x_869_, v_a_863_);
lean_dec(v_a_863_);
v___x_871_ = lean_box(0);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_858_) == 0)
{
lean_object* v___x_878_; 
v___x_878_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_873_ = v___x_878_;
goto v___jp_872_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_879_ = ((lean_object*)(l_Lake_compileSharedLib___closed__3));
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v_macosxDeploymentTarget_x3f_858_);
v___x_881_ = lean_unsigned_to_nat(1u);
v___x_882_ = lean_mk_empty_array_with_capacity(v___x_881_);
v___x_883_ = lean_array_push(v___x_882_, v___x_880_);
v___y_873_ = v___x_883_;
goto v___jp_872_;
}
v___jp_872_:
{
uint8_t v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_874_ = 1;
v___x_875_ = 0;
v___x_876_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_876_, 0, v___x_865_);
lean_ctor_set(v___x_876_, 1, v_linker_857_);
lean_ctor_set(v___x_876_, 2, v___x_870_);
lean_ctor_set(v___x_876_, 3, v___x_871_);
lean_ctor_set(v___x_876_, 4, v___y_873_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*5, v___x_874_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*5 + 1, v___x_875_);
v___x_877_ = l_Lake_proc(v___x_876_, v___x_875_, v___x_871_, v_a_864_);
return v___x_877_;
}
}
else
{
lean_object* v_a_884_; lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_macosxDeploymentTarget_x3f_858_);
lean_dec_ref(v_linker_857_);
lean_dec_ref(v_binFile_855_);
v_a_884_ = lean_ctor_get(v___x_862_, 0);
v_a_885_ = lean_ctor_get(v___x_862_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_862_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_inc(v_a_884_);
lean_dec(v___x_862_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_884_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_894_; uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec(v_macosxDeploymentTarget_x3f_858_);
lean_dec_ref(v_linker_857_);
lean_dec_ref(v_binFile_855_);
v_a_893_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v___x_861_, 1);
v___x_894_ = lean_io_error_to_string(v_a_893_);
v___x_895_ = 3;
v___x_896_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set_uint8(v___x_896_, sizeof(void*)*1, v___x_895_);
v___x_897_ = lean_array_get_size(v_a_859_);
v___x_898_ = lean_array_push(v_a_859_, v___x_896_);
v___x_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object* v_binFile_900_, lean_object* v_linkArgs_901_, lean_object* v_linker_902_, lean_object* v_macosxDeploymentTarget_x3f_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lake_compileExe(v_binFile_900_, v_linkArgs_901_, v_linker_902_, v_macosxDeploymentTarget_x3f_903_, v_a_904_);
lean_dec_ref(v_linkArgs_901_);
return v_res_906_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0));
v___x_909_ = lean_unsigned_to_nat(2u);
v___x_910_ = lean_mk_empty_array_with_capacity(v___x_909_);
v___x_911_ = lean_array_push(v___x_910_, v___x_908_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(lean_object* v_as_912_, size_t v_i_913_, size_t v_stop_914_, lean_object* v_b_915_){
_start:
{
uint8_t v___x_916_; 
v___x_916_ = lean_usize_dec_eq(v_i_913_, v_stop_914_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; size_t v___x_921_; size_t v___x_922_; 
v___x_917_ = lean_array_uget_borrowed(v_as_912_, v_i_913_);
v___x_918_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1);
lean_inc(v___x_917_);
v___x_919_ = lean_array_push(v___x_918_, v___x_917_);
v___x_920_ = l_Array_append___redArg(v_b_915_, v___x_919_);
lean_dec_ref(v___x_919_);
v___x_921_ = ((size_t)1ULL);
v___x_922_ = lean_usize_add(v_i_913_, v___x_921_);
v_i_913_ = v___x_922_;
v_b_915_ = v___x_920_;
goto _start;
}
else
{
return v_b_915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___boxed(lean_object* v_as_924_, lean_object* v_i_925_, lean_object* v_stop_926_, lean_object* v_b_927_){
_start:
{
size_t v_i_boxed_928_; size_t v_stop_boxed_929_; lean_object* v_res_930_; 
v_i_boxed_928_ = lean_unbox_usize(v_i_925_);
lean_dec(v_i_925_);
v_stop_boxed_929_ = lean_unbox_usize(v_stop_926_);
lean_dec(v_stop_926_);
v_res_930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_as_924_, v_i_boxed_928_, v_stop_boxed_929_, v_b_927_);
lean_dec_ref(v_as_924_);
return v_res_930_;
}
}
static lean_object* _init_l_Lake_download___closed__6(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_937_ = ((lean_object*)(l_Lake_download___closed__2));
v___x_938_ = lean_unsigned_to_nat(7u);
v___x_939_ = lean_mk_empty_array_with_capacity(v___x_938_);
v___x_940_ = lean_array_push(v___x_939_, v___x_937_);
return v___x_940_;
}
}
static lean_object* _init_l_Lake_download___closed__7(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_942_ = lean_obj_once(&l_Lake_download___closed__6, &l_Lake_download___closed__6_once, _init_l_Lake_download___closed__6);
v___x_943_ = lean_array_push(v___x_942_, v___x_941_);
return v___x_943_;
}
}
static lean_object* _init_l_Lake_download___closed__8(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_945_ = lean_obj_once(&l_Lake_download___closed__7, &l_Lake_download___closed__7_once, _init_l_Lake_download___closed__7);
v___x_946_ = lean_array_push(v___x_945_, v___x_944_);
return v___x_946_;
}
}
static lean_object* _init_l_Lake_download___closed__9(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = ((lean_object*)(l_Lake_compileLeanModule___closed__12));
v___x_948_ = lean_obj_once(&l_Lake_download___closed__8, &l_Lake_download___closed__8_once, _init_l_Lake_download___closed__8);
v___x_949_ = lean_array_push(v___x_948_, v___x_947_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lake_download(lean_object* v_url_950_, lean_object* v_file_951_, lean_object* v_headers_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v_val_958_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_974_; uint8_t v___x_986_; 
v___x_986_ = l_System_FilePath_pathExists(v_file_951_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
lean_inc_ref(v_file_951_);
v___x_987_ = l_Lake_createParentDirs(v_file_951_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_dec_ref_known(v___x_987_, 1);
v___y_974_ = v_a_953_;
goto v___jp_973_;
}
else
{
lean_object* v_a_988_; lean_object* v___x_989_; uint8_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec_ref(v_file_951_);
lean_dec_ref(v_url_950_);
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = lean_io_error_to_string(v_a_988_);
v___x_990_ = 3;
v___x_991_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set_uint8(v___x_991_, sizeof(void*)*1, v___x_990_);
v___x_992_ = lean_array_get_size(v_a_953_);
v___x_993_ = lean_array_push(v_a_953_, v___x_991_);
v___x_994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
return v___x_994_;
}
}
else
{
lean_object* v___x_995_; 
v___x_995_ = lean_io_remove_file(v_file_951_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_dec_ref_known(v___x_995_, 1);
v___y_974_ = v_a_953_;
goto v___jp_973_;
}
else
{
lean_object* v_a_996_; lean_object* v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_dec_ref(v_file_951_);
lean_dec_ref(v_url_950_);
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v___x_997_ = lean_io_error_to_string(v_a_996_);
v___x_998_ = 3;
v___x_999_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*1, v___x_998_);
v___x_1000_ = lean_array_get_size(v_a_953_);
v___x_1001_ = lean_array_push(v_a_953_, v___x_999_);
v___x_1002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
return v___x_1002_;
}
}
v___jp_955_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_959_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_960_ = lean_box(0);
v___x_961_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_962_ = 1;
v___x_963_ = 0;
v___x_964_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_964_, 0, v___x_959_);
lean_ctor_set(v___x_964_, 1, v_val_958_);
lean_ctor_set(v___x_964_, 2, v___y_957_);
lean_ctor_set(v___x_964_, 3, v___x_960_);
lean_ctor_set(v___x_964_, 4, v___x_961_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*5, v___x_962_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*5 + 1, v___x_963_);
v___x_965_ = l_Lake_proc(v___x_964_, v___x_962_, v___x_960_, v___y_956_);
return v___x_965_;
}
v___jp_966_:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lake_download___closed__0));
v___x_970_ = lean_io_getenv(v___x_969_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v___x_971_; 
v___x_971_ = ((lean_object*)(l_Lake_download___closed__1));
v___y_956_ = v___y_967_;
v___y_957_ = v___y_968_;
v_val_958_ = v___x_971_;
goto v___jp_955_;
}
else
{
lean_object* v_val_972_; 
v_val_972_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_val_972_);
lean_dec_ref_known(v___x_970_, 1);
v___y_956_ = v___y_967_;
v___y_957_ = v___y_968_;
v_val_958_ = v_val_972_;
goto v___jp_955_;
}
}
v___jp_973_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_975_ = ((lean_object*)(l_Lake_download___closed__5));
v___x_976_ = lean_obj_once(&l_Lake_download___closed__9, &l_Lake_download___closed__9_once, _init_l_Lake_download___closed__9);
v___x_977_ = lean_array_push(v___x_976_, v_file_951_);
v___x_978_ = lean_array_push(v___x_977_, v___x_975_);
v___x_979_ = lean_array_push(v___x_978_, v_url_950_);
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_array_get_size(v_headers_952_);
v___x_982_ = lean_nat_dec_lt(v___x_980_, v___x_981_);
if (v___x_982_ == 0)
{
v___y_967_ = v___y_974_;
v___y_968_ = v___x_979_;
goto v___jp_966_;
}
else
{
size_t v___x_983_; size_t v___x_984_; lean_object* v___x_985_; 
v___x_983_ = ((size_t)0ULL);
v___x_984_ = lean_usize_of_nat(v___x_981_);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_952_, v___x_983_, v___x_984_, v___x_979_);
v___y_967_ = v___y_974_;
v___y_968_ = v___x_985_;
goto v___jp_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object* v_url_1003_, lean_object* v_file_1004_, lean_object* v_headers_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lake_download(v_url_1003_, v_file_1004_, v_headers_1005_, v_a_1006_);
lean_dec_ref(v_headers_1005_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lake_untar(lean_object* v_file_1013_, lean_object* v_dir_1014_, uint8_t v_gzip_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_opts_1019_; lean_object* v___y_1020_; lean_object* v___x_1038_; 
lean_inc_ref(v_dir_1014_);
v___x_1038_ = l_IO_FS_createDirAll(v_dir_1014_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_dec_ref_known(v___x_1038_, 1);
if (v_gzip_1015_ == 0)
{
lean_object* v___x_1039_; 
v___x_1039_ = ((lean_object*)(l_Lake_untar___closed__2));
v_opts_1019_ = v___x_1039_;
v___y_1020_ = v_a_1016_;
goto v___jp_1018_;
}
else
{
lean_object* v___x_1040_; 
v___x_1040_ = ((lean_object*)(l_Lake_untar___closed__3));
v_opts_1019_ = v___x_1040_;
v___y_1020_ = v_a_1016_;
goto v___jp_1018_;
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec_ref(v_dir_1014_);
lean_dec_ref(v_file_1013_);
v_a_1041_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1042_ = lean_io_error_to_string(v_a_1041_);
v___x_1043_ = 3;
v___x_1044_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*1, v___x_1043_);
v___x_1045_ = lean_array_get_size(v_a_1016_);
v___x_1046_ = lean_array_push(v_a_1016_, v___x_1044_);
v___x_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
return v___x_1047_;
}
v___jp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1021_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_1022_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_1023_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_1024_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_1025_ = lean_unsigned_to_nat(5u);
v___x_1026_ = lean_mk_empty_array_with_capacity(v___x_1025_);
lean_inc_ref(v_opts_1019_);
v___x_1027_ = lean_array_push(v___x_1026_, v_opts_1019_);
v___x_1028_ = lean_array_push(v___x_1027_, v___x_1023_);
v___x_1029_ = lean_array_push(v___x_1028_, v_file_1013_);
v___x_1030_ = lean_array_push(v___x_1029_, v___x_1024_);
v___x_1031_ = lean_array_push(v___x_1030_, v_dir_1014_);
v___x_1032_ = lean_box(0);
v___x_1033_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_1034_ = 1;
v___x_1035_ = 0;
v___x_1036_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1036_, 0, v___x_1021_);
lean_ctor_set(v___x_1036_, 1, v___x_1022_);
lean_ctor_set(v___x_1036_, 2, v___x_1031_);
lean_ctor_set(v___x_1036_, 3, v___x_1032_);
lean_ctor_set(v___x_1036_, 4, v___x_1033_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*5, v___x_1034_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*5 + 1, v___x_1035_);
v___x_1037_ = l_Lake_proc(v___x_1036_, v___x_1034_, v___x_1032_, v___y_1020_);
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object* v_file_1048_, lean_object* v_dir_1049_, lean_object* v_gzip_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
uint8_t v_gzip_boxed_1053_; lean_object* v_res_1054_; 
v_gzip_boxed_1053_ = lean_unbox(v_gzip_1050_);
v_res_1054_ = l_Lake_untar(v_file_1048_, v_dir_1049_, v_gzip_boxed_1053_, v_a_1051_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(lean_object* v_as_1056_, size_t v_sz_1057_, size_t v_i_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_){
_start:
{
uint8_t v___x_1062_; 
v___x_1062_ = lean_usize_dec_lt(v_i_1058_, v_sz_1057_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v_b_1059_);
lean_ctor_set(v___x_1063_, 1, v___y_1060_);
return v___x_1063_;
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; 
v_a_1064_ = lean_array_uget_borrowed(v_as_1056_, v_i_1058_);
v___x_1065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0));
v___x_1066_ = lean_string_append(v___x_1065_, v_a_1064_);
v___x_1067_ = lean_array_push(v_b_1059_, v___x_1066_);
v___x_1068_ = ((size_t)1ULL);
v___x_1069_ = lean_usize_add(v_i_1058_, v___x_1068_);
v_i_1058_ = v___x_1069_;
v_b_1059_ = v___x_1067_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___boxed(lean_object* v_as_1071_, lean_object* v_sz_1072_, lean_object* v_i_1073_, lean_object* v_b_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
size_t v_sz_boxed_1077_; size_t v_i_boxed_1078_; lean_object* v_res_1079_; 
v_sz_boxed_1077_ = lean_unbox_usize(v_sz_1072_);
lean_dec(v_sz_1072_);
v_i_boxed_1078_ = lean_unbox_usize(v_i_1073_);
lean_dec(v_i_1073_);
v_res_1079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_as_1071_, v_sz_boxed_1077_, v_i_boxed_1078_, v_b_1074_, v___y_1075_);
lean_dec_ref(v_as_1071_);
return v_res_1079_;
}
}
static lean_object* _init_l_Lake_tar___closed__1(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1081_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_1082_ = lean_unsigned_to_nat(5u);
v___x_1083_ = lean_mk_empty_array_with_capacity(v___x_1082_);
v___x_1084_ = lean_array_push(v___x_1083_, v___x_1081_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lake_tar___closed__10(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = ((lean_object*)(l_Lake_tar___closed__9));
v___x_1103_ = ((lean_object*)(l_Lake_tar___closed__8));
v___x_1104_ = lean_array_push(v___x_1103_, v___x_1102_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lake_tar(lean_object* v_dir_1105_, lean_object* v_file_1106_, uint8_t v_gzip_1107_, lean_object* v_excludePaths_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; uint8_t v___y_1117_; lean_object* v___y_1118_; lean_object* v_args_1124_; lean_object* v___y_1125_; lean_object* v___x_1155_; 
lean_inc_ref(v_file_1106_);
v___x_1155_ = l_Lake_createParentDirs(v_file_1106_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v___x_1156_; 
lean_dec_ref_known(v___x_1155_, 1);
v___x_1156_ = ((lean_object*)(l_Lake_tar___closed__8));
if (v_gzip_1107_ == 0)
{
v_args_1124_ = v___x_1156_;
v___y_1125_ = v_a_1109_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_obj_once(&l_Lake_tar___closed__10, &l_Lake_tar___closed__10_once, _init_l_Lake_tar___closed__10);
v_args_1124_ = v___x_1157_;
v___y_1125_ = v_a_1109_;
goto v___jp_1123_;
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec_ref(v_file_1106_);
lean_dec_ref(v_dir_1105_);
v_a_1158_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1159_ = lean_io_error_to_string(v_a_1158_);
v___x_1160_ = 3;
v___x_1161_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*1, v___x_1160_);
v___x_1162_ = lean_array_get_size(v_a_1109_);
v___x_1163_ = lean_array_push(v_a_1109_, v___x_1161_);
v___x_1164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
return v___x_1164_;
}
v___jp_1111_:
{
uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1119_ = 0;
lean_inc_ref(v___y_1118_);
lean_inc(v___y_1112_);
lean_inc_ref(v___y_1115_);
lean_inc_ref(v___y_1116_);
v___x_1120_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1120_, 0, v___y_1116_);
lean_ctor_set(v___x_1120_, 1, v___y_1115_);
lean_ctor_set(v___x_1120_, 2, v___y_1113_);
lean_ctor_set(v___x_1120_, 3, v___y_1112_);
lean_ctor_set(v___x_1120_, 4, v___y_1118_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*5, v___y_1117_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*5 + 1, v___x_1119_);
v___x_1121_ = lean_box(0);
v___x_1122_ = l_Lake_proc(v___x_1120_, v___y_1117_, v___x_1121_, v___y_1114_);
return v___x_1122_;
}
v___jp_1123_:
{
size_t v_sz_1126_; size_t v___x_1127_; lean_object* v___x_1128_; 
v_sz_1126_ = lean_array_size(v_excludePaths_1108_);
v___x_1127_ = ((size_t)0ULL);
lean_inc_ref(v_args_1124_);
v___x_1128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_excludePaths_1108_, v_sz_1126_, v___x_1127_, v_args_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; uint8_t v___x_1143_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
v_a_1130_ = lean_ctor_get(v___x_1128_, 1);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1128_, 2);
v___x_1131_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_1132_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_1133_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_1134_ = ((lean_object*)(l_Lake_tar___closed__0));
v___x_1135_ = lean_obj_once(&l_Lake_tar___closed__1, &l_Lake_tar___closed__1_once, _init_l_Lake_tar___closed__1);
v___x_1136_ = lean_array_push(v___x_1135_, v_file_1106_);
v___x_1137_ = lean_array_push(v___x_1136_, v___x_1133_);
v___x_1138_ = lean_array_push(v___x_1137_, v_dir_1105_);
v___x_1139_ = lean_array_push(v___x_1138_, v___x_1134_);
v___x_1140_ = l_Array_append___redArg(v_a_1129_, v___x_1139_);
lean_dec_ref(v___x_1139_);
v___x_1141_ = lean_box(0);
v___x_1142_ = l_System_Platform_isOSX;
v___x_1143_ = 1;
if (v___x_1142_ == 0)
{
lean_object* v___x_1144_; 
v___x_1144_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_1112_ = v___x_1141_;
v___y_1113_ = v___x_1140_;
v___y_1114_ = v_a_1130_;
v___y_1115_ = v___x_1132_;
v___y_1116_ = v___x_1131_;
v___y_1117_ = v___x_1143_;
v___y_1118_ = v___x_1144_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1145_; 
v___x_1145_ = ((lean_object*)(l_Lake_tar___closed__6));
v___y_1112_ = v___x_1141_;
v___y_1113_ = v___x_1140_;
v___y_1114_ = v_a_1130_;
v___y_1115_ = v___x_1132_;
v___y_1116_ = v___x_1131_;
v___y_1117_ = v___x_1143_;
v___y_1118_ = v___x_1145_;
goto v___jp_1111_;
}
}
else
{
lean_object* v_a_1146_; lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec_ref(v_file_1106_);
lean_dec_ref(v_dir_1105_);
v_a_1146_ = lean_ctor_get(v___x_1128_, 0);
v_a_1147_ = lean_ctor_get(v___x_1128_, 1);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1128_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_inc(v_a_1146_);
lean_dec(v___x_1128_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1146_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object* v_dir_1165_, lean_object* v_file_1166_, lean_object* v_gzip_1167_, lean_object* v_excludePaths_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
uint8_t v_gzip_boxed_1171_; lean_object* v_res_1172_; 
v_gzip_boxed_1171_ = lean_unbox(v_gzip_1167_);
v_res_1172_ = l_Lake_tar(v_dir_1165_, v_file_1166_, v_gzip_boxed_1171_, v_excludePaths_1168_, v_a_1169_);
lean_dec_ref(v_excludePaths_1168_);
return v_res_1172_;
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
