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
lean_object* l_Lake_compileLeanIR(lean_object* v_setupFile_4_, lean_object* v_irFile_5_, lean_object* v_cFile_6_, lean_object* v_leanPath_7_, lean_object* v_leanir_8_, lean_object* v_a_9_){
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
LEAN_EXPORT void l_Lake_compileLeanIR_0interp(lean_interpreter_value* stack)
{
lean_object* v_setupFile_4_ = stack[0].m_obj;
lean_object* v_irFile_5_ = stack[1].m_obj;
lean_object* v_cFile_6_ = stack[2].m_obj;
lean_object* v_leanPath_7_ = stack[3].m_obj;
lean_object* v_leanir_8_ = stack[4].m_obj;
lean_object* v_a_9_ = stack[5].m_obj;
lean_object* v_res_52_;
v_res_52_ = l_Lake_compileLeanIR(v_setupFile_4_, v_irFile_5_, v_cFile_6_, v_leanPath_7_, v_leanir_8_, v_a_9_);
stack->m_obj
 = v_res_52_;
}
LEAN_EXPORT lean_object* l_Lake_compileLeanIR___boxed(lean_object* v_setupFile_53_, lean_object* v_irFile_54_, lean_object* v_cFile_55_, lean_object* v_leanPath_56_, lean_object* v_leanir_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lake_compileLeanIR(v_setupFile_53_, v_irFile_54_, v_cFile_55_, v_leanPath_56_, v_leanir_57_, v_a_58_);
return v_res_60_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg(){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg___closed__0));
return v___x_64_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_65_;
v_res_65_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg();
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg___boxed(lean_object* v___dummy_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg();
return v_res_67_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0(void){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___redArg();
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1(lean_object* v_s_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___boxed(lean_object* v_s_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1(v_s_71_);
lean_dec_ref(v_s_71_);
return v_res_72_;
}
}
uint8_t l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(lean_object* v_opts_73_, lean_object* v_opt_74_){
_start:
{
lean_object* v_name_75_; lean_object* v_defValue_76_; lean_object* v_map_77_; lean_object* v___x_78_; 
v_name_75_ = lean_ctor_get(v_opt_74_, 0);
v_defValue_76_ = lean_ctor_get(v_opt_74_, 1);
v_map_77_ = lean_ctor_get(v_opts_73_, 0);
v___x_78_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_77_, v_name_75_);
if (lean_obj_tag(v___x_78_) == 0)
{
uint8_t v___x_79_; 
v___x_79_ = lean_unbox(v_defValue_76_);
return v___x_79_;
}
else
{
lean_object* v_val_80_; 
v_val_80_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_val_80_);
lean_dec_ref_known(v___x_78_, 1);
if (lean_obj_tag(v_val_80_) == 1)
{
uint8_t v_v_81_; 
v_v_81_ = lean_ctor_get_uint8(v_val_80_, 0);
lean_dec_ref_known(v_val_80_, 0);
return v_v_81_;
}
else
{
uint8_t v___x_82_; 
lean_dec(v_val_80_);
v___x_82_ = lean_unbox(v_defValue_76_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_73_ = stack[0].m_obj;
lean_object* v_opt_74_ = stack[1].m_obj;
uint8_t v_res_83_;
v_res_83_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(v_opts_73_, v_opt_74_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3___boxed(lean_object* v_opts_84_, lean_object* v_opt_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(v_opts_84_, v_opt_85_);
lean_dec_ref(v_opt_85_);
lean_dec_ref(v_opts_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(lean_object* v_as_88_, size_t v_i_89_, size_t v_stop_90_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = lean_usize_dec_eq(v_i_89_, v_stop_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; uint8_t v_level_93_; 
v___x_92_ = lean_array_uget_borrowed(v_as_88_, v_i_89_);
v_level_93_ = lean_ctor_get_uint8(v___x_92_, sizeof(void*)*1);
if (v_level_93_ == 3)
{
uint8_t v___x_94_; 
v___x_94_ = 1;
return v___x_94_;
}
else
{
size_t v___x_95_; size_t v___x_96_; 
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_add(v_i_89_, v___x_95_);
v_i_89_ = v___x_96_;
goto _start;
}
}
else
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_88_ = stack[0].m_obj;
size_t v_i_89_ = stack[1].m_num;
size_t v_stop_90_ = stack[2].m_num;
uint8_t v_res_99_;
v_res_99_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(v_as_88_, v_i_89_, v_stop_90_);
stack->m_num = v_res_99_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0___boxed(lean_object* v_as_100_, lean_object* v_i_101_, lean_object* v_stop_102_){
_start:
{
size_t v_i_boxed_103_; size_t v_stop_boxed_104_; uint8_t v_res_105_; lean_object* v_r_106_; 
v_i_boxed_103_ = lean_unbox_usize(v_i_101_);
lean_dec(v_i_101_);
v_stop_boxed_104_ = lean_unbox_usize(v_stop_102_);
lean_dec(v_stop_102_);
v_res_105_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(v_as_100_, v_i_boxed_103_, v_stop_boxed_104_);
lean_dec_ref(v_as_100_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
lean_object* l_Lake_compileLeanModule___lam__0(uint32_t v_exitCode_109_, lean_object* v___x_110_, lean_object* v_stderr_111_, lean_object* v_____r_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___y_116_; uint32_t v___y_117_; lean_object* v___y_128_; uint32_t v___y_129_; uint8_t v___y_130_; lean_object* v___y_136_; uint8_t v___y_137_; lean_object* v___y_143_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_152_ = lean_string_utf8_byte_size(v_stderr_111_);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_nat_dec_eq(v___x_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_155_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__1));
v___x_156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_156_, 0, v_stderr_111_);
lean_ctor_set(v___x_156_, 1, v___x_153_);
lean_ctor_set(v___x_156_, 2, v___x_152_);
v___x_157_ = l_String_Slice_trimAscii(v___x_156_);
v___x_158_ = l_String_Slice_toString(v___x_157_);
lean_dec_ref(v___x_157_);
v___x_159_ = lean_string_append(v___x_155_, v___x_158_);
lean_dec_ref(v___x_158_);
v___x_160_ = 1;
v___x_161_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*1, v___x_160_);
v___x_162_ = lean_array_push(v___y_113_, v___x_161_);
v___y_143_ = v___x_162_;
goto v___jp_142_;
}
else
{
lean_dec_ref(v_stderr_111_);
v___y_143_ = v___y_113_;
goto v___jp_142_;
}
v___jp_115_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_118_ = ((lean_object*)(l_Lake_compileLeanModule___lam__0___closed__0));
v___x_119_ = lean_uint32_to_nat(v___y_117_);
v___x_120_ = l_Nat_reprFast(v___x_119_);
v___x_121_ = lean_string_append(v___x_118_, v___x_120_);
lean_dec_ref(v___x_120_);
v___x_122_ = 3;
v___x_123_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*1, v___x_122_);
v___x_124_ = lean_array_get_size(v___y_116_);
v___x_125_ = lean_array_push(v___y_116_, v___x_123_);
v___x_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
return v___x_126_;
}
v___jp_127_:
{
uint32_t v___x_131_; uint8_t v___x_132_; 
v___x_131_ = 0;
v___x_132_ = lean_uint32_dec_eq(v___y_129_, v___x_131_);
if (v___x_132_ == 0)
{
v___y_116_ = v___y_128_;
v___y_117_ = v___y_129_;
goto v___jp_115_;
}
else
{
if (v___y_130_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_box(0);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___y_128_);
return v___x_134_;
}
else
{
v___y_116_ = v___y_128_;
v___y_117_ = v___y_129_;
goto v___jp_115_;
}
}
}
v___jp_135_:
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 1;
v___x_139_ = lean_uint32_dec_eq(v_exitCode_109_, v___x_138_);
if (v___x_139_ == 0)
{
v___y_128_ = v___y_136_;
v___y_129_ = v_exitCode_109_;
v___y_130_ = v___y_137_;
goto v___jp_127_;
}
else
{
if (v___y_137_ == 0)
{
v___y_128_ = v___y_136_;
v___y_129_ = v_exitCode_109_;
v___y_130_ = v___y_137_;
goto v___jp_127_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_array_get_size(v___y_136_);
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___y_136_);
return v___x_141_;
}
}
}
v___jp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_144_ = lean_array_get_size(v___y_143_);
v___x_145_ = l_Array_extract___redArg(v___y_143_, v___x_110_, v___x_144_);
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = lean_array_get_size(v___x_145_);
v___x_148_ = lean_nat_dec_lt(v___x_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_dec_ref(v___x_145_);
v___y_136_ = v___y_143_;
v___y_137_ = v___x_148_;
goto v___jp_135_;
}
else
{
if (v___x_148_ == 0)
{
lean_dec_ref(v___x_145_);
v___y_136_ = v___y_143_;
v___y_137_ = v___x_148_;
goto v___jp_135_;
}
else
{
size_t v___x_149_; size_t v___x_150_; uint8_t v___x_151_; 
v___x_149_ = ((size_t)0ULL);
v___x_150_ = lean_usize_of_nat(v___x_147_);
v___x_151_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_compileLeanModule_spec__0(v___x_145_, v___x_149_, v___x_150_);
lean_dec_ref(v___x_145_);
v___y_136_ = v___y_143_;
v___y_137_ = v___x_151_;
goto v___jp_135_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_compileLeanModule___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_exitCode_109_ = stack[0].m_num;
lean_object* v___x_110_ = stack[1].m_obj;
lean_object* v_stderr_111_ = stack[2].m_obj;
lean_object* v_____r_112_ = stack[3].m_obj;
lean_object* v___y_113_ = stack[4].m_obj;
lean_object* v_res_163_;
v_res_163_ = l_Lake_compileLeanModule___lam__0(v_exitCode_109_, v___x_110_, v_stderr_111_, v_____r_112_, v___y_113_);
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object* v_exitCode_164_, lean_object* v___x_165_, lean_object* v_stderr_166_, lean_object* v_____r_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
uint32_t v_exitCode_boxed_170_; lean_object* v_res_171_; 
v_exitCode_boxed_170_ = lean_unbox_uint32(v_exitCode_164_);
lean_dec(v_exitCode_164_);
v_res_171_ = l_Lake_compileLeanModule___lam__0(v_exitCode_boxed_170_, v___x_165_, v_stderr_166_, v_____r_167_, v___y_168_);
return v_res_171_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(lean_object* v_a_172_, lean_object* v_b_173_, lean_object* v_relLeanFile_174_, lean_object* v_____r_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_a_179_; lean_object* v_toBaseMessage_181_; uint8_t v_isSilent_182_; 
v_toBaseMessage_181_ = lean_ctor_get(v_a_172_, 0);
lean_inc_ref(v_toBaseMessage_181_);
v_isSilent_182_ = lean_ctor_get_uint8(v_toBaseMessage_181_, sizeof(void*)*5 + 2);
if (v_isSilent_182_ == 0)
{
lean_object* v_kind_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_207_; 
v_kind_183_ = lean_ctor_get(v_a_172_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v_a_172_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_a_172_, 0);
lean_dec(v_unused_208_);
v___x_185_ = v_a_172_;
v_isShared_186_ = v_isSharedCheck_207_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_kind_183_);
lean_dec(v_a_172_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_207_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v_pos_187_; lean_object* v_endPos_188_; uint8_t v_keepFullRange_189_; uint8_t v_severity_190_; lean_object* v_caption_191_; lean_object* v_data_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_205_; 
v_pos_187_ = lean_ctor_get(v_toBaseMessage_181_, 1);
v_endPos_188_ = lean_ctor_get(v_toBaseMessage_181_, 2);
v_keepFullRange_189_ = lean_ctor_get_uint8(v_toBaseMessage_181_, sizeof(void*)*5);
v_severity_190_ = lean_ctor_get_uint8(v_toBaseMessage_181_, sizeof(void*)*5 + 1);
v_caption_191_ = lean_ctor_get(v_toBaseMessage_181_, 3);
v_data_192_ = lean_ctor_get(v_toBaseMessage_181_, 4);
v_isSharedCheck_205_ = !lean_is_exclusive(v_toBaseMessage_181_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_toBaseMessage_181_, 0);
lean_dec(v_unused_206_);
v___x_194_ = v_toBaseMessage_181_;
v_isShared_195_ = v_isSharedCheck_205_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_data_192_);
lean_inc(v_caption_191_);
lean_inc(v_endPos_188_);
lean_inc(v_pos_187_);
lean_dec(v_toBaseMessage_181_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_205_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_196_ = l_Lake_mkRelPathString(v_relLeanFile_174_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_196_);
v___x_198_ = v___x_194_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_pos_187_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_endPos_188_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v_caption_191_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v_data_192_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*5, v_keepFullRange_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*5 + 1, v_severity_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*5 + 2, v_isSilent_182_);
v___x_198_ = v_reuseFailAlloc_204_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_200_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_198_);
v___x_200_ = v___x_185_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_kind_183_);
v___x_200_ = v_reuseFailAlloc_203_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = l_Lake_LogEntry_ofSerialMessage(v___x_200_);
v___x_202_ = lean_array_push(v___y_176_, v___x_201_);
v_a_179_ = v___x_202_;
goto v___jp_178_;
}
}
}
}
}
else
{
lean_dec_ref(v_toBaseMessage_181_);
lean_dec_ref(v_relLeanFile_174_);
lean_dec_ref(v_a_172_);
v_a_179_ = v___y_176_;
goto v___jp_178_;
}
v___jp_178_:
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_b_173_);
lean_ctor_set(v___x_180_, 1, v_a_179_);
return v___x_180_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_172_ = stack[0].m_obj;
lean_object* v_b_173_ = stack[1].m_obj;
lean_object* v_relLeanFile_174_ = stack[2].m_obj;
lean_object* v_____r_175_ = stack[3].m_obj;
lean_object* v___y_176_ = stack[4].m_obj;
lean_object* v_res_209_;
v_res_209_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_172_, v_b_173_, v_relLeanFile_174_, v_____r_175_, v___y_176_);
stack->m_obj
 = v_res_209_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0___boxed(lean_object* v_a_210_, lean_object* v_b_211_, lean_object* v_relLeanFile_212_, lean_object* v_____r_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_210_, v_b_211_, v_relLeanFile_212_, v_____r_213_, v___y_214_);
return v_res_216_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(lean_object* v_relLeanFile_219_, lean_object* v___x_220_, lean_object* v___x_221_, lean_object* v___x_222_, lean_object* v_a_223_, lean_object* v_b_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v_it_250_; lean_object* v_startInclusive_251_; lean_object* v_endExclusive_252_; 
if (lean_obj_tag(v_a_223_) == 0)
{
lean_object* v_currPos_270_; lean_object* v_searcher_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_294_; 
v_currPos_270_ = lean_ctor_get(v_a_223_, 0);
v_searcher_271_ = lean_ctor_get(v_a_223_, 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v_a_223_);
if (v_isSharedCheck_294_ == 0)
{
v___x_273_ = v_a_223_;
v_isShared_274_ = v_isSharedCheck_294_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_searcher_271_);
lean_inc(v_currPos_270_);
lean_dec(v_a_223_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_294_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint8_t v_decide_275_; 
v_decide_275_ = lean_nat_dec_eq(v_searcher_271_, v___x_222_);
if (v_decide_275_ == 0)
{
uint32_t v___x_276_; uint32_t v___x_277_; uint8_t v___x_278_; 
v___x_276_ = 10;
v___x_277_ = lean_string_utf8_get_fast(v___x_220_, v_searcher_271_);
v___x_278_ = lean_uint32_dec_eq(v___x_277_, v___x_276_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_279_ = lean_string_utf8_next_fast(v___x_220_, v_searcher_271_);
lean_dec(v_searcher_271_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 1, v___x_279_);
v___x_281_ = v___x_273_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_currPos_270_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_279_);
v___x_281_ = v_reuseFailAlloc_283_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
v_a_223_ = v___x_281_;
goto _start;
}
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_slice_287_; lean_object* v_nextIt_289_; 
v___x_284_ = lean_string_utf8_next_fast(v___x_220_, v_searcher_271_);
v___x_285_ = lean_nat_sub(v___x_284_, v_searcher_271_);
v___x_286_ = lean_nat_add(v_searcher_271_, v___x_285_);
lean_dec(v___x_285_);
v_slice_287_ = l_String_Slice_subslice_x21(v___x_221_, v_currPos_270_, v_searcher_271_);
lean_inc(v___x_286_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 1, v___x_286_);
lean_ctor_set(v___x_273_, 0, v___x_286_);
v_nextIt_289_ = v___x_273_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_286_);
v_nextIt_289_ = v_reuseFailAlloc_292_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v_startInclusive_290_; lean_object* v_endExclusive_291_; 
v_startInclusive_290_ = lean_ctor_get(v_slice_287_, 0);
lean_inc(v_startInclusive_290_);
v_endExclusive_291_ = lean_ctor_get(v_slice_287_, 1);
lean_inc(v_endExclusive_291_);
lean_dec_ref(v_slice_287_);
v_it_250_ = v_nextIt_289_;
v_startInclusive_251_ = v_startInclusive_290_;
v_endExclusive_252_ = v_endExclusive_291_;
goto v___jp_249_;
}
}
}
else
{
lean_object* v___x_293_; 
lean_del_object(v___x_273_);
lean_dec(v_searcher_271_);
v___x_293_ = lean_box(1);
lean_inc(v___x_222_);
v_it_250_ = v___x_293_;
v_startInclusive_251_ = v_currPos_270_;
v_endExclusive_252_ = v___x_222_;
goto v___jp_249_;
}
}
}
else
{
lean_object* v___x_295_; 
lean_dec(v___x_222_);
lean_dec_ref(v_relLeanFile_219_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v_b_224_);
lean_ctor_set(v___x_295_, 1, v___y_225_);
return v___x_295_;
}
v___jp_227_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_string_append(v_b_224_, v___y_228_);
lean_dec_ref(v___y_228_);
v___x_231_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__0));
v___x_232_ = lean_string_append(v___x_230_, v___x_231_);
v_a_223_ = v___y_229_;
v_b_224_ = v___x_232_;
goto _start;
}
v___jp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_237_ = lean_string_utf8_byte_size(v_b_224_);
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = lean_nat_dec_eq(v___x_237_, v___x_238_);
if (v___x_239_ == 0)
{
v___y_228_ = v___y_235_;
v___y_229_ = v___y_236_;
goto v___jp_227_;
}
else
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_string_utf8_byte_size(v___y_235_);
v___x_241_ = lean_nat_dec_eq(v___x_240_, v___x_238_);
if (v___x_241_ == 0)
{
v___y_228_ = v___y_235_;
v___y_229_ = v___y_236_;
goto v___jp_227_;
}
else
{
lean_dec_ref(v___y_235_);
v_a_223_ = v___y_236_;
goto _start;
}
}
}
v___jp_243_:
{
if (lean_obj_tag(v___y_245_) == 0)
{
lean_object* v_a_246_; lean_object* v_a_247_; 
v_a_246_ = lean_ctor_get(v___y_245_, 0);
lean_inc(v_a_246_);
v_a_247_ = lean_ctor_get(v___y_245_, 1);
lean_inc(v_a_247_);
lean_dec_ref_known(v___y_245_, 2);
v_a_223_ = v___y_244_;
v_b_224_ = v_a_246_;
v___y_225_ = v_a_247_;
goto _start;
}
else
{
lean_dec(v___y_244_);
lean_dec(v___x_222_);
lean_dec_ref(v_relLeanFile_219_);
return v___y_245_;
}
}
v___jp_249_:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_string_utf8_extract_fast(v___x_220_, v_startInclusive_251_, v_endExclusive_252_);
lean_dec(v_endExclusive_252_);
lean_dec(v_startInclusive_251_);
lean_inc_ref(v___x_253_);
v___x_254_ = l_Lean_Json_parse(v___x_253_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_dec_ref_known(v___x_254_, 1);
v___y_235_ = v___x_253_;
v___y_236_ = v_it_250_;
goto v___jp_234_;
}
else
{
lean_object* v_a_255_; lean_object* v___x_256_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_254_, 1);
v___x_256_ = l_Lean_instFromJsonSerialMessage_fromJson(v_a_255_);
if (lean_obj_tag(v___x_256_) == 1)
{
lean_object* v_a_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
lean_dec_ref(v___x_253_);
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
lean_dec_ref_known(v___x_256_, 1);
v___x_258_ = lean_string_utf8_byte_size(v_b_224_);
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_nat_dec_eq(v___x_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_261_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__1));
v___x_262_ = lean_string_append(v___x_261_, v_b_224_);
v___x_263_ = 1;
v___x_264_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set_uint8(v___x_264_, sizeof(void*)*1, v___x_263_);
v___x_265_ = lean_box(0);
v___x_266_ = lean_array_push(v___y_225_, v___x_264_);
lean_inc_ref(v_relLeanFile_219_);
v___x_267_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_257_, v_b_224_, v_relLeanFile_219_, v___x_265_, v___x_266_);
v___y_244_ = v_it_250_;
v___y_245_ = v___x_267_;
goto v___jp_243_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_box(0);
lean_inc_ref(v_relLeanFile_219_);
v___x_269_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___lam__0(v_a_257_, v_b_224_, v_relLeanFile_219_, v___x_268_, v___y_225_);
v___y_244_ = v_it_250_;
v___y_245_ = v___x_269_;
goto v___jp_243_;
}
}
else
{
lean_dec_ref(v___x_256_);
v___y_235_ = v___x_253_;
v___y_236_ = v_it_250_;
goto v___jp_234_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_relLeanFile_219_ = stack[0].m_obj;
lean_object* v___x_220_ = stack[1].m_obj;
lean_object* v___x_221_ = stack[2].m_obj;
lean_object* v___x_222_ = stack[3].m_obj;
lean_object* v_a_223_ = stack[4].m_obj;
lean_object* v_b_224_ = stack[5].m_obj;
lean_object* v___y_225_ = stack[6].m_obj;
lean_object* v_res_296_;
v_res_296_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(v_relLeanFile_219_, v___x_220_, v___x_221_, v___x_222_, v_a_223_, v_b_224_, v___y_225_);
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___boxed(lean_object* v_relLeanFile_297_, lean_object* v___x_298_, lean_object* v___x_299_, lean_object* v___x_300_, lean_object* v_a_301_, lean_object* v_b_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(v_relLeanFile_297_, v___x_298_, v___x_299_, v___x_300_, v_a_301_, v_b_302_, v___y_303_);
lean_dec_ref(v___x_299_);
lean_dec_ref(v___x_298_);
return v_res_305_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__1(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = ((lean_object*)(l_Lake_compileLeanModule___closed__0));
v___x_308_ = lean_unsigned_to_nat(2u);
v___x_309_ = lean_mk_empty_array_with_capacity(v___x_308_);
v___x_310_ = lean_array_push(v___x_309_, v___x_307_);
return v___x_310_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__7(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_316_ = ((lean_object*)(l_Lake_compileLeanModule___closed__6));
v___x_317_ = lean_unsigned_to_nat(2u);
v___x_318_ = lean_mk_empty_array_with_capacity(v___x_317_);
v___x_319_ = lean_array_push(v___x_318_, v___x_316_);
return v___x_319_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__9(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_321_ = ((lean_object*)(l_Lake_compileLeanModule___closed__8));
v___x_322_ = lean_unsigned_to_nat(2u);
v___x_323_ = lean_mk_empty_array_with_capacity(v___x_322_);
v___x_324_ = lean_array_push(v___x_323_, v___x_321_);
return v___x_324_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__11(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_326_ = ((lean_object*)(l_Lake_compileLeanModule___closed__10));
v___x_327_ = lean_unsigned_to_nat(2u);
v___x_328_ = lean_mk_empty_array_with_capacity(v___x_327_);
v___x_329_ = lean_array_push(v___x_328_, v___x_326_);
return v___x_329_;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__13(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_331_ = ((lean_object*)(l_Lake_compileLeanModule___closed__12));
v___x_332_ = lean_unsigned_to_nat(2u);
v___x_333_ = lean_mk_empty_array_with_capacity(v___x_332_);
v___x_334_ = lean_array_push(v___x_333_, v___x_331_);
return v___x_334_;
}
}
lean_object* l_Lake_compileLeanModule(lean_object* v_leanFile_335_, lean_object* v_relLeanFile_336_, lean_object* v_setup_337_, lean_object* v_setupFile_338_, lean_object* v_arts_339_, lean_object* v_leanArgs_340_, lean_object* v_leanPath_341_, lean_object* v_lean_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___y_346_; lean_object* v_a_347_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v_args_354_; lean_object* v___y_355_; lean_object* v_olean_x3f_443_; lean_object* v_ilean_x3f_444_; lean_object* v_c_x3f_445_; lean_object* v_bc_x3f_446_; lean_object* v_args_448_; lean_object* v___y_449_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v_args_478_; lean_object* v___y_479_; lean_object* v_args_486_; lean_object* v___y_487_; lean_object* v_args_500_; 
v_olean_x3f_443_ = lean_ctor_get(v_arts_339_, 1);
lean_inc(v_olean_x3f_443_);
v_ilean_x3f_444_ = lean_ctor_get(v_arts_339_, 4);
lean_inc(v_ilean_x3f_444_);
v_c_x3f_445_ = lean_ctor_get(v_arts_339_, 7);
lean_inc(v_c_x3f_445_);
v_bc_x3f_446_ = lean_ctor_get(v_arts_339_, 8);
lean_inc(v_bc_x3f_446_);
lean_dec_ref(v_arts_339_);
v_args_500_ = lean_array_push(v_leanArgs_340_, v_leanFile_335_);
if (lean_obj_tag(v_olean_x3f_443_) == 1)
{
lean_object* v_val_501_; lean_object* v___x_502_; 
v_val_501_ = lean_ctor_get(v_olean_x3f_443_, 0);
lean_inc_n(v_val_501_, 2);
lean_dec_ref_known(v_olean_x3f_443_, 1);
v___x_502_ = l_Lake_createParentDirs(v_val_501_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec_ref_known(v___x_502_, 1);
v___x_503_ = lean_obj_once(&l_Lake_compileLeanModule___closed__13, &l_Lake_compileLeanModule___closed__13_once, _init_l_Lake_compileLeanModule___closed__13);
v___x_504_ = lean_array_push(v___x_503_, v_val_501_);
v___x_505_ = l_Array_append___redArg(v_args_500_, v___x_504_);
lean_dec_ref(v___x_504_);
v_args_486_ = v___x_505_;
v___y_487_ = v_a_343_;
goto v___jp_485_;
}
else
{
lean_object* v_a_506_; lean_object* v___x_507_; uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_val_501_);
lean_dec_ref(v_args_500_);
lean_dec(v_bc_x3f_446_);
lean_dec(v_c_x3f_445_);
lean_dec(v_ilean_x3f_444_);
lean_dec_ref(v_lean_342_);
lean_dec(v_leanPath_341_);
lean_dec_ref(v_setupFile_338_);
lean_dec_ref(v_setup_337_);
lean_dec_ref(v_relLeanFile_336_);
v_a_506_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_502_, 1);
v___x_507_ = lean_io_error_to_string(v_a_506_);
v___x_508_ = 3;
v___x_509_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*1, v___x_508_);
v___x_510_ = lean_array_get_size(v_a_343_);
v___x_511_ = lean_array_push(v_a_343_, v___x_509_);
v___x_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
return v___x_512_;
}
}
else
{
lean_dec(v_olean_x3f_443_);
v_args_486_ = v_args_500_;
v___y_487_ = v_a_343_;
goto v___jp_485_;
}
v___jp_345_:
{
lean_object* v___x_348_; 
v___x_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_348_, 0, v___y_346_);
lean_ctor_set(v___x_348_, 1, v_a_347_);
return v___x_348_;
}
v___jp_349_:
{
if (lean_obj_tag(v___y_351_) == 0)
{
lean_dec(v___y_350_);
return v___y_351_;
}
else
{
lean_object* v_a_352_; 
v_a_352_ = lean_ctor_get(v___y_351_, 1);
lean_inc(v_a_352_);
lean_dec_ref_known(v___y_351_, 2);
v___y_346_ = v___y_350_;
v_a_347_ = v_a_352_;
goto v___jp_345_;
}
}
v___jp_353_:
{
lean_object* v___x_356_; 
lean_inc_ref(v_setupFile_338_);
v___x_356_ = l_Lake_createParentDirs(v_setupFile_338_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec_ref_known(v___x_356_, 1);
v___x_357_ = l_Lean_instToJsonModuleSetup_toJson(v_setup_337_);
v___x_358_ = lean_unsigned_to_nat(80u);
v___x_359_ = l_Lean_Json_pretty(v___x_357_, v___x_358_);
v___x_360_ = l_IO_FS_writeFile(v_setupFile_338_, v___x_359_);
lean_dec_ref(v___x_359_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_427_; 
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; 
v_unused_428_ = lean_ctor_get(v___x_360_, 0);
lean_dec(v_unused_428_);
v___x_362_ = v___x_360_;
v_isShared_363_ = v_isSharedCheck_427_;
goto v_resetjp_361_;
}
else
{
lean_dec(v___x_360_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_427_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_364_ = lean_obj_once(&l_Lake_compileLeanModule___closed__1, &l_Lake_compileLeanModule___closed__1_once, _init_l_Lake_compileLeanModule___closed__1);
v___x_365_ = lean_array_push(v___x_364_, v_setupFile_338_);
v___x_366_ = l_Array_append___redArg(v_args_354_, v___x_365_);
lean_dec_ref(v___x_365_);
v___x_367_ = ((lean_object*)(l_Lake_compileLeanModule___closed__2));
v___x_368_ = lean_array_push(v___x_366_, v___x_367_);
v___x_369_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_370_ = lean_box(0);
v___x_371_ = ((lean_object*)(l_Lake_compileLeanIR___closed__1));
v___x_372_ = l_System_SearchPath_toString(v_leanPath_341_);
if (v_isShared_363_ == 0)
{
lean_ctor_set_tag(v___x_362_, 1);
lean_ctor_set(v___x_362_, 0, v___x_372_);
v___x_374_ = v___x_362_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_426_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_371_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_mk_empty_array_with_capacity(v___x_376_);
v___x_378_ = lean_array_push(v___x_377_, v___x_375_);
v___x_379_ = 1;
v___x_380_ = 0;
lean_inc_ref(v_lean_342_);
v___x_381_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_381_, 0, v___x_369_);
lean_ctor_set(v___x_381_, 1, v_lean_342_);
lean_ctor_set(v___x_381_, 2, v___x_368_);
lean_ctor_set(v___x_381_, 3, v___x_370_);
lean_ctor_set(v___x_381_, 4, v___x_378_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*5, v___x_379_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*5 + 1, v___x_380_);
v___x_382_ = lean_array_get_size(v___y_355_);
lean_inc_ref(v___x_381_);
v___x_383_ = l_Lake_mkCmdLog(v___x_381_);
v___x_384_ = 0;
v___x_385_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*1, v___x_384_);
v___x_386_ = lean_array_push(v___y_355_, v___x_385_);
v___x_387_ = l_IO_Process_output(v___x_381_, v___x_370_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; uint32_t v_exitCode_389_; lean_object* v_stdout_390_; lean_object* v_stderr_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
lean_dec_ref(v_lean_342_);
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_387_, 1);
v_exitCode_389_ = lean_ctor_get_uint32(v_a_388_, sizeof(void*)*2);
v_stdout_390_ = lean_ctor_get(v_a_388_, 0);
lean_inc_ref(v_stdout_390_);
v_stderr_391_ = lean_ctor_get(v_a_388_, 1);
lean_inc_ref(v_stderr_391_);
lean_dec(v_a_388_);
v___x_392_ = lean_array_get_size(v___x_386_);
v___x_393_ = lean_string_utf8_byte_size(v_stdout_390_);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_nat_dec_eq(v___x_393_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_inc_ref(v_stdout_390_);
v___x_396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_396_, 0, v_stdout_390_);
lean_ctor_set(v___x_396_, 1, v___x_394_);
lean_ctor_set(v___x_396_, 2, v___x_393_);
v___x_397_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_398_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__1___closed__0);
v___x_399_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(v_relLeanFile_336_, v_stdout_390_, v___x_396_, v___x_393_, v___x_398_, v___x_397_, v___x_386_);
lean_dec_ref_known(v___x_396_, 3);
lean_dec_ref(v_stdout_390_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v_a_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
v_a_401_ = lean_ctor_get(v___x_399_, 1);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_399_, 2);
v___x_402_ = lean_string_utf8_byte_size(v_a_400_);
v___x_403_ = lean_nat_dec_eq(v___x_402_, v___x_394_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_404_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg___closed__1));
v___x_405_ = lean_string_append(v___x_404_, v_a_400_);
lean_dec(v_a_400_);
v___x_406_ = 1;
v___x_407_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*1, v___x_406_);
v___x_408_ = lean_box(0);
v___x_409_ = lean_array_push(v_a_401_, v___x_407_);
v___x_410_ = l_Lake_compileLeanModule___lam__0(v_exitCode_389_, v___x_392_, v_stderr_391_, v___x_408_, v___x_409_);
v___y_350_ = v___x_382_;
v___y_351_ = v___x_410_;
goto v___jp_349_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec(v_a_400_);
v___x_411_ = lean_box(0);
v___x_412_ = l_Lake_compileLeanModule___lam__0(v_exitCode_389_, v___x_392_, v_stderr_391_, v___x_411_, v_a_401_);
v___y_350_ = v___x_382_;
v___y_351_ = v___x_412_;
goto v___jp_349_;
}
}
else
{
lean_object* v_a_413_; 
lean_dec_ref(v_stderr_391_);
v_a_413_ = lean_ctor_get(v___x_399_, 1);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_399_, 2);
v___y_346_ = v___x_382_;
v_a_347_ = v_a_413_;
goto v___jp_345_;
}
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref(v_stdout_390_);
lean_dec_ref(v_relLeanFile_336_);
v___x_414_ = lean_box(0);
v___x_415_ = l_Lake_compileLeanModule___lam__0(v_exitCode_389_, v___x_392_, v_stderr_391_, v___x_414_, v___x_386_);
v___y_350_ = v___x_382_;
v___y_351_ = v___x_415_;
goto v___jp_349_;
}
}
else
{
lean_object* v_a_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec_ref(v_relLeanFile_336_);
v_a_416_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_416_);
lean_dec_ref_known(v___x_387_, 1);
v___x_417_ = ((lean_object*)(l_Lake_compileLeanModule___closed__4));
v___x_418_ = lean_string_append(v___x_417_, v_lean_342_);
lean_dec_ref(v_lean_342_);
v___x_419_ = ((lean_object*)(l_Lake_compileLeanModule___closed__5));
v___x_420_ = lean_string_append(v___x_418_, v___x_419_);
v___x_421_ = lean_io_error_to_string(v_a_416_);
v___x_422_ = lean_string_append(v___x_420_, v___x_421_);
lean_dec_ref(v___x_421_);
v___x_423_ = 3;
v___x_424_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set_uint8(v___x_424_, sizeof(void*)*1, v___x_423_);
v___x_425_ = lean_array_push(v___x_386_, v___x_424_);
v___y_346_ = v___x_382_;
v_a_347_ = v___x_425_;
goto v___jp_345_;
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_430_; uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref(v_args_354_);
lean_dec_ref(v_lean_342_);
lean_dec(v_leanPath_341_);
lean_dec_ref(v_setupFile_338_);
lean_dec_ref(v_relLeanFile_336_);
v_a_429_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_360_, 1);
v___x_430_ = lean_io_error_to_string(v_a_429_);
v___x_431_ = 3;
v___x_432_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*1, v___x_431_);
v___x_433_ = lean_array_get_size(v___y_355_);
v___x_434_ = lean_array_push(v___y_355_, v___x_432_);
v___x_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
return v___x_435_;
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_437_; uint8_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec_ref(v_args_354_);
lean_dec_ref(v_lean_342_);
lean_dec(v_leanPath_341_);
lean_dec_ref(v_setupFile_338_);
lean_dec_ref(v_setup_337_);
lean_dec_ref(v_relLeanFile_336_);
v_a_436_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_356_, 1);
v___x_437_ = lean_io_error_to_string(v_a_436_);
v___x_438_ = 3;
v___x_439_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set_uint8(v___x_439_, sizeof(void*)*1, v___x_438_);
v___x_440_ = lean_array_get_size(v___y_355_);
v___x_441_ = lean_array_push(v___y_355_, v___x_439_);
v___x_442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
return v___x_442_;
}
}
v___jp_447_:
{
if (lean_obj_tag(v_bc_x3f_446_) == 1)
{
lean_object* v_val_450_; lean_object* v___x_451_; 
v_val_450_ = lean_ctor_get(v_bc_x3f_446_, 0);
lean_inc_n(v_val_450_, 2);
lean_dec_ref_known(v_bc_x3f_446_, 1);
v___x_451_ = l_Lake_createParentDirs(v_val_450_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec_ref_known(v___x_451_, 1);
v___x_452_ = lean_obj_once(&l_Lake_compileLeanModule___closed__7, &l_Lake_compileLeanModule___closed__7_once, _init_l_Lake_compileLeanModule___closed__7);
v___x_453_ = lean_array_push(v___x_452_, v_val_450_);
v___x_454_ = l_Array_append___redArg(v_args_448_, v___x_453_);
lean_dec_ref(v___x_453_);
v_args_354_ = v___x_454_;
v___y_355_ = v___y_449_;
goto v___jp_353_;
}
else
{
lean_object* v_a_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec(v_val_450_);
lean_dec_ref(v_args_448_);
lean_dec_ref(v_lean_342_);
lean_dec(v_leanPath_341_);
lean_dec_ref(v_setupFile_338_);
lean_dec_ref(v_setup_337_);
lean_dec_ref(v_relLeanFile_336_);
v_a_455_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_451_, 1);
v___x_456_ = lean_io_error_to_string(v_a_455_);
v___x_457_ = 3;
v___x_458_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1, v___x_457_);
v___x_459_ = lean_array_get_size(v___y_449_);
v___x_460_ = lean_array_push(v___y_449_, v___x_458_);
v___x_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
return v___x_461_;
}
}
else
{
lean_dec(v_bc_x3f_446_);
v_args_354_ = v_args_448_;
v___y_355_ = v___y_449_;
goto v___jp_353_;
}
}
v___jp_462_:
{
if (lean_obj_tag(v_c_x3f_445_) == 1)
{
lean_object* v_val_465_; lean_object* v___x_466_; 
v_val_465_ = lean_ctor_get(v_c_x3f_445_, 0);
lean_inc_n(v_val_465_, 2);
lean_dec_ref_known(v_c_x3f_445_, 1);
v___x_466_ = l_Lake_createParentDirs(v_val_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref_known(v___x_466_, 1);
v___x_467_ = lean_obj_once(&l_Lake_compileLeanModule___closed__9, &l_Lake_compileLeanModule___closed__9_once, _init_l_Lake_compileLeanModule___closed__9);
v___x_468_ = lean_array_push(v___x_467_, v_val_465_);
v___x_469_ = l_Array_append___redArg(v___y_464_, v___x_468_);
lean_dec_ref(v___x_468_);
v_args_448_ = v___x_469_;
v___y_449_ = v___y_463_;
goto v___jp_447_;
}
else
{
lean_object* v_a_470_; lean_object* v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_val_465_);
lean_dec_ref(v___y_464_);
lean_dec(v_bc_x3f_446_);
lean_dec_ref(v_lean_342_);
lean_dec(v_leanPath_341_);
lean_dec_ref(v_setupFile_338_);
lean_dec_ref(v_setup_337_);
lean_dec_ref(v_relLeanFile_336_);
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
lean_dec(v_c_x3f_445_);
v_args_448_ = v___y_464_;
v___y_449_ = v___y_463_;
goto v___jp_447_;
}
}
v___jp_477_:
{
uint8_t v_isModule_480_; 
v_isModule_480_ = lean_ctor_get_uint8(v_setup_337_, sizeof(void*)*7);
if (v_isModule_480_ == 0)
{
v___y_463_ = v___y_479_;
v___y_464_ = v_args_478_;
goto v___jp_462_;
}
else
{
lean_object* v_options_481_; lean_object* v_opts_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_options_481_ = lean_ctor_get(v_setup_337_, 6);
lean_inc(v_options_481_);
v_opts_482_ = l_Lean_LeanOptions_toOptions(v_options_481_);
v___x_483_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_484_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__3(v_opts_482_, v___x_483_);
lean_dec_ref(v_opts_482_);
if (v___x_484_ == 0)
{
v___y_463_ = v___y_479_;
v___y_464_ = v_args_478_;
goto v___jp_462_;
}
else
{
lean_dec(v_c_x3f_445_);
v_args_448_ = v_args_478_;
v___y_449_ = v___y_479_;
goto v___jp_447_;
}
}
}
v___jp_485_:
{
if (lean_obj_tag(v_ilean_x3f_444_) == 1)
{
lean_object* v_val_488_; lean_object* v___x_489_; 
v_val_488_ = lean_ctor_get(v_ilean_x3f_444_, 0);
lean_inc_n(v_val_488_, 2);
lean_dec_ref_known(v_ilean_x3f_444_, 1);
v___x_489_ = l_Lake_createParentDirs(v_val_488_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec_ref_known(v___x_489_, 1);
v___x_490_ = lean_obj_once(&l_Lake_compileLeanModule___closed__11, &l_Lake_compileLeanModule___closed__11_once, _init_l_Lake_compileLeanModule___closed__11);
v___x_491_ = lean_array_push(v___x_490_, v_val_488_);
v___x_492_ = l_Array_append___redArg(v_args_486_, v___x_491_);
lean_dec_ref(v___x_491_);
v_args_478_ = v___x_492_;
v___y_479_ = v___y_487_;
goto v___jp_477_;
}
else
{
lean_object* v_a_493_; lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v_val_488_);
lean_dec_ref(v_args_486_);
lean_dec(v_bc_x3f_446_);
lean_dec(v_c_x3f_445_);
lean_dec_ref(v_lean_342_);
lean_dec(v_leanPath_341_);
lean_dec_ref(v_setupFile_338_);
lean_dec_ref(v_setup_337_);
lean_dec_ref(v_relLeanFile_336_);
v_a_493_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_493_);
lean_dec_ref_known(v___x_489_, 1);
v___x_494_ = lean_io_error_to_string(v_a_493_);
v___x_495_ = 3;
v___x_496_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*1, v___x_495_);
v___x_497_ = lean_array_get_size(v___y_487_);
v___x_498_ = lean_array_push(v___y_487_, v___x_496_);
v___x_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
return v___x_499_;
}
}
else
{
lean_dec(v_ilean_x3f_444_);
v_args_478_ = v_args_486_;
v___y_479_ = v___y_487_;
goto v___jp_477_;
}
}
}
}
LEAN_EXPORT void l_Lake_compileLeanModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_leanFile_335_ = stack[0].m_obj;
lean_object* v_relLeanFile_336_ = stack[1].m_obj;
lean_object* v_setup_337_ = stack[2].m_obj;
lean_object* v_setupFile_338_ = stack[3].m_obj;
lean_object* v_arts_339_ = stack[4].m_obj;
lean_object* v_leanArgs_340_ = stack[5].m_obj;
lean_object* v_leanPath_341_ = stack[6].m_obj;
lean_object* v_lean_342_ = stack[7].m_obj;
lean_object* v_a_343_ = stack[8].m_obj;
lean_object* v_res_513_;
v_res_513_ = l_Lake_compileLeanModule(v_leanFile_335_, v_relLeanFile_336_, v_setup_337_, v_setupFile_338_, v_arts_339_, v_leanArgs_340_, v_leanPath_341_, v_lean_342_, v_a_343_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object* v_leanFile_514_, lean_object* v_relLeanFile_515_, lean_object* v_setup_516_, lean_object* v_setupFile_517_, lean_object* v_arts_518_, lean_object* v_leanArgs_519_, lean_object* v_leanPath_520_, lean_object* v_lean_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lake_compileLeanModule(v_leanFile_514_, v_relLeanFile_515_, v_setup_516_, v_setupFile_517_, v_arts_518_, v_leanArgs_519_, v_leanPath_520_, v_lean_521_, v_a_522_);
return v_res_524_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2(lean_object* v_relLeanFile_525_, lean_object* v___x_526_, lean_object* v___x_527_, lean_object* v___x_528_, lean_object* v_inst_529_, lean_object* v_R_530_, lean_object* v_a_531_, lean_object* v_b_532_, lean_object* v_c_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___redArg(v_relLeanFile_525_, v___x_526_, v___x_527_, v___x_528_, v_a_531_, v_b_532_, v___y_534_);
return v___x_536_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_relLeanFile_525_ = stack[0].m_obj;
lean_object* v___x_526_ = stack[1].m_obj;
lean_object* v___x_527_ = stack[2].m_obj;
lean_object* v___x_528_ = stack[3].m_obj;
lean_object* v_a_531_ = stack[6].m_obj;
lean_object* v_b_532_ = stack[7].m_obj;
lean_object* v___y_534_ = stack[9].m_obj;
lean_object* v_res_537_;
v_res_537_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2(v_relLeanFile_525_, v___x_526_, v___x_527_, v___x_528_, lean_box(0), lean_box(0), v_a_531_, v_b_532_, lean_box(0), v___y_534_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2___boxed(lean_object* v_relLeanFile_538_, lean_object* v___x_539_, lean_object* v___x_540_, lean_object* v___x_541_, lean_object* v_inst_542_, lean_object* v_R_543_, lean_object* v_a_544_, lean_object* v_b_545_, lean_object* v_c_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__2(v_relLeanFile_538_, v___x_539_, v___x_540_, v___x_541_, v_inst_542_, v_R_543_, v_a_544_, v_b_545_, v_c_546_, v___y_547_);
lean_dec_ref(v___x_540_);
lean_dec_ref(v___x_539_);
return v_res_549_;
}
}
static lean_object* _init_l_Lake_compileO___closed__0(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_550_ = ((lean_object*)(l_Lake_compileLeanModule___closed__8));
v___x_551_ = lean_unsigned_to_nat(4u);
v___x_552_ = lean_mk_empty_array_with_capacity(v___x_551_);
v___x_553_ = lean_array_push(v___x_552_, v___x_550_);
return v___x_553_;
}
}
static lean_object* _init_l_Lake_compileO___closed__1(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = ((lean_object*)(l_Lake_compileLeanModule___closed__12));
v___x_555_ = lean_obj_once(&l_Lake_compileO___closed__0, &l_Lake_compileO___closed__0_once, _init_l_Lake_compileO___closed__0);
v___x_556_ = lean_array_push(v___x_555_, v___x_554_);
return v___x_556_;
}
}
lean_object* l_Lake_compileO(lean_object* v_oFile_559_, lean_object* v_srcFile_560_, lean_object* v_moreArgs_561_, lean_object* v_compiler_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___x_565_; 
lean_inc_ref(v_oFile_559_);
v___x_565_ = l_Lake_createParentDirs(v_oFile_559_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec_ref_known(v___x_565_, 1);
v___x_566_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_567_ = lean_obj_once(&l_Lake_compileO___closed__1, &l_Lake_compileO___closed__1_once, _init_l_Lake_compileO___closed__1);
v___x_568_ = lean_array_push(v___x_567_, v_oFile_559_);
v___x_569_ = lean_array_push(v___x_568_, v_srcFile_560_);
v___x_570_ = l_Array_append___redArg(v___x_569_, v_moreArgs_561_);
v___x_571_ = lean_box(0);
v___x_572_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_573_ = 1;
v___x_574_ = 0;
v___x_575_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_575_, 0, v___x_566_);
lean_ctor_set(v___x_575_, 1, v_compiler_562_);
lean_ctor_set(v___x_575_, 2, v___x_570_);
lean_ctor_set(v___x_575_, 3, v___x_571_);
lean_ctor_set(v___x_575_, 4, v___x_572_);
lean_ctor_set_uint8(v___x_575_, sizeof(void*)*5, v___x_573_);
lean_ctor_set_uint8(v___x_575_, sizeof(void*)*5 + 1, v___x_574_);
v___x_576_ = l_Lake_proc(v___x_575_, v___x_574_, v___x_571_, v_a_563_);
return v___x_576_;
}
else
{
lean_object* v_a_577_; lean_object* v___x_578_; uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec_ref(v_compiler_562_);
lean_dec_ref(v_srcFile_560_);
lean_dec_ref(v_oFile_559_);
v_a_577_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_565_, 1);
v___x_578_ = lean_io_error_to_string(v_a_577_);
v___x_579_ = 3;
v___x_580_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set_uint8(v___x_580_, sizeof(void*)*1, v___x_579_);
v___x_581_ = lean_array_get_size(v_a_563_);
v___x_582_ = lean_array_push(v_a_563_, v___x_580_);
v___x_583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
return v___x_583_;
}
}
}
LEAN_EXPORT void l_Lake_compileO_0interp(lean_interpreter_value* stack)
{
lean_object* v_oFile_559_ = stack[0].m_obj;
lean_object* v_srcFile_560_ = stack[1].m_obj;
lean_object* v_moreArgs_561_ = stack[2].m_obj;
lean_object* v_compiler_562_ = stack[3].m_obj;
lean_object* v_a_563_ = stack[4].m_obj;
lean_object* v_res_584_;
v_res_584_ = l_Lake_compileO(v_oFile_559_, v_srcFile_560_, v_moreArgs_561_, v_compiler_562_, v_a_563_);
stack->m_obj
 = v_res_584_;
}
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object* v_oFile_585_, lean_object* v_srcFile_586_, lean_object* v_moreArgs_587_, lean_object* v_compiler_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lake_compileO(v_oFile_585_, v_srcFile_586_, v_moreArgs_587_, v_compiler_588_, v_a_589_);
lean_dec_ref(v_moreArgs_587_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(lean_object* v___x_592_, lean_object* v___y_593_, lean_object* v_a_594_, lean_object* v_b_595_){
_start:
{
uint8_t v_decide_596_; 
v_decide_596_ = lean_nat_dec_eq(v_a_594_, v___x_592_);
if (v_decide_596_ == 0)
{
uint32_t v___x_597_; lean_object* v___x_598_; uint32_t v___x_599_; uint8_t v___x_604_; 
v___x_597_ = lean_string_utf8_get_fast(v___y_593_, v_a_594_);
v___x_598_ = lean_string_utf8_next_fast(v___y_593_, v_a_594_);
lean_dec(v_a_594_);
v___x_599_ = 92;
v___x_604_ = lean_uint32_dec_eq(v___x_597_, v___x_599_);
if (v___x_604_ == 0)
{
uint32_t v___x_605_; uint8_t v___x_606_; 
v___x_605_ = 34;
v___x_606_ = lean_uint32_dec_eq(v___x_597_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
v___x_607_ = lean_string_push(v_b_595_, v___x_597_);
v_a_594_ = v___x_598_;
v_b_595_ = v___x_607_;
goto _start;
}
else
{
goto v___jp_600_;
}
}
else
{
goto v___jp_600_;
}
v___jp_600_:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_string_push(v_b_595_, v___x_599_);
v___x_602_ = lean_string_push(v___x_601_, v___x_597_);
v_a_594_ = v___x_598_;
v_b_595_ = v___x_602_;
goto _start;
}
}
else
{
lean_dec(v_a_594_);
return v_b_595_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg___boxed(lean_object* v___x_609_, lean_object* v___y_610_, lean_object* v_a_611_, lean_object* v_b_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_609_, v___y_610_, v_a_611_, v_b_612_);
lean_dec_ref(v___y_610_);
lean_dec(v___x_609_);
return v_res_613_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(lean_object* v_a_616_, lean_object* v_as_617_, size_t v_i_618_, size_t v_stop_619_, lean_object* v_b_620_, lean_object* v___y_621_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_eq(v_i_618_, v_stop_619_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_624_ = lean_array_uget_borrowed(v_as_617_, v_i_618_);
v___x_625_ = ((lean_object*)(l_Lake_compileLeanModule___closed__3));
v___x_626_ = lean_string_utf8_byte_size(v___x_624_);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_626_, v___x_624_, v___x_627_, v___x_625_);
v___x_629_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0));
v___x_630_ = lean_string_append(v___x_629_, v___x_628_);
lean_dec_ref(v___x_628_);
v___x_631_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1));
v___x_632_ = lean_string_append(v___x_630_, v___x_631_);
v___x_633_ = lean_io_prim_handle_put_str(v_a_616_, v___x_632_);
lean_dec_ref(v___x_632_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; size_t v___x_635_; size_t v___x_636_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = ((size_t)1ULL);
v___x_636_ = lean_usize_add(v_i_618_, v___x_635_);
v_i_618_ = v___x_636_;
v_b_620_ = v_a_634_;
goto _start;
}
else
{
lean_object* v_a_638_; lean_object* v___x_639_; uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_a_638_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_633_, 1);
v___x_639_ = lean_io_error_to_string(v_a_638_);
v___x_640_ = 3;
v___x_641_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*1, v___x_640_);
v___x_642_ = lean_array_get_size(v___y_621_);
v___x_643_ = lean_array_push(v___y_621_, v___x_641_);
v___x_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
return v___x_644_;
}
}
else
{
lean_object* v___x_645_; 
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v_b_620_);
lean_ctor_set(v___x_645_, 1, v___y_621_);
return v___x_645_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_616_ = stack[0].m_obj;
lean_object* v_as_617_ = stack[1].m_obj;
size_t v_i_618_ = stack[2].m_num;
size_t v_stop_619_ = stack[3].m_num;
lean_object* v_b_620_ = stack[4].m_obj;
lean_object* v___y_621_ = stack[5].m_obj;
lean_object* v_res_646_;
v_res_646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_616_, v_as_617_, v_i_618_, v_stop_619_, v_b_620_, v___y_621_);
stack->m_obj
 = v_res_646_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___boxed(lean_object* v_a_647_, lean_object* v_as_648_, lean_object* v_i_649_, lean_object* v_stop_650_, lean_object* v_b_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
size_t v_i_boxed_654_; size_t v_stop_boxed_655_; lean_object* v_res_656_; 
v_i_boxed_654_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_stop_boxed_655_ = lean_unbox_usize(v_stop_650_);
lean_dec(v_stop_650_);
v_res_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_647_, v_as_648_, v_i_boxed_654_, v_stop_boxed_655_, v_b_651_, v___y_652_);
lean_dec_ref(v_as_648_);
lean_dec(v_a_647_);
return v_res_656_;
}
}
lean_object* l_Lake_mkArgs(lean_object* v_basePath_659_, lean_object* v_args_660_, lean_object* v_a_661_){
_start:
{
lean_object* v___x_663_; lean_object* v_rspFile_664_; lean_object* v_a_666_; lean_object* v___y_674_; uint8_t v___x_685_; lean_object* v___x_686_; 
v___x_663_ = ((lean_object*)(l_Lake_mkArgs___closed__0));
v_rspFile_664_ = l_System_FilePath_addExtension(v_basePath_659_, v___x_663_);
v___x_685_ = 1;
v___x_686_ = lean_io_prim_handle_mk(v_rspFile_664_, v___x_685_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_array_get_size(v_args_660_);
v___x_690_ = lean_nat_dec_lt(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_dec(v_a_687_);
v_a_666_ = v_a_661_;
goto v___jp_665_;
}
else
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_box(0);
v___x_692_ = lean_nat_dec_le(v___x_689_, v___x_689_);
if (v___x_692_ == 0)
{
if (v___x_690_ == 0)
{
lean_dec(v_a_687_);
v_a_666_ = v_a_661_;
goto v___jp_665_;
}
else
{
size_t v___x_693_; size_t v___x_694_; lean_object* v___x_695_; 
v___x_693_ = ((size_t)0ULL);
v___x_694_ = lean_usize_of_nat(v___x_689_);
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_687_, v_args_660_, v___x_693_, v___x_694_, v___x_691_, v_a_661_);
lean_dec(v_a_687_);
v___y_674_ = v___x_695_;
goto v___jp_673_;
}
}
else
{
size_t v___x_696_; size_t v___x_697_; lean_object* v___x_698_; 
v___x_696_ = ((size_t)0ULL);
v___x_697_ = lean_usize_of_nat(v___x_689_);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_687_, v_args_660_, v___x_696_, v___x_697_, v___x_691_, v_a_661_);
lean_dec(v_a_687_);
v___y_674_ = v___x_698_;
goto v___jp_673_;
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_700_; uint8_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
lean_dec_ref(v_rspFile_664_);
v_a_699_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_686_, 1);
v___x_700_ = lean_io_error_to_string(v_a_699_);
v___x_701_ = 3;
v___x_702_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*1, v___x_701_);
v___x_703_ = lean_array_get_size(v_a_661_);
v___x_704_ = lean_array_push(v_a_661_, v___x_702_);
v___x_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
return v___x_705_;
}
v___jp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_667_ = ((lean_object*)(l_Lake_mkArgs___closed__1));
v___x_668_ = lean_string_append(v___x_667_, v_rspFile_664_);
lean_dec_ref(v_rspFile_664_);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_mk_empty_array_with_capacity(v___x_669_);
v___x_671_ = lean_array_push(v___x_670_, v___x_668_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v_a_666_);
return v___x_672_;
}
v___jp_673_:
{
if (lean_obj_tag(v___y_674_) == 0)
{
lean_object* v_a_675_; 
v_a_675_ = lean_ctor_get(v___y_674_, 1);
lean_inc(v_a_675_);
lean_dec_ref_known(v___y_674_, 2);
v_a_666_ = v_a_675_;
goto v___jp_665_;
}
else
{
lean_object* v_a_676_; lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v_rspFile_664_);
v_a_676_ = lean_ctor_get(v___y_674_, 0);
v_a_677_ = lean_ctor_get(v___y_674_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v___y_674_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___y_674_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_inc(v_a_676_);
lean_dec(v___y_674_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_676_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_mkArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_basePath_659_ = stack[0].m_obj;
lean_object* v_args_660_ = stack[1].m_obj;
lean_object* v_a_661_ = stack[2].m_obj;
lean_object* v_res_706_;
v_res_706_ = l_Lake_mkArgs(v_basePath_659_, v_args_660_, v_a_661_);
stack->m_obj
 = v_res_706_;
}
LEAN_EXPORT lean_object* l_Lake_mkArgs___boxed(lean_object* v_basePath_707_, lean_object* v_args_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lake_mkArgs(v_basePath_707_, v_args_708_, v_a_709_);
lean_dec_ref(v_args_708_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(lean_object* v___x_712_, lean_object* v___x_713_, lean_object* v___y_714_, lean_object* v_inst_715_, lean_object* v_R_716_, lean_object* v_a_717_, lean_object* v_b_718_, lean_object* v_c_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(v___x_713_, v___y_714_, v_a_717_, v_b_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(lean_object* v___x_721_, lean_object* v___x_722_, lean_object* v___y_723_, lean_object* v_inst_724_, lean_object* v_R_725_, lean_object* v_a_726_, lean_object* v_b_727_, lean_object* v_c_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(v___x_721_, v___x_722_, v___y_723_, v_inst_724_, v_R_725_, v_a_726_, v_b_727_, v_c_728_);
lean_dec_ref(v___y_723_);
lean_dec(v___x_722_);
lean_dec_ref(v___x_721_);
return v_res_729_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(size_t v_sz_730_, size_t v_i_731_, lean_object* v_bs_732_){
_start:
{
uint8_t v___x_733_; 
v___x_733_ = lean_usize_dec_lt(v_i_731_, v_sz_730_);
if (v___x_733_ == 0)
{
return v_bs_732_;
}
else
{
lean_object* v_v_734_; lean_object* v___x_735_; lean_object* v_bs_x27_736_; size_t v___x_737_; size_t v___x_738_; lean_object* v___x_739_; 
v_v_734_ = lean_array_uget(v_bs_732_, v_i_731_);
v___x_735_ = lean_unsigned_to_nat(0u);
v_bs_x27_736_ = lean_array_uset(v_bs_732_, v_i_731_, v___x_735_);
v___x_737_ = ((size_t)1ULL);
v___x_738_ = lean_usize_add(v_i_731_, v___x_737_);
v___x_739_ = lean_array_uset(v_bs_x27_736_, v_i_731_, v_v_734_);
v_i_731_ = v___x_738_;
v_bs_732_ = v___x_739_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_730_ = stack[0].m_num;
size_t v_i_731_ = stack[1].m_num;
lean_object* v_bs_732_ = stack[2].m_obj;
lean_object* v_res_741_;
v_res_741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_730_, v_i_731_, v_bs_732_);
stack->m_obj
 = v_res_741_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0___boxed(lean_object* v_sz_742_, lean_object* v_i_743_, lean_object* v_bs_744_){
_start:
{
size_t v_sz_boxed_745_; size_t v_i_boxed_746_; lean_object* v_res_747_; 
v_sz_boxed_745_ = lean_unbox_usize(v_sz_742_);
lean_dec(v_sz_742_);
v_i_boxed_746_ = lean_unbox_usize(v_i_743_);
lean_dec(v_i_743_);
v_res_747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_boxed_745_, v_i_boxed_746_, v_bs_744_);
return v_res_747_;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__3(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = ((lean_object*)(l_Lake_compileStaticLib___closed__2));
v___x_755_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_756_ = lean_array_push(v___x_755_, v___x_754_);
return v___x_756_;
}
}
lean_object* l_Lake_compileStaticLib(lean_object* v_libFile_757_, lean_object* v_oFiles_758_, lean_object* v_ar_759_, uint8_t v_thin_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___x_763_; 
lean_inc_ref(v_libFile_757_);
v___x_763_ = l_Lake_createParentDirs(v_libFile_757_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v___x_764_; 
lean_dec_ref_known(v___x_763_, 1);
v___x_764_ = l_Lake_removeFileIfExists(v_libFile_757_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v___x_765_; uint8_t v___x_766_; lean_object* v___y_768_; 
lean_dec_ref_known(v___x_764_, 1);
v___x_765_ = ((lean_object*)(l_Lake_compileStaticLib___closed__1));
v___x_766_ = 1;
if (v_thin_760_ == 0)
{
v___y_768_ = v___x_765_;
goto v___jp_767_;
}
else
{
lean_object* v___x_792_; 
v___x_792_ = lean_obj_once(&l_Lake_compileStaticLib___closed__3, &l_Lake_compileStaticLib___closed__3_once, _init_l_Lake_compileStaticLib___closed__3);
v___y_768_ = v___x_792_;
goto v___jp_767_;
}
v___jp_767_:
{
size_t v_sz_769_; size_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_sz_769_ = lean_array_size(v_oFiles_758_);
v___x_770_ = ((size_t)0ULL);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_769_, v___x_770_, v_oFiles_758_);
lean_inc_ref(v_libFile_757_);
v___x_772_ = l_Lake_mkArgs(v_libFile_757_, v___x_771_, v_a_761_);
lean_dec_ref(v___x_771_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v_a_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
v_a_774_ = lean_ctor_get(v___x_772_, 1);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_772_, 2);
lean_inc_ref(v___y_768_);
v___x_775_ = lean_array_push(v___y_768_, v_libFile_757_);
v___x_776_ = l_Array_append___redArg(v___x_775_, v_a_773_);
lean_dec(v_a_773_);
v___x_777_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_778_ = lean_box(0);
v___x_779_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_780_ = 0;
v___x_781_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_781_, 0, v___x_777_);
lean_ctor_set(v___x_781_, 1, v_ar_759_);
lean_ctor_set(v___x_781_, 2, v___x_776_);
lean_ctor_set(v___x_781_, 3, v___x_778_);
lean_ctor_set(v___x_781_, 4, v___x_779_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*5, v___x_766_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*5 + 1, v___x_780_);
v___x_782_ = l_Lake_proc(v___x_781_, v___x_780_, v___x_778_, v_a_774_);
return v___x_782_;
}
else
{
lean_object* v_a_783_; lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v_ar_759_);
lean_dec_ref(v_libFile_757_);
v_a_783_ = lean_ctor_get(v___x_772_, 0);
v_a_784_ = lean_ctor_get(v___x_772_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_772_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_inc(v_a_783_);
lean_dec(v___x_772_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_783_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_794_; uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_ar_759_);
lean_dec_ref(v_oFiles_758_);
lean_dec_ref(v_libFile_757_);
v_a_793_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_764_, 1);
v___x_794_ = lean_io_error_to_string(v_a_793_);
v___x_795_ = 3;
v___x_796_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set_uint8(v___x_796_, sizeof(void*)*1, v___x_795_);
v___x_797_ = lean_array_get_size(v_a_761_);
v___x_798_ = lean_array_push(v_a_761_, v___x_796_);
v___x_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
return v___x_799_;
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_801_; uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref(v_ar_759_);
lean_dec_ref(v_oFiles_758_);
lean_dec_ref(v_libFile_757_);
v_a_800_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_763_, 1);
v___x_801_ = lean_io_error_to_string(v_a_800_);
v___x_802_ = 3;
v___x_803_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*1, v___x_802_);
v___x_804_ = lean_array_get_size(v_a_761_);
v___x_805_ = lean_array_push(v_a_761_, v___x_803_);
v___x_806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
return v___x_806_;
}
}
}
LEAN_EXPORT void l_Lake_compileStaticLib_0interp(lean_interpreter_value* stack)
{
lean_object* v_libFile_757_ = stack[0].m_obj;
lean_object* v_oFiles_758_ = stack[1].m_obj;
lean_object* v_ar_759_ = stack[2].m_obj;
uint8_t v_thin_760_ = stack[3].m_num;
lean_object* v_a_761_ = stack[4].m_obj;
lean_object* v_res_807_;
v_res_807_ = l_Lake_compileStaticLib(v_libFile_757_, v_oFiles_758_, v_ar_759_, v_thin_760_, v_a_761_);
stack->m_obj
 = v_res_807_;
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object* v_libFile_808_, lean_object* v_oFiles_809_, lean_object* v_ar_810_, lean_object* v_thin_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
uint8_t v_thin_boxed_814_; lean_object* v_res_815_; 
v_thin_boxed_814_ = lean_unbox(v_thin_811_);
v_res_815_ = l_Lake_compileStaticLib(v_libFile_808_, v_oFiles_809_, v_ar_810_, v_thin_boxed_814_, v_a_812_);
return v_res_815_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__1(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_817_ = ((lean_object*)(l_Lake_compileSharedLib___closed__0));
v___x_818_ = lean_unsigned_to_nat(3u);
v___x_819_ = lean_mk_empty_array_with_capacity(v___x_818_);
v___x_820_ = lean_array_push(v___x_819_, v___x_817_);
return v___x_820_;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__2(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = ((lean_object*)(l_Lake_compileLeanModule___closed__12));
v___x_822_ = lean_obj_once(&l_Lake_compileSharedLib___closed__1, &l_Lake_compileSharedLib___closed__1_once, _init_l_Lake_compileSharedLib___closed__1);
v___x_823_ = lean_array_push(v___x_822_, v___x_821_);
return v___x_823_;
}
}
lean_object* l_Lake_compileSharedLib(lean_object* v_libFile_825_, lean_object* v_linkArgs_826_, lean_object* v_linker_827_, lean_object* v_macosxDeploymentTarget_x3f_828_, lean_object* v_a_829_){
_start:
{
lean_object* v___x_831_; 
lean_inc_ref(v_libFile_825_);
v___x_831_ = l_Lake_createParentDirs(v_libFile_825_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; 
lean_dec_ref_known(v___x_831_, 1);
lean_inc_ref(v_libFile_825_);
v___x_832_ = l_Lake_mkArgs(v_libFile_825_, v_linkArgs_826_, v_a_829_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v_a_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___y_841_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
v_a_834_ = lean_ctor_get(v___x_832_, 1);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_832_, 2);
v___x_835_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_836_ = lean_obj_once(&l_Lake_compileSharedLib___closed__2, &l_Lake_compileSharedLib___closed__2_once, _init_l_Lake_compileSharedLib___closed__2);
v___x_837_ = lean_array_push(v___x_836_, v_libFile_825_);
v___x_838_ = l_Array_append___redArg(v___x_837_, v_a_833_);
lean_dec(v_a_833_);
v___x_839_ = lean_box(0);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_828_) == 0)
{
lean_object* v___x_846_; 
v___x_846_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_841_ = v___x_846_;
goto v___jp_840_;
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_847_ = ((lean_object*)(l_Lake_compileSharedLib___closed__3));
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v_macosxDeploymentTarget_x3f_828_);
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_mk_empty_array_with_capacity(v___x_849_);
v___x_851_ = lean_array_push(v___x_850_, v___x_848_);
v___y_841_ = v___x_851_;
goto v___jp_840_;
}
v___jp_840_:
{
uint8_t v___x_842_; uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_842_ = 1;
v___x_843_ = 0;
v___x_844_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_844_, 0, v___x_835_);
lean_ctor_set(v___x_844_, 1, v_linker_827_);
lean_ctor_set(v___x_844_, 2, v___x_838_);
lean_ctor_set(v___x_844_, 3, v___x_839_);
lean_ctor_set(v___x_844_, 4, v___y_841_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*5, v___x_842_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*5 + 1, v___x_843_);
v___x_845_ = l_Lake_proc(v___x_844_, v___x_843_, v___x_839_, v_a_834_);
return v___x_845_;
}
}
else
{
lean_object* v_a_852_; lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec(v_macosxDeploymentTarget_x3f_828_);
lean_dec_ref(v_linker_827_);
lean_dec_ref(v_libFile_825_);
v_a_852_ = lean_ctor_get(v___x_832_, 0);
v_a_853_ = lean_ctor_get(v___x_832_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_832_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_inc(v_a_852_);
lean_dec(v___x_832_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_852_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_862_; uint8_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v_macosxDeploymentTarget_x3f_828_);
lean_dec_ref(v_linker_827_);
lean_dec_ref(v_libFile_825_);
v_a_861_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_831_, 1);
v___x_862_ = lean_io_error_to_string(v_a_861_);
v___x_863_ = 3;
v___x_864_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set_uint8(v___x_864_, sizeof(void*)*1, v___x_863_);
v___x_865_ = lean_array_get_size(v_a_829_);
v___x_866_ = lean_array_push(v_a_829_, v___x_864_);
v___x_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
return v___x_867_;
}
}
}
LEAN_EXPORT void l_Lake_compileSharedLib_0interp(lean_interpreter_value* stack)
{
lean_object* v_libFile_825_ = stack[0].m_obj;
lean_object* v_linkArgs_826_ = stack[1].m_obj;
lean_object* v_linker_827_ = stack[2].m_obj;
lean_object* v_macosxDeploymentTarget_x3f_828_ = stack[3].m_obj;
lean_object* v_a_829_ = stack[4].m_obj;
lean_object* v_res_868_;
v_res_868_ = l_Lake_compileSharedLib(v_libFile_825_, v_linkArgs_826_, v_linker_827_, v_macosxDeploymentTarget_x3f_828_, v_a_829_);
stack->m_obj
 = v_res_868_;
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object* v_libFile_869_, lean_object* v_linkArgs_870_, lean_object* v_linker_871_, lean_object* v_macosxDeploymentTarget_x3f_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lake_compileSharedLib(v_libFile_869_, v_linkArgs_870_, v_linker_871_, v_macosxDeploymentTarget_x3f_872_, v_a_873_);
lean_dec_ref(v_linkArgs_870_);
return v_res_875_;
}
}
lean_object* l_Lake_compileExe(lean_object* v_binFile_876_, lean_object* v_linkArgs_877_, lean_object* v_linker_878_, lean_object* v_macosxDeploymentTarget_x3f_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_882_; 
lean_inc_ref(v_binFile_876_);
v___x_882_ = l_Lake_createParentDirs(v_binFile_876_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v___x_883_; 
lean_dec_ref_known(v___x_882_, 1);
lean_inc_ref(v_binFile_876_);
v___x_883_ = l_Lake_mkArgs(v_binFile_876_, v_linkArgs_877_, v_a_880_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v_a_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___y_894_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
v_a_885_ = lean_ctor_get(v___x_883_, 1);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_883_, 2);
v___x_886_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_887_ = lean_unsigned_to_nat(2u);
v___x_888_ = lean_mk_empty_array_with_capacity(v___x_887_);
lean_dec_ref(v___x_888_);
v___x_889_ = lean_obj_once(&l_Lake_compileLeanModule___closed__13, &l_Lake_compileLeanModule___closed__13_once, _init_l_Lake_compileLeanModule___closed__13);
v___x_890_ = lean_array_push(v___x_889_, v_binFile_876_);
v___x_891_ = l_Array_append___redArg(v___x_890_, v_a_884_);
lean_dec(v_a_884_);
v___x_892_ = lean_box(0);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_879_) == 0)
{
lean_object* v___x_899_; 
v___x_899_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_894_ = v___x_899_;
goto v___jp_893_;
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_900_ = ((lean_object*)(l_Lake_compileSharedLib___closed__3));
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v_macosxDeploymentTarget_x3f_879_);
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = lean_mk_empty_array_with_capacity(v___x_902_);
v___x_904_ = lean_array_push(v___x_903_, v___x_901_);
v___y_894_ = v___x_904_;
goto v___jp_893_;
}
v___jp_893_:
{
uint8_t v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_895_ = 1;
v___x_896_ = 0;
v___x_897_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_897_, 0, v___x_886_);
lean_ctor_set(v___x_897_, 1, v_linker_878_);
lean_ctor_set(v___x_897_, 2, v___x_891_);
lean_ctor_set(v___x_897_, 3, v___x_892_);
lean_ctor_set(v___x_897_, 4, v___y_894_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*5, v___x_895_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*5 + 1, v___x_896_);
v___x_898_ = l_Lake_proc(v___x_897_, v___x_896_, v___x_892_, v_a_885_);
return v___x_898_;
}
}
else
{
lean_object* v_a_905_; lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec(v_macosxDeploymentTarget_x3f_879_);
lean_dec_ref(v_linker_878_);
lean_dec_ref(v_binFile_876_);
v_a_905_ = lean_ctor_get(v___x_883_, 0);
v_a_906_ = lean_ctor_get(v___x_883_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_883_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_inc(v_a_905_);
lean_dec(v___x_883_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_905_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_macosxDeploymentTarget_x3f_879_);
lean_dec_ref(v_linker_878_);
lean_dec_ref(v_binFile_876_);
v_a_914_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_882_, 1);
v___x_915_ = lean_io_error_to_string(v_a_914_);
v___x_916_ = 3;
v___x_917_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set_uint8(v___x_917_, sizeof(void*)*1, v___x_916_);
v___x_918_ = lean_array_get_size(v_a_880_);
v___x_919_ = lean_array_push(v_a_880_, v___x_917_);
v___x_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
return v___x_920_;
}
}
}
LEAN_EXPORT void l_Lake_compileExe_0interp(lean_interpreter_value* stack)
{
lean_object* v_binFile_876_ = stack[0].m_obj;
lean_object* v_linkArgs_877_ = stack[1].m_obj;
lean_object* v_linker_878_ = stack[2].m_obj;
lean_object* v_macosxDeploymentTarget_x3f_879_ = stack[3].m_obj;
lean_object* v_a_880_ = stack[4].m_obj;
lean_object* v_res_921_;
v_res_921_ = l_Lake_compileExe(v_binFile_876_, v_linkArgs_877_, v_linker_878_, v_macosxDeploymentTarget_x3f_879_, v_a_880_);
stack->m_obj
 = v_res_921_;
}
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object* v_binFile_922_, lean_object* v_linkArgs_923_, lean_object* v_linker_924_, lean_object* v_macosxDeploymentTarget_x3f_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lake_compileExe(v_binFile_922_, v_linkArgs_923_, v_linker_924_, v_macosxDeploymentTarget_x3f_925_, v_a_926_);
lean_dec_ref(v_linkArgs_923_);
return v_res_928_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0));
v___x_931_ = lean_unsigned_to_nat(2u);
v___x_932_ = lean_mk_empty_array_with_capacity(v___x_931_);
v___x_933_ = lean_array_push(v___x_932_, v___x_930_);
return v___x_933_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(lean_object* v_as_934_, size_t v_i_935_, size_t v_stop_936_, lean_object* v_b_937_){
_start:
{
uint8_t v___x_938_; 
v___x_938_ = lean_usize_dec_eq(v_i_935_, v_stop_936_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; size_t v___x_943_; size_t v___x_944_; 
v___x_939_ = lean_array_uget_borrowed(v_as_934_, v_i_935_);
v___x_940_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1);
lean_inc(v___x_939_);
v___x_941_ = lean_array_push(v___x_940_, v___x_939_);
v___x_942_ = l_Array_append___redArg(v_b_937_, v___x_941_);
lean_dec_ref(v___x_941_);
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_add(v_i_935_, v___x_943_);
v_i_935_ = v___x_944_;
v_b_937_ = v___x_942_;
goto _start;
}
else
{
return v_b_937_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_934_ = stack[0].m_obj;
size_t v_i_935_ = stack[1].m_num;
size_t v_stop_936_ = stack[2].m_num;
lean_object* v_b_937_ = stack[3].m_obj;
lean_object* v_res_946_;
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_as_934_, v_i_935_, v_stop_936_, v_b_937_);
stack->m_obj
 = v_res_946_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___boxed(lean_object* v_as_947_, lean_object* v_i_948_, lean_object* v_stop_949_, lean_object* v_b_950_){
_start:
{
size_t v_i_boxed_951_; size_t v_stop_boxed_952_; lean_object* v_res_953_; 
v_i_boxed_951_ = lean_unbox_usize(v_i_948_);
lean_dec(v_i_948_);
v_stop_boxed_952_ = lean_unbox_usize(v_stop_949_);
lean_dec(v_stop_949_);
v_res_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_as_947_, v_i_boxed_951_, v_stop_boxed_952_, v_b_950_);
lean_dec_ref(v_as_947_);
return v_res_953_;
}
}
static lean_object* _init_l_Lake_download___closed__6(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_960_ = ((lean_object*)(l_Lake_download___closed__2));
v___x_961_ = lean_unsigned_to_nat(7u);
v___x_962_ = lean_mk_empty_array_with_capacity(v___x_961_);
v___x_963_ = lean_array_push(v___x_962_, v___x_960_);
return v___x_963_;
}
}
static lean_object* _init_l_Lake_download___closed__7(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = ((lean_object*)(l_Lake_download___closed__3));
v___x_965_ = lean_obj_once(&l_Lake_download___closed__6, &l_Lake_download___closed__6_once, _init_l_Lake_download___closed__6);
v___x_966_ = lean_array_push(v___x_965_, v___x_964_);
return v___x_966_;
}
}
static lean_object* _init_l_Lake_download___closed__8(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_968_ = lean_obj_once(&l_Lake_download___closed__7, &l_Lake_download___closed__7_once, _init_l_Lake_download___closed__7);
v___x_969_ = lean_array_push(v___x_968_, v___x_967_);
return v___x_969_;
}
}
static lean_object* _init_l_Lake_download___closed__9(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_970_ = ((lean_object*)(l_Lake_compileLeanModule___closed__12));
v___x_971_ = lean_obj_once(&l_Lake_download___closed__8, &l_Lake_download___closed__8_once, _init_l_Lake_download___closed__8);
v___x_972_ = lean_array_push(v___x_971_, v___x_970_);
return v___x_972_;
}
}
lean_object* l_Lake_download(lean_object* v_url_973_, lean_object* v_file_974_, lean_object* v_headers_975_, lean_object* v_a_976_){
_start:
{
lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v_val_981_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_997_; uint8_t v___x_1013_; 
v___x_1013_ = l_System_FilePath_pathExists(v_file_974_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
lean_inc_ref(v_file_974_);
v___x_1014_ = l_Lake_createParentDirs(v_file_974_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_dec_ref_known(v___x_1014_, 1);
v___y_997_ = v_a_976_;
goto v___jp_996_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec_ref(v_file_974_);
lean_dec_ref(v_url_973_);
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = lean_io_error_to_string(v_a_1015_);
v___x_1017_ = 3;
v___x_1018_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set_uint8(v___x_1018_, sizeof(void*)*1, v___x_1017_);
v___x_1019_ = lean_array_get_size(v_a_976_);
v___x_1020_ = lean_array_push(v_a_976_, v___x_1018_);
v___x_1021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
return v___x_1021_;
}
}
else
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_io_remove_file(v_file_974_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_dec_ref_known(v___x_1022_, 1);
v___y_997_ = v_a_976_;
goto v___jp_996_;
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec_ref(v_file_974_);
lean_dec_ref(v_url_973_);
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v___x_1024_ = lean_io_error_to_string(v_a_1023_);
v___x_1025_ = 3;
v___x_1026_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set_uint8(v___x_1026_, sizeof(void*)*1, v___x_1025_);
v___x_1027_ = lean_array_get_size(v_a_976_);
v___x_1028_ = lean_array_push(v_a_976_, v___x_1026_);
v___x_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
return v___x_1029_;
}
}
v___jp_978_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; uint8_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_982_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_983_ = lean_box(0);
v___x_984_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_985_ = 1;
v___x_986_ = 0;
v___x_987_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_987_, 0, v___x_982_);
lean_ctor_set(v___x_987_, 1, v_val_981_);
lean_ctor_set(v___x_987_, 2, v___y_979_);
lean_ctor_set(v___x_987_, 3, v___x_983_);
lean_ctor_set(v___x_987_, 4, v___x_984_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*5, v___x_985_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*5 + 1, v___x_986_);
v___x_988_ = l_Lake_proc(v___x_987_, v___x_985_, v___x_983_, v___y_980_);
return v___x_988_;
}
v___jp_989_:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lake_download___closed__0));
v___x_993_ = lean_io_getenv(v___x_992_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_994_; 
v___x_994_ = ((lean_object*)(l_Lake_download___closed__1));
v___y_979_ = v___y_991_;
v___y_980_ = v___y_990_;
v_val_981_ = v___x_994_;
goto v___jp_978_;
}
else
{
lean_object* v_val_995_; 
v_val_995_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v___x_993_, 1);
v___y_979_ = v___y_991_;
v___y_980_ = v___y_990_;
v_val_981_ = v_val_995_;
goto v___jp_978_;
}
}
v___jp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_998_ = ((lean_object*)(l_Lake_download___closed__5));
v___x_999_ = lean_obj_once(&l_Lake_download___closed__9, &l_Lake_download___closed__9_once, _init_l_Lake_download___closed__9);
v___x_1000_ = lean_array_push(v___x_999_, v_file_974_);
v___x_1001_ = lean_array_push(v___x_1000_, v___x_998_);
v___x_1002_ = lean_array_push(v___x_1001_, v_url_973_);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_array_get_size(v_headers_975_);
v___x_1005_ = lean_nat_dec_lt(v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
v___y_990_ = v___y_997_;
v___y_991_ = v___x_1002_;
goto v___jp_989_;
}
else
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_nat_dec_le(v___x_1004_, v___x_1004_);
if (v___x_1006_ == 0)
{
if (v___x_1005_ == 0)
{
v___y_990_ = v___y_997_;
v___y_991_ = v___x_1002_;
goto v___jp_989_;
}
else
{
size_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = ((size_t)0ULL);
v___x_1008_ = lean_usize_of_nat(v___x_1004_);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_975_, v___x_1007_, v___x_1008_, v___x_1002_);
v___y_990_ = v___y_997_;
v___y_991_ = v___x_1009_;
goto v___jp_989_;
}
}
else
{
size_t v___x_1010_; size_t v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = ((size_t)0ULL);
v___x_1011_ = lean_usize_of_nat(v___x_1004_);
v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_975_, v___x_1010_, v___x_1011_, v___x_1002_);
v___y_990_ = v___y_997_;
v___y_991_ = v___x_1012_;
goto v___jp_989_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_download_0interp(lean_interpreter_value* stack)
{
lean_object* v_url_973_ = stack[0].m_obj;
lean_object* v_file_974_ = stack[1].m_obj;
lean_object* v_headers_975_ = stack[2].m_obj;
lean_object* v_a_976_ = stack[3].m_obj;
lean_object* v_res_1030_;
v_res_1030_ = l_Lake_download(v_url_973_, v_file_974_, v_headers_975_, v_a_976_);
stack->m_obj
 = v_res_1030_;
}
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object* v_url_1031_, lean_object* v_file_1032_, lean_object* v_headers_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lake_download(v_url_1031_, v_file_1032_, v_headers_1033_, v_a_1034_);
lean_dec_ref(v_headers_1033_);
return v_res_1036_;
}
}
lean_object* l_Lake_untar(lean_object* v_file_1041_, lean_object* v_dir_1042_, uint8_t v_gzip_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v_opts_1047_; lean_object* v___y_1048_; lean_object* v___x_1066_; 
lean_inc_ref(v_dir_1042_);
v___x_1066_ = l_IO_FS_createDirAll(v_dir_1042_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_dec_ref_known(v___x_1066_, 1);
if (v_gzip_1043_ == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = ((lean_object*)(l_Lake_untar___closed__2));
v_opts_1047_ = v___x_1067_;
v___y_1048_ = v_a_1044_;
goto v___jp_1046_;
}
else
{
lean_object* v___x_1068_; 
v___x_1068_ = ((lean_object*)(l_Lake_untar___closed__3));
v_opts_1047_ = v___x_1068_;
v___y_1048_ = v_a_1044_;
goto v___jp_1046_;
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec_ref(v_dir_1042_);
lean_dec_ref(v_file_1041_);
v_a_1069_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1070_ = lean_io_error_to_string(v_a_1069_);
v___x_1071_ = 3;
v___x_1072_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set_uint8(v___x_1072_, sizeof(void*)*1, v___x_1071_);
v___x_1073_ = lean_array_get_size(v_a_1044_);
v___x_1074_ = lean_array_push(v_a_1044_, v___x_1072_);
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
return v___x_1075_;
}
v___jp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1049_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_1050_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_1051_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_1052_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_1053_ = lean_unsigned_to_nat(5u);
v___x_1054_ = lean_mk_empty_array_with_capacity(v___x_1053_);
lean_inc_ref(v_opts_1047_);
v___x_1055_ = lean_array_push(v___x_1054_, v_opts_1047_);
v___x_1056_ = lean_array_push(v___x_1055_, v___x_1051_);
v___x_1057_ = lean_array_push(v___x_1056_, v_file_1041_);
v___x_1058_ = lean_array_push(v___x_1057_, v___x_1052_);
v___x_1059_ = lean_array_push(v___x_1058_, v_dir_1042_);
v___x_1060_ = lean_box(0);
v___x_1061_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___x_1062_ = 1;
v___x_1063_ = 0;
v___x_1064_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1064_, 0, v___x_1049_);
lean_ctor_set(v___x_1064_, 1, v___x_1050_);
lean_ctor_set(v___x_1064_, 2, v___x_1059_);
lean_ctor_set(v___x_1064_, 3, v___x_1060_);
lean_ctor_set(v___x_1064_, 4, v___x_1061_);
lean_ctor_set_uint8(v___x_1064_, sizeof(void*)*5, v___x_1062_);
lean_ctor_set_uint8(v___x_1064_, sizeof(void*)*5 + 1, v___x_1063_);
v___x_1065_ = l_Lake_proc(v___x_1064_, v___x_1062_, v___x_1060_, v___y_1048_);
return v___x_1065_;
}
}
}
LEAN_EXPORT void l_Lake_untar_0interp(lean_interpreter_value* stack)
{
lean_object* v_file_1041_ = stack[0].m_obj;
lean_object* v_dir_1042_ = stack[1].m_obj;
uint8_t v_gzip_1043_ = stack[2].m_num;
lean_object* v_a_1044_ = stack[3].m_obj;
lean_object* v_res_1076_;
v_res_1076_ = l_Lake_untar(v_file_1041_, v_dir_1042_, v_gzip_1043_, v_a_1044_);
stack->m_obj
 = v_res_1076_;
}
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object* v_file_1077_, lean_object* v_dir_1078_, lean_object* v_gzip_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
uint8_t v_gzip_boxed_1082_; lean_object* v_res_1083_; 
v_gzip_boxed_1082_ = lean_unbox(v_gzip_1079_);
v_res_1083_ = l_Lake_untar(v_file_1077_, v_dir_1078_, v_gzip_boxed_1082_, v_a_1080_);
return v_res_1083_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(lean_object* v_as_1085_, size_t v_sz_1086_, size_t v_i_1087_, lean_object* v_b_1088_, lean_object* v___y_1089_){
_start:
{
uint8_t v___x_1091_; 
v___x_1091_ = lean_usize_dec_lt(v_i_1087_, v_sz_1086_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v_b_1088_);
lean_ctor_set(v___x_1092_, 1, v___y_1089_);
return v___x_1092_;
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; size_t v___x_1097_; size_t v___x_1098_; 
v_a_1093_ = lean_array_uget_borrowed(v_as_1085_, v_i_1087_);
v___x_1094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0));
v___x_1095_ = lean_string_append(v___x_1094_, v_a_1093_);
v___x_1096_ = lean_array_push(v_b_1088_, v___x_1095_);
v___x_1097_ = ((size_t)1ULL);
v___x_1098_ = lean_usize_add(v_i_1087_, v___x_1097_);
v_i_1087_ = v___x_1098_;
v_b_1088_ = v___x_1096_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1085_ = stack[0].m_obj;
size_t v_sz_1086_ = stack[1].m_num;
size_t v_i_1087_ = stack[2].m_num;
lean_object* v_b_1088_ = stack[3].m_obj;
lean_object* v___y_1089_ = stack[4].m_obj;
lean_object* v_res_1100_;
v_res_1100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_as_1085_, v_sz_1086_, v_i_1087_, v_b_1088_, v___y_1089_);
stack->m_obj
 = v_res_1100_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___boxed(lean_object* v_as_1101_, lean_object* v_sz_1102_, lean_object* v_i_1103_, lean_object* v_b_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
size_t v_sz_boxed_1107_; size_t v_i_boxed_1108_; lean_object* v_res_1109_; 
v_sz_boxed_1107_ = lean_unbox_usize(v_sz_1102_);
lean_dec(v_sz_1102_);
v_i_boxed_1108_ = lean_unbox_usize(v_i_1103_);
lean_dec(v_i_1103_);
v_res_1109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_as_1101_, v_sz_boxed_1107_, v_i_boxed_1108_, v_b_1104_, v___y_1105_);
lean_dec_ref(v_as_1101_);
return v_res_1109_;
}
}
static lean_object* _init_l_Lake_tar___closed__1(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1111_ = ((lean_object*)(l_Lake_download___closed__4));
v___x_1112_ = lean_unsigned_to_nat(5u);
v___x_1113_ = lean_mk_empty_array_with_capacity(v___x_1112_);
v___x_1114_ = lean_array_push(v___x_1113_, v___x_1111_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lake_tar___closed__10(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = ((lean_object*)(l_Lake_tar___closed__9));
v___x_1133_ = ((lean_object*)(l_Lake_tar___closed__8));
v___x_1134_ = lean_array_push(v___x_1133_, v___x_1132_);
return v___x_1134_;
}
}
lean_object* l_Lake_tar(lean_object* v_dir_1135_, lean_object* v_file_1136_, uint8_t v_gzip_1137_, lean_object* v_excludePaths_1138_, lean_object* v_a_1139_){
_start:
{
uint8_t v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v_args_1154_; lean_object* v___y_1155_; lean_object* v___x_1185_; 
lean_inc_ref(v_file_1136_);
v___x_1185_ = l_Lake_createParentDirs(v_file_1136_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v___x_1186_; 
lean_dec_ref_known(v___x_1185_, 1);
v___x_1186_ = ((lean_object*)(l_Lake_tar___closed__8));
if (v_gzip_1137_ == 0)
{
v_args_1154_ = v___x_1186_;
v___y_1155_ = v_a_1139_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_obj_once(&l_Lake_tar___closed__10, &l_Lake_tar___closed__10_once, _init_l_Lake_tar___closed__10);
v_args_1154_ = v___x_1187_;
v___y_1155_ = v_a_1139_;
goto v___jp_1153_;
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec_ref(v_file_1136_);
lean_dec_ref(v_dir_1135_);
v_a_1188_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1185_, 1);
v___x_1189_ = lean_io_error_to_string(v_a_1188_);
v___x_1190_ = 3;
v___x_1191_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set_uint8(v___x_1191_, sizeof(void*)*1, v___x_1190_);
v___x_1192_ = lean_array_get_size(v_a_1139_);
v___x_1193_ = lean_array_push(v_a_1139_, v___x_1191_);
v___x_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
return v___x_1194_;
}
v___jp_1141_:
{
uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1149_ = 0;
lean_inc_ref(v___y_1148_);
lean_inc(v___y_1145_);
lean_inc_ref(v___y_1147_);
lean_inc_ref(v___y_1146_);
v___x_1150_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1150_, 0, v___y_1146_);
lean_ctor_set(v___x_1150_, 1, v___y_1147_);
lean_ctor_set(v___x_1150_, 2, v___y_1143_);
lean_ctor_set(v___x_1150_, 3, v___y_1145_);
lean_ctor_set(v___x_1150_, 4, v___y_1148_);
lean_ctor_set_uint8(v___x_1150_, sizeof(void*)*5, v___y_1142_);
lean_ctor_set_uint8(v___x_1150_, sizeof(void*)*5 + 1, v___x_1149_);
v___x_1151_ = lean_box(0);
v___x_1152_ = l_Lake_proc(v___x_1150_, v___y_1142_, v___x_1151_, v___y_1144_);
return v___x_1152_;
}
v___jp_1153_:
{
size_t v_sz_1156_; size_t v___x_1157_; lean_object* v___x_1158_; 
v_sz_1156_ = lean_array_size(v_excludePaths_1138_);
v___x_1157_ = ((size_t)0ULL);
lean_inc_ref(v_args_1154_);
v___x_1158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_excludePaths_1138_, v_sz_1156_, v___x_1157_, v_args_1154_, v___y_1155_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v_a_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; uint8_t v___x_1173_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
v_a_1160_ = lean_ctor_get(v___x_1158_, 1);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1158_, 2);
v___x_1161_ = ((lean_object*)(l_Lake_compileLeanIR___closed__0));
v___x_1162_ = ((lean_object*)(l_Lake_untar___closed__0));
v___x_1163_ = ((lean_object*)(l_Lake_untar___closed__1));
v___x_1164_ = ((lean_object*)(l_Lake_tar___closed__0));
v___x_1165_ = lean_obj_once(&l_Lake_tar___closed__1, &l_Lake_tar___closed__1_once, _init_l_Lake_tar___closed__1);
v___x_1166_ = lean_array_push(v___x_1165_, v_file_1136_);
v___x_1167_ = lean_array_push(v___x_1166_, v___x_1163_);
v___x_1168_ = lean_array_push(v___x_1167_, v_dir_1135_);
v___x_1169_ = lean_array_push(v___x_1168_, v___x_1164_);
v___x_1170_ = l_Array_append___redArg(v_a_1159_, v___x_1169_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = lean_box(0);
v___x_1172_ = l_System_Platform_isOSX;
v___x_1173_ = 1;
if (v___x_1172_ == 0)
{
lean_object* v___x_1174_; 
v___x_1174_ = ((lean_object*)(l_Lake_compileO___closed__2));
v___y_1142_ = v___x_1173_;
v___y_1143_ = v___x_1170_;
v___y_1144_ = v_a_1160_;
v___y_1145_ = v___x_1171_;
v___y_1146_ = v___x_1161_;
v___y_1147_ = v___x_1162_;
v___y_1148_ = v___x_1174_;
goto v___jp_1141_;
}
else
{
lean_object* v___x_1175_; 
v___x_1175_ = ((lean_object*)(l_Lake_tar___closed__6));
v___y_1142_ = v___x_1173_;
v___y_1143_ = v___x_1170_;
v___y_1144_ = v_a_1160_;
v___y_1145_ = v___x_1171_;
v___y_1146_ = v___x_1161_;
v___y_1147_ = v___x_1162_;
v___y_1148_ = v___x_1175_;
goto v___jp_1141_;
}
}
else
{
lean_object* v_a_1176_; lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec_ref(v_file_1136_);
lean_dec_ref(v_dir_1135_);
v_a_1176_ = lean_ctor_get(v___x_1158_, 0);
v_a_1177_ = lean_ctor_get(v___x_1158_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1158_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_inc(v_a_1176_);
lean_dec(v___x_1158_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1176_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_tar_0interp(lean_interpreter_value* stack)
{
lean_object* v_dir_1135_ = stack[0].m_obj;
lean_object* v_file_1136_ = stack[1].m_obj;
uint8_t v_gzip_1137_ = stack[2].m_num;
lean_object* v_excludePaths_1138_ = stack[3].m_obj;
lean_object* v_a_1139_ = stack[4].m_obj;
lean_object* v_res_1195_;
v_res_1195_ = l_Lake_tar(v_dir_1135_, v_file_1136_, v_gzip_1137_, v_excludePaths_1138_, v_a_1139_);
stack->m_obj
 = v_res_1195_;
}
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object* v_dir_1196_, lean_object* v_file_1197_, lean_object* v_gzip_1198_, lean_object* v_excludePaths_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
uint8_t v_gzip_boxed_1202_; lean_object* v_res_1203_; 
v_gzip_boxed_1202_ = lean_unbox(v_gzip_1198_);
v_res_1203_ = l_Lake_tar(v_dir_1196_, v_file_1197_, v_gzip_boxed_1202_, v_excludePaths_1199_, v_a_1200_);
lean_dec_ref(v_excludePaths_1199_);
return v_res_1203_;
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
