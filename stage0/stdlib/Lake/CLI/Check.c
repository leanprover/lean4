// Lean compiler output
// Module: Lake.CLI.Check
// Imports: public import Lake.Check.Axioms public import Lake.Check.Compare public import Lake.Config.InstallPath public import Lake.Util.Exit public import Lean.Data.Json.FromToJson import Lean.Environment import Lean.Replay import Init.Data.String.Search import Init.Data.String.TakeDrop import Init.Data.ToString.Macro import Init.System.IO import Init.System.Platform
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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_get_stdout();
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* lean_get_stderr();
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_io_error_to_string(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* lean_io_create_tempfile();
lean_object* lean_io_remove_file(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_io_create_dir(lean_object*);
lean_object* l_LeanExport_parseStream(lean_object*);
lean_object* l_Lake_Check_compareAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Check_checkAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_String_compare___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
extern uint8_t l_System_Platform_isLinux;
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_io_realpath(lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Check_usedAxioms(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getTheoremNames(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getTheoremNames___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getDefinitionNames(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getDefinitionNames___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getProjectDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getProjectDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "which"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__1_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_whichExe(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_whichExe___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "`lake "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` needs `"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 315, .m_capacity = 315, .m_length = 314, .m_data = "` to sandbox the code it checks, and it was not found.\n\n  Install it from https://github.com/Zouuup/landrun (build from `main`)\n  and put it on PATH, or set COMPARATOR_LANDRUN to its full path.\n\n  There is no unsandboxed mode: the code being checked is untrusted, and it\n  is built and exported inside the sandbox."};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "--ro"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--connect-tcp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "--rwx"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "--env"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__0_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__1;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--best-effort"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "--rox"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "--rw"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "/dev"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__6 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__6_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__2_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__3_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__4_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__5_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__6_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__7 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_landrunSpawnArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_landrunSpawnArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Child exited with "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LEAN_PATH="};
static const lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATH="};
static const lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "`lake env` did not report the project's search path"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__0_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Resolving dependencies"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".lake"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "env"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__4_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__4_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PATH"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HOME"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "LEAN_ABORT_ON_PANIC"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__9 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__9_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__10 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__10_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__10_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "443"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "22"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__15 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__15_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__15_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__16 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__16_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__17 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__17_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__17_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__17_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__19 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "resolve-deps"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__0_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__0_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Building and exporting"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "check"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__1_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__1_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "LAKE_CHECK_EXPORT"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__3_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__4_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__4_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Building "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "build"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__2_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__2_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LEAN_PATH"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__0_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__0_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__1_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExporter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExporter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__1_value;
static const lean_string_object l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0(lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Exporting "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " from "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "noda"};
static const lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0 = (const lean_object*)&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0_value;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5;
static const lean_ctor_object l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__6 = (const lean_object*)&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__6_value;
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Error while interacting with "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " kernel"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " kernel: "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "use_stdin"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__3_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__4_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "export_file_path"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "permitted_axioms"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unpermitted_axiom_hard_error"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "num_threads"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "nat_extension"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "string_extension"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__20 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__20_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " kernel rejected the solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " exited with "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " kernel accepts the solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Running "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " kernel on solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean default"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--from-export"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__1_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sub"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(9, 137, 41, 185, 216, 152, 145, 196)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__5_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(124, 230, 50, 167, 103, 237, 136, 198)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__6 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pow"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__7 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__7_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(155, 64, 52, 77, 166, 227, 131, 174)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__8 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__8_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "gcd"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__9 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__9_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__10_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(57, 94, 240, 174, 21, 113, 54, 0)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__10 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__10_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "div"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__11 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__11_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__12_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(67, 67, 214, 176, 223, 68, 36, 94)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__12 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__12_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mod"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__13 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__13_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__14_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(244, 133, 16, 0, 168, 19, 182, 179)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__14 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__14_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__15 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__15_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__16_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(58, 27, 161, 98, 177, 242, 252, 86)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__16 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__16_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ble"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__17 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__17_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__18_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(18, 188, 15, 95, 29, 42, 30, 33)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__18 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__18_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "land"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__19 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__19_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__20_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(188, 247, 118, 195, 143, 11, 83, 131)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__20 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__20_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lor"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__21 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__21_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__22_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(189, 20, 242, 236, 1, 249, 227, 248)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__22 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__22_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__23 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__23_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__24_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(42, 157, 235, 85, 27, 16, 17, 168)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__24 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__24_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "shiftLeft"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__25 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__25_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__26_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(85, 136, 172, 27, 109, 172, 80, 195)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__26 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__26_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "shiftRight"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__27 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__27_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__28_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__27_value),LEAN_SCALAR_PTR_LITERAL(119, 176, 216, 253, 49, 85, 187, 63)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__28 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__28_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__29 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__29_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofList"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__30 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__30_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__31_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__30_value),LEAN_SCALAR_PTR_LITERAL(118, 246, 177, 142, 179, 9, 199, 233)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__31 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__31_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__32 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__32_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__33 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__33_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__34_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__33_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__34 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__34_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__35 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__35_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__35_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__36 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__36_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eagerReduce"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__37 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__37_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__37_value),LEAN_SCALAR_PTR_LITERAL(238, 243, 67, 12, 220, 84, 120, 222)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__38 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__38_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__39 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__39_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__40 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__40_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__41 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__41_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__42_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__41_value),LEAN_SCALAR_PTR_LITERAL(118, 80, 194, 26, 119, 145, 0, 103)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__42 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__42_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__43 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__43_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optParam"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__44 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__44_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__44_value),LEAN_SCALAR_PTR_LITERAL(140, 160, 223, 165, 16, 51, 54, 209)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__45 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__45_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "autoParam"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__46 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__46_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__46_value),LEAN_SCALAR_PTR_LITERAL(140, 161, 241, 39, 119, 172, 48, 112)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__47 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__47_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "semiOutParam"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__48 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__48_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__48_value),LEAN_SCALAR_PTR_LITERAL(141, 187, 140, 108, 143, 232, 13, 120)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__49 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__49_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "outParam"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__50 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__50_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__50_value),LEAN_SCALAR_PTR_LITERAL(209, 153, 87, 30, 57, 250, 25, 29)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__51 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__51_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*26, .m_other = 0, .m_tag = 246}, .m_size = 26, .m_capacity = 26, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__2_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__4_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__6_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__8_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__10_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__12_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__14_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__16_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__18_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__20_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__22_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__24_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__26_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__28_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__31_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__34_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__36_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__38_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__39_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__40_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__42_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__43_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__45_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__47_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__49_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__51_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__52 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__52_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sound"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__2_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 255, 230, 69, 40, 79, 199, 28)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__5_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__41_value),LEAN_SCALAR_PTR_LITERAL(255, 113, 137, 82, 82, 132, 58, 248)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__6 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__6_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__7_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__6_value),LEAN_SCALAR_PTR_LITERAL(91, 125, 38, 34, 222, 200, 201, 80)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__7 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ind"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__8 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__9_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__8_value),LEAN_SCALAR_PTR_LITERAL(150, 213, 121, 152, 109, 27, 137, 60)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__9 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__9_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__4_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__5_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__7_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__9_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__10 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__10_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_stringStream(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_stringStream___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Check_compareIt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Your solution is okay!"};
static const lean_object* l_Lake_Check_compareIt___closed__0 = (const lean_object*)&l_Lake_Check_compareIt___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Check_compareIt(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__0_value;
static const lean_closure_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__1 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_Check_instFromJsonConfig_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "challenge_module"};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__0 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__0_value;
static const lean_string_object l_Lake_Check_instFromJsonConfig_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__1 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__1_value;
static const lean_string_object l_Lake_Check_instFromJsonConfig_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Check"};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__2 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__2_value;
static const lean_string_object l_Lake_Check_instFromJsonConfig_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Config"};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__3 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__3_value;
static const lean_ctor_object l_Lake_Check_instFromJsonConfig_fromJson___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Check_instFromJsonConfig_fromJson___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__4_value_aux_0),((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 121, 61, 181, 100, 226, 26, 39)}};
static const lean_ctor_object l_Lake_Check_instFromJsonConfig_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__4_value_aux_1),((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 253, 238, 39, 237, 240, 148, 33)}};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__4 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__4_value;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__5;
static const lean_string_object l_Lake_Check_instFromJsonConfig_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__6 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__6_value;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__7;
static const lean_ctor_object l_Lake_Check_instFromJsonConfig_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 239, 122, 143, 156, 150, 119, 228)}};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__8 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__8_value;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__9;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__10;
static const lean_string_object l_Lake_Check_instFromJsonConfig_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__11 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__11_value;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__12;
static const lean_string_object l_Lake_Check_instFromJsonConfig_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "solution_module"};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__13 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__13_value;
static const lean_ctor_object l_Lake_Check_instFromJsonConfig_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__13_value),LEAN_SCALAR_PTR_LITERAL(196, 97, 97, 57, 150, 39, 125, 168)}};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__14 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__14_value;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__15;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__16;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__17;
static const lean_string_object l_Lake_Check_instFromJsonConfig_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "theorem_names"};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__18 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__18_value;
static const lean_ctor_object l_Lake_Check_instFromJsonConfig_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__18_value),LEAN_SCALAR_PTR_LITERAL(74, 45, 230, 82, 200, 194, 22, 200)}};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__19 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__19_value;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__20;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__21;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__22;
static const lean_string_object l_Lake_Check_instFromJsonConfig_fromJson___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "definition_names"};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__23 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__23_value;
static const lean_ctor_object l_Lake_Check_instFromJsonConfig_fromJson___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__23_value),LEAN_SCALAR_PTR_LITERAL(142, 234, 197, 41, 94, 48, 219, 189)}};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__24 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__24_value;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__25;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__26;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__27;
static const lean_ctor_object l_Lake_Check_instFromJsonConfig_fromJson___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(67, 66, 102, 170, 71, 166, 115, 173)}};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__28 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__28_value;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__29;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__30;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__31;
static const lean_string_object l_Lake_Check_instFromJsonConfig_fromJson___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "enable_nanoda"};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__32 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__32_value;
static const lean_string_object l_Lake_Check_instFromJsonConfig_fromJson___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "enable_nanoda\?"};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__33 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__33_value;
static const lean_ctor_object l_Lake_Check_instFromJsonConfig_fromJson___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__33_value),LEAN_SCALAR_PTR_LITERAL(38, 150, 13, 192, 149, 235, 179, 231)}};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__34 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__34_value;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__35;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__36;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__37;
static const lean_string_object l_Lake_Check_instFromJsonConfig_fromJson___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "external_kernels"};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__38 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__38_value;
static const lean_string_object l_Lake_Check_instFromJsonConfig_fromJson___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "external_kernels\?"};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__39 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__39_value;
static const lean_ctor_object l_Lake_Check_instFromJsonConfig_fromJson___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__39_value),LEAN_SCALAR_PTR_LITERAL(141, 143, 112, 163, 13, 61, 174, 161)}};
static const lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__40 = (const lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__40_value;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__41;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__42;
static lean_once_cell_t l_Lake_Check_instFromJsonConfig_fromJson___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instFromJsonConfig_fromJson___closed__43;
LEAN_EXPORT lean_object* l_Lake_Check_instFromJsonConfig_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Check_instFromJsonConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Check_instFromJsonConfig_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Check_instFromJsonConfig___closed__0 = (const lean_object*)&l_Lake_Check_instFromJsonConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Check_instFromJsonConfig = (const lean_object*)&l_Lake_Check_instFromJsonConfig___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(lean_object*, lean_object*);
static const lean_array_object l_Lake_Check_instToJsonConfig_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Check_instToJsonConfig_toJson___closed__0 = (const lean_object*)&l_Lake_Check_instToJsonConfig_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Check_instToJsonConfig_toJson(lean_object*);
static const lean_closure_object l_Lake_Check_instToJsonConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Check_instToJsonConfig_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Check_instToJsonConfig___closed__0 = (const lean_object*)&l_Lake_Check_instToJsonConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Check_instToJsonConfig = (const lean_object*)&l_Lake_Check_instToJsonConfig___closed__0_value;
static const lean_string_object l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__0 = (const lean_object*)&l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1 = (const lean_object*)&l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__2 = (const lean_object*)&l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3 = (const lean_object*)&l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_Check_instReprConfig_repr_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3_value;
static lean_once_cell_t l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4;
static lean_once_cell_t l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5;
static const lean_ctor_object l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__6_value;
static const lean_ctor_object l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__2_value)}};
static const lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7_value;
static const lean_string_object l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__8_value;
static const lean_ctor_object l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__8_value)}};
static const lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__9_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(lean_object*, lean_object*);
static const lean_ctor_object l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__0_value)}};
static const lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1;
static lean_once_cell_t l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2;
static const lean_ctor_object l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__1_value)}};
static const lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__3 = (const lean_object*)&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(lean_object*);
static const lean_string_object l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.TreeMap.ofList "};
static const lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__0 = (const lean_object*)&l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__1 = (const lean_object*)&l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_Check_instReprConfig_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__0 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__0_value)}};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__1 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__2 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__2_value;
static const lean_string_object l_Lake_Check_instReprConfig_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__3 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__3_value;
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__3_value)}};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__4 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__2_value),((lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__5 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__5_value;
static lean_once_cell_t l_Lake_Check_instReprConfig_repr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__6;
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__13_value)}};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__7 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__7_value;
static lean_once_cell_t l_Lake_Check_instReprConfig_repr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__8;
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__18_value)}};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__9 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lake_Check_instReprConfig_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__10;
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__23_value)}};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__11 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7_value)}};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__12 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__33_value)}};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__13 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__13_value;
static lean_once_cell_t l_Lake_Check_instReprConfig_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__14;
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_Check_instFromJsonConfig_fromJson___closed__39_value)}};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__15 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lake_Check_instReprConfig_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__16;
static const lean_string_object l_Lake_Check_instReprConfig_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__17 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__17_value;
static lean_once_cell_t l_Lake_Check_instReprConfig_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__18;
static lean_once_cell_t l_Lake_Check_instReprConfig_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__19;
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__20 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__20_value;
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__17_value)}};
static const lean_object* l_Lake_Check_instReprConfig_repr___redArg___closed__21 = (const lean_object*)&l_Lake_Check_instReprConfig_repr___redArg___closed__21_value;
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Check_instReprConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Check_instReprConfig_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Check_instReprConfig___closed__0 = (const lean_object*)&l_Lake_Check_instReprConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Check_instReprConfig = (const lean_object*)&l_Lake_Check_instReprConfig___closed__0_value;
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lake-manifest.json"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "' has no `lake-manifest.json`, and `lake "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "` resolves dependencies inside a sandbox that cannot write to the project directory. Run `lake build` there first."};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 153, .m_capacity = 153, .m_length = 152, .m_data = "` sandboxes the code it checks with `landrun`, which needs Linux Landlock. There is no unsandboxed mode, so the command is unavailable on this platform."};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "COMPARATOR_LANDRUN"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leanexport"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leanchecker"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` needs `git` on PATH to build inside the sandbox"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "landrun"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` kernel `"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` was not found"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` has an empty command"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nanoda"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "nanoda_bin"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__1_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__1_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "cannot use `enable_nanoda` and `external_kernels` at the same time; register nanoda in the list instead"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "propext"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 150, 49, 30, 125, 3, 39, 172)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__4_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__3_value),LEAN_SCALAR_PTR_LITERAL(76, 246, 154, 249, 193, 98, 251, 55)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__4_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__1_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__4_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__5_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms___closed__5_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Axiom '"};
static const lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__0_value;
static const lean_string_object l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "' is not permitted; it is used by '"};
static const lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__0_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Uses axioms: "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Uses no axioms"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Check_runChallenge___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "challenge"};
static const lean_object* l_Lake_Check_runChallenge___closed__0 = (const lean_object*)&l_Lake_Check_runChallenge___closed__0_value;
static const lean_string_object l_Lake_Check_runChallenge___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "malformed configuration in '"};
static const lean_object* l_Lake_Check_runChallenge___closed__1 = (const lean_object*)&l_Lake_Check_runChallenge___closed__1_value;
static const lean_string_object l_Lake_Check_runChallenge___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "': "};
static const lean_object* l_Lake_Check_runChallenge___closed__2 = (const lean_object*)&l_Lake_Check_runChallenge___closed__2_value;
static const lean_string_object l_Lake_Check_runChallenge___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "nothing to check: the configuration names no theorems or definitions"};
static const lean_object* l_Lake_Check_runChallenge___closed__3 = (const lean_object*)&l_Lake_Check_runChallenge___closed__3_value;
static const lean_string_object l_Lake_Check_runChallenge___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "could not read the configuration: "};
static const lean_object* l_Lake_Check_runChallenge___closed__4 = (const lean_object*)&l_Lake_Check_runChallenge___closed__4_value;
static const lean_string_object l_Lake_Check_runChallenge___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "no challenge configuration given; pass `--config <file>`"};
static const lean_object* l_Lake_Check_runChallenge___closed__5 = (const lean_object*)&l_Lake_Check_runChallenge___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_Check_runChallenge___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Check_runChallenge___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_Check_runChallenge(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runChallenge___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runCheck(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels(lean_object* v_a_1_){
_start:
{
lean_object* v_externalKernels_3_; lean_object* v___x_4_; 
v_externalKernels_3_ = lean_ctor_get(v_a_1_, 12);
lean_inc(v_externalKernels_3_);
v___x_4_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4_, 0, v_externalKernels_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels___boxed(lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels(v_a_5_);
lean_dec_ref(v_a_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getTheoremNames(lean_object* v_a_8_){
_start:
{
lean_object* v_theoremNames_10_; lean_object* v___x_11_; 
v_theoremNames_10_ = lean_ctor_get(v_a_8_, 3);
lean_inc_ref(v_theoremNames_10_);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v_theoremNames_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getTheoremNames___boxed(lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lake_CLI_Check_0__Lake_Check_getTheoremNames(v_a_12_);
lean_dec_ref(v_a_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getDefinitionNames(lean_object* v_a_15_){
_start:
{
lean_object* v_definitionNames_17_; lean_object* v___x_18_; 
v_definitionNames_17_ = lean_ctor_get(v_a_15_, 4);
lean_inc_ref(v_definitionNames_17_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v_definitionNames_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getDefinitionNames___boxed(lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Lake_CLI_Check_0__Lake_Check_getDefinitionNames(v_a_19_);
lean_dec_ref(v_a_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getProjectDir(lean_object* v_a_22_){
_start:
{
lean_object* v_projectDir_24_; lean_object* v___x_25_; 
v_projectDir_24_ = lean_ctor_get(v_a_22_, 0);
lean_inc_ref(v_projectDir_24_);
v___x_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_25_, 0, v_projectDir_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getProjectDir___boxed(lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Lake_CLI_Check_0__Lake_Check_getProjectDir(v_a_26_);
lean_dec_ref(v_a_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule(lean_object* v_a_29_){
_start:
{
lean_object* v_challengeModule_31_; lean_object* v___x_32_; 
v_challengeModule_31_ = lean_ctor_get(v_a_29_, 1);
lean_inc(v_challengeModule_31_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v_challengeModule_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule___boxed(lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule(v_a_33_);
lean_dec_ref(v_a_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule(lean_object* v_a_36_){
_start:
{
lean_object* v_solutionModule_38_; lean_object* v___x_39_; 
v_solutionModule_38_ = lean_ctor_get(v_a_36_, 2);
lean_inc(v_solutionModule_38_);
v___x_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_39_, 0, v_solutionModule_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule___boxed(lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule(v_a_40_);
lean_dec_ref(v_a_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms(lean_object* v_a_43_){
_start:
{
lean_object* v_legalAxioms_45_; lean_object* v___x_46_; 
v_legalAxioms_45_ = lean_ctor_get(v_a_43_, 5);
lean_inc_ref(v_legalAxioms_45_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v_legalAxioms_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms___boxed(lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms(v_a_47_);
lean_dec_ref(v_a_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_whichExe(lean_object* v_exe_55_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; uint8_t v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_57_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v___x_58_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__1));
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_mk_empty_array_with_capacity(v___x_59_);
v___x_61_ = lean_array_push(v___x_60_, v_exe_55_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__2));
v___x_65_ = 1;
v___x_66_ = 0;
v___x_67_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_67_, 0, v___x_57_);
lean_ctor_set(v___x_67_, 1, v___x_58_);
lean_ctor_set(v___x_67_, 2, v___x_61_);
lean_ctor_set(v___x_67_, 3, v___x_62_);
lean_ctor_set(v___x_67_, 4, v___x_64_);
lean_ctor_set_uint8(v___x_67_, sizeof(void*)*5, v___x_65_);
lean_ctor_set_uint8(v___x_67_, sizeof(void*)*5 + 1, v___x_66_);
v___x_68_ = l_IO_Process_output(v___x_67_, v___x_62_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_93_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_93_ == 0)
{
v___x_71_ = v___x_68_;
v_isShared_72_ = v_isSharedCheck_93_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_93_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
uint32_t v_exitCode_73_; lean_object* v_stdout_74_; uint32_t v___x_75_; uint8_t v___x_76_; 
v_exitCode_73_ = lean_ctor_get_uint32(v_a_69_, sizeof(void*)*2);
v_stdout_74_ = lean_ctor_get(v_a_69_, 0);
lean_inc_ref(v_stdout_74_);
lean_dec(v_a_69_);
v___x_75_ = 0;
v___x_76_ = lean_uint32_dec_eq(v_exitCode_73_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_78_; 
lean_dec_ref(v_stdout_74_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_62_);
v___x_78_ = v___x_71_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_62_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_80_ = lean_string_utf8_byte_size(v_stdout_74_);
v___x_81_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_81_, 0, v_stdout_74_);
lean_ctor_set(v___x_81_, 1, v___x_63_);
lean_ctor_set(v___x_81_, 2, v___x_80_);
v___x_82_ = l_String_Slice_trimAscii(v___x_81_);
v___x_83_ = l_String_Slice_toString(v___x_82_);
lean_dec_ref(v___x_82_);
v___x_84_ = lean_string_utf8_byte_size(v___x_83_);
v___x_85_ = lean_nat_dec_eq(v___x_84_, v___x_63_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_83_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_86_);
v___x_88_ = v___x_71_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
else
{
lean_object* v___x_91_; 
lean_dec_ref(v___x_83_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_62_);
v___x_91_ = v___x_71_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_62_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
}
else
{
lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v___x_68_, 0);
lean_dec(v_unused_101_);
v___x_95_ = v___x_68_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_dec(v___x_68_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set_tag(v___x_95_, 0);
lean_ctor_set(v___x_95_, 0, v___x_62_);
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_62_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_whichExe___boxed(lean_object* v_exe_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v_exe_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError(lean_object* v_cmd_108_, lean_object* v_exe_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_110_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__0));
v___x_111_ = lean_string_append(v___x_110_, v_cmd_108_);
v___x_112_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__1));
v___x_113_ = lean_string_append(v___x_111_, v___x_112_);
v___x_114_ = lean_string_append(v___x_113_, v_exe_109_);
v___x_115_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__2));
v___x_116_ = lean_string_append(v___x_114_, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___boxed(lean_object* v_cmd_117_, lean_object* v_exe_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError(v_cmd_117_, v_exe_118_);
lean_dec_ref(v_exe_118_);
lean_dec_ref(v_cmd_117_);
return v_res_119_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2___closed__1(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2___closed__0));
v___x_122_ = lean_unsigned_to_nat(2u);
v___x_123_ = lean_mk_empty_array_with_capacity(v___x_122_);
v___x_124_ = lean_array_push(v___x_123_, v___x_121_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2(lean_object* v_as_125_, size_t v_i_126_, size_t v_stop_127_, lean_object* v_b_128_){
_start:
{
uint8_t v___x_129_; 
v___x_129_ = lean_usize_dec_eq(v_i_126_, v_stop_127_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; size_t v___x_134_; size_t v___x_135_; 
v___x_130_ = lean_array_uget_borrowed(v_as_125_, v_i_126_);
v___x_131_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2___closed__1);
lean_inc(v___x_130_);
v___x_132_ = lean_array_push(v___x_131_, v___x_130_);
v___x_133_ = l_Array_append___redArg(v_b_128_, v___x_132_);
lean_dec_ref(v___x_132_);
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_add(v_i_126_, v___x_134_);
v_i_126_ = v___x_135_;
v_b_128_ = v___x_133_;
goto _start;
}
else
{
return v_b_128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2___boxed(lean_object* v_as_137_, lean_object* v_i_138_, lean_object* v_stop_139_, lean_object* v_b_140_){
_start:
{
size_t v_i_boxed_141_; size_t v_stop_boxed_142_; lean_object* v_res_143_; 
v_i_boxed_141_ = lean_unbox_usize(v_i_138_);
lean_dec(v_i_138_);
v_stop_boxed_142_ = lean_unbox_usize(v_stop_139_);
lean_dec(v_stop_139_);
v_res_143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2(v_as_137_, v_i_boxed_141_, v_stop_boxed_142_, v_b_140_);
lean_dec_ref(v_as_137_);
return v_res_143_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0___closed__1(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0___closed__0));
v___x_146_ = lean_unsigned_to_nat(2u);
v___x_147_ = lean_mk_empty_array_with_capacity(v___x_146_);
v___x_148_ = lean_array_push(v___x_147_, v___x_145_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0(lean_object* v_as_149_, size_t v_i_150_, size_t v_stop_151_, lean_object* v_b_152_){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = lean_usize_dec_eq(v_i_150_, v_stop_151_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; size_t v___x_158_; size_t v___x_159_; 
v___x_154_ = lean_array_uget_borrowed(v_as_149_, v_i_150_);
v___x_155_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0___closed__1);
lean_inc(v___x_154_);
v___x_156_ = lean_array_push(v___x_155_, v___x_154_);
v___x_157_ = l_Array_append___redArg(v_b_152_, v___x_156_);
lean_dec_ref(v___x_156_);
v___x_158_ = ((size_t)1ULL);
v___x_159_ = lean_usize_add(v_i_150_, v___x_158_);
v_i_150_ = v___x_159_;
v_b_152_ = v___x_157_;
goto _start;
}
else
{
return v_b_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0___boxed(lean_object* v_as_161_, lean_object* v_i_162_, lean_object* v_stop_163_, lean_object* v_b_164_){
_start:
{
size_t v_i_boxed_165_; size_t v_stop_boxed_166_; lean_object* v_res_167_; 
v_i_boxed_165_ = lean_unbox_usize(v_i_162_);
lean_dec(v_i_162_);
v_stop_boxed_166_ = lean_unbox_usize(v_stop_163_);
lean_dec(v_stop_163_);
v_res_167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0(v_as_161_, v_i_boxed_165_, v_stop_boxed_166_, v_b_164_);
lean_dec_ref(v_as_161_);
return v_res_167_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1___closed__1(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1___closed__0));
v___x_170_ = lean_unsigned_to_nat(2u);
v___x_171_ = lean_mk_empty_array_with_capacity(v___x_170_);
v___x_172_ = lean_array_push(v___x_171_, v___x_169_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1(lean_object* v_as_173_, size_t v_i_174_, size_t v_stop_175_, lean_object* v_b_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = lean_usize_dec_eq(v_i_174_, v_stop_175_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; size_t v___x_182_; size_t v___x_183_; 
v___x_178_ = lean_array_uget_borrowed(v_as_173_, v_i_174_);
v___x_179_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1___closed__1);
lean_inc(v___x_178_);
v___x_180_ = lean_array_push(v___x_179_, v___x_178_);
v___x_181_ = l_Array_append___redArg(v_b_176_, v___x_180_);
lean_dec_ref(v___x_180_);
v___x_182_ = ((size_t)1ULL);
v___x_183_ = lean_usize_add(v_i_174_, v___x_182_);
v_i_174_ = v___x_183_;
v_b_176_ = v___x_181_;
goto _start;
}
else
{
return v_b_176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1___boxed(lean_object* v_as_185_, lean_object* v_i_186_, lean_object* v_stop_187_, lean_object* v_b_188_){
_start:
{
size_t v_i_boxed_189_; size_t v_stop_boxed_190_; lean_object* v_res_191_; 
v_i_boxed_189_ = lean_unbox_usize(v_i_186_);
lean_dec(v_i_186_);
v_stop_boxed_190_ = lean_unbox_usize(v_stop_187_);
lean_dec(v_stop_187_);
v_res_191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1(v_as_185_, v_i_boxed_189_, v_stop_boxed_190_, v_b_188_);
lean_dec_ref(v_as_185_);
return v_res_191_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3___closed__1(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3___closed__0));
v___x_194_ = lean_unsigned_to_nat(2u);
v___x_195_ = lean_mk_empty_array_with_capacity(v___x_194_);
v___x_196_ = lean_array_push(v___x_195_, v___x_193_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3(lean_object* v_as_197_, size_t v_i_198_, size_t v_stop_199_, lean_object* v_b_200_){
_start:
{
uint8_t v___x_201_; 
v___x_201_ = lean_usize_dec_eq(v_i_198_, v_stop_199_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; size_t v___x_206_; size_t v___x_207_; 
v___x_202_ = lean_array_uget_borrowed(v_as_197_, v_i_198_);
v___x_203_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3___closed__1);
lean_inc(v___x_202_);
v___x_204_ = lean_array_push(v___x_203_, v___x_202_);
v___x_205_ = l_Array_append___redArg(v_b_200_, v___x_204_);
lean_dec_ref(v___x_204_);
v___x_206_ = ((size_t)1ULL);
v___x_207_ = lean_usize_add(v_i_198_, v___x_206_);
v_i_198_ = v___x_207_;
v_b_200_ = v___x_205_;
goto _start;
}
else
{
return v_b_200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3___boxed(lean_object* v_as_209_, lean_object* v_i_210_, lean_object* v_stop_211_, lean_object* v_b_212_){
_start:
{
size_t v_i_boxed_213_; size_t v_stop_boxed_214_; lean_object* v_res_215_; 
v_i_boxed_213_ = lean_unbox_usize(v_i_210_);
lean_dec(v_i_210_);
v_stop_boxed_214_ = lean_unbox_usize(v_stop_211_);
lean_dec(v_stop_211_);
v_res_215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3(v_as_209_, v_i_boxed_213_, v_stop_boxed_214_, v_b_212_);
lean_dec_ref(v_as_209_);
return v_res_215_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__1(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_217_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__0));
v___x_218_ = lean_unsigned_to_nat(2u);
v___x_219_ = lean_mk_empty_array_with_capacity(v___x_218_);
v___x_220_ = lean_array_push(v___x_219_, v___x_217_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs(lean_object* v_spawnArgs_238_){
_start:
{
lean_object* v_cmd_239_; lean_object* v_args_240_; lean_object* v_envPass_241_; lean_object* v_readablePaths_242_; lean_object* v_writablePaths_243_; lean_object* v_connectPorts_244_; lean_object* v___y_246_; lean_object* v_args_251_; lean_object* v___x_252_; lean_object* v___y_254_; lean_object* v___y_265_; lean_object* v___y_276_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_cmd_239_ = lean_ctor_get(v_spawnArgs_238_, 0);
lean_inc_ref(v_cmd_239_);
v_args_240_ = lean_ctor_get(v_spawnArgs_238_, 1);
lean_inc_ref(v_args_240_);
v_envPass_241_ = lean_ctor_get(v_spawnArgs_238_, 2);
lean_inc_ref(v_envPass_241_);
v_readablePaths_242_ = lean_ctor_get(v_spawnArgs_238_, 4);
lean_inc_ref(v_readablePaths_242_);
v_writablePaths_243_ = lean_ctor_get(v_spawnArgs_238_, 5);
lean_inc_ref(v_writablePaths_243_);
v_connectPorts_244_ = lean_ctor_get(v_spawnArgs_238_, 6);
lean_inc_ref(v_connectPorts_244_);
lean_dec_ref(v_spawnArgs_238_);
v_args_251_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__7));
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_array_get_size(v_envPass_241_);
v___x_287_ = lean_nat_dec_lt(v___x_252_, v___x_286_);
if (v___x_287_ == 0)
{
lean_dec_ref(v_envPass_241_);
v___y_276_ = v_args_251_;
goto v___jp_275_;
}
else
{
uint8_t v___x_288_; 
v___x_288_ = lean_nat_dec_le(v___x_286_, v___x_286_);
if (v___x_288_ == 0)
{
if (v___x_287_ == 0)
{
lean_dec_ref(v_envPass_241_);
v___y_276_ = v_args_251_;
goto v___jp_275_;
}
else
{
size_t v___x_289_; size_t v___x_290_; lean_object* v___x_291_; 
v___x_289_ = ((size_t)0ULL);
v___x_290_ = lean_usize_of_nat(v___x_286_);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3(v_envPass_241_, v___x_289_, v___x_290_, v_args_251_);
lean_dec_ref(v_envPass_241_);
v___y_276_ = v___x_291_;
goto v___jp_275_;
}
}
else
{
size_t v___x_292_; size_t v___x_293_; lean_object* v___x_294_; 
v___x_292_ = ((size_t)0ULL);
v___x_293_ = lean_usize_of_nat(v___x_286_);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__3(v_envPass_241_, v___x_292_, v___x_293_, v_args_251_);
lean_dec_ref(v_envPass_241_);
v___y_276_ = v___x_294_;
goto v___jp_275_;
}
}
v___jp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_247_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__1, &l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__1_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__1);
v___x_248_ = lean_array_push(v___x_247_, v_cmd_239_);
v___x_249_ = l_Array_append___redArg(v___y_246_, v___x_248_);
lean_dec_ref(v___x_248_);
v___x_250_ = l_Array_append___redArg(v___x_249_, v_args_240_);
lean_dec_ref(v_args_240_);
return v___x_250_;
}
v___jp_253_:
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_array_get_size(v_connectPorts_244_);
v___x_256_ = lean_nat_dec_lt(v___x_252_, v___x_255_);
if (v___x_256_ == 0)
{
lean_dec_ref(v_connectPorts_244_);
v___y_246_ = v___y_254_;
goto v___jp_245_;
}
else
{
uint8_t v___x_257_; 
v___x_257_ = lean_nat_dec_le(v___x_255_, v___x_255_);
if (v___x_257_ == 0)
{
if (v___x_256_ == 0)
{
lean_dec_ref(v_connectPorts_244_);
v___y_246_ = v___y_254_;
goto v___jp_245_;
}
else
{
size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; 
v___x_258_ = ((size_t)0ULL);
v___x_259_ = lean_usize_of_nat(v___x_255_);
v___x_260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0(v_connectPorts_244_, v___x_258_, v___x_259_, v___y_254_);
lean_dec_ref(v_connectPorts_244_);
v___y_246_ = v___x_260_;
goto v___jp_245_;
}
}
else
{
size_t v___x_261_; size_t v___x_262_; lean_object* v___x_263_; 
v___x_261_ = ((size_t)0ULL);
v___x_262_ = lean_usize_of_nat(v___x_255_);
v___x_263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__0(v_connectPorts_244_, v___x_261_, v___x_262_, v___y_254_);
lean_dec_ref(v_connectPorts_244_);
v___y_246_ = v___x_263_;
goto v___jp_245_;
}
}
}
v___jp_264_:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_array_get_size(v_writablePaths_243_);
v___x_267_ = lean_nat_dec_lt(v___x_252_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec_ref(v_writablePaths_243_);
v___y_254_ = v___y_265_;
goto v___jp_253_;
}
else
{
uint8_t v___x_268_; 
v___x_268_ = lean_nat_dec_le(v___x_266_, v___x_266_);
if (v___x_268_ == 0)
{
if (v___x_267_ == 0)
{
lean_dec_ref(v_writablePaths_243_);
v___y_254_ = v___y_265_;
goto v___jp_253_;
}
else
{
size_t v___x_269_; size_t v___x_270_; lean_object* v___x_271_; 
v___x_269_ = ((size_t)0ULL);
v___x_270_ = lean_usize_of_nat(v___x_266_);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1(v_writablePaths_243_, v___x_269_, v___x_270_, v___y_265_);
lean_dec_ref(v_writablePaths_243_);
v___y_254_ = v___x_271_;
goto v___jp_253_;
}
}
else
{
size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; 
v___x_272_ = ((size_t)0ULL);
v___x_273_ = lean_usize_of_nat(v___x_266_);
v___x_274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__1(v_writablePaths_243_, v___x_272_, v___x_273_, v___y_265_);
lean_dec_ref(v_writablePaths_243_);
v___y_254_ = v___x_274_;
goto v___jp_253_;
}
}
}
v___jp_275_:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_array_get_size(v_readablePaths_242_);
v___x_278_ = lean_nat_dec_lt(v___x_252_, v___x_277_);
if (v___x_278_ == 0)
{
lean_dec_ref(v_readablePaths_242_);
v___y_265_ = v___y_276_;
goto v___jp_264_;
}
else
{
uint8_t v___x_279_; 
v___x_279_ = lean_nat_dec_le(v___x_277_, v___x_277_);
if (v___x_279_ == 0)
{
if (v___x_278_ == 0)
{
lean_dec_ref(v_readablePaths_242_);
v___y_265_ = v___y_276_;
goto v___jp_264_;
}
else
{
size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; 
v___x_280_ = ((size_t)0ULL);
v___x_281_ = lean_usize_of_nat(v___x_277_);
v___x_282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2(v_readablePaths_242_, v___x_280_, v___x_281_, v___y_276_);
lean_dec_ref(v_readablePaths_242_);
v___y_265_ = v___x_282_;
goto v___jp_264_;
}
}
else
{
size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; 
v___x_283_ = ((size_t)0ULL);
v___x_284_ = lean_usize_of_nat(v___x_277_);
v___x_285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs_spec__2(v_readablePaths_242_, v___x_283_, v___x_284_, v___y_276_);
lean_dec_ref(v_readablePaths_242_);
v___y_265_ = v___x_285_;
goto v___jp_264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_landrunSpawnArgs(lean_object* v_spawnArgs_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_projectDir_298_; lean_object* v_whichLandrun_299_; lean_object* v___x_300_; lean_object* v_envOverride_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_projectDir_298_ = lean_ctor_get(v_a_296_, 0);
v_whichLandrun_299_ = lean_ctor_get(v_a_296_, 8);
v___x_300_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v_envOverride_301_ = lean_ctor_get(v_spawnArgs_295_, 3);
lean_inc_ref(v_envOverride_301_);
v___x_302_ = l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs(v_spawnArgs_295_);
lean_inc_ref(v_projectDir_298_);
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v_projectDir_298_);
v___x_304_ = 1;
v___x_305_ = 0;
lean_inc_ref(v_whichLandrun_299_);
v___x_306_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_306_, 0, v___x_300_);
lean_ctor_set(v___x_306_, 1, v_whichLandrun_299_);
lean_ctor_set(v___x_306_, 2, v___x_302_);
lean_ctor_set(v___x_306_, 3, v___x_303_);
lean_ctor_set(v___x_306_, 4, v_envOverride_301_);
lean_ctor_set_uint8(v___x_306_, sizeof(void*)*5, v___x_304_);
lean_ctor_set_uint8(v___x_306_, sizeof(void*)*5 + 1, v___x_305_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_landrunSpawnArgs___boxed(lean_object* v_spawnArgs_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lake_CLI_Check_0__Lake_Check_landrunSpawnArgs(v_spawnArgs_308_, v_a_309_);
lean_dec_ref(v_a_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0(lean_object* v_s_312_){
_start:
{
lean_object* v___x_314_; lean_object* v_putStr_315_; lean_object* v___x_316_; 
v___x_314_ = lean_get_stderr();
v_putStr_315_ = lean_ctor_get(v___x_314_, 4);
lean_inc_ref(v_putStr_315_);
lean_dec_ref(v___x_314_);
v___x_316_ = lean_apply_2(v_putStr_315_, v_s_312_, lean_box(0));
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0___boxed(lean_object* v_s_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0(v_s_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(lean_object* v_spawnArgs_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_372_; 
v___x_324_ = l___private_Lake_CLI_Check_0__Lake_Check_landrunSpawnArgs(v_spawnArgs_321_, v_a_322_);
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_372_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_372_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_372_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_box(0);
v___x_330_ = l_IO_Process_output(v_a_325_, v___x_329_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; uint32_t v_exitCode_332_; lean_object* v_stdout_333_; lean_object* v_stderr_334_; lean_object* v___x_335_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v_exitCode_332_ = lean_ctor_get_uint32(v_a_331_, sizeof(void*)*2);
v_stdout_333_ = lean_ctor_get(v_a_331_, 0);
lean_inc_ref(v_stdout_333_);
v_stderr_334_ = lean_ctor_get(v_a_331_, 1);
lean_inc_ref(v_stderr_334_);
lean_dec(v_a_331_);
v___x_335_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0(v_stderr_334_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_354_; 
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; 
v_unused_355_ = lean_ctor_get(v___x_335_, 0);
lean_dec(v_unused_355_);
v___x_337_ = v___x_335_;
v_isShared_338_ = v_isSharedCheck_354_;
goto v_resetjp_336_;
}
else
{
lean_dec(v___x_335_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_354_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
uint32_t v___x_339_; uint8_t v___x_340_; 
v___x_339_ = 0;
v___x_340_ = lean_uint32_dec_eq(v_exitCode_332_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
lean_dec_ref(v_stdout_333_);
v___x_341_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___closed__0));
v___x_342_ = lean_uint32_to_nat(v_exitCode_332_);
v___x_343_ = l_Nat_reprFast(v___x_342_);
v___x_344_ = lean_string_append(v___x_341_, v___x_343_);
lean_dec_ref(v___x_343_);
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 18);
lean_ctor_set(v___x_327_, 0, v___x_344_);
v___x_346_ = v___x_327_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_348_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set_tag(v___x_337_, 1);
lean_ctor_set(v___x_337_, 0, v___x_346_);
v___x_348_ = v___x_337_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
else
{
lean_object* v___x_352_; 
lean_del_object(v___x_327_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v_stdout_333_);
v___x_352_ = v___x_337_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_stdout_333_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec_ref(v_stdout_333_);
lean_del_object(v___x_327_);
v_a_356_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_335_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_335_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_del_object(v___x_327_);
v_a_364_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_330_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_330_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___boxed(lean_object* v_spawnArgs_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v_spawnArgs_373_, v_a_374_);
lean_dec_ref(v_a_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(lean_object* v_spawnArgs_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_380_; lean_object* v_a_381_; lean_object* v___x_382_; 
v___x_380_ = l___private_Lake_CLI_Check_0__Lake_Check_landrunSpawnArgs(v_spawnArgs_377_, v_a_378_);
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref(v___x_380_);
v___x_382_ = lean_io_process_spawn(v_a_381_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
v___x_384_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v___x_385_ = lean_io_process_child_wait(v___x_384_, v_a_383_);
lean_dec(v_a_383_);
return v___x_385_;
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v_a_386_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_382_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_382_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode___boxed(lean_object* v_spawnArgs_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v_spawnArgs_394_, v_a_395_);
lean_dec_ref(v_a_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(lean_object* v_spawnArgs_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v_spawnArgs_398_, v_a_399_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_422_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_422_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_422_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_422_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
uint32_t v___x_406_; uint32_t v___x_407_; uint8_t v___x_408_; 
v___x_406_ = 0;
v___x_407_ = lean_unbox_uint32(v_a_402_);
v___x_408_ = lean_uint32_dec_eq(v___x_407_, v___x_406_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; uint32_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_409_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___closed__0));
v___x_410_ = lean_unbox_uint32(v_a_402_);
lean_dec(v_a_402_);
v___x_411_ = lean_uint32_to_nat(v___x_410_);
v___x_412_ = l_Nat_reprFast(v___x_411_);
v___x_413_ = lean_string_append(v___x_409_, v___x_412_);
lean_dec_ref(v___x_412_);
v___x_414_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 1);
lean_ctor_set(v___x_404_, 0, v___x_414_);
v___x_416_ = v___x_404_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
else
{
lean_object* v___x_418_; lean_object* v___x_420_; 
lean_dec(v_a_402_);
v___x_418_ = lean_box(0);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_418_);
v___x_420_ = v___x_404_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
v_a_423_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_401_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_401_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed___boxed(lean_object* v_spawnArgs_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v_spawnArgs_431_, v_a_432_);
lean_dec_ref(v_a_432_);
return v_res_434_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0));
v___x_437_ = lean_string_utf8_byte_size(v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(lean_object* v_s_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_439_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0));
v___x_440_ = lean_string_utf8_byte_size(v_s_438_);
v___x_441_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1);
v___x_442_ = lean_nat_dec_le(v___x_441_, v___x_440_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
lean_dec_ref(v_s_438_);
v___x_443_ = lean_box(0);
return v___x_443_;
}
else
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_string_memcmp(v_s_438_, v___x_439_, v___x_444_, v___x_444_, v___x_441_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
lean_dec_ref(v_s_438_);
v___x_446_ = lean_box(0);
return v___x_446_;
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
lean_inc_ref(v_s_438_);
v___x_447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_447_, 0, v_s_438_);
lean_ctor_set(v___x_447_, 1, v___x_444_);
lean_ctor_set(v___x_447_, 2, v___x_440_);
v___x_448_ = l_String_Slice_pos_x21(v___x_447_, v___x_441_);
lean_dec_ref_known(v___x_447_, 3);
v___x_449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_449_, 0, v_s_438_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
lean_ctor_set(v___x_449_, 2, v___x_440_);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(lean_object* v_s_451_, lean_object* v_pat_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_s_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___boxed(lean_object* v_s_454_, lean_object* v_pat_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(v_s_454_, v_pat_455_);
lean_dec_ref(v_pat_455_);
return v_res_456_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0));
v___x_459_ = lean_string_utf8_byte_size(v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(lean_object* v_s_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_461_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0));
v___x_462_ = lean_string_utf8_byte_size(v_s_460_);
v___x_463_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1);
v___x_464_ = lean_nat_dec_le(v___x_463_, v___x_462_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; 
lean_dec_ref(v_s_460_);
v___x_465_ = lean_box(0);
return v___x_465_;
}
else
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_string_memcmp(v_s_460_, v___x_461_, v___x_466_, v___x_466_, v___x_463_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_dec_ref(v_s_460_);
v___x_468_ = lean_box(0);
return v___x_468_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
lean_inc_ref(v_s_460_);
v___x_469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_469_, 0, v_s_460_);
lean_ctor_set(v___x_469_, 1, v___x_466_);
lean_ctor_set(v___x_469_, 2, v___x_462_);
v___x_470_ = l_String_Slice_pos_x21(v___x_469_, v___x_463_);
lean_dec_ref_known(v___x_469_, 3);
v___x_471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_471_, 0, v_s_460_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
lean_ctor_set(v___x_471_, 2, v___x_462_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(lean_object* v_s_473_, lean_object* v_pat_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_s_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___boxed(lean_object* v_s_476_, lean_object* v_pat_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(v_s_476_, v_pat_477_);
lean_dec_ref(v_pat_477_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(lean_object* v_s_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0));
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___boxed(lean_object* v_s_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(v_s_483_);
lean_dec_ref(v_s_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(lean_object* v_a_485_, lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v_a_488_, lean_object* v_b_489_){
_start:
{
lean_object* v_it_491_; lean_object* v_startInclusive_492_; lean_object* v_endExclusive_493_; 
if (lean_obj_tag(v_a_488_) == 0)
{
lean_object* v_currPos_498_; lean_object* v_searcher_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_522_; 
v_currPos_498_ = lean_ctor_get(v_a_488_, 0);
v_searcher_499_ = lean_ctor_get(v_a_488_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_a_488_);
if (v_isSharedCheck_522_ == 0)
{
v___x_501_ = v_a_488_;
v_isShared_502_ = v_isSharedCheck_522_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_searcher_499_);
lean_inc(v_currPos_498_);
lean_dec(v_a_488_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_522_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
uint8_t v_decide_503_; 
v_decide_503_ = lean_nat_dec_eq(v_searcher_499_, v___x_487_);
if (v_decide_503_ == 0)
{
uint32_t v___x_504_; uint32_t v___x_505_; uint8_t v___x_506_; 
v___x_504_ = 10;
v___x_505_ = lean_string_utf8_get_fast(v_a_485_, v_searcher_499_);
v___x_506_ = lean_uint32_dec_eq(v___x_505_, v___x_504_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = lean_string_utf8_next_fast(v_a_485_, v_searcher_499_);
lean_dec(v_searcher_499_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v___x_507_);
v___x_509_ = v___x_501_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_currPos_498_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_507_);
v___x_509_ = v_reuseFailAlloc_511_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
v_a_488_ = v___x_509_;
goto _start;
}
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_slice_515_; lean_object* v_nextIt_517_; 
v___x_512_ = lean_string_utf8_next_fast(v_a_485_, v_searcher_499_);
v___x_513_ = lean_nat_sub(v___x_512_, v_searcher_499_);
v___x_514_ = lean_nat_add(v_searcher_499_, v___x_513_);
lean_dec(v___x_513_);
v_slice_515_ = l_String_Slice_subslice_x21(v___x_486_, v_currPos_498_, v_searcher_499_);
lean_inc(v___x_514_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v___x_514_);
lean_ctor_set(v___x_501_, 0, v___x_514_);
v_nextIt_517_ = v___x_501_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v___x_514_);
v_nextIt_517_ = v_reuseFailAlloc_520_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v_startInclusive_518_; lean_object* v_endExclusive_519_; 
v_startInclusive_518_ = lean_ctor_get(v_slice_515_, 0);
lean_inc(v_startInclusive_518_);
v_endExclusive_519_ = lean_ctor_get(v_slice_515_, 1);
lean_inc(v_endExclusive_519_);
lean_dec_ref(v_slice_515_);
v_it_491_ = v_nextIt_517_;
v_startInclusive_492_ = v_startInclusive_518_;
v_endExclusive_493_ = v_endExclusive_519_;
goto v___jp_490_;
}
}
}
else
{
lean_object* v___x_521_; 
lean_del_object(v___x_501_);
lean_dec(v_searcher_499_);
v___x_521_ = lean_box(1);
lean_inc(v___x_487_);
v_it_491_ = v___x_521_;
v_startInclusive_492_ = v_currPos_498_;
v_endExclusive_493_ = v___x_487_;
goto v___jp_490_;
}
}
}
else
{
lean_dec(v___x_487_);
lean_dec_ref(v_a_485_);
return v_b_489_;
}
v___jp_490_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
lean_inc_ref(v_a_485_);
v___x_494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_494_, 0, v_a_485_);
lean_ctor_set(v___x_494_, 1, v_startInclusive_492_);
lean_ctor_set(v___x_494_, 2, v_endExclusive_493_);
v___x_495_ = l_String_Slice_toString(v___x_494_);
lean_dec_ref_known(v___x_494_, 3);
v___x_496_ = lean_array_push(v_b_489_, v___x_495_);
v_a_488_ = v_it_491_;
v_b_489_ = v___x_496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg___boxed(lean_object* v_a_523_, lean_object* v___x_524_, lean_object* v___x_525_, lean_object* v_a_526_, lean_object* v_b_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_523_, v___x_524_, v___x_525_, v_a_526_, v_b_527_);
lean_dec_ref(v___x_524_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(lean_object* v_as_x27_529_, lean_object* v_b_530_){
_start:
{
if (lean_obj_tag(v_as_x27_529_) == 0)
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v_b_530_);
return v___x_532_;
}
else
{
lean_object* v_head_533_; lean_object* v_tail_534_; lean_object* v_fst_535_; lean_object* v_snd_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_558_; 
v_head_533_ = lean_ctor_get(v_as_x27_529_, 0);
v_tail_534_ = lean_ctor_get(v_as_x27_529_, 1);
v_fst_535_ = lean_ctor_get(v_b_530_, 0);
v_snd_536_ = lean_ctor_get(v_b_530_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_b_530_);
if (v_isSharedCheck_558_ == 0)
{
v___x_538_ = v_b_530_;
v_isShared_539_ = v_isSharedCheck_558_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_snd_536_);
lean_inc(v_fst_535_);
lean_dec(v_b_530_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_558_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; 
lean_inc(v_head_533_);
v___x_540_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_head_533_);
if (lean_obj_tag(v___x_540_) == 1)
{
lean_object* v_val_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
lean_dec(v_fst_535_);
v_val_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_val_541_);
lean_dec_ref_known(v___x_540_, 1);
v___x_542_ = l_String_Slice_toString(v_val_541_);
lean_dec(v_val_541_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_542_);
v___x_544_ = v___x_538_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_snd_536_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
v_as_x27_529_ = v_tail_534_;
v_b_530_ = v___x_544_;
goto _start;
}
}
else
{
lean_object* v___x_547_; 
lean_dec(v___x_540_);
lean_inc(v_head_533_);
v___x_547_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_head_533_);
if (lean_obj_tag(v___x_547_) == 1)
{
lean_object* v_val_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
lean_dec(v_snd_536_);
v_val_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_val_548_);
lean_dec_ref_known(v___x_547_, 1);
v___x_549_ = l_String_Slice_toString(v_val_548_);
lean_dec(v_val_548_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_549_);
v___x_551_ = v___x_538_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_fst_535_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_549_);
v___x_551_ = v_reuseFailAlloc_553_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
v_as_x27_529_ = v_tail_534_;
v_b_530_ = v___x_551_;
goto _start;
}
}
else
{
lean_object* v___x_555_; 
lean_dec(v___x_547_);
if (v_isShared_539_ == 0)
{
v___x_555_ = v___x_538_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_fst_535_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_snd_536_);
v___x_555_ = v_reuseFailAlloc_557_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
v_as_x27_529_ = v_tail_534_;
v_b_530_ = v___x_555_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg___boxed(lean_object* v_as_x27_559_, lean_object* v_b_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_559_, v_b_560_);
lean_dec(v_as_x27_559_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(lean_object* v_s_563_){
_start:
{
lean_object* v___x_565_; lean_object* v_putStr_566_; lean_object* v___x_567_; 
v___x_565_ = lean_get_stdout();
v_putStr_566_ = lean_ctor_get(v___x_565_, 4);
lean_inc_ref(v_putStr_566_);
lean_dec_ref(v___x_565_);
v___x_567_ = lean_apply_2(v_putStr_566_, v_s_563_, lean_box(0));
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2___boxed(lean_object* v_s_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v_s_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(lean_object* v_s_571_){
_start:
{
uint32_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = 10;
v___x_574_ = lean_string_push(v_s_571_, v___x_573_);
v___x_575_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2___boxed(lean_object* v_s_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v_s_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(lean_object* v_a_623_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_629_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_628_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_projectDir_630_; lean_object* v_whichLake_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___y_635_; lean_object* v_whichLake_636_; uint8_t v___x_686_; 
lean_dec_ref_known(v___x_629_, 1);
v_projectDir_630_ = lean_ctor_get(v_a_623_, 0);
v_whichLake_631_ = lean_ctor_get(v_a_623_, 9);
v___x_632_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_630_);
v___x_633_ = l_System_FilePath_join(v_projectDir_630_, v___x_632_);
v___x_686_ = l_System_FilePath_pathExists(v___x_633_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
v___x_687_ = lean_io_create_dir(v___x_633_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_dec_ref_known(v___x_687_, 1);
v___y_635_ = v_a_623_;
v_whichLake_636_ = v_whichLake_631_;
goto v___jp_634_;
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref(v___x_633_);
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
v___y_635_ = v_a_623_;
v_whichLake_636_ = v_whichLake_631_;
goto v___jp_634_;
}
v___jp_634_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = lean_mk_empty_array_with_capacity(v___x_637_);
v___x_639_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__5));
v___x_640_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__9));
v___x_641_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
lean_inc_ref(v_projectDir_630_);
lean_inc_ref(v___x_638_);
v___x_642_ = lean_array_push(v___x_638_, v_projectDir_630_);
v___x_643_ = lean_array_push(v___x_638_, v___x_633_);
v___x_644_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__16));
lean_inc_ref(v_whichLake_636_);
v___x_645_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_645_, 0, v_whichLake_636_);
lean_ctor_set(v___x_645_, 1, v___x_639_);
lean_ctor_set(v___x_645_, 2, v___x_640_);
lean_ctor_set(v___x_645_, 3, v___x_641_);
lean_ctor_set(v___x_645_, 4, v___x_642_);
lean_ctor_set(v___x_645_, 5, v___x_643_);
lean_ctor_set(v___x_645_, 6, v___x_644_);
v___x_646_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v___x_645_, v___y_635_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_677_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc_n(v_a_647_, 2);
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_string_utf8_byte_size(v_a_647_);
v___x_650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_650_, 0, v_a_647_);
lean_ctor_set(v___x_650_, 1, v___x_648_);
lean_ctor_set(v___x_650_, 2, v___x_649_);
v___x_651_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(v___x_650_);
v___x_652_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18));
v___x_653_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_647_, v___x_650_, v___x_649_, v___x_651_, v___x_652_);
lean_dec_ref_known(v___x_650_, 3);
v___x_654_ = lean_array_to_list(v___x_653_);
v___x_655_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__19));
v___x_656_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v___x_654_, v___x_655_);
lean_dec(v___x_654_);
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_677_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_677_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_677_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_fst_661_; lean_object* v_snd_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_676_; 
v_fst_661_ = lean_ctor_get(v_a_657_, 0);
v_snd_662_ = lean_ctor_get(v_a_657_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_a_657_);
if (v_isSharedCheck_676_ == 0)
{
v___x_664_ = v_a_657_;
v_isShared_665_ = v_isSharedCheck_676_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_snd_662_);
lean_inc(v_fst_661_);
lean_dec(v_a_657_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_676_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_string_utf8_byte_size(v_fst_661_);
v___x_667_ = lean_nat_dec_eq(v___x_666_, v___x_648_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_string_utf8_byte_size(v_snd_662_);
v___x_669_ = lean_nat_dec_eq(v___x_668_, v___x_648_);
if (v___x_669_ == 0)
{
lean_object* v___x_671_; 
if (v_isShared_665_ == 0)
{
v___x_671_ = v___x_664_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_fst_661_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_snd_662_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_673_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_671_);
v___x_673_ = v___x_659_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
else
{
lean_del_object(v___x_664_);
lean_dec(v_snd_662_);
lean_dec(v_fst_661_);
lean_del_object(v___x_659_);
goto v___jp_625_;
}
}
else
{
lean_del_object(v___x_664_);
lean_dec(v_snd_662_);
lean_dec(v_fst_661_);
lean_del_object(v___x_659_);
goto v___jp_625_;
}
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
v_a_678_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_646_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_646_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_a_696_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_629_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_629_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
v___jp_625_:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__1));
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___boxed(lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v_a_704_);
lean_dec_ref(v_a_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(lean_object* v_a_707_, lean_object* v___x_708_, lean_object* v___x_709_, lean_object* v_inst_710_, lean_object* v_R_711_, lean_object* v_a_712_, lean_object* v_b_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_707_, v___x_708_, v___x_709_, v_a_712_, v_b_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___boxed(lean_object* v_a_715_, lean_object* v___x_716_, lean_object* v___x_717_, lean_object* v_inst_718_, lean_object* v_R_719_, lean_object* v_a_720_, lean_object* v_b_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(v_a_715_, v___x_716_, v___x_717_, v_inst_718_, v_R_719_, v_a_720_, v_b_721_);
lean_dec_ref(v___x_716_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(lean_object* v_as_723_, lean_object* v_as_x27_724_, lean_object* v_b_725_, lean_object* v_a_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_724_, v_b_725_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___boxed(lean_object* v_as_730_, lean_object* v_as_x27_731_, lean_object* v_b_732_, lean_object* v_a_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(v_as_730_, v_as_x27_731_, v_b_732_, v_a_733_, v___y_734_);
lean_dec_ref(v___y_734_);
lean_dec(v_as_x27_731_);
lean_dec(v_as_730_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(lean_object* v_a_742_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_745_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_744_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_projectDir_746_; lean_object* v_whichLake_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___y_751_; lean_object* v_whichLake_752_; uint8_t v___x_763_; 
lean_dec_ref_known(v___x_745_, 1);
v_projectDir_746_ = lean_ctor_get(v_a_742_, 0);
v_whichLake_747_ = lean_ctor_get(v_a_742_, 9);
v___x_748_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_746_);
v___x_749_ = l_System_FilePath_join(v_projectDir_746_, v___x_748_);
v___x_763_ = l_System_FilePath_pathExists(v___x_749_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
v___x_764_ = lean_io_create_dir(v___x_749_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_dec_ref_known(v___x_764_, 1);
v___y_751_ = v_a_742_;
v_whichLake_752_ = v_whichLake_747_;
goto v___jp_750_;
}
else
{
lean_dec_ref(v___x_749_);
return v___x_764_;
}
}
else
{
v___y_751_ = v_a_742_;
v_whichLake_752_ = v_whichLake_747_;
goto v___jp_750_;
}
v___jp_750_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_mk_empty_array_with_capacity(v___x_753_);
v___x_755_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__1));
v___x_756_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__9));
v___x_757_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
lean_inc_ref(v_projectDir_746_);
lean_inc_ref(v___x_754_);
v___x_758_ = lean_array_push(v___x_754_, v_projectDir_746_);
v___x_759_ = lean_array_push(v___x_754_, v___x_749_);
v___x_760_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__16));
lean_inc_ref(v_whichLake_752_);
v___x_761_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_761_, 0, v_whichLake_752_);
lean_ctor_set(v___x_761_, 1, v___x_755_);
lean_ctor_set(v___x_761_, 2, v___x_756_);
lean_ctor_set(v___x_761_, 3, v___x_757_);
lean_ctor_set(v___x_761_, 4, v___x_758_);
lean_ctor_set(v___x_761_, 5, v___x_759_);
lean_ctor_set(v___x_761_, 6, v___x_760_);
v___x_762_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_761_, v___y_751_);
return v___x_762_;
}
}
else
{
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___boxed(lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_765_);
lean_dec_ref(v_a_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport(lean_object* v_a_784_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__0));
v___x_787_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_786_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_projectDir_788_; lean_object* v_whichLake_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec_ref_known(v___x_787_, 1);
v_projectDir_788_ = lean_ctor_get(v_a_784_, 0);
v_whichLake_789_ = lean_ctor_get(v_a_784_, 9);
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_mk_empty_array_with_capacity(v___x_790_);
v___x_792_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__2));
v___x_793_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__9));
v___x_794_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__5));
lean_inc_ref_n(v_projectDir_788_, 2);
lean_inc_ref(v___x_791_);
v___x_795_ = lean_array_push(v___x_791_, v_projectDir_788_);
v___x_796_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
v___x_797_ = l_System_FilePath_join(v_projectDir_788_, v___x_796_);
v___x_798_ = lean_array_push(v___x_791_, v___x_797_);
v___x_799_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18));
lean_inc_ref(v_whichLake_789_);
v___x_800_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_800_, 0, v_whichLake_789_);
lean_ctor_set(v___x_800_, 1, v___x_792_);
lean_ctor_set(v___x_800_, 2, v___x_793_);
lean_ctor_set(v___x_800_, 3, v___x_794_);
lean_ctor_set(v___x_800_, 4, v___x_795_);
lean_ctor_set(v___x_800_, 5, v___x_798_);
lean_ctor_set(v___x_800_, 6, v___x_799_);
v___x_801_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v___x_800_, v_a_784_);
return v___x_801_;
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
v_a_802_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_787_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_787_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___boxed(lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport(v_a_810_);
lean_dec_ref(v_a_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(size_t v_sz_813_, size_t v_i_814_, lean_object* v_bs_815_){
_start:
{
uint8_t v___x_816_; 
v___x_816_ = lean_usize_dec_lt(v_i_814_, v_sz_813_);
if (v___x_816_ == 0)
{
return v_bs_815_;
}
else
{
lean_object* v_v_817_; lean_object* v___x_818_; lean_object* v_bs_x27_819_; lean_object* v___x_820_; size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
v_v_817_ = lean_array_uget(v_bs_815_, v_i_814_);
v___x_818_ = lean_unsigned_to_nat(0u);
v_bs_x27_819_ = lean_array_uset(v_bs_815_, v_i_814_, v___x_818_);
v___x_820_ = l_Lean_Name_toString(v_v_817_, v___x_816_);
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_add(v_i_814_, v___x_821_);
v___x_823_ = lean_array_uset(v_bs_x27_819_, v_i_814_, v___x_820_);
v_i_814_ = v___x_822_;
v_bs_815_ = v___x_823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0___boxed(lean_object* v_sz_825_, lean_object* v_i_826_, lean_object* v_bs_827_){
_start:
{
size_t v_sz_boxed_828_; size_t v_i_boxed_829_; lean_object* v_res_830_; 
v_sz_boxed_828_ = lean_unbox_usize(v_sz_825_);
lean_dec(v_sz_825_);
v_i_boxed_829_ = lean_unbox_usize(v_i_826_);
lean_dec(v_i_826_);
v_res_830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_boxed_828_, v_i_boxed_829_, v_bs_827_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(lean_object* v_targets_838_, lean_object* v_a_839_){
_start:
{
size_t v_sz_841_; size_t v___x_842_; lean_object* v_targetArgs_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_targetList_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_sz_841_ = lean_array_size(v_targets_838_);
v___x_842_ = ((size_t)0ULL);
v_targetArgs_843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_841_, v___x_842_, v_targets_838_);
v___x_844_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
lean_inc_ref(v_targetArgs_843_);
v___x_845_ = lean_array_to_list(v_targetArgs_843_);
v_targetList_846_ = l_String_intercalate(v___x_844_, v___x_845_);
v___x_847_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1));
v___x_848_ = lean_string_append(v___x_847_, v_targetList_846_);
lean_dec_ref(v_targetList_846_);
v___x_849_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_848_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_projectDir_850_; lean_object* v_whichLake_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___y_855_; lean_object* v_whichLake_856_; uint8_t v___x_868_; 
lean_dec_ref_known(v___x_849_, 1);
v_projectDir_850_ = lean_ctor_get(v_a_839_, 0);
v_whichLake_851_ = lean_ctor_get(v_a_839_, 9);
v___x_852_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_850_);
v___x_853_ = l_System_FilePath_join(v_projectDir_850_, v___x_852_);
v___x_868_ = l_System_FilePath_pathExists(v___x_853_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
v___x_869_ = lean_io_create_dir(v___x_853_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_dec_ref_known(v___x_869_, 1);
v___y_855_ = v_a_839_;
v_whichLake_856_ = v_whichLake_851_;
goto v___jp_854_;
}
else
{
lean_dec_ref(v___x_853_);
lean_dec_ref(v_targetArgs_843_);
return v___x_869_;
}
}
else
{
v___y_855_ = v_a_839_;
v_whichLake_856_ = v_whichLake_851_;
goto v___jp_854_;
}
v___jp_854_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_857_ = lean_unsigned_to_nat(1u);
v___x_858_ = lean_mk_empty_array_with_capacity(v___x_857_);
v___x_859_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3));
v___x_860_ = l_Array_append___redArg(v___x_859_, v_targetArgs_843_);
lean_dec_ref(v_targetArgs_843_);
v___x_861_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__9));
v___x_862_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
lean_inc_ref(v_projectDir_850_);
lean_inc_ref(v___x_858_);
v___x_863_ = lean_array_push(v___x_858_, v_projectDir_850_);
v___x_864_ = lean_array_push(v___x_858_, v___x_853_);
v___x_865_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18));
lean_inc_ref(v_whichLake_856_);
v___x_866_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_866_, 0, v_whichLake_856_);
lean_ctor_set(v___x_866_, 1, v___x_860_);
lean_ctor_set(v___x_866_, 2, v___x_861_);
lean_ctor_set(v___x_866_, 3, v___x_862_);
lean_ctor_set(v___x_866_, 4, v___x_863_);
lean_ctor_set(v___x_866_, 5, v___x_864_);
lean_ctor_set(v___x_866_, 6, v___x_865_);
v___x_867_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_866_, v___y_855_);
return v___x_867_;
}
}
else
{
lean_dec_ref(v_targetArgs_843_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___boxed(lean_object* v_targets_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v_targets_870_, v_a_871_);
lean_dec_ref(v_a_871_);
return v_res_873_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__2(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_885_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_886_ = lean_unsigned_to_nat(3u);
v___x_887_ = lean_mk_empty_array_with_capacity(v___x_886_);
v___x_888_ = lean_array_push(v___x_887_, v___x_885_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExporter(lean_object* v_args_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_projectDir_892_; lean_object* v_leanPath_893_; lean_object* v_binPath_894_; lean_object* v_whichLean4Export_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_projectDir_892_ = lean_ctor_get(v_a_890_, 0);
v_leanPath_893_ = lean_ctor_get(v_a_890_, 6);
v_binPath_894_ = lean_ctor_get(v_a_890_, 7);
v_whichLean4Export_895_ = lean_ctor_get(v_a_890_, 10);
v___x_896_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6));
v___x_897_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__0));
v___x_898_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__1));
lean_inc_ref(v_leanPath_893_);
v___x_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_899_, 0, v_leanPath_893_);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_897_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
lean_inc_ref(v_binPath_894_);
v___x_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_901_, 0, v_binPath_894_);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_896_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExporter___closed__2);
v___x_904_ = lean_array_push(v___x_903_, v___x_900_);
v___x_905_ = lean_array_push(v___x_904_, v___x_902_);
v___x_906_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref_n(v_projectDir_892_, 2);
v___x_907_ = l_System_FilePath_join(v_projectDir_892_, v___x_906_);
v___x_908_ = lean_unsigned_to_nat(2u);
v___x_909_ = lean_mk_empty_array_with_capacity(v___x_908_);
v___x_910_ = lean_array_push(v___x_909_, v_projectDir_892_);
v___x_911_ = lean_array_push(v___x_910_, v___x_907_);
v___x_912_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18));
lean_inc_ref(v_whichLean4Export_895_);
v___x_913_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_913_, 0, v_whichLean4Export_895_);
lean_ctor_set(v___x_913_, 1, v_args_889_);
lean_ctor_set(v___x_913_, 2, v___x_898_);
lean_ctor_set(v___x_913_, 3, v___x_905_);
lean_ctor_set(v___x_913_, 4, v___x_911_);
lean_ctor_set(v___x_913_, 5, v___x_912_);
lean_ctor_set(v___x_913_, 6, v___x_912_);
v___x_914_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v___x_913_, v_a_890_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExporter___boxed(lean_object* v_args_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Lake_CLI_Check_0__Lake_Check_runExporter(v_args_915_, v_a_916_);
lean_dec_ref(v_a_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__1(size_t v_sz_919_, size_t v_i_920_, lean_object* v_bs_921_){
_start:
{
uint8_t v___x_922_; 
v___x_922_ = lean_usize_dec_lt(v_i_920_, v_sz_919_);
if (v___x_922_ == 0)
{
return v_bs_921_;
}
else
{
lean_object* v_v_923_; lean_object* v___x_924_; lean_object* v_bs_x27_925_; lean_object* v___x_926_; size_t v___x_927_; size_t v___x_928_; lean_object* v___x_929_; 
v_v_923_ = lean_array_uget(v_bs_921_, v_i_920_);
v___x_924_ = lean_unsigned_to_nat(0u);
v_bs_x27_925_ = lean_array_uset(v_bs_921_, v_i_920_, v___x_924_);
v___x_926_ = l_Lean_Name_toString(v_v_923_, v___x_922_);
v___x_927_ = ((size_t)1ULL);
v___x_928_ = lean_usize_add(v_i_920_, v___x_927_);
v___x_929_ = lean_array_uset(v_bs_x27_925_, v_i_920_, v___x_926_);
v_i_920_ = v___x_928_;
v_bs_921_ = v___x_929_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__1___boxed(lean_object* v_sz_931_, lean_object* v_i_932_, lean_object* v_bs_933_){
_start:
{
size_t v_sz_boxed_934_; size_t v_i_boxed_935_; lean_object* v_res_936_; 
v_sz_boxed_934_ = lean_unbox_usize(v_sz_931_);
lean_dec(v_sz_931_);
v_i_boxed_935_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__1(v_sz_boxed_934_, v_i_boxed_935_, v_bs_933_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0_spec__0(lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
if (lean_obj_tag(v_x_939_) == 0)
{
return v_x_938_;
}
else
{
lean_object* v_head_940_; lean_object* v_tail_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_head_940_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_head_940_);
v_tail_941_ = lean_ctor_get(v_x_939_, 1);
lean_inc(v_tail_941_);
lean_dec_ref_known(v_x_939_, 2);
v___x_942_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0_spec__0___closed__0));
v___x_943_ = lean_string_append(v_x_938_, v___x_942_);
v___x_944_ = 1;
v___x_945_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_940_, v___x_944_);
v___x_946_ = lean_string_append(v___x_943_, v___x_945_);
lean_dec_ref(v___x_945_);
v_x_938_ = v___x_946_;
v_x_939_ = v_tail_941_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0(lean_object* v_x_951_){
_start:
{
if (lean_obj_tag(v_x_951_) == 0)
{
lean_object* v___x_952_; 
v___x_952_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__0));
return v___x_952_;
}
else
{
lean_object* v_tail_953_; 
v_tail_953_ = lean_ctor_get(v_x_951_, 1);
if (lean_obj_tag(v_tail_953_) == 0)
{
lean_object* v_head_954_; lean_object* v___x_955_; uint8_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_head_954_ = lean_ctor_get(v_x_951_, 0);
lean_inc(v_head_954_);
lean_dec_ref_known(v_x_951_, 2);
v___x_955_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__1));
v___x_956_ = 1;
v___x_957_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_954_, v___x_956_);
v___x_958_ = lean_string_append(v___x_955_, v___x_957_);
lean_dec_ref(v___x_957_);
v___x_959_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__2));
v___x_960_ = lean_string_append(v___x_958_, v___x_959_);
return v___x_960_;
}
else
{
lean_object* v_head_961_; lean_object* v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint32_t v___x_967_; lean_object* v___x_968_; 
lean_inc(v_tail_953_);
v_head_961_ = lean_ctor_get(v_x_951_, 0);
lean_inc(v_head_961_);
lean_dec_ref_known(v_x_951_, 2);
v___x_962_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__1));
v___x_963_ = 1;
v___x_964_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_961_, v___x_963_);
v___x_965_ = lean_string_append(v___x_962_, v___x_964_);
lean_dec_ref(v___x_964_);
v___x_966_ = l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0_spec__0(v___x_965_, v_tail_953_);
v___x_967_ = 93;
v___x_968_ = lean_string_push(v___x_966_, v___x_967_);
return v___x_968_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport(lean_object* v_module_972_, lean_object* v_decls_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_976_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__0));
v___x_977_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__1));
lean_inc_ref(v_decls_973_);
v___x_978_ = lean_array_to_list(v_decls_973_);
v___x_979_ = l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0(v___x_978_);
v___x_980_ = lean_string_append(v___x_977_, v___x_979_);
lean_dec_ref(v___x_979_);
v___x_981_ = lean_string_append(v___x_976_, v___x_980_);
lean_dec_ref(v___x_980_);
v___x_982_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__2));
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
v___x_984_ = 1;
lean_inc(v_module_972_);
v___x_985_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_972_, v___x_984_);
v___x_986_ = lean_string_append(v___x_983_, v___x_985_);
lean_dec_ref(v___x_985_);
v___x_987_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_986_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; size_t v_sz_994_; size_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec_ref_known(v___x_987_, 1);
v___x_988_ = l_Lean_Name_toString(v_module_972_, v___x_984_);
v___x_989_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__0));
v___x_990_ = lean_unsigned_to_nat(2u);
v___x_991_ = lean_mk_empty_array_with_capacity(v___x_990_);
v___x_992_ = lean_array_push(v___x_991_, v___x_988_);
v___x_993_ = lean_array_push(v___x_992_, v___x_989_);
v_sz_994_ = lean_array_size(v_decls_973_);
v___x_995_ = ((size_t)0ULL);
v___x_996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__1(v_sz_994_, v___x_995_, v_decls_973_);
v___x_997_ = l_Array_append___redArg(v___x_993_, v___x_996_);
lean_dec_ref(v___x_996_);
v___x_998_ = l___private_Lake_CLI_Check_0__Lake_Check_runExporter(v___x_997_, v_a_974_);
return v___x_998_;
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref(v_decls_973_);
lean_dec(v_module_972_);
v_a_999_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_987_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_987_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport___boxed(lean_object* v_module_1007_, lean_object* v_decls_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lake_CLI_Check_0__Lake_Check_safeExport(v_module_1007_, v_decls_1008_, v_a_1009_);
lean_dec_ref(v_a_1009_);
return v_res_1011_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(lean_object* v_s_1012_, lean_object* v_a_1013_, uint8_t v_b_1014_){
_start:
{
uint8_t v___x_1015_; 
v___x_1015_ = 0;
switch(lean_obj_tag(v_a_1013_))
{
case 0:
{
lean_object* v_pos_1016_; lean_object* v_startInclusive_1017_; lean_object* v_endExclusive_1018_; lean_object* v___x_1019_; uint8_t v_decide_1020_; 
v_pos_1016_ = lean_ctor_get(v_a_1013_, 0);
lean_inc(v_pos_1016_);
lean_dec_ref_known(v_a_1013_, 1);
v_startInclusive_1017_ = lean_ctor_get(v_s_1012_, 1);
v_endExclusive_1018_ = lean_ctor_get(v_s_1012_, 2);
v___x_1019_ = lean_nat_sub(v_endExclusive_1018_, v_startInclusive_1017_);
v_decide_1020_ = lean_nat_dec_eq(v_pos_1016_, v___x_1019_);
lean_dec(v___x_1019_);
lean_dec(v_pos_1016_);
if (v_decide_1020_ == 0)
{
uint8_t v___x_1021_; 
v___x_1021_ = 1;
return v___x_1021_;
}
else
{
return v_decide_1020_;
}
}
case 1:
{
lean_object* v_pos_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1035_; 
v_pos_1022_ = lean_ctor_get(v_a_1013_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_a_1013_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1024_ = v_a_1013_;
v_isShared_1025_ = v_isSharedCheck_1035_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_pos_1022_);
lean_dec(v_a_1013_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1035_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v_str_1026_; lean_object* v_startInclusive_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v_str_1026_ = lean_ctor_get(v_s_1012_, 0);
v_startInclusive_1027_ = lean_ctor_get(v_s_1012_, 1);
v___x_1028_ = lean_nat_add(v_startInclusive_1027_, v_pos_1022_);
lean_dec(v_pos_1022_);
v___x_1029_ = lean_string_utf8_next_fast(v_str_1026_, v___x_1028_);
lean_dec(v___x_1028_);
v___x_1030_ = lean_nat_sub(v___x_1029_, v_startInclusive_1027_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1030_);
v___x_1032_ = v___x_1024_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
v_a_1013_ = v___x_1032_;
v_b_1014_ = v___x_1015_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1036_; lean_object* v_table_1037_; lean_object* v_stackPos_1038_; lean_object* v_needlePos_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1094_; 
v_needle_1036_ = lean_ctor_get(v_a_1013_, 0);
v_table_1037_ = lean_ctor_get(v_a_1013_, 1);
v_stackPos_1038_ = lean_ctor_get(v_a_1013_, 2);
v_needlePos_1039_ = lean_ctor_get(v_a_1013_, 3);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_a_1013_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1041_ = v_a_1013_;
v_isShared_1042_ = v_isSharedCheck_1094_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_needlePos_1039_);
lean_inc(v_stackPos_1038_);
lean_inc(v_table_1037_);
lean_inc(v_needle_1036_);
lean_dec(v_a_1013_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1094_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_str_1043_; lean_object* v_startInclusive_1044_; lean_object* v_endExclusive_1045_; lean_object* v_str_1046_; lean_object* v_startInclusive_1047_; lean_object* v_endExclusive_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v_str_1043_ = lean_ctor_get(v_needle_1036_, 0);
v_startInclusive_1044_ = lean_ctor_get(v_needle_1036_, 1);
v_endExclusive_1045_ = lean_ctor_get(v_needle_1036_, 2);
v_str_1046_ = lean_ctor_get(v_s_1012_, 0);
v_startInclusive_1047_ = lean_ctor_get(v_s_1012_, 1);
v_endExclusive_1048_ = lean_ctor_get(v_s_1012_, 2);
v___x_1049_ = lean_nat_sub(v_stackPos_1038_, v_needlePos_1039_);
v___x_1050_ = lean_nat_sub(v_endExclusive_1045_, v_startInclusive_1044_);
v___x_1051_ = lean_nat_add(v___x_1049_, v___x_1050_);
v___x_1052_ = lean_nat_sub(v_endExclusive_1048_, v_startInclusive_1047_);
v___x_1053_ = lean_nat_dec_le(v___x_1051_, v___x_1052_);
lean_dec(v___x_1051_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
lean_dec(v___x_1050_);
lean_del_object(v___x_1041_);
lean_dec(v_needlePos_1039_);
lean_dec(v_stackPos_1038_);
lean_dec_ref(v_table_1037_);
lean_dec_ref(v_needle_1036_);
v___x_1054_ = lean_unsigned_to_nat(1u);
v___x_1055_ = lean_nat_add(v___x_1049_, v___x_1054_);
lean_dec(v___x_1049_);
v___x_1056_ = lean_nat_dec_le(v___x_1055_, v___x_1052_);
lean_dec(v___x_1052_);
lean_dec(v___x_1055_);
if (v___x_1056_ == 0)
{
return v_b_1014_;
}
else
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_box(3);
v_a_1013_ = v___x_1057_;
v_b_1014_ = v___x_1015_;
goto _start;
}
}
else
{
lean_object* v___x_1059_; uint8_t v_stackByte_1060_; lean_object* v___x_1061_; uint8_t v_patByte_1062_; uint8_t v___x_1063_; 
lean_dec(v___x_1052_);
lean_dec(v___x_1049_);
v___x_1059_ = lean_nat_add(v_startInclusive_1047_, v_stackPos_1038_);
v_stackByte_1060_ = lean_string_get_byte_fast(v_str_1046_, v___x_1059_);
v___x_1061_ = lean_nat_add(v_startInclusive_1044_, v_needlePos_1039_);
v_patByte_1062_ = lean_string_get_byte_fast(v_str_1043_, v___x_1061_);
v___x_1063_ = lean_uint8_dec_eq(v_stackByte_1060_, v_patByte_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; uint8_t v_decide_1065_; 
lean_dec(v___x_1050_);
v___x_1064_ = lean_unsigned_to_nat(0u);
v_decide_1065_ = lean_nat_dec_eq(v_needlePos_1039_, v___x_1064_);
if (v_decide_1065_ == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v_newNeedlePos_1068_; uint8_t v___x_1069_; 
v___x_1066_ = lean_unsigned_to_nat(1u);
v___x_1067_ = lean_nat_sub(v_needlePos_1039_, v___x_1066_);
lean_dec(v_needlePos_1039_);
v_newNeedlePos_1068_ = lean_array_fget_borrowed(v_table_1037_, v___x_1067_);
lean_dec(v___x_1067_);
v___x_1069_ = lean_nat_dec_eq(v_newNeedlePos_1068_, v___x_1064_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1071_; 
lean_inc(v_newNeedlePos_1068_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 3, v_newNeedlePos_1068_);
v___x_1071_ = v___x_1041_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_needle_1036_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_table_1037_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_stackPos_1038_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v_newNeedlePos_1068_);
v___x_1071_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
v_a_1013_ = v___x_1071_;
v_b_1014_ = v___x_1015_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1074_; lean_object* v___x_1076_; 
v_nextStackPos_1074_ = l_String_Slice_posGE___redArg(v_s_1012_, v_stackPos_1038_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 3, v___x_1064_);
lean_ctor_set(v___x_1041_, 2, v_nextStackPos_1074_);
v___x_1076_ = v___x_1041_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_needle_1036_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_table_1037_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_nextStackPos_1074_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v___x_1064_);
v___x_1076_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
v_a_1013_ = v___x_1076_;
v_b_1014_ = v___x_1015_;
goto _start;
}
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v_nextStackPos_1081_; lean_object* v___x_1083_; 
lean_dec(v_needlePos_1039_);
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = lean_nat_add(v_stackPos_1038_, v___x_1079_);
lean_dec(v_stackPos_1038_);
v_nextStackPos_1081_ = l_String_Slice_posGE___redArg(v_s_1012_, v___x_1080_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 3, v___x_1064_);
lean_ctor_set(v___x_1041_, 2, v_nextStackPos_1081_);
v___x_1083_ = v___x_1041_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_needle_1036_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_table_1037_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_nextStackPos_1081_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v___x_1064_);
v___x_1083_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
v_a_1013_ = v___x_1083_;
v_b_1014_ = v___x_1015_;
goto _start;
}
}
}
else
{
lean_object* v___x_1086_; lean_object* v_nextNeedlePos_1087_; uint8_t v_decide_1088_; 
v___x_1086_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_1087_ = lean_nat_add(v_needlePos_1039_, v___x_1086_);
lean_dec(v_needlePos_1039_);
v_decide_1088_ = lean_nat_dec_eq(v_nextNeedlePos_1087_, v___x_1050_);
lean_dec(v___x_1050_);
if (v_decide_1088_ == 0)
{
lean_object* v_nextStackPos_1089_; lean_object* v___x_1091_; 
v_nextStackPos_1089_ = lean_nat_add(v_stackPos_1038_, v___x_1086_);
lean_dec(v_stackPos_1038_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 3, v_nextNeedlePos_1087_);
lean_ctor_set(v___x_1041_, 2, v_nextStackPos_1089_);
v___x_1091_ = v___x_1041_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_needle_1036_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_table_1037_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_nextStackPos_1089_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v_nextNeedlePos_1087_);
v___x_1091_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
v_a_1013_ = v___x_1091_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_1087_);
lean_del_object(v___x_1041_);
lean_dec(v_stackPos_1038_);
lean_dec_ref(v_table_1037_);
lean_dec_ref(v_needle_1036_);
return v_decide_1088_;
}
}
}
}
}
default: 
{
return v_b_1014_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg___boxed(lean_object* v_s_1095_, lean_object* v_a_1096_, lean_object* v_b_1097_){
_start:
{
uint8_t v_b_boxed_1098_; uint8_t v_res_1099_; lean_object* v_r_1100_; 
v_b_boxed_1098_ = lean_unbox(v_b_1097_);
v_res_1099_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_1095_, v_a_1096_, v_b_boxed_1098_);
lean_dec_ref(v_s_1095_);
v_r_1100_ = lean_box(v_res_1099_);
return v_r_1100_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0));
v___x_1103_ = lean_string_utf8_byte_size(v___x_1102_);
return v___x_1103_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1);
v___x_1106_ = lean_nat_dec_eq(v___x_1105_, v___x_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1107_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0));
v___x_1110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v___x_1108_);
lean_ctor_set(v___x_1110_, 2, v___x_1107_);
return v___x_1110_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3);
v___x_1112_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1111_);
return v___x_1112_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4);
v___x_1115_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3);
v___x_1116_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v___x_1114_);
lean_ctor_set(v___x_1116_, 2, v___x_1113_);
lean_ctor_set(v___x_1116_, 3, v___x_1113_);
return v___x_1116_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(lean_object* v_s_1119_){
_start:
{
lean_object* v___y_1121_; uint8_t v___x_1124_; 
v___x_1124_ = lean_uint8_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5);
v___y_1121_ = v___x_1125_;
goto v___jp_1120_;
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__6));
v___y_1121_ = v___x_1126_;
goto v___jp_1120_;
}
v___jp_1120_:
{
uint8_t v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = 0;
lean_inc(v___y_1121_);
v___x_1123_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_1119_, v___y_1121_, v___x_1122_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___boxed(lean_object* v_s_1127_){
_start:
{
uint8_t v_res_1128_; lean_object* v_r_1129_; 
v_res_1128_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v_s_1127_);
lean_dec_ref(v_s_1127_);
v_r_1129_ = lean_box(v_res_1128_);
return v_r_1129_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(lean_object* v_kernelName_1130_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_string_utf8_byte_size(v_kernelName_1130_);
v___x_1133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1133_, 0, v_kernelName_1130_);
lean_ctor_set(v___x_1133_, 1, v___x_1131_);
lean_ctor_set(v___x_1133_, 2, v___x_1132_);
v___x_1134_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v___x_1133_);
lean_dec_ref_known(v___x_1133_, 3);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel___boxed(lean_object* v_kernelName_1135_){
_start:
{
uint8_t v_res_1136_; lean_object* v_r_1137_; 
v_res_1136_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_1135_);
v_r_1137_ = lean_box(v_res_1136_);
return v_r_1137_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(lean_object* v_s_1138_, lean_object* v_inst_1139_, lean_object* v_R_1140_, lean_object* v_a_1141_, uint8_t v_b_1142_, lean_object* v_c_1143_){
_start:
{
uint8_t v___x_1144_; 
v___x_1144_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_1138_, v_a_1141_, v_b_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___boxed(lean_object* v_s_1145_, lean_object* v_inst_1146_, lean_object* v_R_1147_, lean_object* v_a_1148_, lean_object* v_b_1149_, lean_object* v_c_1150_){
_start:
{
uint8_t v_b_boxed_1151_; uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_b_boxed_1151_ = lean_unbox(v_b_1149_);
v_res_1152_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(v_s_1145_, v_inst_1146_, v_R_1147_, v_a_1148_, v_b_boxed_1151_, v_c_1150_);
lean_dec_ref(v_s_1145_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg(lean_object* v_f_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v_fst_1159_; lean_object* v_snd_1160_; lean_object* v_r_1161_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1157_, 1);
v_fst_1159_ = lean_ctor_get(v_a_1158_, 0);
lean_inc(v_fst_1159_);
v_snd_1160_ = lean_ctor_get(v_a_1158_, 1);
lean_inc_n(v_snd_1160_, 2);
lean_dec(v_a_1158_);
lean_inc_ref(v___y_1155_);
v_r_1161_ = lean_apply_4(v_f_1154_, v_fst_1159_, v_snd_1160_, v___y_1155_, lean_box(0));
if (lean_obj_tag(v_r_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; 
v_a_1162_ = lean_ctor_get(v_r_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v_r_1161_, 1);
v___x_1163_ = lean_io_remove_file(v_snd_1160_);
lean_dec(v_snd_1160_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; 
v_unused_1171_ = lean_ctor_get(v___x_1163_, 0);
lean_dec(v_unused_1171_);
v___x_1165_ = v___x_1163_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_dec(v___x_1163_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v_a_1162_);
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1162_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_a_1162_);
v_a_1172_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1163_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1163_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1181_; 
v_a_1180_ = lean_ctor_get(v_r_1161_, 0);
lean_inc(v_a_1180_);
lean_dec_ref_known(v_r_1161_, 1);
v___x_1181_ = lean_io_remove_file(v_snd_1160_);
lean_dec(v_snd_1160_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v___x_1181_, 0);
lean_dec(v_unused_1189_);
v___x_1183_ = v___x_1181_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_dec(v___x_1181_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set_tag(v___x_1183_, 1);
lean_ctor_set(v___x_1183_, 0, v_a_1180_);
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1180_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec(v_a_1180_);
v_a_1190_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1181_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1181_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref(v_f_1154_);
v_a_1198_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1157_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1157_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg___boxed(lean_object* v_f_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg(v_f_1206_, v___y_1207_);
lean_dec_ref(v___y_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2(lean_object* v_00_u03b1_1210_, lean_object* v_f_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg(v_f_1211_, v___y_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___boxed(lean_object* v_00_u03b1_1215_, lean_object* v_f_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2(v_00_u03b1_1215_, v_f_1216_, v___y_1217_);
lean_dec_ref(v___y_1217_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(lean_object* v_a_1220_, lean_object* v_b_1221_){
_start:
{
lean_object* v_array_1222_; lean_object* v_start_1223_; lean_object* v_stop_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1237_; 
v_array_1222_ = lean_ctor_get(v_a_1220_, 0);
v_start_1223_ = lean_ctor_get(v_a_1220_, 1);
v_stop_1224_ = lean_ctor_get(v_a_1220_, 2);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_a_1220_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1226_ = v_a_1220_;
v_isShared_1227_ = v_isSharedCheck_1237_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_stop_1224_);
lean_inc(v_start_1223_);
lean_inc(v_array_1222_);
lean_dec(v_a_1220_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1237_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
uint8_t v___x_1228_; 
v___x_1228_ = lean_nat_dec_lt(v_start_1223_, v_stop_1224_);
if (v___x_1228_ == 0)
{
lean_del_object(v___x_1226_);
lean_dec(v_stop_1224_);
lean_dec(v_start_1223_);
lean_dec_ref(v_array_1222_);
return v_b_1221_;
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1229_ = lean_unsigned_to_nat(1u);
v___x_1230_ = lean_nat_add(v_start_1223_, v___x_1229_);
lean_inc_ref(v_array_1222_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___x_1230_);
v___x_1232_ = v___x_1226_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_array_1222_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___x_1230_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_stop_1224_);
v___x_1232_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_array_fget(v_array_1222_, v_start_1223_);
lean_dec(v_start_1223_);
lean_dec_ref(v_array_1222_);
v___x_1234_ = lean_array_push(v_b_1221_, v___x_1233_);
v_a_1220_ = v___x_1232_;
v_b_1221_ = v___x_1234_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(size_t v_sz_1238_, size_t v_i_1239_, lean_object* v_bs_1240_){
_start:
{
uint8_t v___x_1241_; 
v___x_1241_ = lean_usize_dec_lt(v_i_1239_, v_sz_1238_);
if (v___x_1241_ == 0)
{
return v_bs_1240_;
}
else
{
lean_object* v_v_1242_; lean_object* v___x_1243_; lean_object* v_bs_x27_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; lean_object* v___x_1249_; 
v_v_1242_ = lean_array_uget(v_bs_1240_, v_i_1239_);
v___x_1243_ = lean_unsigned_to_nat(0u);
v_bs_x27_1244_ = lean_array_uset(v_bs_1240_, v_i_1239_, v___x_1243_);
v___x_1245_ = l_Lean_Name_toString(v_v_1242_, v___x_1241_);
v___x_1246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
v___x_1247_ = ((size_t)1ULL);
v___x_1248_ = lean_usize_add(v_i_1239_, v___x_1247_);
v___x_1249_ = lean_array_uset(v_bs_x27_1244_, v_i_1239_, v___x_1246_);
v_i_1239_ = v___x_1248_;
v_bs_1240_ = v___x_1249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0___boxed(lean_object* v_sz_1251_, lean_object* v_i_1252_, lean_object* v_bs_1253_){
_start:
{
size_t v_sz_boxed_1254_; size_t v_i_boxed_1255_; lean_object* v_res_1256_; 
v_sz_boxed_1254_ = lean_unbox_usize(v_sz_1251_);
lean_dec(v_sz_1251_);
v_i_boxed_1255_ = lean_unbox_usize(v_i_1252_);
lean_dec(v_i_1252_);
v_res_1256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_boxed_1254_, v_i_boxed_1255_, v_bs_1253_);
return v_res_1256_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_unsigned_to_nat(4u);
v___x_1276_ = l_Lean_JsonNumber_fromNat(v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12);
v___x_1278_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13);
v___x_1280_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v___x_1279_);
return v___x_1281_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__20));
v___x_1297_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14);
v___x_1298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set(v___x_1298_, 1, v___x_1296_);
return v___x_1298_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21);
v___x_1300_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10));
v___x_1301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v___x_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(lean_object* v_configHandle_1309_, lean_object* v_solutionExport_1310_, lean_object* v_kernelName_1311_, lean_object* v___x_1312_, lean_object* v_kernelCommand_1313_, lean_object* v_configPath_1314_, lean_object* v_solutionHandle_1315_, lean_object* v_solutionPath_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_a_1320_; lean_object* v_legalAxioms_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; size_t v_sz_1353_; size_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_legalAxioms_1347_ = lean_ctor_get(v___y_1317_, 5);
v___x_1348_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5));
v___x_1349_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6));
lean_inc_ref(v_solutionPath_1316_);
v___x_1350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1350_, 0, v_solutionPath_1316_);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1349_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7));
v_sz_1353_ = lean_array_size(v_legalAxioms_1347_);
v___x_1354_ = ((size_t)0ULL);
lean_inc_ref(v_legalAxioms_1347_);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_1353_, v___x_1354_, v_legalAxioms_1347_);
v___x_1356_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1352_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22);
v___x_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1351_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1348_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = l_Lean_Json_mkObj(v___x_1361_);
lean_dec_ref_known(v___x_1361_, 2);
v___x_1363_ = l_Lean_Json_compress(v___x_1362_);
v___x_1364_ = lean_io_prim_handle_put_str(v_configHandle_1309_, v___x_1363_);
lean_dec_ref(v___x_1363_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1365_; 
lean_dec_ref_known(v___x_1364_, 1);
v___x_1365_ = lean_io_prim_handle_flush(v_configHandle_1309_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1366_; 
lean_dec_ref_known(v___x_1365_, 1);
v___x_1366_ = lean_io_prim_handle_put_str(v_solutionHandle_1315_, v_solutionExport_1310_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v___x_1367_; 
lean_dec_ref_known(v___x_1366_, 1);
v___x_1367_ = lean_io_prim_handle_flush(v_solutionHandle_1315_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_kernelArgs_1369_; lean_object* v___y_1370_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
lean_dec_ref_known(v___x_1367_, 1);
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = lean_array_get_size(v_kernelCommand_1313_);
lean_inc_ref(v_kernelCommand_1313_);
v___x_1427_ = l_Array_toSubarray___redArg(v_kernelCommand_1313_, v___x_1425_, v___x_1426_);
v___x_1428_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18));
v___x_1429_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v___x_1427_, v___x_1428_);
lean_inc_ref(v_kernelName_1311_);
v___x_1430_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_1311_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; 
lean_inc_ref(v_solutionPath_1316_);
v___x_1431_ = lean_array_push(v___x_1429_, v_solutionPath_1316_);
v_kernelArgs_1369_ = v___x_1431_;
v___y_1370_ = v___y_1317_;
goto v___jp_1368_;
}
else
{
lean_object* v___x_1432_; 
lean_inc_ref(v_configPath_1314_);
v___x_1432_ = lean_array_push(v___x_1429_, v_configPath_1314_);
v_kernelArgs_1369_ = v___x_1432_;
v___y_1370_ = v___y_1317_;
goto v___jp_1368_;
}
v___jp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1371_ = lean_unsigned_to_nat(0u);
v___x_1372_ = lean_array_get(v___x_1312_, v_kernelCommand_1313_, v___x_1371_);
lean_dec_ref(v_kernelCommand_1313_);
v___x_1373_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23));
v___x_1374_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1375_ = lean_unsigned_to_nat(2u);
v___x_1376_ = lean_mk_empty_array_with_capacity(v___x_1375_);
v___x_1377_ = lean_array_push(v___x_1376_, v_configPath_1314_);
v___x_1378_ = lean_array_push(v___x_1377_, v_solutionPath_1316_);
v___x_1379_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18));
v___x_1380_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1372_);
lean_ctor_set(v___x_1380_, 1, v_kernelArgs_1369_);
lean_ctor_set(v___x_1380_, 2, v___x_1373_);
lean_ctor_set(v___x_1380_, 3, v___x_1374_);
lean_ctor_set(v___x_1380_, 4, v___x_1378_);
lean_ctor_set(v___x_1380_, 5, v___x_1379_);
lean_ctor_set(v___x_1380_, 6, v___x_1379_);
v___x_1381_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v___x_1380_, v___y_1370_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1423_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1423_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1423_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
uint32_t v___x_1386_; uint32_t v___x_1387_; uint8_t v___x_1388_; 
v___x_1386_ = 0;
v___x_1387_ = lean_unbox_uint32(v_a_1382_);
v___x_1388_ = lean_uint32_dec_eq(v___x_1387_, v___x_1386_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1389_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24));
lean_inc_ref(v_kernelName_1311_);
v___x_1390_ = lean_string_append(v_kernelName_1311_, v___x_1389_);
v___x_1391_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1390_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1407_; 
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v___x_1391_, 0);
lean_dec(v_unused_1408_);
v___x_1393_ = v___x_1391_;
v_isShared_1394_ = v_isSharedCheck_1407_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v___x_1391_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1407_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; uint32_t v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1395_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25));
v___x_1396_ = lean_string_append(v_kernelName_1311_, v___x_1395_);
v___x_1397_ = lean_unbox_uint32(v_a_1382_);
lean_dec(v_a_1382_);
v___x_1398_ = lean_uint32_to_nat(v___x_1397_);
v___x_1399_ = l_Nat_reprFast(v___x_1398_);
v___x_1400_ = lean_string_append(v___x_1396_, v___x_1399_);
lean_dec_ref(v___x_1399_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set_tag(v___x_1384_, 1);
lean_ctor_set(v___x_1384_, 0, v___x_1400_);
v___x_1402_ = v___x_1384_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1402_);
v___x_1404_ = v___x_1393_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v_a_1409_; 
lean_del_object(v___x_1384_);
lean_dec(v_a_1382_);
v_a_1409_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1391_, 1);
v_a_1320_ = v_a_1409_;
goto v___jp_1319_;
}
}
else
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_del_object(v___x_1384_);
lean_dec(v_a_1382_);
v___x_1410_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26));
lean_inc_ref(v_kernelName_1311_);
v___x_1411_ = lean_string_append(v_kernelName_1311_, v___x_1410_);
v___x_1412_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1411_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_kernelName_1311_);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; 
v_unused_1421_ = lean_ctor_get(v___x_1412_, 0);
lean_dec(v_unused_1421_);
v___x_1414_ = v___x_1412_;
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
else
{
lean_dec(v___x_1412_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1420_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_box(0);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1416_);
v___x_1418_ = v___x_1414_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
else
{
lean_object* v_a_1422_; 
v_a_1422_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1412_, 1);
v_a_1320_ = v_a_1422_;
goto v___jp_1319_;
}
}
}
}
else
{
lean_object* v_a_1424_; 
v_a_1424_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1381_, 1);
v_a_1320_ = v_a_1424_;
goto v___jp_1319_;
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v_solutionPath_1316_);
lean_dec_ref(v_configPath_1314_);
lean_dec_ref(v_kernelCommand_1313_);
lean_dec_ref(v_kernelName_1311_);
v_a_1433_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1367_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1367_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec_ref(v_solutionPath_1316_);
lean_dec_ref(v_configPath_1314_);
lean_dec_ref(v_kernelCommand_1313_);
lean_dec_ref(v_kernelName_1311_);
v_a_1441_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1366_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1366_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref(v_solutionPath_1316_);
lean_dec_ref(v_configPath_1314_);
lean_dec_ref(v_kernelCommand_1313_);
lean_dec_ref(v_kernelName_1311_);
v_a_1449_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1365_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1365_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v_solutionPath_1316_);
lean_dec_ref(v_configPath_1314_);
lean_dec_ref(v_kernelCommand_1313_);
lean_dec_ref(v_kernelName_1311_);
v_a_1457_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1364_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1364_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
v___jp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1321_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__0));
v___x_1322_ = lean_string_append(v___x_1321_, v_kernelName_1311_);
lean_dec_ref(v_kernelName_1311_);
v___x_1323_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__1));
lean_inc_ref(v___x_1322_);
v___x_1324_ = lean_string_append(v___x_1322_, v___x_1323_);
v___x_1325_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1324_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1337_; 
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v___x_1325_, 0);
lean_dec(v_unused_1338_);
v___x_1327_ = v___x_1325_;
v_isShared_1328_ = v_isSharedCheck_1337_;
goto v_resetjp_1326_;
}
else
{
lean_dec(v___x_1325_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1337_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1329_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__2));
v___x_1330_ = lean_string_append(v___x_1322_, v___x_1329_);
v___x_1331_ = lean_io_error_to_string(v_a_1320_);
v___x_1332_ = lean_string_append(v___x_1330_, v___x_1331_);
lean_dec_ref(v___x_1331_);
v___x_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1333_);
v___x_1335_ = v___x_1327_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec_ref(v___x_1322_);
lean_dec(v_a_1320_);
v_a_1339_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1325_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1325_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed(lean_object* v_configHandle_1465_, lean_object* v_solutionExport_1466_, lean_object* v_kernelName_1467_, lean_object* v___x_1468_, lean_object* v_kernelCommand_1469_, lean_object* v_configPath_1470_, lean_object* v_solutionHandle_1471_, lean_object* v_solutionPath_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(v_configHandle_1465_, v_solutionExport_1466_, v_kernelName_1467_, v___x_1468_, v_kernelCommand_1469_, v_configPath_1470_, v_solutionHandle_1471_, v_solutionPath_1472_, v___y_1473_);
lean_dec_ref(v___y_1473_);
lean_dec(v_solutionHandle_1471_);
lean_dec_ref(v___x_1468_);
lean_dec_ref(v_solutionExport_1466_);
lean_dec(v_configHandle_1465_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__1(lean_object* v_solutionExport_1476_, lean_object* v_kernelName_1477_, lean_object* v___x_1478_, lean_object* v_kernelCommand_1479_, lean_object* v_configHandle_1480_, lean_object* v_configPath_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___f_1484_; lean_object* v___x_1485_; 
v___f_1484_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed), 10, 6);
lean_closure_set(v___f_1484_, 0, v_configHandle_1480_);
lean_closure_set(v___f_1484_, 1, v_solutionExport_1476_);
lean_closure_set(v___f_1484_, 2, v_kernelName_1477_);
lean_closure_set(v___f_1484_, 3, v___x_1478_);
lean_closure_set(v___f_1484_, 4, v_kernelCommand_1479_);
lean_closure_set(v___f_1484_, 5, v_configPath_1481_);
v___x_1485_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg(v___f_1484_, v___y_1482_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__1___boxed(lean_object* v_solutionExport_1486_, lean_object* v_kernelName_1487_, lean_object* v___x_1488_, lean_object* v_kernelCommand_1489_, lean_object* v_configHandle_1490_, lean_object* v_configPath_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__1(v_solutionExport_1486_, v_kernelName_1487_, v___x_1488_, v_kernelCommand_1489_, v_configHandle_1490_, v_configPath_1491_, v___y_1492_);
lean_dec_ref(v___y_1492_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(lean_object* v_kernelName_1497_, lean_object* v_kernelCommand_1498_, lean_object* v_solutionExport_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1502_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0));
v___x_1503_ = lean_string_append(v___x_1502_, v_kernelName_1497_);
v___x_1504_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1));
v___x_1505_ = lean_string_append(v___x_1503_, v___x_1504_);
v___x_1506_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1505_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v___x_1507_; lean_object* v___f_1508_; lean_object* v___x_1509_; 
lean_dec_ref_known(v___x_1506_, 1);
v___x_1507_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__17));
v___f_1508_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1508_, 0, v_solutionExport_1499_);
lean_closure_set(v___f_1508_, 1, v_kernelName_1497_);
lean_closure_set(v___f_1508_, 2, v___x_1507_);
lean_closure_set(v___f_1508_, 3, v_kernelCommand_1498_);
v___x_1509_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg(v___f_1508_, v_a_1500_);
return v___x_1509_;
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v_solutionExport_1499_);
lean_dec_ref(v_kernelCommand_1498_);
lean_dec_ref(v_kernelName_1497_);
v_a_1510_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1506_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1506_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___boxed(lean_object* v_kernelName_1518_, lean_object* v_kernelCommand_1519_, lean_object* v_solutionExport_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_kernelName_1518_, v_kernelCommand_1519_, v_solutionExport_1520_, v_a_1521_);
lean_dec_ref(v_a_1521_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1(lean_object* v_inst_1524_, lean_object* v_R_1525_, lean_object* v_a_1526_, lean_object* v_b_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v_a_1526_, v_b_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(lean_object* v_solutionExport_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_whichLeanChecker_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_whichLeanChecker_1534_ = lean_ctor_get(v_a_1532_, 11);
v___x_1535_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0));
v___x_1536_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_1537_ = lean_unsigned_to_nat(2u);
v___x_1538_ = lean_mk_empty_array_with_capacity(v___x_1537_);
lean_inc_ref(v_whichLeanChecker_1534_);
v___x_1539_ = lean_array_push(v___x_1538_, v_whichLeanChecker_1534_);
v___x_1540_ = lean_array_push(v___x_1539_, v___x_1536_);
v___x_1541_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v___x_1535_, v___x_1540_, v_solutionExport_1531_, v_a_1532_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___boxed(lean_object* v_solutionExport_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_solutionExport_1542_, v_a_1543_);
lean_dec_ref(v_a_1543_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg(){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__52));
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___boxed(lean_object* v_a_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___boxed(lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(v_a_1703_);
lean_dec_ref(v_a_1703_);
return v_res_1705_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(lean_object* v_a_1706_, lean_object* v_as_1707_, size_t v_i_1708_, size_t v_stop_1709_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_usize_dec_eq(v_i_1708_, v_stop_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = lean_array_uget_borrowed(v_as_1707_, v_i_1708_);
v___x_1712_ = lean_name_eq(v_a_1706_, v___x_1711_);
if (v___x_1712_ == 0)
{
size_t v___x_1713_; size_t v___x_1714_; 
v___x_1713_ = ((size_t)1ULL);
v___x_1714_ = lean_usize_add(v_i_1708_, v___x_1713_);
v_i_1708_ = v___x_1714_;
goto _start;
}
else
{
return v___x_1712_;
}
}
else
{
uint8_t v___x_1716_; 
v___x_1716_ = 0;
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0___boxed(lean_object* v_a_1717_, lean_object* v_as_1718_, lean_object* v_i_1719_, lean_object* v_stop_1720_){
_start:
{
size_t v_i_boxed_1721_; size_t v_stop_boxed_1722_; uint8_t v_res_1723_; lean_object* v_r_1724_; 
v_i_boxed_1721_ = lean_unbox_usize(v_i_1719_);
lean_dec(v_i_1719_);
v_stop_boxed_1722_ = lean_unbox_usize(v_stop_1720_);
lean_dec(v_stop_1720_);
v_res_1723_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_1717_, v_as_1718_, v_i_boxed_1721_, v_stop_boxed_1722_);
lean_dec_ref(v_as_1718_);
lean_dec(v_a_1717_);
v_r_1724_ = lean_box(v_res_1723_);
return v_r_1724_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(lean_object* v_as_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = lean_array_get_size(v_as_1725_);
v___x_1729_ = lean_nat_dec_lt(v___x_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
return v___x_1729_;
}
else
{
if (v___x_1729_ == 0)
{
return v___x_1729_;
}
else
{
size_t v___x_1730_; size_t v___x_1731_; uint8_t v___x_1732_; 
v___x_1730_ = ((size_t)0ULL);
v___x_1731_ = lean_usize_of_nat(v___x_1728_);
v___x_1732_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_1726_, v_as_1725_, v___x_1730_, v___x_1731_);
return v___x_1732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0___boxed(lean_object* v_as_1733_, lean_object* v_a_1734_){
_start:
{
uint8_t v_res_1735_; lean_object* v_r_1736_; 
v_res_1735_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_as_1733_, v_a_1734_);
lean_dec(v_a_1734_);
lean_dec_ref(v_as_1733_);
v_r_1736_ = lean_box(v_res_1735_);
return v_r_1736_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11(void){
_start:
{
lean_object* v___x_1767_; lean_object* v_additional_1768_; lean_object* v___x_1769_; 
v___x_1767_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__10));
v_additional_1768_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_1769_ = l_Array_append___redArg(v_additional_1768_, v___x_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(lean_object* v_a_1770_){
_start:
{
lean_object* v_legalAxioms_1772_; lean_object* v_additional_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_legalAxioms_1772_ = lean_ctor_get(v_a_1770_, 5);
v_additional_1773_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_1774_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3));
v___x_1775_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_legalAxioms_1772_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v_additional_1773_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
return v___x_1778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___boxed(lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_1779_);
lean_dec_ref(v_a_1779_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_stringStream(lean_object* v_s_1782_){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1784_ = lean_string_to_utf8(v_s_1782_);
v___x_1785_ = lean_unsigned_to_nat(0u);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = lean_st_mk_ref(v___x_1786_);
v___x_1788_ = l_IO_FS_Stream_ofBuffer(v___x_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_stringStream___boxed(lean_object* v_s_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lake_CLI_Check_0__Lake_Check_stringStream(v_s_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg(lean_object* v_e_1792_){
_start:
{
if (lean_obj_tag(v_e_1792_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1802_; 
v_a_1794_ = lean_ctor_get(v_e_1792_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_e_1792_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1796_ = v_e_1792_;
v_isShared_1797_ = v_isSharedCheck_1802_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v_e_1792_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1802_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; lean_object* v___x_1800_; 
v___x_1798_ = lean_mk_io_user_error(v_a_1794_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set_tag(v___x_1796_, 1);
lean_ctor_set(v___x_1796_, 0, v___x_1798_);
v___x_1800_ = v___x_1796_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
v_a_1803_ = lean_ctor_get(v_e_1792_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_e_1792_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v_e_1792_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v_e_1792_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set_tag(v___x_1805_, 0);
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg___boxed(lean_object* v_e_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg(v_e_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0(lean_object* v_00_u03b1_1814_, lean_object* v_e_1815_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg(v_e_1815_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___boxed(lean_object* v_00_u03b1_1818_, lean_object* v_e_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0(v_00_u03b1_1818_, v_e_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__1(lean_object* v_solutionExport_1822_, lean_object* v_init_1823_, lean_object* v_x_1824_, lean_object* v___y_1825_){
_start:
{
if (lean_obj_tag(v_x_1824_) == 0)
{
lean_object* v_k_1827_; lean_object* v_v_1828_; lean_object* v_l_1829_; lean_object* v_r_1830_; lean_object* v___x_1831_; 
v_k_1827_ = lean_ctor_get(v_x_1824_, 1);
lean_inc(v_k_1827_);
v_v_1828_ = lean_ctor_get(v_x_1824_, 2);
lean_inc(v_v_1828_);
v_l_1829_ = lean_ctor_get(v_x_1824_, 3);
lean_inc(v_l_1829_);
v_r_1830_ = lean_ctor_get(v_x_1824_, 4);
lean_inc(v_r_1830_);
lean_dec_ref_known(v_x_1824_, 5);
lean_inc_ref(v_solutionExport_1822_);
v___x_1831_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__1(v_solutionExport_1822_, v_init_1823_, v_l_1829_, v___y_1825_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v_a_1833_; lean_object* v___x_1834_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1831_, 1);
v_a_1833_ = lean_ctor_get(v_a_1832_, 0);
lean_inc(v_a_1833_);
lean_dec(v_a_1832_);
lean_inc_ref(v_solutionExport_1822_);
v___x_1834_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_k_1827_, v_v_1828_, v_solutionExport_1822_, v___y_1825_);
if (lean_obj_tag(v___x_1834_) == 0)
{
if (lean_obj_tag(v_a_1833_) == 0)
{
lean_object* v_a_1835_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v_init_1823_ = v_a_1835_;
v_x_1824_ = v_r_1830_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1834_, 1);
v_init_1823_ = v_a_1833_;
v_x_1824_ = v_r_1830_;
goto _start;
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_a_1833_);
lean_dec(v_r_1830_);
lean_dec_ref(v_solutionExport_1822_);
v_a_1838_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1834_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1834_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_dec(v_r_1830_);
lean_dec(v_v_1828_);
lean_dec(v_k_1827_);
lean_dec_ref(v_solutionExport_1822_);
return v___x_1831_;
}
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_dec_ref(v_solutionExport_1822_);
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v_init_1823_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__1___boxed(lean_object* v_solutionExport_1848_, lean_object* v_init_1849_, lean_object* v_x_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__1(v_solutionExport_1848_, v_init_1849_, v_x_1850_, v___y_1851_);
lean_dec_ref(v___y_1851_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(lean_object* v_challengeExport_1854_, lean_object* v_solutionExport_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_val_1859_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = l___private_Lake_CLI_Check_0__Lake_Check_stringStream(v_challengeExport_1854_);
v___x_1863_ = l_LeanExport_parseStream(v___x_1862_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
lean_inc_ref(v_solutionExport_1855_);
v___x_1865_ = l___private_Lake_CLI_Check_0__Lake_Check_stringStream(v_solutionExport_1855_);
v___x_1866_ = l_LeanExport_parseStream(v___x_1865_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1868_; lean_object* v_a_1869_; lean_object* v_theoremNames_1870_; lean_object* v_definitionNames_1871_; lean_object* v_legalAxioms_1872_; lean_object* v_externalKernels_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc_n(v_a_1867_, 2);
lean_dec_ref_known(v___x_1866_, 1);
v___x_1868_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v___x_1868_);
v_theoremNames_1870_ = lean_ctor_get(v_a_1856_, 3);
v_definitionNames_1871_ = lean_ctor_get(v_a_1856_, 4);
v_legalAxioms_1872_ = lean_ctor_get(v_a_1856_, 5);
v_externalKernels_1873_ = lean_ctor_get(v_a_1856_, 12);
lean_inc_ref(v_theoremNames_1870_);
v___x_1874_ = l_Array_append___redArg(v_theoremNames_1870_, v_legalAxioms_1872_);
v___x_1875_ = l_Lake_Check_compareAt(v_a_1864_, v_a_1867_, v___x_1874_, v_definitionNames_1871_, v_a_1869_);
lean_dec_ref(v___x_1874_);
v___x_1876_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg(v___x_1875_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec_ref_known(v___x_1876_, 1);
v___x_1877_ = l_Lake_Check_checkAxioms(v_a_1867_, v_theoremNames_1870_, v_definitionNames_1871_, v_legalAxioms_1872_);
v___x_1878_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg(v___x_1877_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_dec_ref_known(v___x_1878_, 1);
v___x_1879_ = lean_box(0);
lean_inc(v_externalKernels_1873_);
lean_inc_ref(v_solutionExport_1855_);
v___x_1880_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__1(v_solutionExport_1855_, v___x_1879_, v_externalKernels_1873_, v_a_1856_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v_a_1883_; lean_object* v_a_1904_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v_a_1904_ = lean_ctor_get(v_a_1881_, 0);
lean_inc(v_a_1904_);
lean_dec(v_a_1881_);
v_a_1883_ = v_a_1904_;
goto v___jp_1882_;
v___jp_1882_:
{
lean_object* v___x_1884_; 
v___x_1884_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_solutionExport_1855_, v_a_1856_);
if (lean_obj_tag(v___x_1884_) == 0)
{
if (lean_obj_tag(v_a_1883_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1894_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1887_ = v___x_1884_;
v_isShared_1888_ = v_isSharedCheck_1894_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1894_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
if (lean_obj_tag(v_a_1885_) == 1)
{
lean_object* v_val_1889_; 
lean_del_object(v___x_1887_);
v_val_1889_ = lean_ctor_get(v_a_1885_, 0);
lean_inc(v_val_1889_);
lean_dec_ref_known(v_a_1885_, 1);
v_val_1859_ = v_val_1889_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
lean_dec(v_a_1885_);
v___x_1890_ = lean_box(0);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1890_);
v___x_1892_ = v___x_1887_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
else
{
lean_object* v_val_1895_; 
lean_dec_ref_known(v___x_1884_, 1);
v_val_1895_ = lean_ctor_get(v_a_1883_, 0);
lean_inc(v_val_1895_);
lean_dec_ref_known(v_a_1883_, 1);
v_val_1859_ = v_val_1895_;
goto v___jp_1858_;
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_dec(v_a_1883_);
v_a_1896_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1884_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1884_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec_ref(v_solutionExport_1855_);
v_a_1905_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1880_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1880_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_dec_ref(v_solutionExport_1855_);
return v___x_1878_;
}
}
else
{
lean_dec(v_a_1867_);
lean_dec_ref(v_solutionExport_1855_);
return v___x_1876_;
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v_a_1864_);
lean_dec_ref(v_solutionExport_1855_);
v_a_1913_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1866_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1866_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec_ref(v_solutionExport_1855_);
v_a_1921_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1863_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1863_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
v___jp_1858_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_mk_io_user_error(v_val_1859_);
v___x_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
return v___x_1861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch___boxed(lean_object* v_challengeExport_1929_, lean_object* v_solutionExport_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExport_1929_, v_solutionExport_1930_, v_a_1931_);
lean_dec_ref(v_a_1931_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt(lean_object* v_a_1935_){
_start:
{
lean_object* v___x_1937_; lean_object* v_a_1938_; lean_object* v___x_1939_; lean_object* v_a_1940_; lean_object* v_challengeModule_1941_; lean_object* v_solutionModule_1942_; lean_object* v_theoremNames_1943_; lean_object* v_definitionNames_1944_; lean_object* v_legalAxioms_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1937_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_1935_);
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref(v___x_1937_);
v___x_1939_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref(v___x_1939_);
v_challengeModule_1941_ = lean_ctor_get(v_a_1935_, 1);
v_solutionModule_1942_ = lean_ctor_get(v_a_1935_, 2);
v_theoremNames_1943_ = lean_ctor_get(v_a_1935_, 3);
v_definitionNames_1944_ = lean_ctor_get(v_a_1935_, 4);
v_legalAxioms_1945_ = lean_ctor_get(v_a_1935_, 5);
v___x_1946_ = lean_unsigned_to_nat(1u);
v___x_1947_ = lean_mk_empty_array_with_capacity(v___x_1946_);
lean_inc(v_challengeModule_1941_);
lean_inc_ref(v___x_1947_);
v___x_1948_ = lean_array_push(v___x_1947_, v_challengeModule_1941_);
v___x_1949_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v___x_1948_, v_a_1935_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_dec_ref_known(v___x_1949_, 1);
v___x_1950_ = l_Array_append___redArg(v_a_1938_, v_theoremNames_1943_);
v___x_1951_ = l_Array_append___redArg(v___x_1950_, v_legalAxioms_1945_);
v___x_1952_ = l_Array_append___redArg(v___x_1951_, v_a_1940_);
lean_dec(v_a_1940_);
v___x_1953_ = l_Array_append___redArg(v___x_1952_, v_definitionNames_1944_);
lean_inc_ref(v___x_1953_);
lean_inc(v_challengeModule_1941_);
v___x_1954_ = l___private_Lake_CLI_Check_0__Lake_Check_safeExport(v_challengeModule_1941_, v___x_1953_, v_a_1935_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
lean_inc(v_solutionModule_1942_);
v___x_1956_ = lean_array_push(v___x_1947_, v_solutionModule_1942_);
v___x_1957_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v___x_1956_, v_a_1935_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v___x_1958_; 
lean_dec_ref_known(v___x_1957_, 1);
lean_inc(v_solutionModule_1942_);
v___x_1958_ = l___private_Lake_CLI_Check_0__Lake_Check_safeExport(v_solutionModule_1942_, v___x_1953_, v_a_1935_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1960_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___x_1960_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_a_1955_, v_a_1959_, v_a_1935_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec_ref_known(v___x_1960_, 1);
v___x_1961_ = ((lean_object*)(l_Lake_Check_compareIt___closed__0));
v___x_1962_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1961_);
return v___x_1962_;
}
else
{
return v___x_1960_;
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v_a_1955_);
v_a_1963_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1958_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1958_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
else
{
lean_dec(v_a_1955_);
lean_dec_ref(v___x_1953_);
return v___x_1957_;
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec_ref(v___x_1953_);
lean_dec_ref(v___x_1947_);
v_a_1971_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1954_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1954_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_dec_ref(v___x_1947_);
lean_dec(v_a_1940_);
lean_dec(v_a_1938_);
return v___x_1949_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___boxed(lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lake_Check_compareIt(v_a_1979_);
lean_dec_ref(v_a_1979_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(lean_object* v_j_1982_, lean_object* v_k_1983_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = l_Lean_Json_getObjValD(v_j_1982_, v_k_1983_);
v___x_1985_ = l_Lean_Json_getStr_x3f(v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0___boxed(lean_object* v_j_1986_, lean_object* v_k_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_j_1986_, v_k_1987_);
lean_dec_ref(v_k_1987_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(size_t v_sz_1989_, size_t v_i_1990_, lean_object* v_bs_1991_){
_start:
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_usize_dec_lt(v_i_1990_, v_sz_1989_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_bs_1991_);
return v___x_1993_;
}
else
{
lean_object* v_v_1994_; lean_object* v___x_1995_; 
v_v_1994_ = lean_array_uget_borrowed(v_bs_1991_, v_i_1990_);
lean_inc(v_v_1994_);
v___x_1995_ = l_Lean_Json_getStr_x3f(v_v_1994_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v_bs_1991_);
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2005_; lean_object* v_bs_x27_2006_; size_t v___x_2007_; size_t v___x_2008_; lean_object* v___x_2009_; 
v_a_2004_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_1995_, 1);
v___x_2005_ = lean_unsigned_to_nat(0u);
v_bs_x27_2006_ = lean_array_uset(v_bs_1991_, v_i_1990_, v___x_2005_);
v___x_2007_ = ((size_t)1ULL);
v___x_2008_ = lean_usize_add(v_i_1990_, v___x_2007_);
v___x_2009_ = lean_array_uset(v_bs_x27_2006_, v_i_1990_, v_a_2004_);
v_i_1990_ = v___x_2008_;
v_bs_1991_ = v___x_2009_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2011_, lean_object* v_i_2012_, lean_object* v_bs_2013_){
_start:
{
size_t v_sz_boxed_2014_; size_t v_i_boxed_2015_; lean_object* v_res_2016_; 
v_sz_boxed_2014_ = lean_unbox_usize(v_sz_2011_);
lean_dec(v_sz_2011_);
v_i_boxed_2015_ = lean_unbox_usize(v_i_2012_);
lean_dec(v_i_2012_);
v_res_2016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_2014_, v_i_boxed_2015_, v_bs_2013_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(lean_object* v_x_2019_){
_start:
{
if (lean_obj_tag(v_x_2019_) == 4)
{
lean_object* v_elems_2020_; size_t v_sz_2021_; size_t v___x_2022_; lean_object* v___x_2023_; 
v_elems_2020_ = lean_ctor_get(v_x_2019_, 0);
lean_inc_ref(v_elems_2020_);
lean_dec_ref_known(v_x_2019_, 1);
v_sz_2021_ = lean_array_size(v_elems_2020_);
v___x_2022_ = ((size_t)0ULL);
v___x_2023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_2021_, v___x_2022_, v_elems_2020_);
return v___x_2023_;
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2024_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__0));
v___x_2025_ = lean_unsigned_to_nat(80u);
v___x_2026_ = l_Lean_Json_pretty(v_x_2019_, v___x_2025_);
v___x_2027_ = lean_string_append(v___x_2024_, v___x_2026_);
lean_dec_ref(v___x_2026_);
v___x_2028_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_2029_ = lean_string_append(v___x_2027_, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(lean_object* v_x_2033_){
_start:
{
if (lean_obj_tag(v_x_2033_) == 0)
{
lean_object* v___x_2034_; 
v___x_2034_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3___closed__0));
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_x_2033_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2035_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2052_; 
v_a_2044_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2046_ = v___x_2035_;
v_isShared_2047_ = v_isSharedCheck_2052_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2035_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2052_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_a_2044_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2048_);
v___x_2050_ = v___x_2046_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(lean_object* v_j_2053_, lean_object* v_k_2054_){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = l_Lean_Json_getObjValD(v_j_2053_, v_k_2054_);
v___x_2056_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2___boxed(lean_object* v_j_2057_, lean_object* v_k_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_j_2057_, v_k_2058_);
lean_dec_ref(v_k_2058_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(lean_object* v_x_2062_){
_start:
{
if (lean_obj_tag(v_x_2062_) == 0)
{
lean_object* v___x_2063_; 
v___x_2063_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___closed__0));
return v___x_2063_;
}
else
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_Json_getBool_x3f(v_x_2062_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2081_; 
v_a_2073_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2075_ = v___x_2064_;
v_isShared_2076_ = v_isSharedCheck_2081_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2064_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2081_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2077_, 0, v_a_2073_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2077_);
v___x_2079_ = v___x_2075_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___boxed(lean_object* v_x_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v_x_2082_);
lean_dec(v_x_2082_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(lean_object* v_j_2084_, lean_object* v_k_2085_){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = l_Lean_Json_getObjValD(v_j_2084_, v_k_2085_);
v___x_2087_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v___x_2086_);
lean_dec(v___x_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3___boxed(lean_object* v_j_2088_, lean_object* v_k_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_j_2088_, v_k_2089_);
lean_dec_ref(v_k_2089_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_cmp_2091_, lean_object* v_k_2092_, lean_object* v_v_2093_, lean_object* v_t_2094_){
_start:
{
if (lean_obj_tag(v_t_2094_) == 0)
{
lean_object* v_size_2095_; lean_object* v_k_2096_; lean_object* v_v_2097_; lean_object* v_l_2098_; lean_object* v_r_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2380_; 
v_size_2095_ = lean_ctor_get(v_t_2094_, 0);
v_k_2096_ = lean_ctor_get(v_t_2094_, 1);
v_v_2097_ = lean_ctor_get(v_t_2094_, 2);
v_l_2098_ = lean_ctor_get(v_t_2094_, 3);
v_r_2099_ = lean_ctor_get(v_t_2094_, 4);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_t_2094_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2101_ = v_t_2094_;
v_isShared_2102_ = v_isSharedCheck_2380_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_r_2099_);
lean_inc(v_l_2098_);
lean_inc(v_v_2097_);
lean_inc(v_k_2096_);
lean_inc(v_size_2095_);
lean_dec(v_t_2094_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2380_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
lean_inc_ref(v_cmp_2091_);
lean_inc(v_k_2096_);
lean_inc_ref(v_k_2092_);
v___x_2103_ = lean_apply_2(v_cmp_2091_, v_k_2092_, v_k_2096_);
v___x_2104_ = lean_unbox(v___x_2103_);
switch(v___x_2104_)
{
case 0:
{
lean_object* v_impl_2105_; lean_object* v___x_2106_; 
lean_dec(v_size_2095_);
v_impl_2105_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_2091_, v_k_2092_, v_v_2093_, v_l_2098_);
v___x_2106_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2099_) == 0)
{
lean_object* v_size_2107_; lean_object* v_size_2108_; lean_object* v_k_2109_; lean_object* v_v_2110_; lean_object* v_l_2111_; lean_object* v_r_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v_size_2107_ = lean_ctor_get(v_r_2099_, 0);
v_size_2108_ = lean_ctor_get(v_impl_2105_, 0);
lean_inc(v_size_2108_);
v_k_2109_ = lean_ctor_get(v_impl_2105_, 1);
lean_inc(v_k_2109_);
v_v_2110_ = lean_ctor_get(v_impl_2105_, 2);
lean_inc(v_v_2110_);
v_l_2111_ = lean_ctor_get(v_impl_2105_, 3);
lean_inc(v_l_2111_);
v_r_2112_ = lean_ctor_get(v_impl_2105_, 4);
lean_inc(v_r_2112_);
v___x_2113_ = lean_unsigned_to_nat(3u);
v___x_2114_ = lean_nat_mul(v___x_2113_, v_size_2107_);
v___x_2115_ = lean_nat_dec_lt(v___x_2114_, v_size_2108_);
lean_dec(v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
lean_dec(v_r_2112_);
lean_dec(v_l_2111_);
lean_dec(v_v_2110_);
lean_dec(v_k_2109_);
v___x_2116_ = lean_nat_add(v___x_2106_, v_size_2108_);
lean_dec(v_size_2108_);
v___x_2117_ = lean_nat_add(v___x_2116_, v_size_2107_);
lean_dec(v___x_2116_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 3, v_impl_2105_);
lean_ctor_set(v___x_2101_, 0, v___x_2117_);
v___x_2119_ = v___x_2101_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2120_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2120_, 3, v_impl_2105_);
lean_ctor_set(v_reuseFailAlloc_2120_, 4, v_r_2099_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
else
{
lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2186_; 
v_isSharedCheck_2186_ = !lean_is_exclusive(v_impl_2105_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; lean_object* v_unused_2188_; lean_object* v_unused_2189_; lean_object* v_unused_2190_; lean_object* v_unused_2191_; 
v_unused_2187_ = lean_ctor_get(v_impl_2105_, 4);
lean_dec(v_unused_2187_);
v_unused_2188_ = lean_ctor_get(v_impl_2105_, 3);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_impl_2105_, 2);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_impl_2105_, 1);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_impl_2105_, 0);
lean_dec(v_unused_2191_);
v___x_2122_ = v_impl_2105_;
v_isShared_2123_ = v_isSharedCheck_2186_;
goto v_resetjp_2121_;
}
else
{
lean_dec(v_impl_2105_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2186_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v_size_2124_; lean_object* v_size_2125_; lean_object* v_k_2126_; lean_object* v_v_2127_; lean_object* v_l_2128_; lean_object* v_r_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v_size_2124_ = lean_ctor_get(v_l_2111_, 0);
v_size_2125_ = lean_ctor_get(v_r_2112_, 0);
v_k_2126_ = lean_ctor_get(v_r_2112_, 1);
v_v_2127_ = lean_ctor_get(v_r_2112_, 2);
v_l_2128_ = lean_ctor_get(v_r_2112_, 3);
v_r_2129_ = lean_ctor_get(v_r_2112_, 4);
v___x_2130_ = lean_unsigned_to_nat(2u);
v___x_2131_ = lean_nat_mul(v___x_2130_, v_size_2124_);
v___x_2132_ = lean_nat_dec_lt(v_size_2125_, v___x_2131_);
lean_dec(v___x_2131_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2161_; 
lean_inc(v_r_2129_);
lean_inc(v_l_2128_);
lean_inc(v_v_2127_);
lean_inc(v_k_2126_);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_r_2112_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; lean_object* v_unused_2163_; lean_object* v_unused_2164_; lean_object* v_unused_2165_; lean_object* v_unused_2166_; 
v_unused_2162_ = lean_ctor_get(v_r_2112_, 4);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v_r_2112_, 3);
lean_dec(v_unused_2163_);
v_unused_2164_ = lean_ctor_get(v_r_2112_, 2);
lean_dec(v_unused_2164_);
v_unused_2165_ = lean_ctor_get(v_r_2112_, 1);
lean_dec(v_unused_2165_);
v_unused_2166_ = lean_ctor_get(v_r_2112_, 0);
lean_dec(v_unused_2166_);
v___x_2134_ = v_r_2112_;
v_isShared_2135_ = v_isSharedCheck_2161_;
goto v_resetjp_2133_;
}
else
{
lean_dec(v_r_2112_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2161_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___x_2149_; lean_object* v___y_2151_; 
v___x_2136_ = lean_nat_add(v___x_2106_, v_size_2108_);
lean_dec(v_size_2108_);
v___x_2137_ = lean_nat_add(v___x_2136_, v_size_2107_);
lean_dec(v___x_2136_);
v___x_2149_ = lean_nat_add(v___x_2106_, v_size_2124_);
if (lean_obj_tag(v_l_2128_) == 0)
{
lean_object* v_size_2159_; 
v_size_2159_ = lean_ctor_get(v_l_2128_, 0);
lean_inc(v_size_2159_);
v___y_2151_ = v_size_2159_;
goto v___jp_2150_;
}
else
{
lean_object* v___x_2160_; 
v___x_2160_ = lean_unsigned_to_nat(0u);
v___y_2151_ = v___x_2160_;
goto v___jp_2150_;
}
v___jp_2138_:
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = lean_nat_add(v___y_2139_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec(v___y_2139_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 4, v_r_2099_);
lean_ctor_set(v___x_2134_, 3, v_r_2129_);
lean_ctor_set(v___x_2134_, 2, v_v_2097_);
lean_ctor_set(v___x_2134_, 1, v_k_2096_);
lean_ctor_set(v___x_2134_, 0, v___x_2142_);
v___x_2144_ = v___x_2134_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2148_, 3, v_r_2129_);
lean_ctor_set(v_reuseFailAlloc_2148_, 4, v_r_2099_);
v___x_2144_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2146_; 
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 4, v___x_2144_);
lean_ctor_set(v___x_2122_, 3, v___y_2140_);
lean_ctor_set(v___x_2122_, 2, v_v_2127_);
lean_ctor_set(v___x_2122_, 1, v_k_2126_);
lean_ctor_set(v___x_2122_, 0, v___x_2137_);
v___x_2146_ = v___x_2122_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_k_2126_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_v_2127_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v___y_2140_);
lean_ctor_set(v_reuseFailAlloc_2147_, 4, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
v___jp_2150_:
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2152_ = lean_nat_add(v___x_2149_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec(v___x_2149_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 4, v_l_2128_);
lean_ctor_set(v___x_2101_, 3, v_l_2111_);
lean_ctor_set(v___x_2101_, 2, v_v_2110_);
lean_ctor_set(v___x_2101_, 1, v_k_2109_);
lean_ctor_set(v___x_2101_, 0, v___x_2152_);
v___x_2154_ = v___x_2101_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_k_2109_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v_v_2110_);
lean_ctor_set(v_reuseFailAlloc_2158_, 3, v_l_2111_);
lean_ctor_set(v_reuseFailAlloc_2158_, 4, v_l_2128_);
v___x_2154_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_nat_add(v___x_2106_, v_size_2107_);
if (lean_obj_tag(v_r_2129_) == 0)
{
lean_object* v_size_2156_; 
v_size_2156_ = lean_ctor_get(v_r_2129_, 0);
lean_inc(v_size_2156_);
v___y_2139_ = v___x_2155_;
v___y_2140_ = v___x_2154_;
v___y_2141_ = v_size_2156_;
goto v___jp_2138_;
}
else
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_unsigned_to_nat(0u);
v___y_2139_ = v___x_2155_;
v___y_2140_ = v___x_2154_;
v___y_2141_ = v___x_2157_;
goto v___jp_2138_;
}
}
}
}
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2172_; 
lean_del_object(v___x_2101_);
v___x_2167_ = lean_nat_add(v___x_2106_, v_size_2108_);
lean_dec(v_size_2108_);
v___x_2168_ = lean_nat_add(v___x_2167_, v_size_2107_);
lean_dec(v___x_2167_);
v___x_2169_ = lean_nat_add(v___x_2106_, v_size_2107_);
v___x_2170_ = lean_nat_add(v___x_2169_, v_size_2125_);
lean_dec(v___x_2169_);
lean_inc_ref(v_r_2099_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 4, v_r_2099_);
lean_ctor_set(v___x_2122_, 3, v_r_2112_);
lean_ctor_set(v___x_2122_, 2, v_v_2097_);
lean_ctor_set(v___x_2122_, 1, v_k_2096_);
lean_ctor_set(v___x_2122_, 0, v___x_2170_);
v___x_2172_ = v___x_2122_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2185_, 3, v_r_2112_);
lean_ctor_set(v_reuseFailAlloc_2185_, 4, v_r_2099_);
v___x_2172_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
v_isSharedCheck_2179_ = !lean_is_exclusive(v_r_2099_);
if (v_isSharedCheck_2179_ == 0)
{
lean_object* v_unused_2180_; lean_object* v_unused_2181_; lean_object* v_unused_2182_; lean_object* v_unused_2183_; lean_object* v_unused_2184_; 
v_unused_2180_ = lean_ctor_get(v_r_2099_, 4);
lean_dec(v_unused_2180_);
v_unused_2181_ = lean_ctor_get(v_r_2099_, 3);
lean_dec(v_unused_2181_);
v_unused_2182_ = lean_ctor_get(v_r_2099_, 2);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_r_2099_, 1);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_r_2099_, 0);
lean_dec(v_unused_2184_);
v___x_2174_ = v_r_2099_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_dec(v_r_2099_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 4, v___x_2172_);
lean_ctor_set(v___x_2174_, 3, v_l_2111_);
lean_ctor_set(v___x_2174_, 2, v_v_2110_);
lean_ctor_set(v___x_2174_, 1, v_k_2109_);
lean_ctor_set(v___x_2174_, 0, v___x_2168_);
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_k_2109_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_v_2110_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v_l_2111_);
lean_ctor_set(v_reuseFailAlloc_2178_, 4, v___x_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2192_; 
v_l_2192_ = lean_ctor_get(v_impl_2105_, 3);
lean_inc(v_l_2192_);
if (lean_obj_tag(v_l_2192_) == 0)
{
lean_object* v_r_2193_; lean_object* v_k_2194_; lean_object* v_v_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2206_; 
v_r_2193_ = lean_ctor_get(v_impl_2105_, 4);
v_k_2194_ = lean_ctor_get(v_impl_2105_, 1);
v_v_2195_ = lean_ctor_get(v_impl_2105_, 2);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_impl_2105_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; lean_object* v_unused_2208_; 
v_unused_2207_ = lean_ctor_get(v_impl_2105_, 3);
lean_dec(v_unused_2207_);
v_unused_2208_ = lean_ctor_get(v_impl_2105_, 0);
lean_dec(v_unused_2208_);
v___x_2197_ = v_impl_2105_;
v_isShared_2198_ = v_isSharedCheck_2206_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_r_2193_);
lean_inc(v_v_2195_);
lean_inc(v_k_2194_);
lean_dec(v_impl_2105_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2206_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2199_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2193_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 3, v_r_2193_);
lean_ctor_set(v___x_2197_, 2, v_v_2097_);
lean_ctor_set(v___x_2197_, 1, v_k_2096_);
lean_ctor_set(v___x_2197_, 0, v___x_2106_);
v___x_2201_ = v___x_2197_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_r_2193_);
lean_ctor_set(v_reuseFailAlloc_2205_, 4, v_r_2193_);
v___x_2201_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2203_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 4, v___x_2201_);
lean_ctor_set(v___x_2101_, 3, v_l_2192_);
lean_ctor_set(v___x_2101_, 2, v_v_2195_);
lean_ctor_set(v___x_2101_, 1, v_k_2194_);
lean_ctor_set(v___x_2101_, 0, v___x_2199_);
v___x_2203_ = v___x_2101_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_k_2194_);
lean_ctor_set(v_reuseFailAlloc_2204_, 2, v_v_2195_);
lean_ctor_set(v_reuseFailAlloc_2204_, 3, v_l_2192_);
lean_ctor_set(v_reuseFailAlloc_2204_, 4, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v_r_2209_; 
v_r_2209_ = lean_ctor_get(v_impl_2105_, 4);
lean_inc(v_r_2209_);
if (lean_obj_tag(v_r_2209_) == 0)
{
lean_object* v_k_2210_; lean_object* v_v_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2234_; 
v_k_2210_ = lean_ctor_get(v_impl_2105_, 1);
v_v_2211_ = lean_ctor_get(v_impl_2105_, 2);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_impl_2105_);
if (v_isSharedCheck_2234_ == 0)
{
lean_object* v_unused_2235_; lean_object* v_unused_2236_; lean_object* v_unused_2237_; 
v_unused_2235_ = lean_ctor_get(v_impl_2105_, 4);
lean_dec(v_unused_2235_);
v_unused_2236_ = lean_ctor_get(v_impl_2105_, 3);
lean_dec(v_unused_2236_);
v_unused_2237_ = lean_ctor_get(v_impl_2105_, 0);
lean_dec(v_unused_2237_);
v___x_2213_ = v_impl_2105_;
v_isShared_2214_ = v_isSharedCheck_2234_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_v_2211_);
lean_inc(v_k_2210_);
lean_dec(v_impl_2105_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2234_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v_k_2215_; lean_object* v_v_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2230_; 
v_k_2215_ = lean_ctor_get(v_r_2209_, 1);
v_v_2216_ = lean_ctor_get(v_r_2209_, 2);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_r_2209_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; lean_object* v_unused_2232_; lean_object* v_unused_2233_; 
v_unused_2231_ = lean_ctor_get(v_r_2209_, 4);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_r_2209_, 3);
lean_dec(v_unused_2232_);
v_unused_2233_ = lean_ctor_get(v_r_2209_, 0);
lean_dec(v_unused_2233_);
v___x_2218_ = v_r_2209_;
v_isShared_2219_ = v_isSharedCheck_2230_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_v_2216_);
lean_inc(v_k_2215_);
lean_dec(v_r_2209_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2230_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = lean_unsigned_to_nat(3u);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 4, v_l_2192_);
lean_ctor_set(v___x_2218_, 3, v_l_2192_);
lean_ctor_set(v___x_2218_, 2, v_v_2211_);
lean_ctor_set(v___x_2218_, 1, v_k_2210_);
lean_ctor_set(v___x_2218_, 0, v___x_2106_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_k_2210_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_v_2211_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_l_2192_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_l_2192_);
v___x_2222_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2224_; 
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 4, v_l_2192_);
lean_ctor_set(v___x_2213_, 2, v_v_2097_);
lean_ctor_set(v___x_2213_, 1, v_k_2096_);
lean_ctor_set(v___x_2213_, 0, v___x_2106_);
v___x_2224_ = v___x_2213_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_l_2192_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v_l_2192_);
v___x_2224_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2226_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 4, v___x_2224_);
lean_ctor_set(v___x_2101_, 3, v___x_2222_);
lean_ctor_set(v___x_2101_, 2, v_v_2216_);
lean_ctor_set(v___x_2101_, 1, v_k_2215_);
lean_ctor_set(v___x_2101_, 0, v___x_2220_);
v___x_2226_ = v___x_2101_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_k_2215_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_v_2216_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2238_ = lean_unsigned_to_nat(2u);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 4, v_r_2209_);
lean_ctor_set(v___x_2101_, 3, v_impl_2105_);
lean_ctor_set(v___x_2101_, 0, v___x_2238_);
v___x_2240_ = v___x_2101_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_impl_2105_);
lean_ctor_set(v_reuseFailAlloc_2241_, 4, v_r_2209_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2243_; 
lean_dec(v_v_2097_);
lean_dec(v_k_2096_);
lean_dec_ref(v_cmp_2091_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 2, v_v_2093_);
lean_ctor_set(v___x_2101_, 1, v_k_2092_);
v___x_2243_ = v___x_2101_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_size_2095_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2244_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2244_, 3, v_l_2098_);
lean_ctor_set(v_reuseFailAlloc_2244_, 4, v_r_2099_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
default: 
{
lean_object* v_impl_2245_; lean_object* v___x_2246_; 
lean_dec(v_size_2095_);
v_impl_2245_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_2091_, v_k_2092_, v_v_2093_, v_r_2099_);
v___x_2246_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2098_) == 0)
{
lean_object* v_size_2247_; lean_object* v_size_2248_; lean_object* v_k_2249_; lean_object* v_v_2250_; lean_object* v_l_2251_; lean_object* v_r_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; 
v_size_2247_ = lean_ctor_get(v_l_2098_, 0);
v_size_2248_ = lean_ctor_get(v_impl_2245_, 0);
lean_inc(v_size_2248_);
v_k_2249_ = lean_ctor_get(v_impl_2245_, 1);
lean_inc(v_k_2249_);
v_v_2250_ = lean_ctor_get(v_impl_2245_, 2);
lean_inc(v_v_2250_);
v_l_2251_ = lean_ctor_get(v_impl_2245_, 3);
lean_inc(v_l_2251_);
v_r_2252_ = lean_ctor_get(v_impl_2245_, 4);
lean_inc(v_r_2252_);
v___x_2253_ = lean_unsigned_to_nat(3u);
v___x_2254_ = lean_nat_mul(v___x_2253_, v_size_2247_);
v___x_2255_ = lean_nat_dec_lt(v___x_2254_, v_size_2248_);
lean_dec(v___x_2254_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
lean_dec(v_r_2252_);
lean_dec(v_l_2251_);
lean_dec(v_v_2250_);
lean_dec(v_k_2249_);
v___x_2256_ = lean_nat_add(v___x_2246_, v_size_2247_);
v___x_2257_ = lean_nat_add(v___x_2256_, v_size_2248_);
lean_dec(v_size_2248_);
lean_dec(v___x_2256_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 4, v_impl_2245_);
lean_ctor_set(v___x_2101_, 0, v___x_2257_);
v___x_2259_ = v___x_2101_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2260_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2260_, 3, v_l_2098_);
lean_ctor_set(v_reuseFailAlloc_2260_, 4, v_impl_2245_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
else
{
lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2324_; 
v_isSharedCheck_2324_ = !lean_is_exclusive(v_impl_2245_);
if (v_isSharedCheck_2324_ == 0)
{
lean_object* v_unused_2325_; lean_object* v_unused_2326_; lean_object* v_unused_2327_; lean_object* v_unused_2328_; lean_object* v_unused_2329_; 
v_unused_2325_ = lean_ctor_get(v_impl_2245_, 4);
lean_dec(v_unused_2325_);
v_unused_2326_ = lean_ctor_get(v_impl_2245_, 3);
lean_dec(v_unused_2326_);
v_unused_2327_ = lean_ctor_get(v_impl_2245_, 2);
lean_dec(v_unused_2327_);
v_unused_2328_ = lean_ctor_get(v_impl_2245_, 1);
lean_dec(v_unused_2328_);
v_unused_2329_ = lean_ctor_get(v_impl_2245_, 0);
lean_dec(v_unused_2329_);
v___x_2262_ = v_impl_2245_;
v_isShared_2263_ = v_isSharedCheck_2324_;
goto v_resetjp_2261_;
}
else
{
lean_dec(v_impl_2245_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2324_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v_size_2264_; lean_object* v_k_2265_; lean_object* v_v_2266_; lean_object* v_l_2267_; lean_object* v_r_2268_; lean_object* v_size_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v_size_2264_ = lean_ctor_get(v_l_2251_, 0);
v_k_2265_ = lean_ctor_get(v_l_2251_, 1);
v_v_2266_ = lean_ctor_get(v_l_2251_, 2);
v_l_2267_ = lean_ctor_get(v_l_2251_, 3);
v_r_2268_ = lean_ctor_get(v_l_2251_, 4);
v_size_2269_ = lean_ctor_get(v_r_2252_, 0);
v___x_2270_ = lean_unsigned_to_nat(2u);
v___x_2271_ = lean_nat_mul(v___x_2270_, v_size_2269_);
v___x_2272_ = lean_nat_dec_lt(v_size_2264_, v___x_2271_);
lean_dec(v___x_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2300_; 
lean_inc(v_r_2268_);
lean_inc(v_l_2267_);
lean_inc(v_v_2266_);
lean_inc(v_k_2265_);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_l_2251_);
if (v_isSharedCheck_2300_ == 0)
{
lean_object* v_unused_2301_; lean_object* v_unused_2302_; lean_object* v_unused_2303_; lean_object* v_unused_2304_; lean_object* v_unused_2305_; 
v_unused_2301_ = lean_ctor_get(v_l_2251_, 4);
lean_dec(v_unused_2301_);
v_unused_2302_ = lean_ctor_get(v_l_2251_, 3);
lean_dec(v_unused_2302_);
v_unused_2303_ = lean_ctor_get(v_l_2251_, 2);
lean_dec(v_unused_2303_);
v_unused_2304_ = lean_ctor_get(v_l_2251_, 1);
lean_dec(v_unused_2304_);
v_unused_2305_ = lean_ctor_get(v_l_2251_, 0);
lean_dec(v_unused_2305_);
v___x_2274_ = v_l_2251_;
v_isShared_2275_ = v_isSharedCheck_2300_;
goto v_resetjp_2273_;
}
else
{
lean_dec(v_l_2251_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2300_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2290_; 
v___x_2276_ = lean_nat_add(v___x_2246_, v_size_2247_);
v___x_2277_ = lean_nat_add(v___x_2276_, v_size_2248_);
lean_dec(v_size_2248_);
if (lean_obj_tag(v_l_2267_) == 0)
{
lean_object* v_size_2298_; 
v_size_2298_ = lean_ctor_get(v_l_2267_, 0);
lean_inc(v_size_2298_);
v___y_2290_ = v_size_2298_;
goto v___jp_2289_;
}
else
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_unsigned_to_nat(0u);
v___y_2290_ = v___x_2299_;
goto v___jp_2289_;
}
v___jp_2278_:
{
lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2282_ = lean_nat_add(v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec(v___y_2280_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 4, v_r_2252_);
lean_ctor_set(v___x_2274_, 3, v_r_2268_);
lean_ctor_set(v___x_2274_, 2, v_v_2250_);
lean_ctor_set(v___x_2274_, 1, v_k_2249_);
lean_ctor_set(v___x_2274_, 0, v___x_2282_);
v___x_2284_ = v___x_2274_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_k_2249_);
lean_ctor_set(v_reuseFailAlloc_2288_, 2, v_v_2250_);
lean_ctor_set(v_reuseFailAlloc_2288_, 3, v_r_2268_);
lean_ctor_set(v_reuseFailAlloc_2288_, 4, v_r_2252_);
v___x_2284_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2286_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 4, v___x_2284_);
lean_ctor_set(v___x_2262_, 3, v___y_2279_);
lean_ctor_set(v___x_2262_, 2, v_v_2266_);
lean_ctor_set(v___x_2262_, 1, v_k_2265_);
lean_ctor_set(v___x_2262_, 0, v___x_2277_);
v___x_2286_ = v___x_2262_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_k_2265_);
lean_ctor_set(v_reuseFailAlloc_2287_, 2, v_v_2266_);
lean_ctor_set(v_reuseFailAlloc_2287_, 3, v___y_2279_);
lean_ctor_set(v_reuseFailAlloc_2287_, 4, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
v___jp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2291_ = lean_nat_add(v___x_2276_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec(v___x_2276_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 4, v_l_2267_);
lean_ctor_set(v___x_2101_, 0, v___x_2291_);
v___x_2293_ = v___x_2101_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2297_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2297_, 3, v_l_2098_);
lean_ctor_set(v_reuseFailAlloc_2297_, 4, v_l_2267_);
v___x_2293_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2294_; 
v___x_2294_ = lean_nat_add(v___x_2246_, v_size_2269_);
if (lean_obj_tag(v_r_2268_) == 0)
{
lean_object* v_size_2295_; 
v_size_2295_ = lean_ctor_get(v_r_2268_, 0);
lean_inc(v_size_2295_);
v___y_2279_ = v___x_2293_;
v___y_2280_ = v___x_2294_;
v___y_2281_ = v_size_2295_;
goto v___jp_2278_;
}
else
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_unsigned_to_nat(0u);
v___y_2279_ = v___x_2293_;
v___y_2280_ = v___x_2294_;
v___y_2281_ = v___x_2296_;
goto v___jp_2278_;
}
}
}
}
}
else
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2310_; 
lean_del_object(v___x_2101_);
v___x_2306_ = lean_nat_add(v___x_2246_, v_size_2247_);
v___x_2307_ = lean_nat_add(v___x_2306_, v_size_2248_);
lean_dec(v_size_2248_);
v___x_2308_ = lean_nat_add(v___x_2306_, v_size_2264_);
lean_dec(v___x_2306_);
lean_inc_ref(v_l_2098_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 4, v_l_2251_);
lean_ctor_set(v___x_2262_, 3, v_l_2098_);
lean_ctor_set(v___x_2262_, 2, v_v_2097_);
lean_ctor_set(v___x_2262_, 1, v_k_2096_);
lean_ctor_set(v___x_2262_, 0, v___x_2308_);
v___x_2310_ = v___x_2262_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2308_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2323_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2323_, 3, v_l_2098_);
lean_ctor_set(v_reuseFailAlloc_2323_, 4, v_l_2251_);
v___x_2310_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
v_isSharedCheck_2317_ = !lean_is_exclusive(v_l_2098_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; lean_object* v_unused_2319_; lean_object* v_unused_2320_; lean_object* v_unused_2321_; lean_object* v_unused_2322_; 
v_unused_2318_ = lean_ctor_get(v_l_2098_, 4);
lean_dec(v_unused_2318_);
v_unused_2319_ = lean_ctor_get(v_l_2098_, 3);
lean_dec(v_unused_2319_);
v_unused_2320_ = lean_ctor_get(v_l_2098_, 2);
lean_dec(v_unused_2320_);
v_unused_2321_ = lean_ctor_get(v_l_2098_, 1);
lean_dec(v_unused_2321_);
v_unused_2322_ = lean_ctor_get(v_l_2098_, 0);
lean_dec(v_unused_2322_);
v___x_2312_ = v_l_2098_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_dec(v_l_2098_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 4, v_r_2252_);
lean_ctor_set(v___x_2312_, 3, v___x_2310_);
lean_ctor_set(v___x_2312_, 2, v_v_2250_);
lean_ctor_set(v___x_2312_, 1, v_k_2249_);
lean_ctor_set(v___x_2312_, 0, v___x_2307_);
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_k_2249_);
lean_ctor_set(v_reuseFailAlloc_2316_, 2, v_v_2250_);
lean_ctor_set(v_reuseFailAlloc_2316_, 3, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2316_, 4, v_r_2252_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2330_; 
v_l_2330_ = lean_ctor_get(v_impl_2245_, 3);
lean_inc(v_l_2330_);
if (lean_obj_tag(v_l_2330_) == 0)
{
lean_object* v_r_2331_; lean_object* v_k_2332_; lean_object* v_v_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2356_; 
v_r_2331_ = lean_ctor_get(v_impl_2245_, 4);
v_k_2332_ = lean_ctor_get(v_impl_2245_, 1);
v_v_2333_ = lean_ctor_get(v_impl_2245_, 2);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_impl_2245_);
if (v_isSharedCheck_2356_ == 0)
{
lean_object* v_unused_2357_; lean_object* v_unused_2358_; 
v_unused_2357_ = lean_ctor_get(v_impl_2245_, 3);
lean_dec(v_unused_2357_);
v_unused_2358_ = lean_ctor_get(v_impl_2245_, 0);
lean_dec(v_unused_2358_);
v___x_2335_ = v_impl_2245_;
v_isShared_2336_ = v_isSharedCheck_2356_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_r_2331_);
lean_inc(v_v_2333_);
lean_inc(v_k_2332_);
lean_dec(v_impl_2245_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2356_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v_k_2337_; lean_object* v_v_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2352_; 
v_k_2337_ = lean_ctor_get(v_l_2330_, 1);
v_v_2338_ = lean_ctor_get(v_l_2330_, 2);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_l_2330_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; lean_object* v_unused_2354_; lean_object* v_unused_2355_; 
v_unused_2353_ = lean_ctor_get(v_l_2330_, 4);
lean_dec(v_unused_2353_);
v_unused_2354_ = lean_ctor_get(v_l_2330_, 3);
lean_dec(v_unused_2354_);
v_unused_2355_ = lean_ctor_get(v_l_2330_, 0);
lean_dec(v_unused_2355_);
v___x_2340_ = v_l_2330_;
v_isShared_2341_ = v_isSharedCheck_2352_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_v_2338_);
lean_inc(v_k_2337_);
lean_dec(v_l_2330_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2352_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2342_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2331_, 2);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 4, v_r_2331_);
lean_ctor_set(v___x_2340_, 3, v_r_2331_);
lean_ctor_set(v___x_2340_, 2, v_v_2097_);
lean_ctor_set(v___x_2340_, 1, v_k_2096_);
lean_ctor_set(v___x_2340_, 0, v___x_2246_);
v___x_2344_ = v___x_2340_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2351_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2351_, 3, v_r_2331_);
lean_ctor_set(v_reuseFailAlloc_2351_, 4, v_r_2331_);
v___x_2344_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2346_; 
lean_inc(v_r_2331_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 3, v_r_2331_);
lean_ctor_set(v___x_2335_, 0, v___x_2246_);
v___x_2346_ = v___x_2335_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_k_2332_);
lean_ctor_set(v_reuseFailAlloc_2350_, 2, v_v_2333_);
lean_ctor_set(v_reuseFailAlloc_2350_, 3, v_r_2331_);
lean_ctor_set(v_reuseFailAlloc_2350_, 4, v_r_2331_);
v___x_2346_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2348_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 4, v___x_2346_);
lean_ctor_set(v___x_2101_, 3, v___x_2344_);
lean_ctor_set(v___x_2101_, 2, v_v_2338_);
lean_ctor_set(v___x_2101_, 1, v_k_2337_);
lean_ctor_set(v___x_2101_, 0, v___x_2342_);
v___x_2348_ = v___x_2101_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2342_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_k_2337_);
lean_ctor_set(v_reuseFailAlloc_2349_, 2, v_v_2338_);
lean_ctor_set(v_reuseFailAlloc_2349_, 3, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2349_, 4, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
}
else
{
lean_object* v_r_2359_; 
v_r_2359_ = lean_ctor_get(v_impl_2245_, 4);
lean_inc(v_r_2359_);
if (lean_obj_tag(v_r_2359_) == 0)
{
lean_object* v_k_2360_; lean_object* v_v_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2372_; 
v_k_2360_ = lean_ctor_get(v_impl_2245_, 1);
v_v_2361_ = lean_ctor_get(v_impl_2245_, 2);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_impl_2245_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; lean_object* v_unused_2374_; lean_object* v_unused_2375_; 
v_unused_2373_ = lean_ctor_get(v_impl_2245_, 4);
lean_dec(v_unused_2373_);
v_unused_2374_ = lean_ctor_get(v_impl_2245_, 3);
lean_dec(v_unused_2374_);
v_unused_2375_ = lean_ctor_get(v_impl_2245_, 0);
lean_dec(v_unused_2375_);
v___x_2363_ = v_impl_2245_;
v_isShared_2364_ = v_isSharedCheck_2372_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_v_2361_);
lean_inc(v_k_2360_);
lean_dec(v_impl_2245_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2372_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2365_ = lean_unsigned_to_nat(3u);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 4, v_l_2330_);
lean_ctor_set(v___x_2363_, 2, v_v_2097_);
lean_ctor_set(v___x_2363_, 1, v_k_2096_);
lean_ctor_set(v___x_2363_, 0, v___x_2246_);
v___x_2367_ = v___x_2363_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2371_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2371_, 3, v_l_2330_);
lean_ctor_set(v_reuseFailAlloc_2371_, 4, v_l_2330_);
v___x_2367_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2369_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 4, v_r_2359_);
lean_ctor_set(v___x_2101_, 3, v___x_2367_);
lean_ctor_set(v___x_2101_, 2, v_v_2361_);
lean_ctor_set(v___x_2101_, 1, v_k_2360_);
lean_ctor_set(v___x_2101_, 0, v___x_2365_);
v___x_2369_ = v___x_2101_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2365_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_k_2360_);
lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_v_2361_);
lean_ctor_set(v_reuseFailAlloc_2370_, 3, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2370_, 4, v_r_2359_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2376_ = lean_unsigned_to_nat(2u);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 4, v_impl_2245_);
lean_ctor_set(v___x_2101_, 3, v_r_2359_);
lean_ctor_set(v___x_2101_, 0, v___x_2376_);
v___x_2378_ = v___x_2101_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2379_, 3, v_r_2359_);
lean_ctor_set(v_reuseFailAlloc_2379_, 4, v_impl_2245_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_dec_ref(v_cmp_2091_);
v___x_2381_ = lean_unsigned_to_nat(1u);
v___x_2382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
lean_ctor_set(v___x_2382_, 1, v_k_2092_);
lean_ctor_set(v___x_2382_, 2, v_v_2093_);
lean_ctor_set(v___x_2382_, 3, v_t_2094_);
lean_ctor_set(v___x_2382_, 4, v_t_2094_);
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(lean_object* v_cmp_2383_, lean_object* v_init_2384_, lean_object* v_x_2385_){
_start:
{
if (lean_obj_tag(v_x_2385_) == 0)
{
lean_object* v_k_2386_; lean_object* v_v_2387_; lean_object* v_l_2388_; lean_object* v_r_2389_; lean_object* v___x_2390_; 
v_k_2386_ = lean_ctor_get(v_x_2385_, 1);
lean_inc(v_k_2386_);
v_v_2387_ = lean_ctor_get(v_x_2385_, 2);
lean_inc(v_v_2387_);
v_l_2388_ = lean_ctor_get(v_x_2385_, 3);
lean_inc(v_l_2388_);
v_r_2389_ = lean_ctor_get(v_x_2385_, 4);
lean_inc(v_r_2389_);
lean_dec_ref_known(v_x_2385_, 5);
lean_inc_ref(v_cmp_2383_);
v___x_2390_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_2383_, v_init_2384_, v_l_2388_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_dec(v_r_2389_);
lean_dec(v_v_2387_);
lean_dec(v_k_2386_);
lean_dec_ref(v_cmp_2383_);
return v___x_2390_;
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2392_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2392_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_v_2387_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v_a_2391_);
lean_dec(v_r_2389_);
lean_dec(v_k_2386_);
lean_dec_ref(v_cmp_2383_);
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2402_; 
v_a_2401_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2392_, 1);
lean_inc_ref(v_cmp_2383_);
v___x_2402_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_2383_, v_k_2386_, v_a_2401_, v_a_2391_);
v_init_2384_ = v___x_2402_;
v_x_2385_ = v_r_2389_;
goto _start;
}
}
}
else
{
lean_object* v___x_2404_; 
lean_dec_ref(v_cmp_2383_);
v___x_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2404_, 0, v_init_2384_);
return v___x_2404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(lean_object* v_cmp_2405_, lean_object* v_j_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_Json_getObj_x3f(v_j_2406_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_dec_ref(v_cmp_2405_);
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v_a_2416_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2407_, 1);
v___x_2417_ = lean_box(1);
v___x_2418_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_2405_, v___x_2417_, v_a_2416_);
return v___x_2418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(lean_object* v_x_2422_){
_start:
{
if (lean_obj_tag(v_x_2422_) == 0)
{
lean_object* v___x_2423_; 
v___x_2423_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__0));
return v___x_2423_;
}
else
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__1));
v___x_2425_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(v___x_2424_, v_x_2422_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2442_; 
v_a_2434_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2436_ = v___x_2425_;
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2425_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2438_, 0, v_a_2434_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2438_);
v___x_2440_ = v___x_2436_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(lean_object* v_j_2443_, lean_object* v_k_2444_){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = l_Lean_Json_getObjValD(v_j_2443_, v_k_2444_);
v___x_2446_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(v___x_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4___boxed(lean_object* v_j_2447_, lean_object* v_k_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_j_2447_, v_k_2448_);
lean_dec_ref(v_k_2448_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(lean_object* v_j_2450_, lean_object* v_k_2451_){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = l_Lean_Json_getObjValD(v_j_2450_, v_k_2451_);
v___x_2453_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v___x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1___boxed(lean_object* v_j_2454_, lean_object* v_k_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_j_2454_, v_k_2455_);
lean_dec_ref(v_k_2455_);
return v_res_2456_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5(void){
_start:
{
uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = 1;
v___x_2466_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__4));
v___x_2467_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2466_, v___x_2465_);
return v___x_2467_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__6));
v___x_2470_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__5, &l_Lake_Check_instFromJsonConfig_fromJson___closed__5_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5);
v___x_2471_ = lean_string_append(v___x_2470_, v___x_2469_);
return v___x_2471_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9(void){
_start:
{
uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = 1;
v___x_2475_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__8));
v___x_2476_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2475_, v___x_2474_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__9, &l_Lake_Check_instFromJsonConfig_fromJson___closed__9_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9);
v___x_2478_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2479_ = lean_string_append(v___x_2478_, v___x_2477_);
return v___x_2479_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2482_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__10, &l_Lake_Check_instFromJsonConfig_fromJson___closed__10_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10);
v___x_2483_ = lean_string_append(v___x_2482_, v___x_2481_);
return v___x_2483_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15(void){
_start:
{
uint8_t v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = 1;
v___x_2488_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__14));
v___x_2489_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2488_, v___x_2487_);
return v___x_2489_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__15, &l_Lake_Check_instFromJsonConfig_fromJson___closed__15_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15);
v___x_2491_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2492_ = lean_string_append(v___x_2491_, v___x_2490_);
return v___x_2492_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2494_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__16, &l_Lake_Check_instFromJsonConfig_fromJson___closed__16_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16);
v___x_2495_ = lean_string_append(v___x_2494_, v___x_2493_);
return v___x_2495_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20(void){
_start:
{
uint8_t v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = 1;
v___x_2500_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__19));
v___x_2501_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2500_, v___x_2499_);
return v___x_2501_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__20, &l_Lake_Check_instFromJsonConfig_fromJson___closed__20_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20);
v___x_2503_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2504_ = lean_string_append(v___x_2503_, v___x_2502_);
return v___x_2504_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2506_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__21, &l_Lake_Check_instFromJsonConfig_fromJson___closed__21_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21);
v___x_2507_ = lean_string_append(v___x_2506_, v___x_2505_);
return v___x_2507_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25(void){
_start:
{
uint8_t v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = 1;
v___x_2512_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__24));
v___x_2513_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2512_, v___x_2511_);
return v___x_2513_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__25, &l_Lake_Check_instFromJsonConfig_fromJson___closed__25_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25);
v___x_2515_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2516_ = lean_string_append(v___x_2515_, v___x_2514_);
return v___x_2516_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2517_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2518_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__26, &l_Lake_Check_instFromJsonConfig_fromJson___closed__26_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26);
v___x_2519_ = lean_string_append(v___x_2518_, v___x_2517_);
return v___x_2519_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29(void){
_start:
{
uint8_t v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = 1;
v___x_2523_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__28));
v___x_2524_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2523_, v___x_2522_);
return v___x_2524_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__29, &l_Lake_Check_instFromJsonConfig_fromJson___closed__29_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29);
v___x_2526_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2527_ = lean_string_append(v___x_2526_, v___x_2525_);
return v___x_2527_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2529_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__30, &l_Lake_Check_instFromJsonConfig_fromJson___closed__30_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30);
v___x_2530_ = lean_string_append(v___x_2529_, v___x_2528_);
return v___x_2530_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35(void){
_start:
{
uint8_t v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = 1;
v___x_2536_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__34));
v___x_2537_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2536_, v___x_2535_);
return v___x_2537_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__35, &l_Lake_Check_instFromJsonConfig_fromJson___closed__35_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35);
v___x_2539_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2540_ = lean_string_append(v___x_2539_, v___x_2538_);
return v___x_2540_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2542_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__36, &l_Lake_Check_instFromJsonConfig_fromJson___closed__36_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36);
v___x_2543_ = lean_string_append(v___x_2542_, v___x_2541_);
return v___x_2543_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41(void){
_start:
{
uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = 1;
v___x_2549_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__40));
v___x_2550_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2549_, v___x_2548_);
return v___x_2550_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2551_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__41, &l_Lake_Check_instFromJsonConfig_fromJson___closed__41_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41);
v___x_2552_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2553_ = lean_string_append(v___x_2552_, v___x_2551_);
return v___x_2553_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2555_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__42, &l_Lake_Check_instFromJsonConfig_fromJson___closed__42_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42);
v___x_2556_ = lean_string_append(v___x_2555_, v___x_2554_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instFromJsonConfig_fromJson(lean_object* v_json_2557_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
lean_inc(v_json_2557_);
v___x_2559_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_2557_, v___x_2558_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2569_; 
lean_dec(v_json_2557_);
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2569_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2569_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2564_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__12, &l_Lake_Check_instFromJsonConfig_fromJson___closed__12_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12);
v___x_2565_ = lean_string_append(v___x_2564_, v_a_2560_);
lean_dec(v_a_2560_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2565_);
v___x_2567_ = v___x_2562_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
else
{
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec(v_json_2557_);
v_a_2570_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2559_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2559_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
lean_ctor_set_tag(v___x_2572_, 0);
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_a_2578_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2578_);
lean_dec_ref_known(v___x_2559_, 1);
v___x_2579_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
lean_inc(v_json_2557_);
v___x_2580_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_2557_, v___x_2579_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2590_; 
lean_dec(v_a_2578_);
lean_dec(v_json_2557_);
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2590_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2590_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2585_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__17, &l_Lake_Check_instFromJsonConfig_fromJson___closed__17_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17);
v___x_2586_ = lean_string_append(v___x_2585_, v_a_2581_);
lean_dec(v_a_2581_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2586_);
v___x_2588_ = v___x_2583_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
else
{
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec(v_a_2578_);
lean_dec(v_json_2557_);
v_a_2591_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2580_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2580_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 0);
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_a_2599_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2580_, 1);
v___x_2600_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
lean_inc(v_json_2557_);
v___x_2601_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_2557_, v___x_2600_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v_a_2599_);
lean_dec(v_a_2578_);
lean_dec(v_json_2557_);
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2611_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2611_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; 
v___x_2606_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__22, &l_Lake_Check_instFromJsonConfig_fromJson___closed__22_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22);
v___x_2607_ = lean_string_append(v___x_2606_, v_a_2602_);
lean_dec(v_a_2602_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2607_);
v___x_2609_ = v___x_2604_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
else
{
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec(v_a_2599_);
lean_dec(v_a_2578_);
lean_dec(v_json_2557_);
v_a_2612_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2601_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2601_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set_tag(v___x_2614_, 0);
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_a_2620_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2621_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
lean_inc(v_json_2557_);
v___x_2622_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_json_2557_, v___x_2621_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_a_2620_);
lean_dec(v_a_2599_);
lean_dec(v_a_2578_);
lean_dec(v_json_2557_);
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2627_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__27, &l_Lake_Check_instFromJsonConfig_fromJson___closed__27_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27);
v___x_2628_ = lean_string_append(v___x_2627_, v_a_2623_);
lean_dec(v_a_2623_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2628_);
v___x_2630_ = v___x_2625_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
else
{
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v_a_2620_);
lean_dec(v_a_2599_);
lean_dec(v_a_2578_);
lean_dec(v_json_2557_);
v_a_2633_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2622_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2622_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set_tag(v___x_2635_, 0);
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v_a_2641_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2622_, 1);
v___x_2642_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7));
lean_inc(v_json_2557_);
v___x_2643_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_2557_, v___x_2642_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_a_2599_);
lean_dec(v_a_2578_);
lean_dec(v_json_2557_);
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2653_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2653_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2648_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__31, &l_Lake_Check_instFromJsonConfig_fromJson___closed__31_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31);
v___x_2649_ = lean_string_append(v___x_2648_, v_a_2644_);
lean_dec(v_a_2644_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2649_);
v___x_2651_ = v___x_2646_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
else
{
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_a_2599_);
lean_dec(v_a_2578_);
lean_dec(v_json_2557_);
v_a_2654_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2643_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2643_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
lean_ctor_set_tag(v___x_2656_, 0);
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v_a_2662_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2663_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
lean_inc(v_json_2557_);
v___x_2664_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_json_2557_, v___x_2663_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2674_; 
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_a_2599_);
lean_dec(v_a_2578_);
lean_dec(v_json_2557_);
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2674_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2674_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2669_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__37, &l_Lake_Check_instFromJsonConfig_fromJson___closed__37_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37);
v___x_2670_ = lean_string_append(v___x_2669_, v_a_2665_);
lean_dec(v_a_2665_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2670_);
v___x_2672_ = v___x_2667_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
else
{
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_a_2599_);
lean_dec(v_a_2578_);
lean_dec(v_json_2557_);
v_a_2675_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2664_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2664_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
lean_ctor_set_tag(v___x_2677_, 0);
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v_a_2683_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2664_, 1);
v___x_2684_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_2685_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_json_2557_, v___x_2684_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_a_2599_);
lean_dec(v_a_2578_);
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2695_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2695_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2693_; 
v___x_2690_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__43, &l_Lake_Check_instFromJsonConfig_fromJson___closed__43_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43);
v___x_2691_ = lean_string_append(v___x_2690_, v_a_2686_);
lean_dec(v_a_2686_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2691_);
v___x_2693_ = v___x_2688_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
else
{
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_a_2599_);
lean_dec(v_a_2578_);
v_a_2696_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2685_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2685_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 0);
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2712_; 
v_a_2704_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2706_ = v___x_2685_;
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2685_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2708_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2708_, 0, v_a_2578_);
lean_ctor_set(v___x_2708_, 1, v_a_2599_);
lean_ctor_set(v___x_2708_, 2, v_a_2620_);
lean_ctor_set(v___x_2708_, 3, v_a_2641_);
lean_ctor_set(v___x_2708_, 4, v_a_2662_);
lean_ctor_set(v___x_2708_, 5, v_a_2683_);
lean_ctor_set(v___x_2708_, 6, v_a_2704_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2708_);
v___x_2710_ = v___x_2706_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10(lean_object* v_cmp_2713_, lean_object* v_00_u03b2_2714_, lean_object* v_k_2715_, lean_object* v_v_2716_, lean_object* v_t_2717_, lean_object* v_hl_2718_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_2713_, v_k_2715_, v_v_2716_, v_t_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(lean_object* v_k_2722_, lean_object* v_x_2723_){
_start:
{
if (lean_obj_tag(v_x_2723_) == 0)
{
lean_object* v___x_2724_; 
lean_dec_ref(v_k_2722_);
v___x_2724_ = lean_box(0);
return v___x_2724_;
}
else
{
lean_object* v_val_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_val_2725_ = lean_ctor_get(v_x_2723_, 0);
v___x_2726_ = lean_alloc_ctor(1, 0, 1);
v___x_2727_ = lean_unbox(v_val_2725_);
lean_ctor_set_uint8(v___x_2726_, 0, v___x_2727_);
v___x_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2728_, 0, v_k_2722_);
lean_ctor_set(v___x_2728_, 1, v___x_2726_);
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2728_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
return v___x_2730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2___boxed(lean_object* v_k_2731_, lean_object* v_x_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v_k_2731_, v_x_2732_);
lean_dec(v_x_2732_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(size_t v_sz_2734_, size_t v_i_2735_, lean_object* v_bs_2736_){
_start:
{
uint8_t v___x_2737_; 
v___x_2737_ = lean_usize_dec_lt(v_i_2735_, v_sz_2734_);
if (v___x_2737_ == 0)
{
return v_bs_2736_;
}
else
{
lean_object* v_v_2738_; lean_object* v___x_2739_; lean_object* v_bs_x27_2740_; lean_object* v___x_2741_; size_t v___x_2742_; size_t v___x_2743_; lean_object* v___x_2744_; 
v_v_2738_ = lean_array_uget(v_bs_2736_, v_i_2735_);
v___x_2739_ = lean_unsigned_to_nat(0u);
v_bs_x27_2740_ = lean_array_uset(v_bs_2736_, v_i_2735_, v___x_2739_);
v___x_2741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2741_, 0, v_v_2738_);
v___x_2742_ = ((size_t)1ULL);
v___x_2743_ = lean_usize_add(v_i_2735_, v___x_2742_);
v___x_2744_ = lean_array_uset(v_bs_x27_2740_, v_i_2735_, v___x_2741_);
v_i_2735_ = v___x_2743_;
v_bs_2736_ = v___x_2744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0___boxed(lean_object* v_sz_2746_, lean_object* v_i_2747_, lean_object* v_bs_2748_){
_start:
{
size_t v_sz_boxed_2749_; size_t v_i_boxed_2750_; lean_object* v_res_2751_; 
v_sz_boxed_2749_ = lean_unbox_usize(v_sz_2746_);
lean_dec(v_sz_2746_);
v_i_boxed_2750_ = lean_unbox_usize(v_i_2747_);
lean_dec(v_i_2747_);
v_res_2751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_boxed_2749_, v_i_boxed_2750_, v_bs_2748_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(lean_object* v_a_2752_){
_start:
{
size_t v_sz_2753_; size_t v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v_sz_2753_ = lean_array_size(v_a_2752_);
v___x_2754_ = ((size_t)0ULL);
v___x_2755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_2753_, v___x_2754_, v_a_2752_);
v___x_2756_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(lean_object* v_x_2757_){
_start:
{
if (lean_obj_tag(v_x_2757_) == 0)
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_box(0);
return v___x_2758_;
}
else
{
lean_object* v_val_2759_; lean_object* v___x_2760_; 
v_val_2759_ = lean_ctor_get(v_x_2757_, 0);
lean_inc(v_val_2759_);
lean_dec_ref_known(v_x_2757_, 1);
v___x_2760_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_val_2759_);
return v___x_2760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
if (lean_obj_tag(v_a_2761_) == 0)
{
lean_object* v___x_2763_; 
v___x_2763_ = lean_array_to_list(v_a_2762_);
return v___x_2763_;
}
else
{
lean_object* v_head_2764_; lean_object* v_tail_2765_; lean_object* v___x_2766_; 
v_head_2764_ = lean_ctor_get(v_a_2761_, 0);
lean_inc(v_head_2764_);
v_tail_2765_ = lean_ctor_get(v_a_2761_, 1);
lean_inc(v_tail_2765_);
lean_dec_ref_known(v_a_2761_, 2);
v___x_2766_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2762_, v_head_2764_);
v_a_2761_ = v_tail_2765_;
v_a_2762_ = v___x_2766_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(lean_object* v_t_2768_){
_start:
{
if (lean_obj_tag(v_t_2768_) == 0)
{
lean_object* v_size_2769_; lean_object* v_k_2770_; lean_object* v_v_2771_; lean_object* v_l_2772_; lean_object* v_r_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2783_; 
v_size_2769_ = lean_ctor_get(v_t_2768_, 0);
v_k_2770_ = lean_ctor_get(v_t_2768_, 1);
v_v_2771_ = lean_ctor_get(v_t_2768_, 2);
v_l_2772_ = lean_ctor_get(v_t_2768_, 3);
v_r_2773_ = lean_ctor_get(v_t_2768_, 4);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_t_2768_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2775_ = v_t_2768_;
v_isShared_2776_ = v_isSharedCheck_2783_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_r_2773_);
lean_inc(v_l_2772_);
lean_inc(v_v_2771_);
lean_inc(v_k_2770_);
lean_inc(v_size_2769_);
lean_dec(v_t_2768_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2783_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2777_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_v_2771_);
v___x_2778_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_l_2772_);
v___x_2779_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_r_2773_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 4, v___x_2779_);
lean_ctor_set(v___x_2775_, 3, v___x_2778_);
lean_ctor_set(v___x_2775_, 2, v___x_2777_);
v___x_2781_ = v___x_2775_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_size_2769_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_k_2770_);
lean_ctor_set(v_reuseFailAlloc_2782_, 2, v___x_2777_);
lean_ctor_set(v_reuseFailAlloc_2782_, 3, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2782_, 4, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
else
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_box(1);
return v___x_2784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(lean_object* v_map_2785_){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_map_2785_);
v___x_2787_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(lean_object* v_k_2788_, lean_object* v_x_2789_){
_start:
{
if (lean_obj_tag(v_x_2789_) == 0)
{
lean_object* v___x_2790_; 
lean_dec_ref(v_k_2788_);
v___x_2790_ = lean_box(0);
return v___x_2790_;
}
else
{
lean_object* v_val_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_val_2791_ = lean_ctor_get(v_x_2789_, 0);
lean_inc(v_val_2791_);
lean_dec_ref_known(v_x_2789_, 1);
v___x_2792_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(v_val_2791_);
v___x_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2793_, 0, v_k_2788_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_box(0);
v___x_2795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
return v___x_2795_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instToJsonConfig_toJson(lean_object* v_x_2798_){
_start:
{
lean_object* v_challenge__module_2799_; lean_object* v_solution__module_2800_; lean_object* v_theorem__names_2801_; lean_object* v_definition__names_2802_; lean_object* v_permitted__axioms_2803_; lean_object* v_enable__nanoda_x3f_2804_; lean_object* v_external__kernels_x3f_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v_challenge__module_2799_ = lean_ctor_get(v_x_2798_, 0);
lean_inc_ref(v_challenge__module_2799_);
v_solution__module_2800_ = lean_ctor_get(v_x_2798_, 1);
lean_inc_ref(v_solution__module_2800_);
v_theorem__names_2801_ = lean_ctor_get(v_x_2798_, 2);
lean_inc_ref(v_theorem__names_2801_);
v_definition__names_2802_ = lean_ctor_get(v_x_2798_, 3);
lean_inc(v_definition__names_2802_);
v_permitted__axioms_2803_ = lean_ctor_get(v_x_2798_, 4);
lean_inc_ref(v_permitted__axioms_2803_);
v_enable__nanoda_x3f_2804_ = lean_ctor_get(v_x_2798_, 5);
lean_inc(v_enable__nanoda_x3f_2804_);
v_external__kernels_x3f_2805_ = lean_ctor_get(v_x_2798_, 6);
lean_inc(v_external__kernels_x3f_2805_);
lean_dec_ref(v_x_2798_);
v___x_2806_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
v___x_2807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2807_, 0, v_challenge__module_2799_);
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = lean_box(0);
v___x_2810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
v___x_2812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2812_, 0, v_solution__module_2800_);
v___x_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v___x_2809_);
v___x_2815_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
v___x_2816_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_theorem__names_2801_);
v___x_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2815_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v___x_2818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
lean_ctor_set(v___x_2818_, 1, v___x_2809_);
v___x_2819_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
v___x_2820_ = l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(v_definition__names_2802_);
v___x_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
lean_ctor_set(v___x_2822_, 1, v___x_2809_);
v___x_2823_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7));
v___x_2824_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_permitted__axioms_2803_);
v___x_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2823_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
lean_ctor_set(v___x_2826_, 1, v___x_2809_);
v___x_2827_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
v___x_2828_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v___x_2827_, v_enable__nanoda_x3f_2804_);
lean_dec(v_enable__nanoda_x3f_2804_);
v___x_2829_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_2830_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(v___x_2829_, v_external__kernels_x3f_2805_);
v___x_2831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
lean_ctor_set(v___x_2831_, 1, v___x_2809_);
v___x_2832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2828_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
v___x_2833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2826_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2822_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2818_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2814_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2810_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = ((lean_object*)(l_Lake_Check_instToJsonConfig_toJson___closed__0));
v___x_2839_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(v___x_2837_, v___x_2838_);
v___x_2840_ = l_Lean_Json_mkObj(v___x_2839_);
lean_dec(v___x_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(lean_object* v_x_2849_, lean_object* v_x_2850_){
_start:
{
if (lean_obj_tag(v_x_2849_) == 0)
{
lean_object* v___x_2851_; 
v___x_2851_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_2851_;
}
else
{
lean_object* v_val_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_val_2852_ = lean_ctor_get(v_x_2849_, 0);
v___x_2853_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_2854_ = lean_unbox(v_val_2852_);
v___x_2855_ = l_Bool_repr___redArg(v___x_2854_);
v___x_2856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2853_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = l_Repr_addAppParen(v___x_2856_, v_x_2850_);
return v___x_2857_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___boxed(lean_object* v_x_2858_, lean_object* v_x_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_x_2858_, v_x_2859_);
lean_dec(v_x_2859_);
lean_dec(v_x_2858_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_Check_instReprConfig_repr_spec__4(lean_object* v_a_2861_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = lean_nat_to_int(v_a_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(lean_object* v_x_2863_, lean_object* v_x_2864_, lean_object* v_x_2865_){
_start:
{
if (lean_obj_tag(v_x_2865_) == 0)
{
lean_dec(v_x_2863_);
return v_x_2864_;
}
else
{
lean_object* v_head_2866_; lean_object* v_tail_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2878_; 
v_head_2866_ = lean_ctor_get(v_x_2865_, 0);
v_tail_2867_ = lean_ctor_get(v_x_2865_, 1);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_x_2865_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2869_ = v_x_2865_;
v_isShared_2870_ = v_isSharedCheck_2878_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_tail_2867_);
lean_inc(v_head_2866_);
lean_dec(v_x_2865_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2878_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
lean_inc(v_x_2863_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set_tag(v___x_2869_, 5);
lean_ctor_set(v___x_2869_, 1, v_x_2863_);
lean_ctor_set(v___x_2869_, 0, v_x_2864_);
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_x_2864_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_x_2863_);
v___x_2872_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2873_ = l_String_quote(v_head_2866_);
v___x_2874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
v___x_2875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2872_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v_x_2864_ = v___x_2875_;
v_x_2865_ = v_tail_2867_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_2879_, lean_object* v_x_2880_, lean_object* v_x_2881_){
_start:
{
if (lean_obj_tag(v_x_2881_) == 0)
{
lean_dec(v_x_2879_);
return v_x_2880_;
}
else
{
lean_object* v_head_2882_; lean_object* v_tail_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2894_; 
v_head_2882_ = lean_ctor_get(v_x_2881_, 0);
v_tail_2883_ = lean_ctor_get(v_x_2881_, 1);
v_isSharedCheck_2894_ = !lean_is_exclusive(v_x_2881_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2885_ = v_x_2881_;
v_isShared_2886_ = v_isSharedCheck_2894_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_tail_2883_);
lean_inc(v_head_2882_);
lean_dec(v_x_2881_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2894_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
lean_inc(v_x_2879_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set_tag(v___x_2885_, 5);
lean_ctor_set(v___x_2885_, 1, v_x_2879_);
lean_ctor_set(v___x_2885_, 0, v_x_2880_);
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_x_2880_);
lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_x_2879_);
v___x_2888_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2889_ = l_String_quote(v_head_2882_);
v___x_2890_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
v___x_2891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2888_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(v_x_2879_, v___x_2891_, v_tail_2883_);
return v___x_2892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = l_String_quote(v___y_2895_);
v___x_2897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(lean_object* v_x_2898_, lean_object* v_x_2899_){
_start:
{
if (lean_obj_tag(v_x_2898_) == 0)
{
lean_object* v___x_2900_; 
lean_dec(v_x_2899_);
v___x_2900_ = lean_box(0);
return v___x_2900_;
}
else
{
lean_object* v_tail_2901_; 
v_tail_2901_ = lean_ctor_get(v_x_2898_, 1);
if (lean_obj_tag(v_tail_2901_) == 0)
{
lean_object* v_head_2902_; lean_object* v___x_2903_; 
lean_dec(v_x_2899_);
v_head_2902_ = lean_ctor_get(v_x_2898_, 0);
lean_inc(v_head_2902_);
lean_dec_ref_known(v_x_2898_, 2);
v___x_2903_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_2902_);
return v___x_2903_;
}
else
{
lean_object* v_head_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
lean_inc(v_tail_2901_);
v_head_2904_ = lean_ctor_get(v_x_2898_, 0);
lean_inc(v_head_2904_);
lean_dec_ref_known(v_x_2898_, 2);
v___x_2905_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_2904_);
v___x_2906_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(v_x_2899_, v___x_2905_, v_tail_2901_);
return v___x_2906_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__0));
v___x_2915_ = lean_string_length(v___x_2914_);
return v___x_2915_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4);
v___x_2917_ = lean_nat_to_int(v___x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(lean_object* v_xs_2925_){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; 
v___x_2926_ = lean_array_get_size(v_xs_2925_);
v___x_2927_ = lean_unsigned_to_nat(0u);
v___x_2928_ = lean_nat_dec_eq(v___x_2926_, v___x_2927_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2929_ = lean_array_to_list(v_xs_2925_);
v___x_2930_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_2931_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(v___x_2929_, v___x_2930_);
v___x_2932_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5);
v___x_2933_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__6));
v___x_2934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
lean_ctor_set(v___x_2934_, 1, v___x_2931_);
v___x_2935_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_2936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2934_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
v___x_2937_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2932_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
v___x_2938_ = l_Std_Format_fill(v___x_2937_);
return v___x_2938_;
}
else
{
lean_object* v___x_2939_; 
lean_dec_ref(v_xs_2925_);
v___x_2939_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__9));
return v___x_2939_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(lean_object* v_x_2940_, lean_object* v_x_2941_){
_start:
{
if (lean_obj_tag(v_x_2940_) == 0)
{
lean_object* v___x_2942_; 
v___x_2942_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_2942_;
}
else
{
lean_object* v_val_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_val_2943_ = lean_ctor_get(v_x_2940_, 0);
lean_inc(v_val_2943_);
lean_dec_ref_known(v_x_2940_, 1);
v___x_2944_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_2945_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_val_2943_);
v___x_2946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2944_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
v___x_2947_ = l_Repr_addAppParen(v___x_2946_, v_x_2941_);
return v___x_2947_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1___boxed(lean_object* v_x_2948_, lean_object* v_x_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_x_2948_, v_x_2949_);
lean_dec(v_x_2949_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(lean_object* v_init_2951_, lean_object* v_x_2952_){
_start:
{
if (lean_obj_tag(v_x_2952_) == 0)
{
lean_object* v_k_2953_; lean_object* v_v_2954_; lean_object* v_l_2955_; lean_object* v_r_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v_k_2953_ = lean_ctor_get(v_x_2952_, 1);
v_v_2954_ = lean_ctor_get(v_x_2952_, 2);
v_l_2955_ = lean_ctor_get(v_x_2952_, 3);
v_r_2956_ = lean_ctor_get(v_x_2952_, 4);
v___x_2957_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_2951_, v_r_2956_);
lean_inc(v_v_2954_);
lean_inc(v_k_2953_);
v___x_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2958_, 0, v_k_2953_);
lean_ctor_set(v___x_2958_, 1, v_v_2954_);
v___x_2959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
lean_ctor_set(v___x_2959_, 1, v___x_2957_);
v_init_2951_ = v___x_2959_;
v_x_2952_ = v_l_2955_;
goto _start;
}
else
{
return v_init_2951_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4___boxed(lean_object* v_init_2961_, lean_object* v_x_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_2961_, v_x_2962_);
lean_dec(v_x_2962_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(lean_object* v_x_2964_, lean_object* v_x_2965_, lean_object* v_x_2966_){
_start:
{
if (lean_obj_tag(v_x_2966_) == 0)
{
lean_dec(v_x_2964_);
return v_x_2965_;
}
else
{
lean_object* v_head_2967_; lean_object* v_tail_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2977_; 
v_head_2967_ = lean_ctor_get(v_x_2966_, 0);
v_tail_2968_ = lean_ctor_get(v_x_2966_, 1);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_x_2966_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2970_ = v_x_2966_;
v_isShared_2971_ = v_isSharedCheck_2977_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_tail_2968_);
lean_inc(v_head_2967_);
lean_dec(v_x_2966_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2977_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
lean_inc(v_x_2964_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set_tag(v___x_2970_, 5);
lean_ctor_set(v___x_2970_, 1, v_x_2964_);
lean_ctor_set(v___x_2970_, 0, v_x_2965_);
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_x_2965_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_x_2964_);
v___x_2973_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
lean_ctor_set(v___x_2974_, 1, v_head_2967_);
v_x_2965_ = v___x_2974_;
v_x_2966_ = v_tail_2968_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(lean_object* v_x_2978_, lean_object* v_x_2979_){
_start:
{
if (lean_obj_tag(v_x_2978_) == 0)
{
lean_object* v___x_2980_; 
lean_dec(v_x_2979_);
v___x_2980_ = lean_box(0);
return v___x_2980_;
}
else
{
lean_object* v_tail_2981_; 
v_tail_2981_ = lean_ctor_get(v_x_2978_, 1);
if (lean_obj_tag(v_tail_2981_) == 0)
{
lean_object* v_head_2982_; 
lean_dec(v_x_2979_);
v_head_2982_ = lean_ctor_get(v_x_2978_, 0);
lean_inc(v_head_2982_);
lean_dec_ref_known(v_x_2978_, 2);
return v_head_2982_;
}
else
{
lean_object* v_head_2983_; lean_object* v___x_2984_; 
lean_inc(v_tail_2981_);
v_head_2983_ = lean_ctor_get(v_x_2978_, 0);
lean_inc(v_head_2983_);
lean_dec_ref_known(v_x_2978_, 2);
v___x_2984_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(v_x_2979_, v_head_2983_, v_tail_2981_);
return v___x_2984_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__0));
v___x_2988_ = lean_string_length(v___x_2987_);
return v___x_2988_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2);
v___x_2990_ = lean_nat_to_int(v___x_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(lean_object* v_x_2995_){
_start:
{
lean_object* v_fst_2996_; lean_object* v_snd_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3020_; 
v_fst_2996_ = lean_ctor_get(v_x_2995_, 0);
v_snd_2997_ = lean_ctor_get(v_x_2995_, 1);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_x_2995_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_2999_ = v_x_2995_;
v_isShared_3000_ = v_isSharedCheck_3020_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_snd_2997_);
lean_inc(v_fst_2996_);
lean_dec(v_x_2995_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3020_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_3001_ = l_String_quote(v_fst_2996_);
v___x_3002_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
v___x_3003_ = lean_box(0);
if (v_isShared_3000_ == 0)
{
lean_ctor_set_tag(v___x_2999_, 1);
lean_ctor_set(v___x_2999_, 1, v___x_3003_);
lean_ctor_set(v___x_2999_, 0, v___x_3002_);
v___x_3005_ = v___x_2999_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3002_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v___x_3003_);
v___x_3005_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; 
v___x_3006_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_snd_2997_);
v___x_3007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
lean_ctor_set(v___x_3007_, 1, v___x_3005_);
v___x_3008_ = l_List_reverse___redArg(v___x_3007_);
v___x_3009_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3010_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(v___x_3008_, v___x_3009_);
v___x_3011_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3);
v___x_3012_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__4));
v___x_3013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v___x_3010_);
v___x_3014_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__5));
v___x_3015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3011_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = 0;
v___x_3018_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3018_, 0, v___x_3016_);
lean_ctor_set_uint8(v___x_3018_, sizeof(void*)*1, v___x_3017_);
return v___x_3018_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(lean_object* v_x_3021_, lean_object* v_x_3022_, lean_object* v_x_3023_){
_start:
{
if (lean_obj_tag(v_x_3023_) == 0)
{
lean_dec(v_x_3021_);
return v_x_3022_;
}
else
{
lean_object* v_head_3024_; lean_object* v_tail_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3035_; 
v_head_3024_ = lean_ctor_get(v_x_3023_, 0);
v_tail_3025_ = lean_ctor_get(v_x_3023_, 1);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_x_3023_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3027_ = v_x_3023_;
v_isShared_3028_ = v_isSharedCheck_3035_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_tail_3025_);
lean_inc(v_head_3024_);
lean_dec(v_x_3023_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3035_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
lean_inc(v_x_3021_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set_tag(v___x_3027_, 5);
lean_ctor_set(v___x_3027_, 1, v_x_3021_);
lean_ctor_set(v___x_3027_, 0, v_x_3022_);
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_x_3022_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_x_3021_);
v___x_3030_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3024_);
v___x_3032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v_x_3022_ = v___x_3032_;
v_x_3023_ = v_tail_3025_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(lean_object* v_x_3036_, lean_object* v_x_3037_, lean_object* v_x_3038_){
_start:
{
if (lean_obj_tag(v_x_3038_) == 0)
{
lean_dec(v_x_3036_);
return v_x_3037_;
}
else
{
lean_object* v_head_3039_; lean_object* v_tail_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3050_; 
v_head_3039_ = lean_ctor_get(v_x_3038_, 0);
v_tail_3040_ = lean_ctor_get(v_x_3038_, 1);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_x_3038_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3042_ = v_x_3038_;
v_isShared_3043_ = v_isSharedCheck_3050_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_tail_3040_);
lean_inc(v_head_3039_);
lean_dec(v_x_3038_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3050_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
lean_inc(v_x_3036_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set_tag(v___x_3042_, 5);
lean_ctor_set(v___x_3042_, 1, v_x_3036_);
lean_ctor_set(v___x_3042_, 0, v_x_3037_);
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_x_3037_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_x_3036_);
v___x_3045_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3039_);
v___x_3047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3045_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(v_x_3036_, v___x_3047_, v_tail_3040_);
return v___x_3048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(lean_object* v_x_3051_, lean_object* v_x_3052_){
_start:
{
if (lean_obj_tag(v_x_3051_) == 0)
{
lean_object* v___x_3053_; 
lean_dec(v_x_3052_);
v___x_3053_ = lean_box(0);
return v___x_3053_;
}
else
{
lean_object* v_tail_3054_; 
v_tail_3054_ = lean_ctor_get(v_x_3051_, 1);
if (lean_obj_tag(v_tail_3054_) == 0)
{
lean_object* v_head_3055_; lean_object* v___x_3056_; 
lean_dec(v_x_3052_);
v_head_3055_ = lean_ctor_get(v_x_3051_, 0);
lean_inc(v_head_3055_);
lean_dec_ref_known(v_x_3051_, 2);
v___x_3056_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3055_);
return v___x_3056_;
}
else
{
lean_object* v_head_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
lean_inc(v_tail_3054_);
v_head_3057_ = lean_ctor_get(v_x_3051_, 0);
lean_inc(v_head_3057_);
lean_dec_ref_known(v_x_3051_, 2);
v___x_3058_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3057_);
v___x_3059_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(v_x_3052_, v___x_3058_, v_tail_3054_);
return v___x_3059_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__1));
v___x_3063_ = lean_string_length(v___x_3062_);
return v___x_3063_;
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1);
v___x_3065_ = lean_nat_to_int(v___x_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(lean_object* v_a_3068_){
_start:
{
if (lean_obj_tag(v_a_3068_) == 0)
{
lean_object* v___x_3069_; 
v___x_3069_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0));
return v___x_3069_;
}
else
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; lean_object* v___x_3079_; 
v___x_3070_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3071_ = l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(v_a_3068_, v___x_3070_);
v___x_3072_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2);
v___x_3073_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__3));
v___x_3074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set(v___x_3074_, 1, v___x_3071_);
v___x_3075_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_3076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3072_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = 0;
v___x_3079_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3079_, 0, v___x_3077_);
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*1, v___x_3078_);
return v___x_3079_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(lean_object* v_x_3083_, lean_object* v_x_3084_){
_start:
{
if (lean_obj_tag(v_x_3083_) == 0)
{
lean_object* v___x_3085_; 
v___x_3085_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3085_;
}
else
{
lean_object* v_val_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v_val_3086_ = lean_ctor_get(v_x_3083_, 0);
v___x_3087_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3088_ = lean_unsigned_to_nat(1024u);
v___x_3089_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__1));
v___x_3090_ = lean_box(0);
v___x_3091_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v___x_3090_, v_val_3086_);
v___x_3092_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v___x_3091_);
v___x_3093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3089_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = l_Repr_addAppParen(v___x_3093_, v___x_3088_);
v___x_3095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3087_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
v___x_3096_ = l_Repr_addAppParen(v___x_3095_, v_x_3084_);
return v___x_3096_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___boxed(lean_object* v_x_3097_, lean_object* v_x_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_x_3097_, v_x_3098_);
lean_dec(v_x_3098_);
lean_dec(v_x_3097_);
return v_res_3099_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = lean_unsigned_to_nat(20u);
v___x_3113_ = lean_nat_to_int(v___x_3112_);
return v___x_3113_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_unsigned_to_nat(19u);
v___x_3117_ = lean_nat_to_int(v___x_3116_);
return v___x_3117_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = lean_unsigned_to_nat(17u);
v___x_3121_ = lean_nat_to_int(v___x_3120_);
return v___x_3121_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = lean_unsigned_to_nat(18u);
v___x_3129_ = lean_nat_to_int(v___x_3128_);
return v___x_3129_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = lean_unsigned_to_nat(21u);
v___x_3133_ = lean_nat_to_int(v___x_3132_);
return v___x_3133_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__0));
v___x_3136_ = lean_string_length(v___x_3135_);
return v___x_3136_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__18, &l_Lake_Check_instReprConfig_repr___redArg___closed__18_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18);
v___x_3138_ = lean_nat_to_int(v___x_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___redArg(lean_object* v_x_3143_){
_start:
{
lean_object* v_challenge__module_3144_; lean_object* v_solution__module_3145_; lean_object* v_theorem__names_3146_; lean_object* v_definition__names_3147_; lean_object* v_permitted__axioms_3148_; lean_object* v_enable__nanoda_x3f_3149_; lean_object* v_external__kernels_x3f_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v_challenge__module_3144_ = lean_ctor_get(v_x_3143_, 0);
lean_inc_ref(v_challenge__module_3144_);
v_solution__module_3145_ = lean_ctor_get(v_x_3143_, 1);
lean_inc_ref(v_solution__module_3145_);
v_theorem__names_3146_ = lean_ctor_get(v_x_3143_, 2);
lean_inc_ref(v_theorem__names_3146_);
v_definition__names_3147_ = lean_ctor_get(v_x_3143_, 3);
lean_inc(v_definition__names_3147_);
v_permitted__axioms_3148_ = lean_ctor_get(v_x_3143_, 4);
lean_inc_ref(v_permitted__axioms_3148_);
v_enable__nanoda_x3f_3149_ = lean_ctor_get(v_x_3143_, 5);
lean_inc(v_enable__nanoda_x3f_3149_);
v_external__kernels_x3f_3150_ = lean_ctor_get(v_x_3143_, 6);
lean_inc(v_external__kernels_x3f_3150_);
lean_dec_ref(v_x_3143_);
v___x_3151_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__4));
v___x_3152_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__5));
v___x_3153_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__6, &l_Lake_Check_instReprConfig_repr___redArg___closed__6_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6);
v___x_3154_ = l_String_quote(v_challenge__module_3144_);
v___x_3155_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
v___x_3156_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3153_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = 0;
v___x_3158_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3158_, 0, v___x_3156_);
lean_ctor_set_uint8(v___x_3158_, sizeof(void*)*1, v___x_3157_);
v___x_3159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3152_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__2));
v___x_3161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3159_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = lean_box(1);
v___x_3163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__7));
v___x_3165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3163_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3151_);
v___x_3167_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__8, &l_Lake_Check_instReprConfig_repr___redArg___closed__8_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8);
v___x_3168_ = l_String_quote(v_solution__module_3145_);
v___x_3169_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
v___x_3170_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3167_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
lean_ctor_set_uint8(v___x_3171_, sizeof(void*)*1, v___x_3157_);
v___x_3172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3166_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v___x_3160_);
v___x_3174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v___x_3162_);
v___x_3175_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__9));
v___x_3176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3174_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
lean_ctor_set(v___x_3177_, 1, v___x_3151_);
v___x_3178_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__10, &l_Lake_Check_instReprConfig_repr___redArg___closed__10_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10);
v___x_3179_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_theorem__names_3146_);
v___x_3180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3178_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
lean_ctor_set_uint8(v___x_3181_, sizeof(void*)*1, v___x_3157_);
v___x_3182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3177_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
lean_ctor_set(v___x_3183_, 1, v___x_3160_);
v___x_3184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_ctor_set(v___x_3184_, 1, v___x_3162_);
v___x_3185_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__11));
v___x_3186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3184_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
lean_ctor_set(v___x_3187_, 1, v___x_3151_);
v___x_3188_ = lean_unsigned_to_nat(0u);
v___x_3189_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_definition__names_3147_, v___x_3188_);
v___x_3190_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3153_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
v___x_3191_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set_uint8(v___x_3191_, sizeof(void*)*1, v___x_3157_);
v___x_3192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3187_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v___x_3193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
lean_ctor_set(v___x_3193_, 1, v___x_3160_);
v___x_3194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
lean_ctor_set(v___x_3194_, 1, v___x_3162_);
v___x_3195_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__12));
v___x_3196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3194_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
lean_ctor_set(v___x_3197_, 1, v___x_3151_);
v___x_3198_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_permitted__axioms_3148_);
v___x_3199_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3153_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
lean_ctor_set_uint8(v___x_3200_, sizeof(void*)*1, v___x_3157_);
v___x_3201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3197_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
v___x_3202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
lean_ctor_set(v___x_3202_, 1, v___x_3160_);
v___x_3203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
lean_ctor_set(v___x_3203_, 1, v___x_3162_);
v___x_3204_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__13));
v___x_3205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3203_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
lean_ctor_set(v___x_3206_, 1, v___x_3151_);
v___x_3207_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__14, &l_Lake_Check_instReprConfig_repr___redArg___closed__14_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14);
v___x_3208_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_enable__nanoda_x3f_3149_, v___x_3188_);
lean_dec(v_enable__nanoda_x3f_3149_);
v___x_3209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3207_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set_uint8(v___x_3210_, sizeof(void*)*1, v___x_3157_);
v___x_3211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3206_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_ctor_set(v___x_3212_, 1, v___x_3160_);
v___x_3213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
lean_ctor_set(v___x_3213_, 1, v___x_3162_);
v___x_3214_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__15));
v___x_3215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3213_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
lean_ctor_set(v___x_3216_, 1, v___x_3151_);
v___x_3217_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__16, &l_Lake_Check_instReprConfig_repr___redArg___closed__16_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16);
v___x_3218_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_external__kernels_x3f_3150_, v___x_3188_);
lean_dec(v_external__kernels_x3f_3150_);
v___x_3219_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3217_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
lean_ctor_set_uint8(v___x_3220_, sizeof(void*)*1, v___x_3157_);
v___x_3221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3216_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__19, &l_Lake_Check_instReprConfig_repr___redArg___closed__19_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19);
v___x_3223_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__20));
v___x_3224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v___x_3221_);
v___x_3225_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__21));
v___x_3226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3224_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3222_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set_uint8(v___x_3228_, sizeof(void*)*1, v___x_3157_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr(lean_object* v_x_3229_, lean_object* v_prec_3230_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lake_Check_instReprConfig_repr___redArg(v_x_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___boxed(lean_object* v_x_3232_, lean_object* v_prec_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Lake_Check_instReprConfig_repr(v_x_3232_, v_prec_3233_);
lean_dec(v_prec_3233_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(lean_object* v_a_3235_, lean_object* v_n_3236_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v_a_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___boxed(lean_object* v_a_3238_, lean_object* v_n_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(v_a_3238_, v_n_3239_);
lean_dec(v_n_3239_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(lean_object* v_x_3241_, lean_object* v_x_3242_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_x_3241_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___boxed(lean_object* v_x_3244_, lean_object* v_x_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(v_x_3244_, v_x_3245_);
lean_dec(v_x_3245_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(lean_object* v_s_3249_){
_start:
{
uint32_t v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3251_ = 10;
v___x_3252_ = lean_string_push(v_s_3249_, v___x_3251_);
v___x_3253_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0(v___x_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0___boxed(lean_object* v_s_3254_, lean_object* v_a_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v_s_3254_);
return v_res_3256_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1(void){
_start:
{
uint32_t v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = 2;
v___x_3259_ = lean_box_uint32(v___x_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(lean_object* v_msg_3260_){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3262_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_3263_ = lean_string_append(v___x_3262_, v_msg_3260_);
v___x_3264_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_3263_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3272_; 
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3272_ == 0)
{
lean_object* v_unused_3273_; 
v_unused_3273_ = lean_ctor_get(v___x_3264_, 0);
lean_dec(v_unused_3273_);
v___x_3266_ = v___x_3264_;
v_isShared_3267_ = v_isSharedCheck_3272_;
goto v_resetjp_3265_;
}
else
{
lean_dec(v___x_3264_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3272_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3268_; lean_object* v___x_3270_; 
v___x_3268_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1;
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v___x_3268_);
v___x_3270_ = v___x_3266_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3268_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
v_a_3274_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3264_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3264_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed(lean_object* v_msg_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v_msg_3282_);
lean_dec_ref(v_msg_3282_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(lean_object* v_cmd_3288_, lean_object* v_projectDir_3289_){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; 
v___x_3291_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__0));
lean_inc_ref(v_projectDir_3289_);
v___x_3292_ = l_System_FilePath_join(v_projectDir_3289_, v___x_3291_);
v___x_3293_ = l_System_FilePath_pathExists(v___x_3292_);
lean_dec_ref(v___x_3292_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3294_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_3295_ = lean_string_append(v___x_3294_, v_projectDir_3289_);
lean_dec_ref(v_projectDir_3289_);
v___x_3296_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__1));
v___x_3297_ = lean_string_append(v___x_3295_, v___x_3296_);
v___x_3298_ = lean_string_append(v___x_3297_, v_cmd_3288_);
v___x_3299_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__2));
v___x_3300_ = lean_string_append(v___x_3298_, v___x_3299_);
v___x_3301_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3300_);
lean_dec_ref(v___x_3300_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3310_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3310_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3310_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3306_, 0, v_a_3302_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v___x_3306_);
v___x_3308_ = v___x_3304_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
v_a_3311_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3301_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3301_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
else
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
lean_dec_ref(v_projectDir_3289_);
v___x_3319_ = lean_box(0);
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
return v___x_3320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___boxed(lean_object* v_cmd_3321_, lean_object* v_projectDir_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v_cmd_3321_, v_projectDir_3322_);
lean_dec_ref(v_cmd_3321_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext(lean_object* v_cmd_3332_, lean_object* v_lean_3333_, lean_object* v_lake_3334_, lean_object* v_projectDir_3335_){
_start:
{
uint8_t v___x_3337_; 
v___x_3337_ = l_System_Platform_isLinux;
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
lean_dec_ref(v_projectDir_3335_);
lean_dec_ref(v_lean_3333_);
v___x_3338_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__0));
v___x_3339_ = lean_string_append(v___x_3338_, v_cmd_3332_);
v___x_3340_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0));
v___x_3341_ = lean_string_append(v___x_3339_, v___x_3340_);
v___x_3342_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3341_);
lean_dec_ref(v___x_3341_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3351_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3351_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3351_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_a_3343_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v___x_3347_);
v___x_3349_ = v___x_3345_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
v_a_3352_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3342_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3342_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
else
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___y_3363_; 
v___x_3360_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1));
v___x_3361_ = lean_io_getenv(v___x_3360_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v___x_3462_; 
v___x_3462_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6));
v___y_3363_ = v___x_3462_;
goto v___jp_3362_;
}
else
{
lean_object* v_val_3463_; 
v_val_3463_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_val_3463_);
lean_dec_ref_known(v___x_3361_, 1);
v___y_3363_ = v_val_3463_;
goto v___jp_3362_;
}
v___jp_3362_:
{
lean_object* v___x_3364_; lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3461_; 
lean_inc_ref(v___y_3363_);
v___x_3364_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___y_3363_);
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3367_ = v___x_3364_;
v_isShared_3368_ = v_isSharedCheck_3461_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3364_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3461_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
if (lean_obj_tag(v_a_3365_) == 1)
{
lean_object* v_val_3369_; lean_object* v_binDir_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3439_; 
lean_del_object(v___x_3367_);
lean_dec_ref(v___y_3363_);
v_val_3369_ = lean_ctor_get(v_a_3365_, 0);
lean_inc(v_val_3369_);
lean_dec_ref_known(v_a_3365_, 1);
v_binDir_3370_ = lean_ctor_get(v_lean_3333_, 6);
lean_inc_ref(v_binDir_3370_);
lean_dec_ref(v_lean_3333_);
v___x_3371_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2));
v___x_3372_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_3371_);
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3439_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3439_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
if (lean_obj_tag(v_a_3373_) == 1)
{
lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3413_; 
lean_del_object(v___x_3375_);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_a_3373_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; 
v_unused_3414_ = lean_ctor_get(v_a_3373_, 0);
lean_dec(v_unused_3414_);
v___x_3378_ = v_a_3373_;
v_isShared_3379_ = v_isSharedCheck_3413_;
goto v_resetjp_3377_;
}
else
{
lean_dec(v_a_3373_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3413_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_io_realpath(v_projectDir_3335_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3404_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3404_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3404_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v_lake_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3399_; 
v_lake_3385_ = lean_ctor_get(v_lake_3334_, 5);
v___x_3386_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3));
lean_inc_ref(v_binDir_3370_);
v___x_3387_ = l_System_FilePath_join(v_binDir_3370_, v___x_3386_);
v___x_3388_ = l_System_FilePath_exeExtension;
v___x_3389_ = l_System_FilePath_addExtension(v___x_3387_, v___x_3388_);
v___x_3390_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4));
v___x_3391_ = l_System_FilePath_join(v_binDir_3370_, v___x_3390_);
v___x_3392_ = l_System_FilePath_addExtension(v___x_3391_, v___x_3388_);
v___x_3393_ = lean_box(0);
v___x_3394_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_3395_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__17));
v___x_3396_ = lean_box(1);
lean_inc_ref(v_lake_3385_);
v___x_3397_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_3397_, 0, v_a_3381_);
lean_ctor_set(v___x_3397_, 1, v___x_3393_);
lean_ctor_set(v___x_3397_, 2, v___x_3393_);
lean_ctor_set(v___x_3397_, 3, v___x_3394_);
lean_ctor_set(v___x_3397_, 4, v___x_3394_);
lean_ctor_set(v___x_3397_, 5, v___x_3394_);
lean_ctor_set(v___x_3397_, 6, v___x_3395_);
lean_ctor_set(v___x_3397_, 7, v___x_3395_);
lean_ctor_set(v___x_3397_, 8, v_val_3369_);
lean_ctor_set(v___x_3397_, 9, v_lake_3385_);
lean_ctor_set(v___x_3397_, 10, v___x_3389_);
lean_ctor_set(v___x_3397_, 11, v___x_3392_);
lean_ctor_set(v___x_3397_, 12, v___x_3396_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v___x_3397_);
v___x_3399_ = v___x_3378_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3397_);
v___x_3399_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
lean_object* v___x_3401_; 
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3399_);
v___x_3401_ = v___x_3383_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3399_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_del_object(v___x_3378_);
lean_dec_ref(v_binDir_3370_);
lean_dec(v_val_3369_);
v_a_3405_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3380_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3380_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
}
else
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec(v_a_3373_);
lean_dec_ref(v_binDir_3370_);
lean_dec(v_val_3369_);
lean_dec_ref(v_projectDir_3335_);
v___x_3415_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__0));
v___x_3416_ = lean_string_append(v___x_3415_, v_cmd_3332_);
v___x_3417_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5));
v___x_3418_ = lean_string_append(v___x_3416_, v___x_3417_);
v___x_3419_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3418_);
lean_dec_ref(v___x_3418_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3430_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3422_ = v___x_3419_;
v_isShared_3423_ = v_isSharedCheck_3430_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3419_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3430_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v_a_3420_);
v___x_3425_ = v___x_3375_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3427_; 
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3425_);
v___x_3427_ = v___x_3422_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_del_object(v___x_3375_);
v_a_3431_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3419_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3419_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
}
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_dec(v_a_3365_);
lean_dec_ref(v_projectDir_3335_);
lean_dec_ref(v_lean_3333_);
v___x_3440_ = l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError(v_cmd_3332_, v___y_3363_);
lean_dec_ref(v___y_3363_);
v___x_3441_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3440_);
lean_dec_ref(v___x_3440_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3452_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3444_ = v___x_3441_;
v_isShared_3445_ = v_isSharedCheck_3452_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3441_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3452_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v_a_3442_);
v___x_3447_ = v___x_3367_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3449_; 
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v___x_3447_);
v___x_3449_ = v___x_3444_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_del_object(v___x_3367_);
v_a_3453_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3441_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3441_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___boxed(lean_object* v_cmd_3464_, lean_object* v_lean_3465_, lean_object* v_lake_3466_, lean_object* v_projectDir_3467_, lean_object* v_a_3468_){
_start:
{
lean_object* v_res_3469_; 
v_res_3469_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v_cmd_3464_, v_lean_3465_, v_lake_3466_, v_projectDir_3467_);
lean_dec_ref(v_lake_3466_);
lean_dec_ref(v_cmd_3464_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(lean_object* v_init_3476_, lean_object* v_x_3477_){
_start:
{
lean_object* v_d_3480_; 
if (lean_obj_tag(v_x_3477_) == 0)
{
lean_object* v_k_3483_; lean_object* v_v_3484_; lean_object* v_l_3485_; lean_object* v_r_3486_; lean_object* v___x_3487_; 
v_k_3483_ = lean_ctor_get(v_x_3477_, 1);
v_v_3484_ = lean_ctor_get(v_x_3477_, 2);
v_l_3485_ = lean_ctor_get(v_x_3477_, 3);
v_r_3486_ = lean_ctor_get(v_x_3477_, 4);
v___x_3487_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_3476_, v_l_3485_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
if (lean_obj_tag(v_a_3488_) == 0)
{
lean_object* v_a_3489_; 
v_a_3489_ = lean_ctor_get(v_a_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v_a_3488_, 1);
v_d_3480_ = v_a_3489_;
goto v___jp_3479_;
}
else
{
lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3529_; 
v_isSharedCheck_3529_ = !lean_is_exclusive(v_a_3488_);
if (v_isSharedCheck_3529_ == 0)
{
lean_object* v_unused_3530_; 
v_unused_3530_ = lean_ctor_get(v_a_3488_, 0);
lean_dec(v_unused_3530_);
v___x_3491_ = v_a_3488_;
v_isShared_3492_ = v_isSharedCheck_3529_;
goto v_resetjp_3490_;
}
else
{
lean_dec(v_a_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3529_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3528_; 
v___x_3493_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__17));
v___x_3494_ = lean_unsigned_to_nat(0u);
v___x_3495_ = lean_array_get_borrowed(v___x_3493_, v_v_3484_, v___x_3494_);
lean_inc(v___x_3495_);
v___x_3496_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_3495_);
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3528_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3528_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3501_; 
v___x_3501_ = lean_box(0);
if (lean_obj_tag(v_a_3497_) == 0)
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3502_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_3503_ = lean_string_append(v___x_3502_, v_k_3483_);
v___x_3504_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1));
v___x_3505_ = lean_string_append(v___x_3503_, v___x_3504_);
v___x_3506_ = lean_string_append(v___x_3505_, v___x_3495_);
v___x_3507_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2));
v___x_3508_ = lean_string_append(v___x_3506_, v___x_3507_);
v___x_3509_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3508_);
lean_dec_ref(v___x_3508_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3512_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v_a_3510_);
v___x_3512_ = v___x_3499_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3510_);
v___x_3512_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3514_; 
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v___x_3512_);
v___x_3514_ = v___x_3491_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3512_);
v___x_3514_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3515_; 
v___x_3515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3514_);
lean_ctor_set(v___x_3515_, 1, v___x_3501_);
v_d_3480_ = v___x_3515_;
goto v___jp_3479_;
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_del_object(v___x_3499_);
lean_del_object(v___x_3491_);
v_a_3518_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3509_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3509_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
else
{
lean_object* v___x_3526_; 
lean_dec_ref_known(v_a_3497_, 1);
lean_del_object(v___x_3499_);
lean_del_object(v___x_3491_);
v___x_3526_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v_init_3476_ = v___x_3526_;
v_x_3477_ = v_r_3486_;
goto _start;
}
}
}
}
}
else
{
return v___x_3487_;
}
}
else
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3531_, 0, v_init_3476_);
v___x_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
return v___x_3532_;
}
v___jp_3479_:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v_d_3480_);
v___x_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
return v___x_3482_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___boxed(lean_object* v_init_3533_, lean_object* v_x_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_3533_, v_x_3534_);
lean_dec(v_x_3534_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(lean_object* v_init_3538_, lean_object* v_x_3539_){
_start:
{
lean_object* v_d_3542_; 
if (lean_obj_tag(v_x_3539_) == 0)
{
lean_object* v_k_3545_; lean_object* v_v_3546_; lean_object* v_l_3547_; lean_object* v_r_3548_; lean_object* v___x_3549_; 
v_k_3545_ = lean_ctor_get(v_x_3539_, 1);
v_v_3546_ = lean_ctor_get(v_x_3539_, 2);
v_l_3547_ = lean_ctor_get(v_x_3539_, 3);
v_r_3548_ = lean_ctor_get(v_x_3539_, 4);
v___x_3549_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(v_init_3538_, v_l_3547_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3587_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3552_ = v___x_3549_;
v_isShared_3553_ = v_isSharedCheck_3587_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3549_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3587_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
if (lean_obj_tag(v_a_3550_) == 0)
{
lean_object* v_a_3554_; 
lean_del_object(v___x_3552_);
v_a_3554_ = lean_ctor_get(v_a_3550_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v_a_3550_, 1);
v_d_3542_ = v_a_3554_;
goto v___jp_3541_;
}
else
{
lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3585_; 
v_isSharedCheck_3585_ = !lean_is_exclusive(v_a_3550_);
if (v_isSharedCheck_3585_ == 0)
{
lean_object* v_unused_3586_; 
v_unused_3586_ = lean_ctor_get(v_a_3550_, 0);
lean_dec(v_unused_3586_);
v___x_3556_ = v_a_3550_;
v_isShared_3557_ = v_isSharedCheck_3585_;
goto v_resetjp_3555_;
}
else
{
lean_dec(v_a_3550_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3585_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; 
v___x_3558_ = lean_box(0);
v___x_3559_ = lean_array_get_size(v_v_3546_);
v___x_3560_ = lean_unsigned_to_nat(0u);
v___x_3561_ = lean_nat_dec_eq(v___x_3559_, v___x_3560_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; 
lean_del_object(v___x_3556_);
lean_del_object(v___x_3552_);
v___x_3562_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v_init_3538_ = v___x_3562_;
v_x_3539_ = v_r_3548_;
goto _start;
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3564_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_3565_ = lean_string_append(v___x_3564_, v_k_3545_);
v___x_3566_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___closed__0));
v___x_3567_ = lean_string_append(v___x_3565_, v___x_3566_);
v___x_3568_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3567_);
lean_dec_ref(v___x_3567_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3571_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref_known(v___x_3568_, 1);
if (v_isShared_3557_ == 0)
{
lean_ctor_set_tag(v___x_3556_, 0);
lean_ctor_set(v___x_3556_, 0, v_a_3569_);
v___x_3571_ = v___x_3556_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3569_);
v___x_3571_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3573_; 
if (v_isShared_3553_ == 0)
{
lean_ctor_set_tag(v___x_3552_, 1);
lean_ctor_set(v___x_3552_, 0, v___x_3571_);
v___x_3573_ = v___x_3552_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
lean_object* v___x_3574_; 
v___x_3574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
lean_ctor_set(v___x_3574_, 1, v___x_3558_);
v_d_3542_ = v___x_3574_;
goto v___jp_3541_;
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_del_object(v___x_3556_);
lean_del_object(v___x_3552_);
v_a_3577_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3568_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3568_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
}
}
}
else
{
return v___x_3549_;
}
}
else
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3588_, 0, v_init_3538_);
v___x_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
return v___x_3589_;
}
v___jp_3541_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3543_, 0, v_d_3542_);
v___x_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
return v___x_3544_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___boxed(lean_object* v_init_3590_, lean_object* v_x_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(v_init_3590_, v_x_3591_);
lean_dec(v_x_3591_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(lean_object* v_k_3594_, lean_object* v_v_3595_, lean_object* v_t_3596_){
_start:
{
if (lean_obj_tag(v_t_3596_) == 0)
{
lean_object* v_size_3597_; lean_object* v_k_3598_; lean_object* v_v_3599_; lean_object* v_l_3600_; lean_object* v_r_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3881_; 
v_size_3597_ = lean_ctor_get(v_t_3596_, 0);
v_k_3598_ = lean_ctor_get(v_t_3596_, 1);
v_v_3599_ = lean_ctor_get(v_t_3596_, 2);
v_l_3600_ = lean_ctor_get(v_t_3596_, 3);
v_r_3601_ = lean_ctor_get(v_t_3596_, 4);
v_isSharedCheck_3881_ = !lean_is_exclusive(v_t_3596_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3603_ = v_t_3596_;
v_isShared_3604_ = v_isSharedCheck_3881_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_r_3601_);
lean_inc(v_l_3600_);
lean_inc(v_v_3599_);
lean_inc(v_k_3598_);
lean_inc(v_size_3597_);
lean_dec(v_t_3596_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3881_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
uint8_t v___x_3605_; 
v___x_3605_ = lean_string_compare(v_k_3594_, v_k_3598_);
switch(v___x_3605_)
{
case 0:
{
lean_object* v_impl_3606_; lean_object* v___x_3607_; 
lean_dec(v_size_3597_);
v_impl_3606_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(v_k_3594_, v_v_3595_, v_l_3600_);
v___x_3607_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3601_) == 0)
{
lean_object* v_size_3608_; lean_object* v_size_3609_; lean_object* v_k_3610_; lean_object* v_v_3611_; lean_object* v_l_3612_; lean_object* v_r_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; uint8_t v___x_3616_; 
v_size_3608_ = lean_ctor_get(v_r_3601_, 0);
v_size_3609_ = lean_ctor_get(v_impl_3606_, 0);
lean_inc(v_size_3609_);
v_k_3610_ = lean_ctor_get(v_impl_3606_, 1);
lean_inc(v_k_3610_);
v_v_3611_ = lean_ctor_get(v_impl_3606_, 2);
lean_inc(v_v_3611_);
v_l_3612_ = lean_ctor_get(v_impl_3606_, 3);
lean_inc(v_l_3612_);
v_r_3613_ = lean_ctor_get(v_impl_3606_, 4);
lean_inc(v_r_3613_);
v___x_3614_ = lean_unsigned_to_nat(3u);
v___x_3615_ = lean_nat_mul(v___x_3614_, v_size_3608_);
v___x_3616_ = lean_nat_dec_lt(v___x_3615_, v_size_3609_);
lean_dec(v___x_3615_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3620_; 
lean_dec(v_r_3613_);
lean_dec(v_l_3612_);
lean_dec(v_v_3611_);
lean_dec(v_k_3610_);
v___x_3617_ = lean_nat_add(v___x_3607_, v_size_3609_);
lean_dec(v_size_3609_);
v___x_3618_ = lean_nat_add(v___x_3617_, v_size_3608_);
lean_dec(v___x_3617_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 3, v_impl_3606_);
lean_ctor_set(v___x_3603_, 0, v___x_3618_);
v___x_3620_ = v___x_3603_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3618_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_k_3598_);
lean_ctor_set(v_reuseFailAlloc_3621_, 2, v_v_3599_);
lean_ctor_set(v_reuseFailAlloc_3621_, 3, v_impl_3606_);
lean_ctor_set(v_reuseFailAlloc_3621_, 4, v_r_3601_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
else
{
lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3687_; 
v_isSharedCheck_3687_ = !lean_is_exclusive(v_impl_3606_);
if (v_isSharedCheck_3687_ == 0)
{
lean_object* v_unused_3688_; lean_object* v_unused_3689_; lean_object* v_unused_3690_; lean_object* v_unused_3691_; lean_object* v_unused_3692_; 
v_unused_3688_ = lean_ctor_get(v_impl_3606_, 4);
lean_dec(v_unused_3688_);
v_unused_3689_ = lean_ctor_get(v_impl_3606_, 3);
lean_dec(v_unused_3689_);
v_unused_3690_ = lean_ctor_get(v_impl_3606_, 2);
lean_dec(v_unused_3690_);
v_unused_3691_ = lean_ctor_get(v_impl_3606_, 1);
lean_dec(v_unused_3691_);
v_unused_3692_ = lean_ctor_get(v_impl_3606_, 0);
lean_dec(v_unused_3692_);
v___x_3623_ = v_impl_3606_;
v_isShared_3624_ = v_isSharedCheck_3687_;
goto v_resetjp_3622_;
}
else
{
lean_dec(v_impl_3606_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3687_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v_size_3625_; lean_object* v_size_3626_; lean_object* v_k_3627_; lean_object* v_v_3628_; lean_object* v_l_3629_; lean_object* v_r_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; uint8_t v___x_3633_; 
v_size_3625_ = lean_ctor_get(v_l_3612_, 0);
v_size_3626_ = lean_ctor_get(v_r_3613_, 0);
v_k_3627_ = lean_ctor_get(v_r_3613_, 1);
v_v_3628_ = lean_ctor_get(v_r_3613_, 2);
v_l_3629_ = lean_ctor_get(v_r_3613_, 3);
v_r_3630_ = lean_ctor_get(v_r_3613_, 4);
v___x_3631_ = lean_unsigned_to_nat(2u);
v___x_3632_ = lean_nat_mul(v___x_3631_, v_size_3625_);
v___x_3633_ = lean_nat_dec_lt(v_size_3626_, v___x_3632_);
lean_dec(v___x_3632_);
if (v___x_3633_ == 0)
{
lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3662_; 
lean_inc(v_r_3630_);
lean_inc(v_l_3629_);
lean_inc(v_v_3628_);
lean_inc(v_k_3627_);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_r_3613_);
if (v_isSharedCheck_3662_ == 0)
{
lean_object* v_unused_3663_; lean_object* v_unused_3664_; lean_object* v_unused_3665_; lean_object* v_unused_3666_; lean_object* v_unused_3667_; 
v_unused_3663_ = lean_ctor_get(v_r_3613_, 4);
lean_dec(v_unused_3663_);
v_unused_3664_ = lean_ctor_get(v_r_3613_, 3);
lean_dec(v_unused_3664_);
v_unused_3665_ = lean_ctor_get(v_r_3613_, 2);
lean_dec(v_unused_3665_);
v_unused_3666_ = lean_ctor_get(v_r_3613_, 1);
lean_dec(v_unused_3666_);
v_unused_3667_ = lean_ctor_get(v_r_3613_, 0);
lean_dec(v_unused_3667_);
v___x_3635_ = v_r_3613_;
v_isShared_3636_ = v_isSharedCheck_3662_;
goto v_resetjp_3634_;
}
else
{
lean_dec(v_r_3613_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3662_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___x_3650_; lean_object* v___y_3652_; 
v___x_3637_ = lean_nat_add(v___x_3607_, v_size_3609_);
lean_dec(v_size_3609_);
v___x_3638_ = lean_nat_add(v___x_3637_, v_size_3608_);
lean_dec(v___x_3637_);
v___x_3650_ = lean_nat_add(v___x_3607_, v_size_3625_);
if (lean_obj_tag(v_l_3629_) == 0)
{
lean_object* v_size_3660_; 
v_size_3660_ = lean_ctor_get(v_l_3629_, 0);
lean_inc(v_size_3660_);
v___y_3652_ = v_size_3660_;
goto v___jp_3651_;
}
else
{
lean_object* v___x_3661_; 
v___x_3661_ = lean_unsigned_to_nat(0u);
v___y_3652_ = v___x_3661_;
goto v___jp_3651_;
}
v___jp_3639_:
{
lean_object* v___x_3643_; lean_object* v___x_3645_; 
v___x_3643_ = lean_nat_add(v___y_3640_, v___y_3642_);
lean_dec(v___y_3642_);
lean_dec(v___y_3640_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 4, v_r_3601_);
lean_ctor_set(v___x_3635_, 3, v_r_3630_);
lean_ctor_set(v___x_3635_, 2, v_v_3599_);
lean_ctor_set(v___x_3635_, 1, v_k_3598_);
lean_ctor_set(v___x_3635_, 0, v___x_3643_);
v___x_3645_ = v___x_3635_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3643_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_k_3598_);
lean_ctor_set(v_reuseFailAlloc_3649_, 2, v_v_3599_);
lean_ctor_set(v_reuseFailAlloc_3649_, 3, v_r_3630_);
lean_ctor_set(v_reuseFailAlloc_3649_, 4, v_r_3601_);
v___x_3645_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3647_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 4, v___x_3645_);
lean_ctor_set(v___x_3623_, 3, v___y_3641_);
lean_ctor_set(v___x_3623_, 2, v_v_3628_);
lean_ctor_set(v___x_3623_, 1, v_k_3627_);
lean_ctor_set(v___x_3623_, 0, v___x_3638_);
v___x_3647_ = v___x_3623_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3638_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_k_3627_);
lean_ctor_set(v_reuseFailAlloc_3648_, 2, v_v_3628_);
lean_ctor_set(v_reuseFailAlloc_3648_, 3, v___y_3641_);
lean_ctor_set(v_reuseFailAlloc_3648_, 4, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
v___jp_3651_:
{
lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3653_ = lean_nat_add(v___x_3650_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec(v___x_3650_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 4, v_l_3629_);
lean_ctor_set(v___x_3603_, 3, v_l_3612_);
lean_ctor_set(v___x_3603_, 2, v_v_3611_);
lean_ctor_set(v___x_3603_, 1, v_k_3610_);
lean_ctor_set(v___x_3603_, 0, v___x_3653_);
v___x_3655_ = v___x_3603_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_k_3610_);
lean_ctor_set(v_reuseFailAlloc_3659_, 2, v_v_3611_);
lean_ctor_set(v_reuseFailAlloc_3659_, 3, v_l_3612_);
lean_ctor_set(v_reuseFailAlloc_3659_, 4, v_l_3629_);
v___x_3655_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3656_; 
v___x_3656_ = lean_nat_add(v___x_3607_, v_size_3608_);
if (lean_obj_tag(v_r_3630_) == 0)
{
lean_object* v_size_3657_; 
v_size_3657_ = lean_ctor_get(v_r_3630_, 0);
lean_inc(v_size_3657_);
v___y_3640_ = v___x_3656_;
v___y_3641_ = v___x_3655_;
v___y_3642_ = v_size_3657_;
goto v___jp_3639_;
}
else
{
lean_object* v___x_3658_; 
v___x_3658_ = lean_unsigned_to_nat(0u);
v___y_3640_ = v___x_3656_;
v___y_3641_ = v___x_3655_;
v___y_3642_ = v___x_3658_;
goto v___jp_3639_;
}
}
}
}
}
else
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3673_; 
lean_del_object(v___x_3603_);
v___x_3668_ = lean_nat_add(v___x_3607_, v_size_3609_);
lean_dec(v_size_3609_);
v___x_3669_ = lean_nat_add(v___x_3668_, v_size_3608_);
lean_dec(v___x_3668_);
v___x_3670_ = lean_nat_add(v___x_3607_, v_size_3608_);
v___x_3671_ = lean_nat_add(v___x_3670_, v_size_3626_);
lean_dec(v___x_3670_);
lean_inc_ref(v_r_3601_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 4, v_r_3601_);
lean_ctor_set(v___x_3623_, 3, v_r_3613_);
lean_ctor_set(v___x_3623_, 2, v_v_3599_);
lean_ctor_set(v___x_3623_, 1, v_k_3598_);
lean_ctor_set(v___x_3623_, 0, v___x_3671_);
v___x_3673_ = v___x_3623_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3671_);
lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_k_3598_);
lean_ctor_set(v_reuseFailAlloc_3686_, 2, v_v_3599_);
lean_ctor_set(v_reuseFailAlloc_3686_, 3, v_r_3613_);
lean_ctor_set(v_reuseFailAlloc_3686_, 4, v_r_3601_);
v___x_3673_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
v_isSharedCheck_3680_ = !lean_is_exclusive(v_r_3601_);
if (v_isSharedCheck_3680_ == 0)
{
lean_object* v_unused_3681_; lean_object* v_unused_3682_; lean_object* v_unused_3683_; lean_object* v_unused_3684_; lean_object* v_unused_3685_; 
v_unused_3681_ = lean_ctor_get(v_r_3601_, 4);
lean_dec(v_unused_3681_);
v_unused_3682_ = lean_ctor_get(v_r_3601_, 3);
lean_dec(v_unused_3682_);
v_unused_3683_ = lean_ctor_get(v_r_3601_, 2);
lean_dec(v_unused_3683_);
v_unused_3684_ = lean_ctor_get(v_r_3601_, 1);
lean_dec(v_unused_3684_);
v_unused_3685_ = lean_ctor_get(v_r_3601_, 0);
lean_dec(v_unused_3685_);
v___x_3675_ = v_r_3601_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_dec(v_r_3601_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 4, v___x_3673_);
lean_ctor_set(v___x_3675_, 3, v_l_3612_);
lean_ctor_set(v___x_3675_, 2, v_v_3611_);
lean_ctor_set(v___x_3675_, 1, v_k_3610_);
lean_ctor_set(v___x_3675_, 0, v___x_3669_);
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_k_3610_);
lean_ctor_set(v_reuseFailAlloc_3679_, 2, v_v_3611_);
lean_ctor_set(v_reuseFailAlloc_3679_, 3, v_l_3612_);
lean_ctor_set(v_reuseFailAlloc_3679_, 4, v___x_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3693_; 
v_l_3693_ = lean_ctor_get(v_impl_3606_, 3);
lean_inc(v_l_3693_);
if (lean_obj_tag(v_l_3693_) == 0)
{
lean_object* v_r_3694_; lean_object* v_k_3695_; lean_object* v_v_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3707_; 
v_r_3694_ = lean_ctor_get(v_impl_3606_, 4);
v_k_3695_ = lean_ctor_get(v_impl_3606_, 1);
v_v_3696_ = lean_ctor_get(v_impl_3606_, 2);
v_isSharedCheck_3707_ = !lean_is_exclusive(v_impl_3606_);
if (v_isSharedCheck_3707_ == 0)
{
lean_object* v_unused_3708_; lean_object* v_unused_3709_; 
v_unused_3708_ = lean_ctor_get(v_impl_3606_, 3);
lean_dec(v_unused_3708_);
v_unused_3709_ = lean_ctor_get(v_impl_3606_, 0);
lean_dec(v_unused_3709_);
v___x_3698_ = v_impl_3606_;
v_isShared_3699_ = v_isSharedCheck_3707_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_r_3694_);
lean_inc(v_v_3696_);
lean_inc(v_k_3695_);
lean_dec(v_impl_3606_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3707_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; lean_object* v___x_3702_; 
v___x_3700_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3694_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 3, v_r_3694_);
lean_ctor_set(v___x_3698_, 2, v_v_3599_);
lean_ctor_set(v___x_3698_, 1, v_k_3598_);
lean_ctor_set(v___x_3698_, 0, v___x_3607_);
v___x_3702_ = v___x_3698_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3706_, 1, v_k_3598_);
lean_ctor_set(v_reuseFailAlloc_3706_, 2, v_v_3599_);
lean_ctor_set(v_reuseFailAlloc_3706_, 3, v_r_3694_);
lean_ctor_set(v_reuseFailAlloc_3706_, 4, v_r_3694_);
v___x_3702_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3704_; 
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 4, v___x_3702_);
lean_ctor_set(v___x_3603_, 3, v_l_3693_);
lean_ctor_set(v___x_3603_, 2, v_v_3696_);
lean_ctor_set(v___x_3603_, 1, v_k_3695_);
lean_ctor_set(v___x_3603_, 0, v___x_3700_);
v___x_3704_ = v___x_3603_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3700_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_k_3695_);
lean_ctor_set(v_reuseFailAlloc_3705_, 2, v_v_3696_);
lean_ctor_set(v_reuseFailAlloc_3705_, 3, v_l_3693_);
lean_ctor_set(v_reuseFailAlloc_3705_, 4, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
else
{
lean_object* v_r_3710_; 
v_r_3710_ = lean_ctor_get(v_impl_3606_, 4);
lean_inc(v_r_3710_);
if (lean_obj_tag(v_r_3710_) == 0)
{
lean_object* v_k_3711_; lean_object* v_v_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3735_; 
v_k_3711_ = lean_ctor_get(v_impl_3606_, 1);
v_v_3712_ = lean_ctor_get(v_impl_3606_, 2);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_impl_3606_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; lean_object* v_unused_3737_; lean_object* v_unused_3738_; 
v_unused_3736_ = lean_ctor_get(v_impl_3606_, 4);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_impl_3606_, 3);
lean_dec(v_unused_3737_);
v_unused_3738_ = lean_ctor_get(v_impl_3606_, 0);
lean_dec(v_unused_3738_);
v___x_3714_ = v_impl_3606_;
v_isShared_3715_ = v_isSharedCheck_3735_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_v_3712_);
lean_inc(v_k_3711_);
lean_dec(v_impl_3606_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3735_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v_k_3716_; lean_object* v_v_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3731_; 
v_k_3716_ = lean_ctor_get(v_r_3710_, 1);
v_v_3717_ = lean_ctor_get(v_r_3710_, 2);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_r_3710_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; 
v_unused_3732_ = lean_ctor_get(v_r_3710_, 4);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_r_3710_, 3);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_r_3710_, 0);
lean_dec(v_unused_3734_);
v___x_3719_ = v_r_3710_;
v_isShared_3720_ = v_isSharedCheck_3731_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_v_3717_);
lean_inc(v_k_3716_);
lean_dec(v_r_3710_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3731_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3721_ = lean_unsigned_to_nat(3u);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 4, v_l_3693_);
lean_ctor_set(v___x_3719_, 3, v_l_3693_);
lean_ctor_set(v___x_3719_, 2, v_v_3712_);
lean_ctor_set(v___x_3719_, 1, v_k_3711_);
lean_ctor_set(v___x_3719_, 0, v___x_3607_);
v___x_3723_ = v___x_3719_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3730_, 3, v_l_3693_);
lean_ctor_set(v_reuseFailAlloc_3730_, 4, v_l_3693_);
v___x_3723_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3725_; 
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 4, v_l_3693_);
lean_ctor_set(v___x_3714_, 2, v_v_3599_);
lean_ctor_set(v___x_3714_, 1, v_k_3598_);
lean_ctor_set(v___x_3714_, 0, v___x_3607_);
v___x_3725_ = v___x_3714_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_k_3598_);
lean_ctor_set(v_reuseFailAlloc_3729_, 2, v_v_3599_);
lean_ctor_set(v_reuseFailAlloc_3729_, 3, v_l_3693_);
lean_ctor_set(v_reuseFailAlloc_3729_, 4, v_l_3693_);
v___x_3725_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3727_; 
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 4, v___x_3725_);
lean_ctor_set(v___x_3603_, 3, v___x_3723_);
lean_ctor_set(v___x_3603_, 2, v_v_3717_);
lean_ctor_set(v___x_3603_, 1, v_k_3716_);
lean_ctor_set(v___x_3603_, 0, v___x_3721_);
v___x_3727_ = v___x_3603_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_k_3716_);
lean_ctor_set(v_reuseFailAlloc_3728_, 2, v_v_3717_);
lean_ctor_set(v_reuseFailAlloc_3728_, 3, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3728_, 4, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
}
else
{
lean_object* v___x_3739_; lean_object* v___x_3741_; 
v___x_3739_ = lean_unsigned_to_nat(2u);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 4, v_r_3710_);
lean_ctor_set(v___x_3603_, 3, v_impl_3606_);
lean_ctor_set(v___x_3603_, 0, v___x_3739_);
v___x_3741_ = v___x_3603_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_k_3598_);
lean_ctor_set(v_reuseFailAlloc_3742_, 2, v_v_3599_);
lean_ctor_set(v_reuseFailAlloc_3742_, 3, v_impl_3606_);
lean_ctor_set(v_reuseFailAlloc_3742_, 4, v_r_3710_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3744_; 
lean_dec(v_v_3599_);
lean_dec(v_k_3598_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 2, v_v_3595_);
lean_ctor_set(v___x_3603_, 1, v_k_3594_);
v___x_3744_ = v___x_3603_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_size_3597_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_k_3594_);
lean_ctor_set(v_reuseFailAlloc_3745_, 2, v_v_3595_);
lean_ctor_set(v_reuseFailAlloc_3745_, 3, v_l_3600_);
lean_ctor_set(v_reuseFailAlloc_3745_, 4, v_r_3601_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
default: 
{
lean_object* v_impl_3746_; lean_object* v___x_3747_; 
lean_dec(v_size_3597_);
v_impl_3746_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(v_k_3594_, v_v_3595_, v_r_3601_);
v___x_3747_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3600_) == 0)
{
lean_object* v_size_3748_; lean_object* v_size_3749_; lean_object* v_k_3750_; lean_object* v_v_3751_; lean_object* v_l_3752_; lean_object* v_r_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; uint8_t v___x_3756_; 
v_size_3748_ = lean_ctor_get(v_l_3600_, 0);
v_size_3749_ = lean_ctor_get(v_impl_3746_, 0);
lean_inc(v_size_3749_);
v_k_3750_ = lean_ctor_get(v_impl_3746_, 1);
lean_inc(v_k_3750_);
v_v_3751_ = lean_ctor_get(v_impl_3746_, 2);
lean_inc(v_v_3751_);
v_l_3752_ = lean_ctor_get(v_impl_3746_, 3);
lean_inc(v_l_3752_);
v_r_3753_ = lean_ctor_get(v_impl_3746_, 4);
lean_inc(v_r_3753_);
v___x_3754_ = lean_unsigned_to_nat(3u);
v___x_3755_ = lean_nat_mul(v___x_3754_, v_size_3748_);
v___x_3756_ = lean_nat_dec_lt(v___x_3755_, v_size_3749_);
lean_dec(v___x_3755_);
if (v___x_3756_ == 0)
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3760_; 
lean_dec(v_r_3753_);
lean_dec(v_l_3752_);
lean_dec(v_v_3751_);
lean_dec(v_k_3750_);
v___x_3757_ = lean_nat_add(v___x_3747_, v_size_3748_);
v___x_3758_ = lean_nat_add(v___x_3757_, v_size_3749_);
lean_dec(v_size_3749_);
lean_dec(v___x_3757_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 4, v_impl_3746_);
lean_ctor_set(v___x_3603_, 0, v___x_3758_);
v___x_3760_ = v___x_3603_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3758_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_k_3598_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_v_3599_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v_l_3600_);
lean_ctor_set(v_reuseFailAlloc_3761_, 4, v_impl_3746_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
else
{
lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3825_; 
v_isSharedCheck_3825_ = !lean_is_exclusive(v_impl_3746_);
if (v_isSharedCheck_3825_ == 0)
{
lean_object* v_unused_3826_; lean_object* v_unused_3827_; lean_object* v_unused_3828_; lean_object* v_unused_3829_; lean_object* v_unused_3830_; 
v_unused_3826_ = lean_ctor_get(v_impl_3746_, 4);
lean_dec(v_unused_3826_);
v_unused_3827_ = lean_ctor_get(v_impl_3746_, 3);
lean_dec(v_unused_3827_);
v_unused_3828_ = lean_ctor_get(v_impl_3746_, 2);
lean_dec(v_unused_3828_);
v_unused_3829_ = lean_ctor_get(v_impl_3746_, 1);
lean_dec(v_unused_3829_);
v_unused_3830_ = lean_ctor_get(v_impl_3746_, 0);
lean_dec(v_unused_3830_);
v___x_3763_ = v_impl_3746_;
v_isShared_3764_ = v_isSharedCheck_3825_;
goto v_resetjp_3762_;
}
else
{
lean_dec(v_impl_3746_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3825_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v_size_3765_; lean_object* v_k_3766_; lean_object* v_v_3767_; lean_object* v_l_3768_; lean_object* v_r_3769_; lean_object* v_size_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; uint8_t v___x_3773_; 
v_size_3765_ = lean_ctor_get(v_l_3752_, 0);
v_k_3766_ = lean_ctor_get(v_l_3752_, 1);
v_v_3767_ = lean_ctor_get(v_l_3752_, 2);
v_l_3768_ = lean_ctor_get(v_l_3752_, 3);
v_r_3769_ = lean_ctor_get(v_l_3752_, 4);
v_size_3770_ = lean_ctor_get(v_r_3753_, 0);
v___x_3771_ = lean_unsigned_to_nat(2u);
v___x_3772_ = lean_nat_mul(v___x_3771_, v_size_3770_);
v___x_3773_ = lean_nat_dec_lt(v_size_3765_, v___x_3772_);
lean_dec(v___x_3772_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3801_; 
lean_inc(v_r_3769_);
lean_inc(v_l_3768_);
lean_inc(v_v_3767_);
lean_inc(v_k_3766_);
v_isSharedCheck_3801_ = !lean_is_exclusive(v_l_3752_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; lean_object* v_unused_3803_; lean_object* v_unused_3804_; lean_object* v_unused_3805_; lean_object* v_unused_3806_; 
v_unused_3802_ = lean_ctor_get(v_l_3752_, 4);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_l_3752_, 3);
lean_dec(v_unused_3803_);
v_unused_3804_ = lean_ctor_get(v_l_3752_, 2);
lean_dec(v_unused_3804_);
v_unused_3805_ = lean_ctor_get(v_l_3752_, 1);
lean_dec(v_unused_3805_);
v_unused_3806_ = lean_ctor_get(v_l_3752_, 0);
lean_dec(v_unused_3806_);
v___x_3775_ = v_l_3752_;
v_isShared_3776_ = v_isSharedCheck_3801_;
goto v_resetjp_3774_;
}
else
{
lean_dec(v_l_3752_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3801_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3791_; 
v___x_3777_ = lean_nat_add(v___x_3747_, v_size_3748_);
v___x_3778_ = lean_nat_add(v___x_3777_, v_size_3749_);
lean_dec(v_size_3749_);
if (lean_obj_tag(v_l_3768_) == 0)
{
lean_object* v_size_3799_; 
v_size_3799_ = lean_ctor_get(v_l_3768_, 0);
lean_inc(v_size_3799_);
v___y_3791_ = v_size_3799_;
goto v___jp_3790_;
}
else
{
lean_object* v___x_3800_; 
v___x_3800_ = lean_unsigned_to_nat(0u);
v___y_3791_ = v___x_3800_;
goto v___jp_3790_;
}
v___jp_3779_:
{
lean_object* v___x_3783_; lean_object* v___x_3785_; 
v___x_3783_ = lean_nat_add(v___y_3780_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec(v___y_3780_);
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 4, v_r_3753_);
lean_ctor_set(v___x_3775_, 3, v_r_3769_);
lean_ctor_set(v___x_3775_, 2, v_v_3751_);
lean_ctor_set(v___x_3775_, 1, v_k_3750_);
lean_ctor_set(v___x_3775_, 0, v___x_3783_);
v___x_3785_ = v___x_3775_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_k_3750_);
lean_ctor_set(v_reuseFailAlloc_3789_, 2, v_v_3751_);
lean_ctor_set(v_reuseFailAlloc_3789_, 3, v_r_3769_);
lean_ctor_set(v_reuseFailAlloc_3789_, 4, v_r_3753_);
v___x_3785_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
lean_object* v___x_3787_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 4, v___x_3785_);
lean_ctor_set(v___x_3763_, 3, v___y_3781_);
lean_ctor_set(v___x_3763_, 2, v_v_3767_);
lean_ctor_set(v___x_3763_, 1, v_k_3766_);
lean_ctor_set(v___x_3763_, 0, v___x_3778_);
v___x_3787_ = v___x_3763_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3778_);
lean_ctor_set(v_reuseFailAlloc_3788_, 1, v_k_3766_);
lean_ctor_set(v_reuseFailAlloc_3788_, 2, v_v_3767_);
lean_ctor_set(v_reuseFailAlloc_3788_, 3, v___y_3781_);
lean_ctor_set(v_reuseFailAlloc_3788_, 4, v___x_3785_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
v___jp_3790_:
{
lean_object* v___x_3792_; lean_object* v___x_3794_; 
v___x_3792_ = lean_nat_add(v___x_3777_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec(v___x_3777_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 4, v_l_3768_);
lean_ctor_set(v___x_3603_, 0, v___x_3792_);
v___x_3794_ = v___x_3603_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3792_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_k_3598_);
lean_ctor_set(v_reuseFailAlloc_3798_, 2, v_v_3599_);
lean_ctor_set(v_reuseFailAlloc_3798_, 3, v_l_3600_);
lean_ctor_set(v_reuseFailAlloc_3798_, 4, v_l_3768_);
v___x_3794_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3795_; 
v___x_3795_ = lean_nat_add(v___x_3747_, v_size_3770_);
if (lean_obj_tag(v_r_3769_) == 0)
{
lean_object* v_size_3796_; 
v_size_3796_ = lean_ctor_get(v_r_3769_, 0);
lean_inc(v_size_3796_);
v___y_3780_ = v___x_3795_;
v___y_3781_ = v___x_3794_;
v___y_3782_ = v_size_3796_;
goto v___jp_3779_;
}
else
{
lean_object* v___x_3797_; 
v___x_3797_ = lean_unsigned_to_nat(0u);
v___y_3780_ = v___x_3795_;
v___y_3781_ = v___x_3794_;
v___y_3782_ = v___x_3797_;
goto v___jp_3779_;
}
}
}
}
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
lean_del_object(v___x_3603_);
v___x_3807_ = lean_nat_add(v___x_3747_, v_size_3748_);
v___x_3808_ = lean_nat_add(v___x_3807_, v_size_3749_);
lean_dec(v_size_3749_);
v___x_3809_ = lean_nat_add(v___x_3807_, v_size_3765_);
lean_dec(v___x_3807_);
lean_inc_ref(v_l_3600_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 4, v_l_3752_);
lean_ctor_set(v___x_3763_, 3, v_l_3600_);
lean_ctor_set(v___x_3763_, 2, v_v_3599_);
lean_ctor_set(v___x_3763_, 1, v_k_3598_);
lean_ctor_set(v___x_3763_, 0, v___x_3809_);
v___x_3811_ = v___x_3763_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v_k_3598_);
lean_ctor_set(v_reuseFailAlloc_3824_, 2, v_v_3599_);
lean_ctor_set(v_reuseFailAlloc_3824_, 3, v_l_3600_);
lean_ctor_set(v_reuseFailAlloc_3824_, 4, v_l_3752_);
v___x_3811_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
v_isSharedCheck_3818_ = !lean_is_exclusive(v_l_3600_);
if (v_isSharedCheck_3818_ == 0)
{
lean_object* v_unused_3819_; lean_object* v_unused_3820_; lean_object* v_unused_3821_; lean_object* v_unused_3822_; lean_object* v_unused_3823_; 
v_unused_3819_ = lean_ctor_get(v_l_3600_, 4);
lean_dec(v_unused_3819_);
v_unused_3820_ = lean_ctor_get(v_l_3600_, 3);
lean_dec(v_unused_3820_);
v_unused_3821_ = lean_ctor_get(v_l_3600_, 2);
lean_dec(v_unused_3821_);
v_unused_3822_ = lean_ctor_get(v_l_3600_, 1);
lean_dec(v_unused_3822_);
v_unused_3823_ = lean_ctor_get(v_l_3600_, 0);
lean_dec(v_unused_3823_);
v___x_3813_ = v_l_3600_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_dec(v_l_3600_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 4, v_r_3753_);
lean_ctor_set(v___x_3813_, 3, v___x_3811_);
lean_ctor_set(v___x_3813_, 2, v_v_3751_);
lean_ctor_set(v___x_3813_, 1, v_k_3750_);
lean_ctor_set(v___x_3813_, 0, v___x_3808_);
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v_k_3750_);
lean_ctor_set(v_reuseFailAlloc_3817_, 2, v_v_3751_);
lean_ctor_set(v_reuseFailAlloc_3817_, 3, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3817_, 4, v_r_3753_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3831_; 
v_l_3831_ = lean_ctor_get(v_impl_3746_, 3);
lean_inc(v_l_3831_);
if (lean_obj_tag(v_l_3831_) == 0)
{
lean_object* v_r_3832_; lean_object* v_k_3833_; lean_object* v_v_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3857_; 
v_r_3832_ = lean_ctor_get(v_impl_3746_, 4);
v_k_3833_ = lean_ctor_get(v_impl_3746_, 1);
v_v_3834_ = lean_ctor_get(v_impl_3746_, 2);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_impl_3746_);
if (v_isSharedCheck_3857_ == 0)
{
lean_object* v_unused_3858_; lean_object* v_unused_3859_; 
v_unused_3858_ = lean_ctor_get(v_impl_3746_, 3);
lean_dec(v_unused_3858_);
v_unused_3859_ = lean_ctor_get(v_impl_3746_, 0);
lean_dec(v_unused_3859_);
v___x_3836_ = v_impl_3746_;
v_isShared_3837_ = v_isSharedCheck_3857_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_r_3832_);
lean_inc(v_v_3834_);
lean_inc(v_k_3833_);
lean_dec(v_impl_3746_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3857_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v_k_3838_; lean_object* v_v_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3853_; 
v_k_3838_ = lean_ctor_get(v_l_3831_, 1);
v_v_3839_ = lean_ctor_get(v_l_3831_, 2);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_l_3831_);
if (v_isSharedCheck_3853_ == 0)
{
lean_object* v_unused_3854_; lean_object* v_unused_3855_; lean_object* v_unused_3856_; 
v_unused_3854_ = lean_ctor_get(v_l_3831_, 4);
lean_dec(v_unused_3854_);
v_unused_3855_ = lean_ctor_get(v_l_3831_, 3);
lean_dec(v_unused_3855_);
v_unused_3856_ = lean_ctor_get(v_l_3831_, 0);
lean_dec(v_unused_3856_);
v___x_3841_ = v_l_3831_;
v_isShared_3842_ = v_isSharedCheck_3853_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_v_3839_);
lean_inc(v_k_3838_);
lean_dec(v_l_3831_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3853_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3843_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3832_, 2);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 4, v_r_3832_);
lean_ctor_set(v___x_3841_, 3, v_r_3832_);
lean_ctor_set(v___x_3841_, 2, v_v_3599_);
lean_ctor_set(v___x_3841_, 1, v_k_3598_);
lean_ctor_set(v___x_3841_, 0, v___x_3747_);
v___x_3845_ = v___x_3841_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3747_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v_k_3598_);
lean_ctor_set(v_reuseFailAlloc_3852_, 2, v_v_3599_);
lean_ctor_set(v_reuseFailAlloc_3852_, 3, v_r_3832_);
lean_ctor_set(v_reuseFailAlloc_3852_, 4, v_r_3832_);
v___x_3845_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3847_; 
lean_inc(v_r_3832_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 3, v_r_3832_);
lean_ctor_set(v___x_3836_, 0, v___x_3747_);
v___x_3847_ = v___x_3836_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3747_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v_k_3833_);
lean_ctor_set(v_reuseFailAlloc_3851_, 2, v_v_3834_);
lean_ctor_set(v_reuseFailAlloc_3851_, 3, v_r_3832_);
lean_ctor_set(v_reuseFailAlloc_3851_, 4, v_r_3832_);
v___x_3847_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v___x_3849_; 
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 4, v___x_3847_);
lean_ctor_set(v___x_3603_, 3, v___x_3845_);
lean_ctor_set(v___x_3603_, 2, v_v_3839_);
lean_ctor_set(v___x_3603_, 1, v_k_3838_);
lean_ctor_set(v___x_3603_, 0, v___x_3843_);
v___x_3849_ = v___x_3603_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v_k_3838_);
lean_ctor_set(v_reuseFailAlloc_3850_, 2, v_v_3839_);
lean_ctor_set(v_reuseFailAlloc_3850_, 3, v___x_3845_);
lean_ctor_set(v_reuseFailAlloc_3850_, 4, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
}
}
else
{
lean_object* v_r_3860_; 
v_r_3860_ = lean_ctor_get(v_impl_3746_, 4);
lean_inc(v_r_3860_);
if (lean_obj_tag(v_r_3860_) == 0)
{
lean_object* v_k_3861_; lean_object* v_v_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3873_; 
v_k_3861_ = lean_ctor_get(v_impl_3746_, 1);
v_v_3862_ = lean_ctor_get(v_impl_3746_, 2);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_impl_3746_);
if (v_isSharedCheck_3873_ == 0)
{
lean_object* v_unused_3874_; lean_object* v_unused_3875_; lean_object* v_unused_3876_; 
v_unused_3874_ = lean_ctor_get(v_impl_3746_, 4);
lean_dec(v_unused_3874_);
v_unused_3875_ = lean_ctor_get(v_impl_3746_, 3);
lean_dec(v_unused_3875_);
v_unused_3876_ = lean_ctor_get(v_impl_3746_, 0);
lean_dec(v_unused_3876_);
v___x_3864_ = v_impl_3746_;
v_isShared_3865_ = v_isSharedCheck_3873_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_v_3862_);
lean_inc(v_k_3861_);
lean_dec(v_impl_3746_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3873_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3866_; lean_object* v___x_3868_; 
v___x_3866_ = lean_unsigned_to_nat(3u);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 4, v_l_3831_);
lean_ctor_set(v___x_3864_, 2, v_v_3599_);
lean_ctor_set(v___x_3864_, 1, v_k_3598_);
lean_ctor_set(v___x_3864_, 0, v___x_3747_);
v___x_3868_ = v___x_3864_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3747_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_k_3598_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_v_3599_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v_l_3831_);
lean_ctor_set(v_reuseFailAlloc_3872_, 4, v_l_3831_);
v___x_3868_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3870_; 
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 4, v_r_3860_);
lean_ctor_set(v___x_3603_, 3, v___x_3868_);
lean_ctor_set(v___x_3603_, 2, v_v_3862_);
lean_ctor_set(v___x_3603_, 1, v_k_3861_);
lean_ctor_set(v___x_3603_, 0, v___x_3866_);
v___x_3870_ = v___x_3603_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_k_3861_);
lean_ctor_set(v_reuseFailAlloc_3871_, 2, v_v_3862_);
lean_ctor_set(v_reuseFailAlloc_3871_, 3, v___x_3868_);
lean_ctor_set(v_reuseFailAlloc_3871_, 4, v_r_3860_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
else
{
lean_object* v___x_3877_; lean_object* v___x_3879_; 
v___x_3877_ = lean_unsigned_to_nat(2u);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 4, v_impl_3746_);
lean_ctor_set(v___x_3603_, 3, v_r_3860_);
lean_ctor_set(v___x_3603_, 0, v___x_3877_);
v___x_3879_ = v___x_3603_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3877_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v_k_3598_);
lean_ctor_set(v_reuseFailAlloc_3880_, 2, v_v_3599_);
lean_ctor_set(v_reuseFailAlloc_3880_, 3, v_r_3860_);
lean_ctor_set(v_reuseFailAlloc_3880_, 4, v_impl_3746_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = lean_unsigned_to_nat(1u);
v___x_3883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
lean_ctor_set(v___x_3883_, 1, v_k_3594_);
lean_ctor_set(v___x_3883_, 2, v_v_3595_);
lean_ctor_set(v___x_3883_, 3, v_t_3596_);
lean_ctor_set(v___x_3883_, 4, v_t_3596_);
return v___x_3883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(lean_object* v_cfg_3891_){
_start:
{
lean_object* v___y_3894_; lean_object* v_a_3895_; lean_object* v___y_3908_; lean_object* v_externalKernels_3909_; lean_object* v___y_3922_; lean_object* v___y_3923_; uint8_t v___y_3924_; lean_object* v_a_3925_; lean_object* v___y_3939_; uint8_t v___y_3940_; lean_object* v_enable__nanoda_x3f_3953_; lean_object* v_external__kernels_x3f_3954_; lean_object* v___y_3956_; 
v_enable__nanoda_x3f_3953_ = lean_ctor_get(v_cfg_3891_, 5);
lean_inc(v_enable__nanoda_x3f_3953_);
v_external__kernels_x3f_3954_ = lean_ctor_get(v_cfg_3891_, 6);
lean_inc(v_external__kernels_x3f_3954_);
lean_dec_ref(v_cfg_3891_);
if (lean_obj_tag(v_external__kernels_x3f_3954_) == 0)
{
lean_object* v___x_3987_; 
v___x_3987_ = lean_box(1);
v___y_3956_ = v___x_3987_;
goto v___jp_3955_;
}
else
{
lean_object* v_val_3988_; 
v_val_3988_ = lean_ctor_get(v_external__kernels_x3f_3954_, 0);
lean_inc(v_val_3988_);
lean_dec_ref_known(v_external__kernels_x3f_3954_, 1);
v___y_3956_ = v_val_3988_;
goto v___jp_3955_;
}
v___jp_3893_:
{
lean_object* v_fst_3896_; 
v_fst_3896_ = lean_ctor_get(v_a_3895_, 0);
lean_inc(v_fst_3896_);
lean_dec_ref(v_a_3895_);
if (lean_obj_tag(v_fst_3896_) == 0)
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___y_3894_);
v___x_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
return v___x_3898_;
}
else
{
lean_object* v_val_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_dec(v___y_3894_);
v_val_3899_ = lean_ctor_get(v_fst_3896_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_fst_3896_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v_fst_3896_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_val_3899_);
lean_dec(v_fst_3896_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
lean_ctor_set_tag(v___x_3901_, 0);
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_val_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
v___jp_3907_:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v___y_3908_, v_externalKernels_3909_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v_a_3912_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v_a_3912_ = lean_ctor_get(v_a_3911_, 0);
lean_inc(v_a_3912_);
lean_dec(v_a_3911_);
v___y_3894_ = v_externalKernels_3909_;
v_a_3895_ = v_a_3912_;
goto v___jp_3893_;
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec(v_externalKernels_3909_);
v_a_3913_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3910_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3910_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
v___jp_3921_:
{
lean_object* v_fst_3926_; 
v_fst_3926_ = lean_ctor_get(v_a_3925_, 0);
lean_inc(v_fst_3926_);
lean_dec_ref(v_a_3925_);
if (lean_obj_tag(v_fst_3926_) == 0)
{
if (v___y_3924_ == 0)
{
v___y_3908_ = v___y_3923_;
v_externalKernels_3909_ = v___y_3922_;
goto v___jp_3907_;
}
else
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3927_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0));
v___x_3928_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__2));
v___x_3929_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(v___x_3927_, v___x_3928_, v___y_3922_);
v___y_3908_ = v___y_3923_;
v_externalKernels_3909_ = v___x_3929_;
goto v___jp_3907_;
}
}
else
{
lean_object* v_val_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
v_val_3930_ = lean_ctor_get(v_fst_3926_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_fst_3926_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v_fst_3926_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_val_3930_);
lean_dec(v_fst_3926_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
lean_ctor_set_tag(v___x_3932_, 0);
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_val_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
v___jp_3938_:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v___x_3942_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(v___x_3941_, v___y_3939_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v_a_3944_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___x_3942_, 1);
v_a_3944_ = lean_ctor_get(v_a_3943_, 0);
lean_inc(v_a_3944_);
lean_dec(v_a_3943_);
v___y_3922_ = v___y_3939_;
v___y_3923_ = v___x_3941_;
v___y_3924_ = v___y_3940_;
v_a_3925_ = v_a_3944_;
goto v___jp_3921_;
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec(v___y_3939_);
v_a_3945_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3942_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3942_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
v___jp_3955_:
{
if (lean_obj_tag(v_enable__nanoda_x3f_3953_) == 0)
{
uint8_t v___x_3957_; 
v___x_3957_ = 0;
v___y_3939_ = v___y_3956_;
v___y_3940_ = v___x_3957_;
goto v___jp_3938_;
}
else
{
lean_object* v_val_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3986_; 
v_val_3958_ = lean_ctor_get(v_enable__nanoda_x3f_3953_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v_enable__nanoda_x3f_3953_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3960_ = v_enable__nanoda_x3f_3953_;
v_isShared_3961_ = v_isSharedCheck_3986_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_val_3958_);
lean_dec(v_enable__nanoda_x3f_3953_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3986_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
uint8_t v___x_3962_; 
v___x_3962_ = lean_unbox(v_val_3958_);
if (v___x_3962_ == 0)
{
uint8_t v___x_3963_; 
lean_del_object(v___x_3960_);
v___x_3963_ = lean_unbox(v_val_3958_);
lean_dec(v_val_3958_);
v___y_3939_ = v___y_3956_;
v___y_3940_ = v___x_3963_;
goto v___jp_3938_;
}
else
{
if (lean_obj_tag(v___y_3956_) == 0)
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
lean_dec_ref_known(v___y_3956_, 5);
lean_dec(v_val_3958_);
v___x_3964_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__3));
v___x_3965_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3964_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3976_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3968_ = v___x_3965_;
v_isShared_3969_ = v_isSharedCheck_3976_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3965_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3976_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3961_ == 0)
{
lean_ctor_set_tag(v___x_3960_, 0);
lean_ctor_set(v___x_3960_, 0, v_a_3966_);
v___x_3971_ = v___x_3960_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
lean_object* v___x_3973_; 
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v___x_3971_);
v___x_3973_ = v___x_3968_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3971_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_del_object(v___x_3960_);
v_a_3977_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3965_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3965_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
else
{
uint8_t v___x_3985_; 
lean_del_object(v___x_3960_);
v___x_3985_ = lean_unbox(v_val_3958_);
lean_dec(v_val_3958_);
v___y_3939_ = v___y_3956_;
v___y_3940_ = v___x_3985_;
goto v___jp_3938_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___boxed(lean_object* v_cfg_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v_cfg_3989_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(lean_object* v_00_u03b2_3992_, lean_object* v_k_3993_, lean_object* v_v_3994_, lean_object* v_t_3995_, lean_object* v_hl_3996_){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(v_k_3993_, v_v_3994_, v_t_3995_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(lean_object* v_a_4015_, lean_object* v_a_4016_){
_start:
{
if (lean_obj_tag(v_a_4015_) == 0)
{
lean_object* v___x_4017_; 
v___x_4017_ = l_List_reverse___redArg(v_a_4016_);
return v___x_4017_;
}
else
{
lean_object* v_head_4018_; lean_object* v_tail_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4030_; 
v_head_4018_ = lean_ctor_get(v_a_4015_, 0);
v_tail_4019_ = lean_ctor_get(v_a_4015_, 1);
v_isSharedCheck_4030_ = !lean_is_exclusive(v_a_4015_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4021_ = v_a_4015_;
v_isShared_4022_ = v_isSharedCheck_4030_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_tail_4019_);
lean_inc(v_head_4018_);
lean_dec(v_a_4015_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4030_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v_fst_4023_; uint8_t v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4027_; 
v_fst_4023_ = lean_ctor_get(v_head_4018_, 0);
lean_inc(v_fst_4023_);
lean_dec(v_head_4018_);
v___x_4024_ = 1;
v___x_4025_ = l_Lean_Name_toString(v_fst_4023_, v___x_4024_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 1, v_a_4016_);
lean_ctor_set(v___x_4021_, 0, v___x_4025_);
v___x_4027_ = v___x_4021_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4029_, 1, v_a_4016_);
v___x_4027_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
v_a_4015_ = v_tail_4019_;
v_a_4016_ = v___x_4027_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(lean_object* v_as_4031_, size_t v_i_4032_, size_t v_stop_4033_, lean_object* v_b_4034_){
_start:
{
lean_object* v___y_4036_; uint8_t v___x_4040_; 
v___x_4040_ = lean_usize_dec_eq(v_i_4032_, v_stop_4033_);
if (v___x_4040_ == 0)
{
lean_object* v___x_4041_; lean_object* v_fst_4042_; lean_object* v___x_4043_; uint8_t v___x_4044_; 
v___x_4041_ = lean_array_uget_borrowed(v_as_4031_, v_i_4032_);
v_fst_4042_ = lean_ctor_get(v___x_4041_, 0);
v___x_4043_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms));
v___x_4044_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v___x_4043_, v_fst_4042_);
if (v___x_4044_ == 0)
{
lean_object* v___x_4045_; 
lean_inc(v___x_4041_);
v___x_4045_ = lean_array_push(v_b_4034_, v___x_4041_);
v___y_4036_ = v___x_4045_;
goto v___jp_4035_;
}
else
{
v___y_4036_ = v_b_4034_;
goto v___jp_4035_;
}
}
else
{
return v_b_4034_;
}
v___jp_4035_:
{
size_t v___x_4037_; size_t v___x_4038_; 
v___x_4037_ = ((size_t)1ULL);
v___x_4038_ = lean_usize_add(v_i_4032_, v___x_4037_);
v_i_4032_ = v___x_4038_;
v_b_4034_ = v___y_4036_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1___boxed(lean_object* v_as_4046_, lean_object* v_i_4047_, lean_object* v_stop_4048_, lean_object* v_b_4049_){
_start:
{
size_t v_i_boxed_4050_; size_t v_stop_boxed_4051_; lean_object* v_res_4052_; 
v_i_boxed_4050_ = lean_unbox_usize(v_i_4047_);
lean_dec(v_i_4047_);
v_stop_boxed_4051_ = lean_unbox_usize(v_stop_4048_);
lean_dec(v_stop_4048_);
v_res_4052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_as_4046_, v_i_boxed_4050_, v_stop_boxed_4051_, v_b_4049_);
lean_dec_ref(v_as_4046_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(lean_object* v_a_4055_, lean_object* v_a_4056_){
_start:
{
if (lean_obj_tag(v_a_4055_) == 0)
{
lean_object* v___x_4057_; 
v___x_4057_ = l_List_reverse___redArg(v_a_4056_);
return v___x_4057_;
}
else
{
lean_object* v_head_4058_; lean_object* v_tail_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4079_; 
v_head_4058_ = lean_ctor_get(v_a_4055_, 0);
v_tail_4059_ = lean_ctor_get(v_a_4055_, 1);
v_isSharedCheck_4079_ = !lean_is_exclusive(v_a_4055_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4061_ = v_a_4055_;
v_isShared_4062_ = v_isSharedCheck_4079_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_tail_4059_);
lean_inc(v_head_4058_);
lean_dec(v_a_4055_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4079_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v_fst_4063_; lean_object* v_snd_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4076_; 
v_fst_4063_ = lean_ctor_get(v_head_4058_, 0);
lean_inc(v_fst_4063_);
v_snd_4064_ = lean_ctor_get(v_head_4058_, 1);
lean_inc(v_snd_4064_);
lean_dec(v_head_4058_);
v___x_4065_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__0));
v___x_4066_ = 1;
v___x_4067_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_4063_, v___x_4066_);
v___x_4068_ = lean_string_append(v___x_4065_, v___x_4067_);
lean_dec_ref(v___x_4067_);
v___x_4069_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__1));
v___x_4070_ = lean_string_append(v___x_4068_, v___x_4069_);
v___x_4071_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_snd_4064_, v___x_4066_);
v___x_4072_ = lean_string_append(v___x_4070_, v___x_4071_);
lean_dec_ref(v___x_4071_);
v___x_4073_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_4074_ = lean_string_append(v___x_4072_, v___x_4073_);
if (v_isShared_4062_ == 0)
{
lean_ctor_set(v___x_4061_, 1, v_a_4056_);
lean_ctor_set(v___x_4061_, 0, v___x_4074_);
v___x_4076_ = v___x_4061_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4074_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v_a_4056_);
v___x_4076_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
v_a_4055_ = v_tail_4059_;
v_a_4056_ = v___x_4076_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(lean_object* v_exported_4085_){
_start:
{
lean_object* v___y_4088_; lean_object* v_used_4101_; lean_object* v___x_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; 
v_used_4101_ = l_Lake_Check_usedAxioms(v_exported_4085_);
v___x_4114_ = lean_array_get_size(v_used_4101_);
v___x_4115_ = lean_unsigned_to_nat(0u);
v___x_4116_ = lean_nat_dec_eq(v___x_4114_, v___x_4115_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4117_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__2));
v___x_4118_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0_spec__0___closed__0));
lean_inc_ref(v_used_4101_);
v___x_4119_ = lean_array_to_list(v_used_4101_);
v___x_4120_ = lean_box(0);
v___x_4121_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(v___x_4119_, v___x_4120_);
v___x_4122_ = l_String_intercalate(v___x_4118_, v___x_4121_);
v___x_4123_ = lean_string_append(v___x_4117_, v___x_4122_);
lean_dec_ref(v___x_4122_);
v___x_4124_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_4123_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_dec_ref_known(v___x_4124_, 1);
goto v___jp_4102_;
}
else
{
lean_dec_ref(v_used_4101_);
return v___x_4124_;
}
}
else
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4125_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__3));
v___x_4126_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_4125_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_dec_ref_known(v___x_4126_, 1);
goto v___jp_4102_;
}
else
{
lean_dec_ref(v_used_4101_);
return v___x_4126_;
}
}
v___jp_4087_:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; uint8_t v___x_4091_; 
v___x_4089_ = lean_array_get_size(v___y_4088_);
v___x_4090_ = lean_unsigned_to_nat(0u);
v___x_4091_ = lean_nat_dec_eq(v___x_4089_, v___x_4090_);
if (v___x_4091_ == 0)
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4092_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__0));
v___x_4093_ = lean_array_to_list(v___y_4088_);
v___x_4094_ = lean_box(0);
v___x_4095_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(v___x_4093_, v___x_4094_);
v___x_4096_ = l_String_intercalate(v___x_4092_, v___x_4095_);
v___x_4097_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4096_);
v___x_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
return v___x_4098_;
}
else
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
lean_dec_ref(v___y_4088_);
v___x_4099_ = lean_box(0);
v___x_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
return v___x_4100_;
}
}
v___jp_4102_:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; uint8_t v___x_4106_; 
v___x_4103_ = lean_unsigned_to_nat(0u);
v___x_4104_ = lean_array_get_size(v_used_4101_);
v___x_4105_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__1));
v___x_4106_ = lean_nat_dec_lt(v___x_4103_, v___x_4104_);
if (v___x_4106_ == 0)
{
lean_dec_ref(v_used_4101_);
v___y_4088_ = v___x_4105_;
goto v___jp_4087_;
}
else
{
uint8_t v___x_4107_; 
v___x_4107_ = lean_nat_dec_le(v___x_4104_, v___x_4104_);
if (v___x_4107_ == 0)
{
if (v___x_4106_ == 0)
{
lean_dec_ref(v_used_4101_);
v___y_4088_ = v___x_4105_;
goto v___jp_4087_;
}
else
{
size_t v___x_4108_; size_t v___x_4109_; lean_object* v___x_4110_; 
v___x_4108_ = ((size_t)0ULL);
v___x_4109_ = lean_usize_of_nat(v___x_4104_);
v___x_4110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_used_4101_, v___x_4108_, v___x_4109_, v___x_4105_);
lean_dec_ref(v_used_4101_);
v___y_4088_ = v___x_4110_;
goto v___jp_4087_;
}
}
else
{
size_t v___x_4111_; size_t v___x_4112_; lean_object* v___x_4113_; 
v___x_4111_ = ((size_t)0ULL);
v___x_4112_ = lean_usize_of_nat(v___x_4104_);
v___x_4113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_used_4101_, v___x_4111_, v___x_4112_, v___x_4105_);
lean_dec_ref(v_used_4101_);
v___y_4088_ = v___x_4113_;
goto v___jp_4087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___boxed(lean_object* v_exported_4127_, lean_object* v_a_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_4127_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(lean_object* v_exported_4130_, lean_object* v_a_4131_){
_start:
{
lean_object* v___x_4133_; 
v___x_4133_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_4130_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___boxed(lean_object* v_exported_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(v_exported_4134_, v_a_4135_);
lean_dec_ref(v_a_4135_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject(lean_object* v_a_4138_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_4138_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v___x_4141_; 
lean_dec_ref_known(v___x_4140_, 1);
v___x_4141_ = l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport(v_a_4138_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4143_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc_n(v_a_4142_, 2);
lean_dec_ref_known(v___x_4141_, 1);
v___x_4143_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_a_4142_, v_a_4138_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4171_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4146_ = v___x_4143_;
v_isShared_4147_ = v_isSharedCheck_4171_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4143_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4171_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
if (lean_obj_tag(v_a_4144_) == 1)
{
lean_object* v_val_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4158_; 
lean_dec(v_a_4142_);
v_val_4148_ = lean_ctor_get(v_a_4144_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v_a_4144_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4150_ = v_a_4144_;
v_isShared_4151_ = v_isSharedCheck_4158_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_val_4148_);
lean_dec(v_a_4144_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4158_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
lean_ctor_set_tag(v___x_4150_, 18);
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_val_4148_);
v___x_4153_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
lean_object* v___x_4155_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set_tag(v___x_4146_, 1);
lean_ctor_set(v___x_4146_, 0, v___x_4153_);
v___x_4155_ = v___x_4146_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v___x_4153_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
else
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
lean_del_object(v___x_4146_);
lean_dec(v_a_4144_);
v___x_4159_ = l___private_Lake_CLI_Check_0__Lake_Check_stringStream(v_a_4142_);
v___x_4160_ = l_LeanExport_parseStream(v___x_4159_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4162_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4160_, 1);
v___x_4162_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_a_4161_);
return v___x_4162_;
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
v_a_4163_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4165_ = v___x_4160_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4160_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_a_4163_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
}
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
lean_dec(v_a_4142_);
v_a_4172_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___x_4143_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4143_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4172_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
v_a_4180_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4141_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4141_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
else
{
return v___x_4140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___boxed(lean_object* v_a_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v_a_4188_);
lean_dec_ref(v_a_4188_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(size_t v_sz_4191_, size_t v_i_4192_, lean_object* v_bs_4193_){
_start:
{
uint8_t v___x_4194_; 
v___x_4194_ = lean_usize_dec_lt(v_i_4192_, v_sz_4191_);
if (v___x_4194_ == 0)
{
return v_bs_4193_;
}
else
{
lean_object* v_v_4195_; lean_object* v___x_4196_; lean_object* v_bs_x27_4197_; lean_object* v___x_4198_; size_t v___x_4199_; size_t v___x_4200_; lean_object* v___x_4201_; 
v_v_4195_ = lean_array_uget(v_bs_4193_, v_i_4192_);
v___x_4196_ = lean_unsigned_to_nat(0u);
v_bs_x27_4197_ = lean_array_uset(v_bs_4193_, v_i_4192_, v___x_4196_);
v___x_4198_ = l_String_toName(v_v_4195_);
v___x_4199_ = ((size_t)1ULL);
v___x_4200_ = lean_usize_add(v_i_4192_, v___x_4199_);
v___x_4201_ = lean_array_uset(v_bs_x27_4197_, v_i_4192_, v___x_4198_);
v_i_4192_ = v___x_4200_;
v_bs_4193_ = v___x_4201_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0___boxed(lean_object* v_sz_4203_, lean_object* v_i_4204_, lean_object* v_bs_4205_){
_start:
{
size_t v_sz_boxed_4206_; size_t v_i_boxed_4207_; lean_object* v_res_4208_; 
v_sz_boxed_4206_ = lean_unbox_usize(v_sz_4203_);
lean_dec(v_sz_4203_);
v_i_boxed_4207_ = lean_unbox_usize(v_i_4204_);
lean_dec(v_i_4204_);
v_res_4208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_boxed_4206_, v_i_boxed_4207_, v_bs_4205_);
return v_res_4208_;
}
}
static lean_object* _init_l_Lake_Check_runChallenge___boxed__const__1(void){
_start:
{
uint32_t v___x_4215_; lean_object* v___x_4216_; 
v___x_4215_ = 1;
v___x_4216_ = lean_box_uint32(v___x_4215_);
return v___x_4216_;
}
}
static lean_object* _init_l_Lake_Check_runChallenge___boxed__const__2(void){
_start:
{
uint32_t v___x_4217_; lean_object* v___x_4218_; 
v___x_4217_ = 0;
v___x_4218_ = lean_box_uint32(v___x_4217_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runChallenge(lean_object* v_configFile_x3f_4219_, lean_object* v_lean_4220_, lean_object* v_lake_4221_, lean_object* v_projectDir_4222_){
_start:
{
lean_object* v_a_4225_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4247_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__0));
v___x_4248_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_4247_, v_lean_4220_, v_lake_4221_, v_projectDir_4222_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4383_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4251_ = v___x_4248_;
v_isShared_4252_ = v_isSharedCheck_4383_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4248_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4383_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
if (lean_obj_tag(v_a_4249_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4255_; 
v_a_4253_ = lean_ctor_get(v_a_4249_, 0);
lean_inc(v_a_4253_);
lean_dec_ref_known(v_a_4249_, 1);
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 0, v_a_4253_);
v___x_4255_ = v___x_4251_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4253_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
else
{
lean_del_object(v___x_4251_);
if (lean_obj_tag(v_configFile_x3f_4219_) == 1)
{
lean_object* v_a_4257_; lean_object* v_val_4258_; lean_object* v___x_4259_; 
v_a_4257_ = lean_ctor_get(v_a_4249_, 0);
lean_inc(v_a_4257_);
lean_dec_ref_known(v_a_4249_, 1);
v_val_4258_ = lean_ctor_get(v_configFile_x3f_4219_, 0);
v___x_4259_ = l_IO_FS_readFile(v_val_4258_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v_a_4262_; lean_object* v___x_4269_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
lean_dec_ref_known(v___x_4259_, 1);
v___x_4269_ = l_Lean_Json_parse(v_a_4260_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; 
lean_dec(v_a_4257_);
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
lean_inc(v_a_4270_);
lean_dec_ref_known(v___x_4269_, 1);
v_a_4262_ = v_a_4270_;
goto v___jp_4261_;
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4272_; 
v_a_4271_ = lean_ctor_get(v___x_4269_, 0);
lean_inc(v_a_4271_);
lean_dec_ref_known(v___x_4269_, 1);
v___x_4272_ = l_Lake_Check_instFromJsonConfig_fromJson(v_a_4271_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; 
lean_dec(v_a_4257_);
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4273_);
lean_dec_ref_known(v___x_4272_, 1);
v_a_4262_ = v_a_4273_;
goto v___jp_4261_;
}
else
{
lean_object* v_a_4274_; lean_object* v_challenge__module_4275_; lean_object* v_solution__module_4276_; lean_object* v_theorem__names_4277_; lean_object* v_definition__names_4278_; lean_object* v_permitted__axioms_4279_; size_t v_sz_4280_; size_t v___x_4281_; lean_object* v___x_4282_; lean_object* v___y_4284_; lean_object* v___y_4364_; 
v_a_4274_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4274_);
lean_dec_ref_known(v___x_4272_, 1);
v_challenge__module_4275_ = lean_ctor_get(v_a_4274_, 0);
lean_inc_ref(v_challenge__module_4275_);
v_solution__module_4276_ = lean_ctor_get(v_a_4274_, 1);
lean_inc_ref(v_solution__module_4276_);
v_theorem__names_4277_ = lean_ctor_get(v_a_4274_, 2);
v_definition__names_4278_ = lean_ctor_get(v_a_4274_, 3);
v_permitted__axioms_4279_ = lean_ctor_get(v_a_4274_, 4);
lean_inc_ref(v_permitted__axioms_4279_);
v_sz_4280_ = lean_array_size(v_theorem__names_4277_);
v___x_4281_ = ((size_t)0ULL);
lean_inc_ref(v_theorem__names_4277_);
v___x_4282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_4280_, v___x_4281_, v_theorem__names_4277_);
if (lean_obj_tag(v_definition__names_4278_) == 0)
{
lean_object* v___x_4374_; 
v___x_4374_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18));
v___y_4364_ = v___x_4374_;
goto v___jp_4363_;
}
else
{
lean_object* v_val_4375_; 
v_val_4375_ = lean_ctor_get(v_definition__names_4278_, 0);
lean_inc(v_val_4375_);
v___y_4364_ = v_val_4375_;
goto v___jp_4363_;
}
v___jp_4283_:
{
lean_object* v___x_4285_; 
v___x_4285_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v_a_4274_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4354_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4288_ = v___x_4285_;
v_isShared_4289_ = v_isSharedCheck_4354_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4285_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4354_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
if (lean_obj_tag(v_a_4286_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4292_; 
lean_dec_ref(v___y_4284_);
lean_dec_ref(v___x_4282_);
lean_dec_ref(v_permitted__axioms_4279_);
lean_dec_ref(v_solution__module_4276_);
lean_dec_ref(v_challenge__module_4275_);
lean_dec(v_a_4257_);
v_a_4290_ = lean_ctor_get(v_a_4286_, 0);
lean_inc(v_a_4290_);
lean_dec_ref_known(v_a_4286_, 1);
if (v_isShared_4289_ == 0)
{
lean_ctor_set(v___x_4288_, 0, v_a_4290_);
v___x_4292_ = v___x_4288_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4290_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
else
{
lean_object* v_a_4294_; lean_object* v_projectDir_4295_; lean_object* v_leanPath_4296_; lean_object* v_binPath_4297_; lean_object* v_whichLandrun_4298_; lean_object* v_whichLake_4299_; lean_object* v_whichLean4Export_4300_; lean_object* v_whichLeanChecker_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4347_; 
lean_del_object(v___x_4288_);
v_a_4294_ = lean_ctor_get(v_a_4286_, 0);
lean_inc(v_a_4294_);
lean_dec_ref_known(v_a_4286_, 1);
v_projectDir_4295_ = lean_ctor_get(v_a_4257_, 0);
v_leanPath_4296_ = lean_ctor_get(v_a_4257_, 6);
v_binPath_4297_ = lean_ctor_get(v_a_4257_, 7);
v_whichLandrun_4298_ = lean_ctor_get(v_a_4257_, 8);
v_whichLake_4299_ = lean_ctor_get(v_a_4257_, 9);
v_whichLean4Export_4300_ = lean_ctor_get(v_a_4257_, 10);
v_whichLeanChecker_4301_ = lean_ctor_get(v_a_4257_, 11);
v_isSharedCheck_4347_ = !lean_is_exclusive(v_a_4257_);
if (v_isSharedCheck_4347_ == 0)
{
lean_object* v_unused_4348_; lean_object* v_unused_4349_; lean_object* v_unused_4350_; lean_object* v_unused_4351_; lean_object* v_unused_4352_; lean_object* v_unused_4353_; 
v_unused_4348_ = lean_ctor_get(v_a_4257_, 12);
lean_dec(v_unused_4348_);
v_unused_4349_ = lean_ctor_get(v_a_4257_, 5);
lean_dec(v_unused_4349_);
v_unused_4350_ = lean_ctor_get(v_a_4257_, 4);
lean_dec(v_unused_4350_);
v_unused_4351_ = lean_ctor_get(v_a_4257_, 3);
lean_dec(v_unused_4351_);
v_unused_4352_ = lean_ctor_get(v_a_4257_, 2);
lean_dec(v_unused_4352_);
v_unused_4353_ = lean_ctor_get(v_a_4257_, 1);
lean_dec(v_unused_4353_);
v___x_4303_ = v_a_4257_;
v_isShared_4304_ = v_isSharedCheck_4347_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_whichLeanChecker_4301_);
lean_inc(v_whichLean4Export_4300_);
lean_inc(v_whichLake_4299_);
lean_inc(v_whichLandrun_4298_);
lean_inc(v_binPath_4297_);
lean_inc(v_leanPath_4296_);
lean_inc(v_projectDir_4295_);
lean_dec(v_a_4257_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4347_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4305_; 
lean_inc_ref(v_projectDir_4295_);
v___x_4305_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_4247_, v_projectDir_4295_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4338_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4308_ = v___x_4305_;
v_isShared_4309_ = v_isSharedCheck_4338_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4305_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4338_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
if (lean_obj_tag(v_a_4306_) == 1)
{
lean_object* v_val_4310_; lean_object* v___x_4312_; 
lean_del_object(v___x_4303_);
lean_dec_ref(v_whichLeanChecker_4301_);
lean_dec_ref(v_whichLean4Export_4300_);
lean_dec_ref(v_whichLake_4299_);
lean_dec_ref(v_whichLandrun_4298_);
lean_dec_ref(v_binPath_4297_);
lean_dec_ref(v_leanPath_4296_);
lean_dec_ref(v_projectDir_4295_);
lean_dec(v_a_4294_);
lean_dec_ref(v___y_4284_);
lean_dec_ref(v___x_4282_);
lean_dec_ref(v_permitted__axioms_4279_);
lean_dec_ref(v_solution__module_4276_);
lean_dec_ref(v_challenge__module_4275_);
v_val_4310_ = lean_ctor_get(v_a_4306_, 0);
lean_inc(v_val_4310_);
lean_dec_ref_known(v_a_4306_, 1);
if (v_isShared_4309_ == 0)
{
lean_ctor_set(v___x_4308_, 0, v_val_4310_);
v___x_4312_ = v___x_4308_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_val_4310_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
else
{
lean_object* v___x_4314_; lean_object* v___x_4315_; size_t v_sz_4316_; lean_object* v___x_4317_; lean_object* v___x_4319_; 
lean_del_object(v___x_4308_);
lean_dec(v_a_4306_);
v___x_4314_ = l_String_toName(v_challenge__module_4275_);
v___x_4315_ = l_String_toName(v_solution__module_4276_);
v_sz_4316_ = lean_array_size(v_permitted__axioms_4279_);
v___x_4317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_4316_, v___x_4281_, v_permitted__axioms_4279_);
lean_inc(v_a_4294_);
lean_inc_ref(v_whichLeanChecker_4301_);
lean_inc_ref(v_whichLean4Export_4300_);
lean_inc_ref(v_whichLake_4299_);
lean_inc_ref(v_whichLandrun_4298_);
lean_inc_ref(v___x_4317_);
lean_inc_ref(v___y_4284_);
lean_inc_ref(v___x_4282_);
lean_inc(v___x_4315_);
lean_inc(v___x_4314_);
lean_inc_ref(v_projectDir_4295_);
if (v_isShared_4304_ == 0)
{
lean_ctor_set(v___x_4303_, 12, v_a_4294_);
lean_ctor_set(v___x_4303_, 5, v___x_4317_);
lean_ctor_set(v___x_4303_, 4, v___y_4284_);
lean_ctor_set(v___x_4303_, 3, v___x_4282_);
lean_ctor_set(v___x_4303_, 2, v___x_4315_);
lean_ctor_set(v___x_4303_, 1, v___x_4314_);
v___x_4319_ = v___x_4303_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_projectDir_4295_);
lean_ctor_set(v_reuseFailAlloc_4337_, 1, v___x_4314_);
lean_ctor_set(v_reuseFailAlloc_4337_, 2, v___x_4315_);
lean_ctor_set(v_reuseFailAlloc_4337_, 3, v___x_4282_);
lean_ctor_set(v_reuseFailAlloc_4337_, 4, v___y_4284_);
lean_ctor_set(v_reuseFailAlloc_4337_, 5, v___x_4317_);
lean_ctor_set(v_reuseFailAlloc_4337_, 6, v_leanPath_4296_);
lean_ctor_set(v_reuseFailAlloc_4337_, 7, v_binPath_4297_);
lean_ctor_set(v_reuseFailAlloc_4337_, 8, v_whichLandrun_4298_);
lean_ctor_set(v_reuseFailAlloc_4337_, 9, v_whichLake_4299_);
lean_ctor_set(v_reuseFailAlloc_4337_, 10, v_whichLean4Export_4300_);
lean_ctor_set(v_reuseFailAlloc_4337_, 11, v_whichLeanChecker_4301_);
lean_ctor_set(v_reuseFailAlloc_4337_, 12, v_a_4294_);
v___x_4319_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
lean_object* v___x_4320_; 
v___x_4320_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v___x_4319_);
lean_dec_ref(v___x_4319_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v_a_4321_; lean_object* v_fst_4322_; lean_object* v_snd_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v_a_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_a_4321_);
lean_dec_ref_known(v___x_4320_, 1);
v_fst_4322_ = lean_ctor_get(v_a_4321_, 0);
lean_inc(v_fst_4322_);
v_snd_4323_ = lean_ctor_get(v_a_4321_, 1);
lean_inc(v_snd_4323_);
lean_dec(v_a_4321_);
v___x_4324_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_4324_, 0, v_projectDir_4295_);
lean_ctor_set(v___x_4324_, 1, v___x_4314_);
lean_ctor_set(v___x_4324_, 2, v___x_4315_);
lean_ctor_set(v___x_4324_, 3, v___x_4282_);
lean_ctor_set(v___x_4324_, 4, v___y_4284_);
lean_ctor_set(v___x_4324_, 5, v___x_4317_);
lean_ctor_set(v___x_4324_, 6, v_fst_4322_);
lean_ctor_set(v___x_4324_, 7, v_snd_4323_);
lean_ctor_set(v___x_4324_, 8, v_whichLandrun_4298_);
lean_ctor_set(v___x_4324_, 9, v_whichLake_4299_);
lean_ctor_set(v___x_4324_, 10, v_whichLean4Export_4300_);
lean_ctor_set(v___x_4324_, 11, v_whichLeanChecker_4301_);
lean_ctor_set(v___x_4324_, 12, v_a_4294_);
v___x_4325_ = l_Lake_Check_compareIt(v___x_4324_);
lean_dec_ref_known(v___x_4324_, 13);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4333_; 
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4333_ == 0)
{
lean_object* v_unused_4334_; 
v_unused_4334_ = lean_ctor_get(v___x_4325_, 0);
lean_dec(v_unused_4334_);
v___x_4327_ = v___x_4325_;
v_isShared_4328_ = v_isSharedCheck_4333_;
goto v_resetjp_4326_;
}
else
{
lean_dec(v___x_4325_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4333_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4329_; lean_object* v___x_4331_; 
v___x_4329_ = l_Lake_Check_runChallenge___boxed__const__2;
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v___x_4329_);
v___x_4331_ = v___x_4327_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4329_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
else
{
lean_object* v_a_4335_; 
v_a_4335_ = lean_ctor_get(v___x_4325_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4325_, 1);
v_a_4225_ = v_a_4335_;
goto v___jp_4224_;
}
}
else
{
lean_object* v_a_4336_; 
lean_dec_ref(v___x_4317_);
lean_dec(v___x_4315_);
lean_dec(v___x_4314_);
lean_dec_ref(v_whichLeanChecker_4301_);
lean_dec_ref(v_whichLean4Export_4300_);
lean_dec_ref(v_whichLake_4299_);
lean_dec_ref(v_whichLandrun_4298_);
lean_dec_ref(v_projectDir_4295_);
lean_dec(v_a_4294_);
lean_dec_ref(v___y_4284_);
lean_dec_ref(v___x_4282_);
v_a_4336_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v___x_4320_, 1);
v_a_4225_ = v_a_4336_;
goto v___jp_4224_;
}
}
}
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_del_object(v___x_4303_);
lean_dec_ref(v_whichLeanChecker_4301_);
lean_dec_ref(v_whichLean4Export_4300_);
lean_dec_ref(v_whichLake_4299_);
lean_dec_ref(v_whichLandrun_4298_);
lean_dec_ref(v_binPath_4297_);
lean_dec_ref(v_leanPath_4296_);
lean_dec_ref(v_projectDir_4295_);
lean_dec(v_a_4294_);
lean_dec_ref(v___y_4284_);
lean_dec_ref(v___x_4282_);
lean_dec_ref(v_permitted__axioms_4279_);
lean_dec_ref(v_solution__module_4276_);
lean_dec_ref(v_challenge__module_4275_);
v_a_4339_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4305_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4305_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
lean_dec_ref(v___y_4284_);
lean_dec_ref(v___x_4282_);
lean_dec_ref(v_permitted__axioms_4279_);
lean_dec_ref(v_solution__module_4276_);
lean_dec_ref(v_challenge__module_4275_);
lean_dec(v_a_4257_);
v_a_4355_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4357_ = v___x_4285_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4285_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
v___jp_4363_:
{
size_t v_sz_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; uint8_t v___x_4369_; 
v_sz_4365_ = lean_array_size(v___y_4364_);
v___x_4366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_4365_, v___x_4281_, v___y_4364_);
v___x_4367_ = lean_array_get_size(v___x_4282_);
v___x_4368_ = lean_unsigned_to_nat(0u);
v___x_4369_ = lean_nat_dec_eq(v___x_4367_, v___x_4368_);
if (v___x_4369_ == 0)
{
v___y_4284_ = v___x_4366_;
goto v___jp_4283_;
}
else
{
lean_object* v___x_4370_; uint8_t v___x_4371_; 
v___x_4370_ = lean_array_get_size(v___x_4366_);
v___x_4371_ = lean_nat_dec_eq(v___x_4370_, v___x_4368_);
if (v___x_4371_ == 0)
{
v___y_4284_ = v___x_4366_;
goto v___jp_4283_;
}
else
{
lean_object* v___x_4372_; lean_object* v___x_4373_; 
lean_dec_ref(v___x_4366_);
lean_dec_ref(v___x_4282_);
lean_dec_ref(v_permitted__axioms_4279_);
lean_dec_ref(v_solution__module_4276_);
lean_dec_ref(v_challenge__module_4275_);
lean_dec(v_a_4274_);
lean_dec(v_a_4257_);
v___x_4372_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__3));
v___x_4373_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4372_);
return v___x_4373_;
}
}
}
}
}
v___jp_4261_:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4263_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__1));
v___x_4264_ = lean_string_append(v___x_4263_, v_val_4258_);
v___x_4265_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__2));
v___x_4266_ = lean_string_append(v___x_4264_, v___x_4265_);
v___x_4267_ = lean_string_append(v___x_4266_, v_a_4262_);
lean_dec_ref(v_a_4262_);
v___x_4268_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4267_);
lean_dec_ref(v___x_4267_);
return v___x_4268_;
}
}
else
{
lean_object* v_a_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
lean_dec(v_a_4257_);
v_a_4376_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4376_);
lean_dec_ref_known(v___x_4259_, 1);
v___x_4377_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__4));
v___x_4378_ = lean_io_error_to_string(v_a_4376_);
v___x_4379_ = lean_string_append(v___x_4377_, v___x_4378_);
lean_dec_ref(v___x_4378_);
v___x_4380_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4379_);
lean_dec_ref(v___x_4379_);
return v___x_4380_;
}
}
else
{
lean_object* v___x_4381_; lean_object* v___x_4382_; 
lean_dec_ref_known(v_a_4249_, 1);
v___x_4381_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__5));
v___x_4382_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4381_);
return v___x_4382_;
}
}
}
}
else
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4391_; 
v_a_4384_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4386_ = v___x_4248_;
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v___x_4248_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4389_; 
if (v_isShared_4387_ == 0)
{
v___x_4389_ = v___x_4386_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4384_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
v___jp_4224_:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4226_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_4227_ = lean_io_error_to_string(v_a_4225_);
v___x_4228_ = lean_string_append(v___x_4226_, v___x_4227_);
lean_dec_ref(v___x_4227_);
v___x_4229_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_4228_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4237_; 
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4237_ == 0)
{
lean_object* v_unused_4238_; 
v_unused_4238_ = lean_ctor_get(v___x_4229_, 0);
lean_dec(v_unused_4238_);
v___x_4231_ = v___x_4229_;
v_isShared_4232_ = v_isSharedCheck_4237_;
goto v_resetjp_4230_;
}
else
{
lean_dec(v___x_4229_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4237_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4233_; lean_object* v___x_4235_; 
v___x_4233_ = l_Lake_Check_runChallenge___boxed__const__1;
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 0, v___x_4233_);
v___x_4235_ = v___x_4231_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4233_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
v_a_4239_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4229_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4229_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runChallenge___boxed(lean_object* v_configFile_x3f_4392_, lean_object* v_lean_4393_, lean_object* v_lake_4394_, lean_object* v_projectDir_4395_, lean_object* v_a_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_Lake_Check_runChallenge(v_configFile_x3f_4392_, v_lean_4393_, v_lake_4394_, v_projectDir_4395_);
lean_dec_ref(v_lake_4394_);
lean_dec(v_configFile_x3f_4392_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runCheck(lean_object* v_lean_4398_, lean_object* v_lake_4399_, lean_object* v_projectDir_4400_){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4402_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeBuildAndExport___closed__1));
v___x_4403_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_4402_, v_lean_4398_, v_lake_4399_, v_projectDir_4400_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4464_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4406_ = v___x_4403_;
v_isShared_4407_ = v_isSharedCheck_4464_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4403_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4464_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
if (lean_obj_tag(v_a_4404_) == 0)
{
lean_object* v_a_4408_; lean_object* v___x_4410_; 
v_a_4408_ = lean_ctor_get(v_a_4404_, 0);
lean_inc(v_a_4408_);
lean_dec_ref_known(v_a_4404_, 1);
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 0, v_a_4408_);
v___x_4410_ = v___x_4406_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v_a_4408_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
else
{
lean_object* v_a_4412_; lean_object* v_projectDir_4413_; lean_object* v___x_4414_; 
lean_del_object(v___x_4406_);
v_a_4412_ = lean_ctor_get(v_a_4404_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v_a_4404_, 1);
v_projectDir_4413_ = lean_ctor_get(v_a_4412_, 0);
lean_inc_ref(v_projectDir_4413_);
v___x_4414_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_4402_, v_projectDir_4413_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4455_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4417_ = v___x_4414_;
v_isShared_4418_ = v_isSharedCheck_4455_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4414_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4455_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
if (lean_obj_tag(v_a_4415_) == 1)
{
lean_object* v_val_4419_; lean_object* v___x_4421_; 
lean_dec(v_a_4412_);
v_val_4419_ = lean_ctor_get(v_a_4415_, 0);
lean_inc(v_val_4419_);
lean_dec_ref_known(v_a_4415_, 1);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v_val_4419_);
v___x_4421_ = v___x_4417_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_val_4419_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
else
{
lean_object* v___x_4423_; 
lean_del_object(v___x_4417_);
lean_dec(v_a_4415_);
v___x_4423_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v_a_4412_);
lean_dec(v_a_4412_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4431_; 
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4431_ == 0)
{
lean_object* v_unused_4432_; 
v_unused_4432_ = lean_ctor_get(v___x_4423_, 0);
lean_dec(v_unused_4432_);
v___x_4425_ = v___x_4423_;
v_isShared_4426_ = v_isSharedCheck_4431_;
goto v_resetjp_4424_;
}
else
{
lean_dec(v___x_4423_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4431_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4427_; lean_object* v___x_4429_; 
v___x_4427_ = l_Lake_Check_runChallenge___boxed__const__2;
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___x_4427_);
v___x_4429_ = v___x_4425_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v___x_4427_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v_a_4433_ = lean_ctor_get(v___x_4423_, 0);
lean_inc(v_a_4433_);
lean_dec_ref_known(v___x_4423_, 1);
v___x_4434_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_4435_ = lean_io_error_to_string(v_a_4433_);
v___x_4436_ = lean_string_append(v___x_4434_, v___x_4435_);
lean_dec_ref(v___x_4435_);
v___x_4437_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_4436_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4445_; 
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4445_ == 0)
{
lean_object* v_unused_4446_; 
v_unused_4446_ = lean_ctor_get(v___x_4437_, 0);
lean_dec(v_unused_4446_);
v___x_4439_ = v___x_4437_;
v_isShared_4440_ = v_isSharedCheck_4445_;
goto v_resetjp_4438_;
}
else
{
lean_dec(v___x_4437_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4445_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4441_; lean_object* v___x_4443_; 
v___x_4441_ = l_Lake_Check_runChallenge___boxed__const__1;
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 0, v___x_4441_);
v___x_4443_ = v___x_4439_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4441_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
v_a_4447_ = lean_ctor_get(v___x_4437_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4437_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4437_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4463_; 
lean_dec(v_a_4412_);
v_a_4456_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4458_ = v___x_4414_;
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4414_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4461_; 
if (v_isShared_4459_ == 0)
{
v___x_4461_ = v___x_4458_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_a_4456_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
}
}
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
v_a_4465_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4403_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4403_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runCheck___boxed(lean_object* v_lean_4473_, lean_object* v_lake_4474_, lean_object* v_projectDir_4475_, lean_object* v_a_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_Lake_Check_runCheck(v_lean_4473_, v_lake_4474_, v_projectDir_4475_);
lean_dec_ref(v_lake_4474_);
return v_res_4477_;
}
}
lean_object* runtime_initialize_Lake_Check_Axioms(uint8_t builtin);
lean_object* runtime_initialize_Lake_Check_Compare(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_InstallPath(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Exit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json_FromToJson(uint8_t builtin);
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Replay(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Check(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Check_Axioms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Check_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_FromToJson(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Replay(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1 = _init_l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1();
lean_mark_persistent(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1);
l_Lake_Check_runChallenge___boxed__const__1 = _init_l_Lake_Check_runChallenge___boxed__const__1();
lean_mark_persistent(l_Lake_Check_runChallenge___boxed__const__1);
l_Lake_Check_runChallenge___boxed__const__2 = _init_l_Lake_Check_runChallenge___boxed__const__2();
lean_mark_persistent(l_Lake_Check_runChallenge___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_Check(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Check_Axioms(uint8_t builtin);
lean_object* initialize_Lake_Check_Compare(uint8_t builtin);
lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin);
lean_object* initialize_Lake_Util_Exit(uint8_t builtin);
lean_object* initialize_Lean_Data_Json_FromToJson(uint8_t builtin);
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Lean_Replay(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Check(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Check_Axioms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Check_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_FromToJson(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Replay(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Check(builtin);
}
#ifdef __cplusplus
}
#endif
