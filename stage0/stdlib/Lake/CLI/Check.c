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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_get_stdout();
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_mkEmptyEnvironment(uint32_t);
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Environment_replay(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
uint8_t l_Lake_Check_Compare_instBEqConstantInfo__lake_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* lean_get_stderr();
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* lean_io_create_tempfile();
lean_object* lean_io_remove_file(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_io_create_dir(lean_object*);
lean_object* l_LeanExport_parseStream(lean_object*);
lean_object* l_Lake_Check_compareAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Check_checkAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Child exited with "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Building "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "build"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__2;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Exporting "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " from "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LEAN_PATH"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__3_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__3_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__4_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__5;
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
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " kernel rejected the solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " exited with "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " kernel accepts the solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25_value;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Quotient constant mismatch on: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "Could not find quotient constant in final kernel env: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean default kernel rejects the solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Running Lean default kernel on solution."};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__3_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__4_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 113, 137, 82, 82, 132, 58, 248)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__5_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__6_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__5_value),LEAN_SCALAR_PTR_LITERAL(91, 125, 38, 34, 222, 200, 201, 80)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__6 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ind"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__7 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__7_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__8_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__7_value),LEAN_SCALAR_PTR_LITERAL(150, 213, 121, 152, 109, 27, 137, 60)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__8 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__9 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__9_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__6_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__9_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__10 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__10_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__4_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__10_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__11 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__11_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean default kernel accepts the solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__12 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__12_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__13 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__13_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__13_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__11_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__14 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__14_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Quotient post-check rejects the solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__15 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__41_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__3_value),LEAN_SCALAR_PTR_LITERAL(118, 80, 194, 26, 119, 145, 0, 103)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__41 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__41_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__42 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__42_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optParam"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__43 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__43_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__43_value),LEAN_SCALAR_PTR_LITERAL(140, 160, 223, 165, 16, 51, 54, 209)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__44 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__44_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "autoParam"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__45 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__45_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__45_value),LEAN_SCALAR_PTR_LITERAL(140, 161, 241, 39, 119, 172, 48, 112)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__46 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__46_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "semiOutParam"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__47 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__47_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__47_value),LEAN_SCALAR_PTR_LITERAL(141, 187, 140, 108, 143, 232, 13, 120)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__48 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__48_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "outParam"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__49 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__49_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__49_value),LEAN_SCALAR_PTR_LITERAL(209, 153, 87, 30, 57, 250, 25, 29)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__50 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__50_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*26, .m_other = 0, .m_tag = 246}, .m_size = 26, .m_capacity = 26, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__2_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__4_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__6_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__8_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__10_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__12_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__14_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__16_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__18_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__20_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__22_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__24_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__26_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__28_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__31_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__34_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__36_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__38_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__39_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__40_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__41_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__42_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__44_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__46_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__48_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__50_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__51 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__51_value;
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
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sound"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__1_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__2_value_aux_0),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 255, 230, 69, 40, 79, 199, 28)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__2_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__13_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__4_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__6_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__8_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__4;
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
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` needs `git` on PATH to build inside the sandbox"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "landrun"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5_value;
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels(lean_object* v_a_1_){
_start:
{
lean_object* v_externalKernels_3_; lean_object* v___x_4_; 
v_externalKernels_3_ = lean_ctor_get(v_a_1_, 11);
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
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0(lean_object* v_s_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_putStr_298_; lean_object* v___x_299_; 
v___x_297_ = lean_get_stderr();
v_putStr_298_ = lean_ctor_get(v___x_297_, 4);
lean_inc_ref(v_putStr_298_);
lean_dec_ref(v___x_297_);
v___x_299_ = lean_apply_2(v_putStr_298_, v_s_295_, lean_box(0));
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0___boxed(lean_object* v_s_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0(v_s_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(lean_object* v_spawnArgs_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_projectDir_307_; lean_object* v_whichLandrun_308_; lean_object* v___x_309_; lean_object* v_envOverride_310_; lean_object* v_args_311_; lean_object* v___x_312_; uint8_t v___x_313_; uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_projectDir_307_ = lean_ctor_get(v_a_305_, 0);
v_whichLandrun_308_ = lean_ctor_get(v_a_305_, 8);
v___x_309_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v_envOverride_310_ = lean_ctor_get(v_spawnArgs_304_, 3);
lean_inc_ref(v_envOverride_310_);
v_args_311_ = l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs(v_spawnArgs_304_);
lean_inc_ref(v_projectDir_307_);
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v_projectDir_307_);
v___x_313_ = 1;
v___x_314_ = 0;
lean_inc_ref(v_whichLandrun_308_);
v___x_315_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_315_, 0, v___x_309_);
lean_ctor_set(v___x_315_, 1, v_whichLandrun_308_);
lean_ctor_set(v___x_315_, 2, v_args_311_);
lean_ctor_set(v___x_315_, 3, v___x_312_);
lean_ctor_set(v___x_315_, 4, v_envOverride_310_);
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*5, v___x_313_);
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*5 + 1, v___x_314_);
v___x_316_ = lean_box(0);
v___x_317_ = l_IO_Process_output(v___x_315_, v___x_316_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; uint32_t v_exitCode_319_; lean_object* v_stdout_320_; lean_object* v_stderr_321_; lean_object* v___x_322_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
v_exitCode_319_ = lean_ctor_get_uint32(v_a_318_, sizeof(void*)*2);
v_stdout_320_ = lean_ctor_get(v_a_318_, 0);
lean_inc_ref(v_stdout_320_);
v_stderr_321_ = lean_ctor_get(v_a_318_, 1);
lean_inc_ref(v_stderr_321_);
lean_dec(v_a_318_);
v___x_322_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0(v_stderr_321_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_339_; 
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; 
v_unused_340_ = lean_ctor_get(v___x_322_, 0);
lean_dec(v_unused_340_);
v___x_324_ = v___x_322_;
v_isShared_325_ = v_isSharedCheck_339_;
goto v_resetjp_323_;
}
else
{
lean_dec(v___x_322_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_339_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
uint32_t v___x_326_; uint8_t v___x_327_; 
v___x_326_ = 0;
v___x_327_ = lean_uint32_dec_eq(v_exitCode_319_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
lean_dec_ref(v_stdout_320_);
v___x_328_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___closed__0));
v___x_329_ = lean_uint32_to_nat(v_exitCode_319_);
v___x_330_ = l_Nat_reprFast(v___x_329_);
v___x_331_ = lean_string_append(v___x_328_, v___x_330_);
lean_dec_ref(v___x_330_);
v___x_332_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 1);
lean_ctor_set(v___x_324_, 0, v___x_332_);
v___x_334_ = v___x_324_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
else
{
lean_object* v___x_337_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v_stdout_320_);
v___x_337_ = v___x_324_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_stdout_320_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec_ref(v_stdout_320_);
v_a_341_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_322_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_322_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
v_a_349_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_317_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_317_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___boxed(lean_object* v_spawnArgs_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v_spawnArgs_357_, v_a_358_);
lean_dec_ref(v_a_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(lean_object* v_spawnArgs_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_projectDir_364_; lean_object* v_whichLandrun_365_; lean_object* v___x_366_; lean_object* v_envOverride_367_; lean_object* v_args_368_; lean_object* v___x_369_; uint8_t v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_projectDir_364_ = lean_ctor_get(v_a_362_, 0);
v_whichLandrun_365_ = lean_ctor_get(v_a_362_, 8);
v___x_366_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v_envOverride_367_ = lean_ctor_get(v_spawnArgs_361_, 3);
lean_inc_ref(v_envOverride_367_);
v_args_368_ = l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs(v_spawnArgs_361_);
lean_inc_ref(v_projectDir_364_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v_projectDir_364_);
v___x_370_ = 1;
v___x_371_ = 0;
lean_inc_ref(v_whichLandrun_365_);
v___x_372_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_372_, 0, v___x_366_);
lean_ctor_set(v___x_372_, 1, v_whichLandrun_365_);
lean_ctor_set(v___x_372_, 2, v_args_368_);
lean_ctor_set(v___x_372_, 3, v___x_369_);
lean_ctor_set(v___x_372_, 4, v_envOverride_367_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*5, v___x_370_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*5 + 1, v___x_371_);
v___x_373_ = lean_io_process_spawn(v___x_372_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_375_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref_known(v___x_373_, 1);
v___x_375_ = lean_io_process_child_wait(v___x_366_, v_a_374_);
lean_dec(v_a_374_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_396_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_396_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_396_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_396_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
uint32_t v___x_380_; uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_380_ = 0;
v___x_381_ = lean_unbox_uint32(v_a_376_);
v___x_382_ = lean_uint32_dec_eq(v___x_381_, v___x_380_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; uint32_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_383_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___closed__0));
v___x_384_ = lean_unbox_uint32(v_a_376_);
lean_dec(v_a_376_);
v___x_385_ = lean_uint32_to_nat(v___x_384_);
v___x_386_ = l_Nat_reprFast(v___x_385_);
v___x_387_ = lean_string_append(v___x_383_, v___x_386_);
lean_dec_ref(v___x_386_);
v___x_388_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
if (v_isShared_379_ == 0)
{
lean_ctor_set_tag(v___x_378_, 1);
lean_ctor_set(v___x_378_, 0, v___x_388_);
v___x_390_ = v___x_378_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
else
{
lean_object* v___x_392_; lean_object* v___x_394_; 
lean_dec(v_a_376_);
v___x_392_ = lean_box(0);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_392_);
v___x_394_ = v___x_378_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
v_a_397_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_375_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_375_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
v_a_405_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_373_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_373_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed___boxed(lean_object* v_spawnArgs_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v_spawnArgs_413_, v_a_414_);
lean_dec_ref(v_a_414_);
return v_res_416_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0));
v___x_419_ = lean_string_utf8_byte_size(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(lean_object* v_s_420_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_421_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0));
v___x_422_ = lean_string_utf8_byte_size(v_s_420_);
v___x_423_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1);
v___x_424_ = lean_nat_dec_le(v___x_423_, v___x_422_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
lean_dec_ref(v_s_420_);
v___x_425_ = lean_box(0);
return v___x_425_;
}
else
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_string_memcmp(v_s_420_, v___x_421_, v___x_426_, v___x_426_, v___x_423_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec_ref(v_s_420_);
v___x_428_ = lean_box(0);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
lean_inc_ref(v_s_420_);
v___x_429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_429_, 0, v_s_420_);
lean_ctor_set(v___x_429_, 1, v___x_426_);
lean_ctor_set(v___x_429_, 2, v___x_422_);
v___x_430_ = l_String_Slice_pos_x21(v___x_429_, v___x_423_);
lean_dec_ref_known(v___x_429_, 3);
v___x_431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_431_, 0, v_s_420_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
lean_ctor_set(v___x_431_, 2, v___x_422_);
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(lean_object* v_s_433_, lean_object* v_pat_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_s_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___boxed(lean_object* v_s_436_, lean_object* v_pat_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(v_s_436_, v_pat_437_);
lean_dec_ref(v_pat_437_);
return v_res_438_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0));
v___x_441_ = lean_string_utf8_byte_size(v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(lean_object* v_s_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_443_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0));
v___x_444_ = lean_string_utf8_byte_size(v_s_442_);
v___x_445_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1);
v___x_446_ = lean_nat_dec_le(v___x_445_, v___x_444_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
lean_dec_ref(v_s_442_);
v___x_447_ = lean_box(0);
return v___x_447_;
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_string_memcmp(v_s_442_, v___x_443_, v___x_448_, v___x_448_, v___x_445_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
lean_dec_ref(v_s_442_);
v___x_450_ = lean_box(0);
return v___x_450_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc_ref(v_s_442_);
v___x_451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_451_, 0, v_s_442_);
lean_ctor_set(v___x_451_, 1, v___x_448_);
lean_ctor_set(v___x_451_, 2, v___x_444_);
v___x_452_ = l_String_Slice_pos_x21(v___x_451_, v___x_445_);
lean_dec_ref_known(v___x_451_, 3);
v___x_453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_453_, 0, v_s_442_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
lean_ctor_set(v___x_453_, 2, v___x_444_);
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(lean_object* v_s_455_, lean_object* v_pat_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_s_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___boxed(lean_object* v_s_458_, lean_object* v_pat_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(v_s_458_, v_pat_459_);
lean_dec_ref(v_pat_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(lean_object* v_s_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0));
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___boxed(lean_object* v_s_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(v_s_465_);
lean_dec_ref(v_s_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(lean_object* v_a_467_, lean_object* v___x_468_, lean_object* v___x_469_, lean_object* v_a_470_, lean_object* v_b_471_){
_start:
{
lean_object* v_it_473_; lean_object* v_startInclusive_474_; lean_object* v_endExclusive_475_; 
if (lean_obj_tag(v_a_470_) == 0)
{
lean_object* v_currPos_480_; lean_object* v_searcher_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_504_; 
v_currPos_480_ = lean_ctor_get(v_a_470_, 0);
v_searcher_481_ = lean_ctor_get(v_a_470_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_a_470_);
if (v_isSharedCheck_504_ == 0)
{
v___x_483_ = v_a_470_;
v_isShared_484_ = v_isSharedCheck_504_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_searcher_481_);
lean_inc(v_currPos_480_);
lean_dec(v_a_470_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_504_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
uint8_t v_decide_485_; 
v_decide_485_ = lean_nat_dec_eq(v_searcher_481_, v___x_469_);
if (v_decide_485_ == 0)
{
uint32_t v___x_486_; uint32_t v___x_487_; uint8_t v___x_488_; 
v___x_486_ = 10;
v___x_487_ = lean_string_utf8_get_fast(v_a_467_, v_searcher_481_);
v___x_488_ = lean_uint32_dec_eq(v___x_487_, v___x_486_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = lean_string_utf8_next_fast(v_a_467_, v_searcher_481_);
lean_dec(v_searcher_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_489_);
v___x_491_ = v___x_483_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_currPos_480_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_489_);
v___x_491_ = v_reuseFailAlloc_493_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
v_a_470_ = v___x_491_;
goto _start;
}
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_slice_497_; lean_object* v_nextIt_499_; 
v___x_494_ = lean_string_utf8_next_fast(v_a_467_, v_searcher_481_);
v___x_495_ = lean_nat_sub(v___x_494_, v_searcher_481_);
v___x_496_ = lean_nat_add(v_searcher_481_, v___x_495_);
lean_dec(v___x_495_);
v_slice_497_ = l_String_Slice_subslice_x21(v___x_468_, v_currPos_480_, v_searcher_481_);
lean_inc(v___x_496_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_496_);
lean_ctor_set(v___x_483_, 0, v___x_496_);
v_nextIt_499_ = v___x_483_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_496_);
v_nextIt_499_ = v_reuseFailAlloc_502_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v_startInclusive_500_; lean_object* v_endExclusive_501_; 
v_startInclusive_500_ = lean_ctor_get(v_slice_497_, 0);
lean_inc(v_startInclusive_500_);
v_endExclusive_501_ = lean_ctor_get(v_slice_497_, 1);
lean_inc(v_endExclusive_501_);
lean_dec_ref(v_slice_497_);
v_it_473_ = v_nextIt_499_;
v_startInclusive_474_ = v_startInclusive_500_;
v_endExclusive_475_ = v_endExclusive_501_;
goto v___jp_472_;
}
}
}
else
{
lean_object* v___x_503_; 
lean_del_object(v___x_483_);
lean_dec(v_searcher_481_);
v___x_503_ = lean_box(1);
lean_inc(v___x_469_);
v_it_473_ = v___x_503_;
v_startInclusive_474_ = v_currPos_480_;
v_endExclusive_475_ = v___x_469_;
goto v___jp_472_;
}
}
}
else
{
lean_dec(v___x_469_);
lean_dec_ref(v_a_467_);
return v_b_471_;
}
v___jp_472_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
lean_inc_ref(v_a_467_);
v___x_476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_476_, 0, v_a_467_);
lean_ctor_set(v___x_476_, 1, v_startInclusive_474_);
lean_ctor_set(v___x_476_, 2, v_endExclusive_475_);
v___x_477_ = l_String_Slice_toString(v___x_476_);
lean_dec_ref_known(v___x_476_, 3);
v___x_478_ = lean_array_push(v_b_471_, v___x_477_);
v_a_470_ = v_it_473_;
v_b_471_ = v___x_478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg___boxed(lean_object* v_a_505_, lean_object* v___x_506_, lean_object* v___x_507_, lean_object* v_a_508_, lean_object* v_b_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_505_, v___x_506_, v___x_507_, v_a_508_, v_b_509_);
lean_dec_ref(v___x_506_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(lean_object* v_as_x27_511_, lean_object* v_b_512_){
_start:
{
if (lean_obj_tag(v_as_x27_511_) == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v_b_512_);
return v___x_514_;
}
else
{
lean_object* v_head_515_; lean_object* v_tail_516_; lean_object* v_fst_517_; lean_object* v_snd_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_540_; 
v_head_515_ = lean_ctor_get(v_as_x27_511_, 0);
v_tail_516_ = lean_ctor_get(v_as_x27_511_, 1);
v_fst_517_ = lean_ctor_get(v_b_512_, 0);
v_snd_518_ = lean_ctor_get(v_b_512_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_b_512_);
if (v_isSharedCheck_540_ == 0)
{
v___x_520_ = v_b_512_;
v_isShared_521_ = v_isSharedCheck_540_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_snd_518_);
lean_inc(v_fst_517_);
lean_dec(v_b_512_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_540_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; 
lean_inc(v_head_515_);
v___x_522_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_head_515_);
if (lean_obj_tag(v___x_522_) == 1)
{
lean_object* v_val_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec(v_fst_517_);
v_val_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = l_String_Slice_toString(v_val_523_);
lean_dec(v_val_523_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_524_);
v___x_526_ = v___x_520_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_snd_518_);
v___x_526_ = v_reuseFailAlloc_528_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v_as_x27_511_ = v_tail_516_;
v_b_512_ = v___x_526_;
goto _start;
}
}
else
{
lean_object* v___x_529_; 
lean_dec(v___x_522_);
lean_inc(v_head_515_);
v___x_529_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_head_515_);
if (lean_obj_tag(v___x_529_) == 1)
{
lean_object* v_val_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
lean_dec(v_snd_518_);
v_val_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_val_530_);
lean_dec_ref_known(v___x_529_, 1);
v___x_531_ = l_String_Slice_toString(v_val_530_);
lean_dec(v_val_530_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v___x_531_);
v___x_533_ = v___x_520_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_fst_517_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_535_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
v_as_x27_511_ = v_tail_516_;
v_b_512_ = v___x_533_;
goto _start;
}
}
else
{
lean_object* v___x_537_; 
lean_dec(v___x_529_);
if (v_isShared_521_ == 0)
{
v___x_537_ = v___x_520_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_fst_517_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_snd_518_);
v___x_537_ = v_reuseFailAlloc_539_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
v_as_x27_511_ = v_tail_516_;
v_b_512_ = v___x_537_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg___boxed(lean_object* v_as_x27_541_, lean_object* v_b_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_541_, v_b_542_);
lean_dec(v_as_x27_541_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(lean_object* v_s_545_){
_start:
{
lean_object* v___x_547_; lean_object* v_putStr_548_; lean_object* v___x_549_; 
v___x_547_ = lean_get_stdout();
v_putStr_548_ = lean_ctor_get(v___x_547_, 4);
lean_inc_ref(v_putStr_548_);
lean_dec_ref(v___x_547_);
v___x_549_ = lean_apply_2(v_putStr_548_, v_s_545_, lean_box(0));
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2___boxed(lean_object* v_s_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v_s_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(lean_object* v_s_553_){
_start:
{
uint32_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = 10;
v___x_556_ = lean_string_push(v_s_553_, v___x_555_);
v___x_557_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2___boxed(lean_object* v_s_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v_s_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(lean_object* v_a_605_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_611_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_610_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_projectDir_612_; lean_object* v_whichLake_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___y_617_; lean_object* v_whichLake_618_; uint8_t v___x_668_; 
lean_dec_ref_known(v___x_611_, 1);
v_projectDir_612_ = lean_ctor_get(v_a_605_, 0);
v_whichLake_613_ = lean_ctor_get(v_a_605_, 9);
v___x_614_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_612_);
v___x_615_ = l_System_FilePath_join(v_projectDir_612_, v___x_614_);
v___x_668_ = l_System_FilePath_pathExists(v___x_615_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
v___x_669_ = lean_io_create_dir(v___x_615_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_dec_ref_known(v___x_669_, 1);
v___y_617_ = v_a_605_;
v_whichLake_618_ = v_whichLake_613_;
goto v___jp_616_;
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v___x_615_);
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
else
{
v___y_617_ = v_a_605_;
v_whichLake_618_ = v_whichLake_613_;
goto v___jp_616_;
}
v___jp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_mk_empty_array_with_capacity(v___x_619_);
v___x_621_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__5));
v___x_622_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__9));
v___x_623_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
lean_inc_ref(v_projectDir_612_);
lean_inc_ref(v___x_620_);
v___x_624_ = lean_array_push(v___x_620_, v_projectDir_612_);
v___x_625_ = lean_array_push(v___x_620_, v___x_615_);
v___x_626_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__16));
lean_inc_ref(v_whichLake_618_);
v___x_627_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_627_, 0, v_whichLake_618_);
lean_ctor_set(v___x_627_, 1, v___x_621_);
lean_ctor_set(v___x_627_, 2, v___x_622_);
lean_ctor_set(v___x_627_, 3, v___x_623_);
lean_ctor_set(v___x_627_, 4, v___x_624_);
lean_ctor_set(v___x_627_, 5, v___x_625_);
lean_ctor_set(v___x_627_, 6, v___x_626_);
v___x_628_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v___x_627_, v___y_617_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_659_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc_n(v_a_629_, 2);
lean_dec_ref_known(v___x_628_, 1);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_string_utf8_byte_size(v_a_629_);
v___x_632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_632_, 0, v_a_629_);
lean_ctor_set(v___x_632_, 1, v___x_630_);
lean_ctor_set(v___x_632_, 2, v___x_631_);
v___x_633_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(v___x_632_);
v___x_634_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18));
v___x_635_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_629_, v___x_632_, v___x_631_, v___x_633_, v___x_634_);
lean_dec_ref_known(v___x_632_, 3);
v___x_636_ = lean_array_to_list(v___x_635_);
v___x_637_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__19));
v___x_638_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v___x_636_, v___x_637_);
lean_dec(v___x_636_);
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_659_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_659_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_659_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_fst_643_; lean_object* v_snd_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_658_; 
v_fst_643_ = lean_ctor_get(v_a_639_, 0);
v_snd_644_ = lean_ctor_get(v_a_639_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_a_639_);
if (v_isSharedCheck_658_ == 0)
{
v___x_646_ = v_a_639_;
v_isShared_647_ = v_isSharedCheck_658_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_snd_644_);
lean_inc(v_fst_643_);
lean_dec(v_a_639_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_658_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = lean_string_utf8_byte_size(v_fst_643_);
v___x_649_ = lean_nat_dec_eq(v___x_648_, v___x_630_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = lean_string_utf8_byte_size(v_snd_644_);
v___x_651_ = lean_nat_dec_eq(v___x_650_, v___x_630_);
if (v___x_651_ == 0)
{
lean_object* v___x_653_; 
if (v_isShared_647_ == 0)
{
v___x_653_ = v___x_646_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_fst_643_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_snd_644_);
v___x_653_ = v_reuseFailAlloc_657_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_655_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_653_);
v___x_655_ = v___x_641_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
else
{
lean_del_object(v___x_646_);
lean_dec(v_snd_644_);
lean_dec(v_fst_643_);
lean_del_object(v___x_641_);
goto v___jp_607_;
}
}
else
{
lean_del_object(v___x_646_);
lean_dec(v_snd_644_);
lean_dec(v_fst_643_);
lean_del_object(v___x_641_);
goto v___jp_607_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
v_a_660_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_628_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_628_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
v_a_678_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_611_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_611_);
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
v___jp_607_:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__1));
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___boxed(lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v_a_686_);
lean_dec_ref(v_a_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(lean_object* v_a_689_, lean_object* v___x_690_, lean_object* v___x_691_, lean_object* v_inst_692_, lean_object* v_R_693_, lean_object* v_a_694_, lean_object* v_b_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_689_, v___x_690_, v___x_691_, v_a_694_, v_b_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___boxed(lean_object* v_a_697_, lean_object* v___x_698_, lean_object* v___x_699_, lean_object* v_inst_700_, lean_object* v_R_701_, lean_object* v_a_702_, lean_object* v_b_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(v_a_697_, v___x_698_, v___x_699_, v_inst_700_, v_R_701_, v_a_702_, v_b_703_);
lean_dec_ref(v___x_698_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(lean_object* v_as_705_, lean_object* v_as_x27_706_, lean_object* v_b_707_, lean_object* v_a_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_706_, v_b_707_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___boxed(lean_object* v_as_712_, lean_object* v_as_x27_713_, lean_object* v_b_714_, lean_object* v_a_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(v_as_712_, v_as_x27_713_, v_b_714_, v_a_715_, v___y_716_);
lean_dec_ref(v___y_716_);
lean_dec(v_as_x27_713_);
lean_dec(v_as_712_);
return v_res_718_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__2(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_721_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1));
v___x_722_ = lean_unsigned_to_nat(2u);
v___x_723_ = lean_mk_empty_array_with_capacity(v___x_722_);
v___x_724_ = lean_array_push(v___x_723_, v___x_721_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(lean_object* v_target_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_732_; uint8_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_732_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
v___x_733_ = 1;
lean_inc(v_target_729_);
v___x_734_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_729_, v___x_733_);
v___x_735_ = lean_string_append(v___x_732_, v___x_734_);
lean_dec_ref(v___x_734_);
v___x_736_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_735_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_projectDir_737_; lean_object* v_whichLake_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___y_742_; lean_object* v_whichLake_743_; uint8_t v___x_756_; 
lean_dec_ref_known(v___x_736_, 1);
v_projectDir_737_ = lean_ctor_get(v_a_730_, 0);
v_whichLake_738_ = lean_ctor_get(v_a_730_, 9);
v___x_739_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_737_);
v___x_740_ = l_System_FilePath_join(v_projectDir_737_, v___x_739_);
v___x_756_ = l_System_FilePath_pathExists(v___x_740_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
v___x_757_ = lean_io_create_dir(v___x_740_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_dec_ref_known(v___x_757_, 1);
v___y_742_ = v_a_730_;
v_whichLake_743_ = v_whichLake_738_;
goto v___jp_741_;
}
else
{
lean_dec_ref(v___x_740_);
lean_dec(v_target_729_);
return v___x_757_;
}
}
else
{
v___y_742_ = v_a_730_;
v_whichLake_743_ = v_whichLake_738_;
goto v___jp_741_;
}
v___jp_741_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_744_ = l_Lean_Name_toString(v_target_729_, v___x_733_);
v___x_745_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__2);
v___x_746_ = lean_array_push(v___x_745_, v___x_744_);
v___x_747_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__9));
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_mk_empty_array_with_capacity(v___x_748_);
v___x_750_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3));
lean_inc_ref(v_projectDir_737_);
lean_inc_ref(v___x_749_);
v___x_751_ = lean_array_push(v___x_749_, v_projectDir_737_);
v___x_752_ = lean_array_push(v___x_749_, v___x_740_);
v___x_753_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18));
lean_inc_ref(v_whichLake_743_);
v___x_754_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_754_, 0, v_whichLake_743_);
lean_ctor_set(v___x_754_, 1, v___x_746_);
lean_ctor_set(v___x_754_, 2, v___x_747_);
lean_ctor_set(v___x_754_, 3, v___x_750_);
lean_ctor_set(v___x_754_, 4, v___x_751_);
lean_ctor_set(v___x_754_, 5, v___x_752_);
lean_ctor_set(v___x_754_, 6, v___x_753_);
v___x_755_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_754_, v___y_742_);
return v___x_755_;
}
}
else
{
lean_dec(v_target_729_);
return v___x_736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___boxed(lean_object* v_target_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v_target_758_, v_a_759_);
lean_dec_ref(v_a_759_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0_spec__0(lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
if (lean_obj_tag(v_x_764_) == 0)
{
return v_x_763_;
}
else
{
lean_object* v_head_765_; lean_object* v_tail_766_; lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_head_765_ = lean_ctor_get(v_x_764_, 0);
lean_inc(v_head_765_);
v_tail_766_ = lean_ctor_get(v_x_764_, 1);
lean_inc(v_tail_766_);
lean_dec_ref_known(v_x_764_, 2);
v___x_767_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0_spec__0___closed__0));
v___x_768_ = lean_string_append(v_x_763_, v___x_767_);
v___x_769_ = 1;
v___x_770_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_765_, v___x_769_);
v___x_771_ = lean_string_append(v___x_768_, v___x_770_);
lean_dec_ref(v___x_770_);
v_x_763_ = v___x_771_;
v_x_764_ = v_tail_766_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0(lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_776_) == 0)
{
lean_object* v___x_777_; 
v___x_777_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__0));
return v___x_777_;
}
else
{
lean_object* v_tail_778_; 
v_tail_778_ = lean_ctor_get(v_x_776_, 1);
if (lean_obj_tag(v_tail_778_) == 0)
{
lean_object* v_head_779_; lean_object* v___x_780_; uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_head_779_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_head_779_);
lean_dec_ref_known(v_x_776_, 2);
v___x_780_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__1));
v___x_781_ = 1;
v___x_782_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_779_, v___x_781_);
v___x_783_ = lean_string_append(v___x_780_, v___x_782_);
lean_dec_ref(v___x_782_);
v___x_784_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__2));
v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
return v___x_785_;
}
else
{
lean_object* v_head_786_; lean_object* v___x_787_; uint8_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint32_t v___x_792_; lean_object* v___x_793_; 
lean_inc(v_tail_778_);
v_head_786_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_head_786_);
lean_dec_ref_known(v_x_776_, 2);
v___x_787_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__1));
v___x_788_ = 1;
v___x_789_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_786_, v___x_788_);
v___x_790_ = lean_string_append(v___x_787_, v___x_789_);
lean_dec_ref(v___x_789_);
v___x_791_ = l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0_spec__0(v___x_790_, v_tail_778_);
v___x_792_ = 93;
v___x_793_ = lean_string_push(v___x_791_, v___x_792_);
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__1(lean_object* v_as_794_, size_t v_i_795_, size_t v_stop_796_, lean_object* v_b_797_){
_start:
{
uint8_t v___x_798_; 
v___x_798_ = lean_usize_dec_eq(v_i_795_, v_stop_796_);
if (v___x_798_ == 0)
{
uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; size_t v___x_803_; size_t v___x_804_; 
v___x_799_ = 1;
v___x_800_ = lean_array_uget_borrowed(v_as_794_, v_i_795_);
lean_inc(v___x_800_);
v___x_801_ = l_Lean_Name_toString(v___x_800_, v___x_799_);
v___x_802_ = lean_array_push(v_b_797_, v___x_801_);
v___x_803_ = ((size_t)1ULL);
v___x_804_ = lean_usize_add(v_i_795_, v___x_803_);
v_i_795_ = v___x_804_;
v_b_797_ = v___x_802_;
goto _start;
}
else
{
return v_b_797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__1___boxed(lean_object* v_as_806_, lean_object* v_i_807_, lean_object* v_stop_808_, lean_object* v_b_809_){
_start:
{
size_t v_i_boxed_810_; size_t v_stop_boxed_811_; lean_object* v_res_812_; 
v_i_boxed_810_ = lean_unbox_usize(v_i_807_);
lean_dec(v_i_807_);
v_stop_boxed_811_ = lean_unbox_usize(v_stop_808_);
lean_dec(v_stop_808_);
v_res_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__1(v_as_806_, v_i_boxed_810_, v_stop_boxed_811_, v_b_809_);
lean_dec_ref(v_as_806_);
return v_res_812_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__5(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_827_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_828_ = lean_unsigned_to_nat(3u);
v___x_829_ = lean_mk_empty_array_with_capacity(v___x_828_);
v___x_830_ = lean_array_push(v___x_829_, v___x_827_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport(lean_object* v_module_831_, lean_object* v_decls_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_835_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__0));
v___x_836_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__1));
lean_inc_ref(v_decls_832_);
v___x_837_ = lean_array_to_list(v_decls_832_);
v___x_838_ = l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0(v___x_837_);
v___x_839_ = lean_string_append(v___x_836_, v___x_838_);
lean_dec_ref(v___x_838_);
v___x_840_ = lean_string_append(v___x_835_, v___x_839_);
lean_dec_ref(v___x_839_);
v___x_841_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__2));
v___x_842_ = lean_string_append(v___x_840_, v___x_841_);
v___x_843_ = 1;
lean_inc(v_module_831_);
v___x_844_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_831_, v___x_843_);
v___x_845_ = lean_string_append(v___x_842_, v___x_844_);
lean_dec_ref(v___x_844_);
v___x_846_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_845_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v___y_848_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
lean_dec_ref_known(v___x_846_, 1);
v___x_872_ = l_Lean_Name_toString(v_module_831_, v___x_843_);
v___x_873_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs___closed__0));
v___x_874_ = lean_unsigned_to_nat(2u);
v___x_875_ = lean_mk_empty_array_with_capacity(v___x_874_);
v___x_876_ = lean_array_push(v___x_875_, v___x_872_);
v___x_877_ = lean_array_push(v___x_876_, v___x_873_);
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_array_get_size(v_decls_832_);
v___x_880_ = lean_nat_dec_lt(v___x_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_dec_ref(v_decls_832_);
v___y_848_ = v___x_877_;
goto v___jp_847_;
}
else
{
uint8_t v___x_881_; 
v___x_881_ = lean_nat_dec_le(v___x_879_, v___x_879_);
if (v___x_881_ == 0)
{
if (v___x_880_ == 0)
{
lean_dec_ref(v_decls_832_);
v___y_848_ = v___x_877_;
goto v___jp_847_;
}
else
{
size_t v___x_882_; size_t v___x_883_; lean_object* v___x_884_; 
v___x_882_ = ((size_t)0ULL);
v___x_883_ = lean_usize_of_nat(v___x_879_);
v___x_884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__1(v_decls_832_, v___x_882_, v___x_883_, v___x_877_);
lean_dec_ref(v_decls_832_);
v___y_848_ = v___x_884_;
goto v___jp_847_;
}
}
else
{
size_t v___x_885_; size_t v___x_886_; lean_object* v___x_887_; 
v___x_885_ = ((size_t)0ULL);
v___x_886_ = lean_usize_of_nat(v___x_879_);
v___x_887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__1(v_decls_832_, v___x_885_, v___x_886_, v___x_877_);
lean_dec_ref(v_decls_832_);
v___y_848_ = v___x_887_;
goto v___jp_847_;
}
}
v___jp_847_:
{
lean_object* v_projectDir_849_; lean_object* v_leanPath_850_; lean_object* v_binPath_851_; lean_object* v_whichLean4Export_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_projectDir_849_ = lean_ctor_get(v_a_833_, 0);
v_leanPath_850_ = lean_ctor_get(v_a_833_, 6);
v_binPath_851_ = lean_ctor_get(v_a_833_, 7);
v_whichLean4Export_852_ = lean_ctor_get(v_a_833_, 10);
v___x_853_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref_n(v_projectDir_849_, 2);
v___x_854_ = l_System_FilePath_join(v_projectDir_849_, v___x_853_);
v___x_855_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6));
v___x_856_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__3));
v___x_857_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__4));
lean_inc_ref(v_leanPath_850_);
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v_leanPath_850_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_856_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
lean_inc_ref(v_binPath_851_);
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v_binPath_851_);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_855_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__5, &l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__5_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_safeExport___closed__5);
v___x_863_ = lean_array_push(v___x_862_, v___x_859_);
v___x_864_ = lean_array_push(v___x_863_, v___x_861_);
v___x_865_ = lean_unsigned_to_nat(2u);
v___x_866_ = lean_mk_empty_array_with_capacity(v___x_865_);
v___x_867_ = lean_array_push(v___x_866_, v_projectDir_849_);
v___x_868_ = lean_array_push(v___x_867_, v___x_854_);
v___x_869_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18));
lean_inc_ref(v_whichLean4Export_852_);
v___x_870_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_870_, 0, v_whichLean4Export_852_);
lean_ctor_set(v___x_870_, 1, v___y_848_);
lean_ctor_set(v___x_870_, 2, v___x_857_);
lean_ctor_set(v___x_870_, 3, v___x_864_);
lean_ctor_set(v___x_870_, 4, v___x_868_);
lean_ctor_set(v___x_870_, 5, v___x_869_);
lean_ctor_set(v___x_870_, 6, v___x_869_);
v___x_871_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v___x_870_, v_a_833_);
return v___x_871_;
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v_decls_832_);
lean_dec(v_module_831_);
v_a_888_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_846_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_846_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeExport___boxed(lean_object* v_module_896_, lean_object* v_decls_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l___private_Lake_CLI_Check_0__Lake_Check_safeExport(v_module_896_, v_decls_897_, v_a_898_);
lean_dec_ref(v_a_898_);
return v_res_900_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(lean_object* v_s_901_, lean_object* v_a_902_, uint8_t v_b_903_){
_start:
{
uint8_t v___x_904_; 
v___x_904_ = 0;
switch(lean_obj_tag(v_a_902_))
{
case 0:
{
lean_object* v_pos_905_; lean_object* v_startInclusive_906_; lean_object* v_endExclusive_907_; lean_object* v___x_908_; uint8_t v_decide_909_; 
v_pos_905_ = lean_ctor_get(v_a_902_, 0);
lean_inc(v_pos_905_);
lean_dec_ref_known(v_a_902_, 1);
v_startInclusive_906_ = lean_ctor_get(v_s_901_, 1);
v_endExclusive_907_ = lean_ctor_get(v_s_901_, 2);
v___x_908_ = lean_nat_sub(v_endExclusive_907_, v_startInclusive_906_);
v_decide_909_ = lean_nat_dec_eq(v_pos_905_, v___x_908_);
lean_dec(v___x_908_);
lean_dec(v_pos_905_);
if (v_decide_909_ == 0)
{
uint8_t v___x_910_; 
v___x_910_ = 1;
return v___x_910_;
}
else
{
return v_decide_909_;
}
}
case 1:
{
lean_object* v_pos_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_924_; 
v_pos_911_ = lean_ctor_get(v_a_902_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v_a_902_);
if (v_isSharedCheck_924_ == 0)
{
v___x_913_ = v_a_902_;
v_isShared_914_ = v_isSharedCheck_924_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_pos_911_);
lean_dec(v_a_902_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_924_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_str_915_; lean_object* v_startInclusive_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v_str_915_ = lean_ctor_get(v_s_901_, 0);
v_startInclusive_916_ = lean_ctor_get(v_s_901_, 1);
v___x_917_ = lean_nat_add(v_startInclusive_916_, v_pos_911_);
lean_dec(v_pos_911_);
v___x_918_ = lean_string_utf8_next_fast(v_str_915_, v___x_917_);
lean_dec(v___x_917_);
v___x_919_ = lean_nat_sub(v___x_918_, v_startInclusive_916_);
if (v_isShared_914_ == 0)
{
lean_ctor_set_tag(v___x_913_, 0);
lean_ctor_set(v___x_913_, 0, v___x_919_);
v___x_921_ = v___x_913_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_923_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
v_a_902_ = v___x_921_;
v_b_903_ = v___x_904_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_925_; lean_object* v_table_926_; lean_object* v_stackPos_927_; lean_object* v_needlePos_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_983_; 
v_needle_925_ = lean_ctor_get(v_a_902_, 0);
v_table_926_ = lean_ctor_get(v_a_902_, 1);
v_stackPos_927_ = lean_ctor_get(v_a_902_, 2);
v_needlePos_928_ = lean_ctor_get(v_a_902_, 3);
v_isSharedCheck_983_ = !lean_is_exclusive(v_a_902_);
if (v_isSharedCheck_983_ == 0)
{
v___x_930_ = v_a_902_;
v_isShared_931_ = v_isSharedCheck_983_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_needlePos_928_);
lean_inc(v_stackPos_927_);
lean_inc(v_table_926_);
lean_inc(v_needle_925_);
lean_dec(v_a_902_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_983_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_str_932_; lean_object* v_startInclusive_933_; lean_object* v_endExclusive_934_; lean_object* v_str_935_; lean_object* v_startInclusive_936_; lean_object* v_endExclusive_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v_str_932_ = lean_ctor_get(v_needle_925_, 0);
v_startInclusive_933_ = lean_ctor_get(v_needle_925_, 1);
v_endExclusive_934_ = lean_ctor_get(v_needle_925_, 2);
v_str_935_ = lean_ctor_get(v_s_901_, 0);
v_startInclusive_936_ = lean_ctor_get(v_s_901_, 1);
v_endExclusive_937_ = lean_ctor_get(v_s_901_, 2);
v___x_938_ = lean_nat_sub(v_stackPos_927_, v_needlePos_928_);
v___x_939_ = lean_nat_sub(v_endExclusive_934_, v_startInclusive_933_);
v___x_940_ = lean_nat_add(v___x_938_, v___x_939_);
v___x_941_ = lean_nat_sub(v_endExclusive_937_, v_startInclusive_936_);
v___x_942_ = lean_nat_dec_le(v___x_940_, v___x_941_);
lean_dec(v___x_940_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
lean_dec(v___x_939_);
lean_del_object(v___x_930_);
lean_dec(v_needlePos_928_);
lean_dec(v_stackPos_927_);
lean_dec_ref(v_table_926_);
lean_dec_ref(v_needle_925_);
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_add(v___x_938_, v___x_943_);
lean_dec(v___x_938_);
v___x_945_ = lean_nat_dec_le(v___x_944_, v___x_941_);
lean_dec(v___x_941_);
lean_dec(v___x_944_);
if (v___x_945_ == 0)
{
return v_b_903_;
}
else
{
lean_object* v___x_946_; 
v___x_946_ = lean_box(3);
v_a_902_ = v___x_946_;
v_b_903_ = v___x_904_;
goto _start;
}
}
else
{
lean_object* v___x_948_; uint8_t v_stackByte_949_; lean_object* v___x_950_; uint8_t v_patByte_951_; uint8_t v___x_952_; 
lean_dec(v___x_941_);
lean_dec(v___x_938_);
v___x_948_ = lean_nat_add(v_startInclusive_936_, v_stackPos_927_);
v_stackByte_949_ = lean_string_get_byte_fast(v_str_935_, v___x_948_);
v___x_950_ = lean_nat_add(v_startInclusive_933_, v_needlePos_928_);
v_patByte_951_ = lean_string_get_byte_fast(v_str_932_, v___x_950_);
v___x_952_ = lean_uint8_dec_eq(v_stackByte_949_, v_patByte_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; uint8_t v_decide_954_; 
lean_dec(v___x_939_);
v___x_953_ = lean_unsigned_to_nat(0u);
v_decide_954_ = lean_nat_dec_eq(v_needlePos_928_, v___x_953_);
if (v_decide_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v_newNeedlePos_957_; uint8_t v___x_958_; 
v___x_955_ = lean_unsigned_to_nat(1u);
v___x_956_ = lean_nat_sub(v_needlePos_928_, v___x_955_);
lean_dec(v_needlePos_928_);
v_newNeedlePos_957_ = lean_array_fget_borrowed(v_table_926_, v___x_956_);
lean_dec(v___x_956_);
v___x_958_ = lean_nat_dec_eq(v_newNeedlePos_957_, v___x_953_);
if (v___x_958_ == 0)
{
lean_object* v___x_960_; 
lean_inc(v_newNeedlePos_957_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 3, v_newNeedlePos_957_);
v___x_960_ = v___x_930_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_needle_925_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_table_926_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_stackPos_927_);
lean_ctor_set(v_reuseFailAlloc_962_, 3, v_newNeedlePos_957_);
v___x_960_ = v_reuseFailAlloc_962_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
v_a_902_ = v___x_960_;
v_b_903_ = v___x_904_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_963_; lean_object* v___x_965_; 
v_nextStackPos_963_ = l_String_Slice_posGE___redArg(v_s_901_, v_stackPos_927_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 3, v___x_953_);
lean_ctor_set(v___x_930_, 2, v_nextStackPos_963_);
v___x_965_ = v___x_930_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_needle_925_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_table_926_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_nextStackPos_963_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v___x_953_);
v___x_965_ = v_reuseFailAlloc_967_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
v_a_902_ = v___x_965_;
v_b_903_ = v___x_904_;
goto _start;
}
}
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v_nextStackPos_970_; lean_object* v___x_972_; 
lean_dec(v_needlePos_928_);
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_nat_add(v_stackPos_927_, v___x_968_);
lean_dec(v_stackPos_927_);
v_nextStackPos_970_ = l_String_Slice_posGE___redArg(v_s_901_, v___x_969_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 3, v___x_953_);
lean_ctor_set(v___x_930_, 2, v_nextStackPos_970_);
v___x_972_ = v___x_930_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_needle_925_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_table_926_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_nextStackPos_970_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v___x_953_);
v___x_972_ = v_reuseFailAlloc_974_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
v_a_902_ = v___x_972_;
v_b_903_ = v___x_904_;
goto _start;
}
}
}
else
{
lean_object* v___x_975_; lean_object* v_nextNeedlePos_976_; uint8_t v_decide_977_; 
v___x_975_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_976_ = lean_nat_add(v_needlePos_928_, v___x_975_);
lean_dec(v_needlePos_928_);
v_decide_977_ = lean_nat_dec_eq(v_nextNeedlePos_976_, v___x_939_);
lean_dec(v___x_939_);
if (v_decide_977_ == 0)
{
lean_object* v_nextStackPos_978_; lean_object* v___x_980_; 
v_nextStackPos_978_ = lean_nat_add(v_stackPos_927_, v___x_975_);
lean_dec(v_stackPos_927_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 3, v_nextNeedlePos_976_);
lean_ctor_set(v___x_930_, 2, v_nextStackPos_978_);
v___x_980_ = v___x_930_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_needle_925_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_table_926_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_nextStackPos_978_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v_nextNeedlePos_976_);
v___x_980_ = v_reuseFailAlloc_982_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
v_a_902_ = v___x_980_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_976_);
lean_del_object(v___x_930_);
lean_dec(v_stackPos_927_);
lean_dec_ref(v_table_926_);
lean_dec_ref(v_needle_925_);
return v_decide_977_;
}
}
}
}
}
default: 
{
return v_b_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg___boxed(lean_object* v_s_984_, lean_object* v_a_985_, lean_object* v_b_986_){
_start:
{
uint8_t v_b_boxed_987_; uint8_t v_res_988_; lean_object* v_r_989_; 
v_b_boxed_987_ = lean_unbox(v_b_986_);
v_res_988_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_984_, v_a_985_, v_b_boxed_987_);
lean_dec_ref(v_s_984_);
v_r_989_ = lean_box(v_res_988_);
return v_r_989_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0));
v___x_992_ = lean_string_utf8_byte_size(v___x_991_);
return v___x_992_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1);
v___x_995_ = lean_nat_dec_eq(v___x_994_, v___x_993_);
return v___x_995_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_996_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1);
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0));
v___x_999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_997_);
lean_ctor_set(v___x_999_, 2, v___x_996_);
return v___x_999_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3);
v___x_1001_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4);
v___x_1004_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3);
v___x_1005_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_1003_);
lean_ctor_set(v___x_1005_, 2, v___x_1002_);
lean_ctor_set(v___x_1005_, 3, v___x_1002_);
return v___x_1005_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(lean_object* v_s_1008_){
_start:
{
lean_object* v___y_1010_; uint8_t v___x_1013_; 
v___x_1013_ = lean_uint8_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5);
v___y_1010_ = v___x_1014_;
goto v___jp_1009_;
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__6));
v___y_1010_ = v___x_1015_;
goto v___jp_1009_;
}
v___jp_1009_:
{
uint8_t v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = 0;
lean_inc(v___y_1010_);
v___x_1012_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_1008_, v___y_1010_, v___x_1011_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___boxed(lean_object* v_s_1016_){
_start:
{
uint8_t v_res_1017_; lean_object* v_r_1018_; 
v_res_1017_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v_s_1016_);
lean_dec_ref(v_s_1016_);
v_r_1018_ = lean_box(v_res_1017_);
return v_r_1018_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(lean_object* v_kernelName_1019_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = lean_string_utf8_byte_size(v_kernelName_1019_);
v___x_1022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1022_, 0, v_kernelName_1019_);
lean_ctor_set(v___x_1022_, 1, v___x_1020_);
lean_ctor_set(v___x_1022_, 2, v___x_1021_);
v___x_1023_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v___x_1022_);
lean_dec_ref_known(v___x_1022_, 3);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel___boxed(lean_object* v_kernelName_1024_){
_start:
{
uint8_t v_res_1025_; lean_object* v_r_1026_; 
v_res_1025_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_1024_);
v_r_1026_ = lean_box(v_res_1025_);
return v_r_1026_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(lean_object* v_s_1027_, lean_object* v_inst_1028_, lean_object* v_R_1029_, lean_object* v_a_1030_, uint8_t v_b_1031_, lean_object* v_c_1032_){
_start:
{
uint8_t v___x_1033_; 
v___x_1033_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_1027_, v_a_1030_, v_b_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___boxed(lean_object* v_s_1034_, lean_object* v_inst_1035_, lean_object* v_R_1036_, lean_object* v_a_1037_, lean_object* v_b_1038_, lean_object* v_c_1039_){
_start:
{
uint8_t v_b_boxed_1040_; uint8_t v_res_1041_; lean_object* v_r_1042_; 
v_b_boxed_1040_ = lean_unbox(v_b_1038_);
v_res_1041_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(v_s_1034_, v_inst_1035_, v_R_1036_, v_a_1037_, v_b_boxed_1040_, v_c_1039_);
lean_dec_ref(v_s_1034_);
v_r_1042_ = lean_box(v_res_1041_);
return v_r_1042_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg(lean_object* v_f_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v_fst_1048_; lean_object* v_snd_1049_; lean_object* v_r_1050_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v_fst_1048_ = lean_ctor_get(v_a_1047_, 0);
lean_inc(v_fst_1048_);
v_snd_1049_ = lean_ctor_get(v_a_1047_, 1);
lean_inc_n(v_snd_1049_, 2);
lean_dec(v_a_1047_);
lean_inc_ref(v___y_1044_);
v_r_1050_ = lean_apply_4(v_f_1043_, v_fst_1048_, v_snd_1049_, v___y_1044_, lean_box(0));
if (lean_obj_tag(v_r_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1052_; 
v_a_1051_ = lean_ctor_get(v_r_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v_r_1050_, 1);
v___x_1052_ = lean_io_remove_file(v_snd_1049_);
lean_dec(v_snd_1049_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v___x_1052_, 0);
lean_dec(v_unused_1060_);
v___x_1054_ = v___x_1052_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_dec(v___x_1052_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v_a_1051_);
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1051_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_a_1051_);
v_a_1061_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1052_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1052_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1070_; 
v_a_1069_ = lean_ctor_get(v_r_1050_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v_r_1050_, 1);
v___x_1070_ = lean_io_remove_file(v_snd_1049_);
lean_dec(v_snd_1049_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v___x_1070_, 0);
lean_dec(v_unused_1078_);
v___x_1072_ = v___x_1070_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_dec(v___x_1070_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 1);
lean_ctor_set(v___x_1072_, 0, v_a_1069_);
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1069_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec(v_a_1069_);
v_a_1079_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1070_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1070_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v_f_1043_);
v_a_1087_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1046_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1046_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg___boxed(lean_object* v_f_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg(v_f_1095_, v___y_1096_);
lean_dec_ref(v___y_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2(lean_object* v_00_u03b1_1099_, lean_object* v_f_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg(v_f_1100_, v___y_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___boxed(lean_object* v_00_u03b1_1104_, lean_object* v_f_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2(v_00_u03b1_1104_, v_f_1105_, v___y_1106_);
lean_dec_ref(v___y_1106_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(lean_object* v_a_1109_, lean_object* v_b_1110_){
_start:
{
lean_object* v_array_1111_; lean_object* v_start_1112_; lean_object* v_stop_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1126_; 
v_array_1111_ = lean_ctor_get(v_a_1109_, 0);
v_start_1112_ = lean_ctor_get(v_a_1109_, 1);
v_stop_1113_ = lean_ctor_get(v_a_1109_, 2);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_a_1109_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1115_ = v_a_1109_;
v_isShared_1116_ = v_isSharedCheck_1126_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_stop_1113_);
lean_inc(v_start_1112_);
lean_inc(v_array_1111_);
lean_dec(v_a_1109_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1126_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_nat_dec_lt(v_start_1112_, v_stop_1113_);
if (v___x_1117_ == 0)
{
lean_del_object(v___x_1115_);
lean_dec(v_stop_1113_);
lean_dec(v_start_1112_);
lean_dec_ref(v_array_1111_);
return v_b_1110_;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = lean_nat_add(v_start_1112_, v___x_1118_);
lean_inc_ref(v_array_1111_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 1, v___x_1119_);
v___x_1121_ = v___x_1115_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_array_1111_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v_stop_1113_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_array_fget(v_array_1111_, v_start_1112_);
lean_dec(v_start_1112_);
lean_dec_ref(v_array_1111_);
v___x_1123_ = lean_array_push(v_b_1110_, v___x_1122_);
v_a_1109_ = v___x_1121_;
v_b_1110_ = v___x_1123_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(size_t v_sz_1127_, size_t v_i_1128_, lean_object* v_bs_1129_){
_start:
{
uint8_t v___x_1130_; 
v___x_1130_ = lean_usize_dec_lt(v_i_1128_, v_sz_1127_);
if (v___x_1130_ == 0)
{
return v_bs_1129_;
}
else
{
lean_object* v_v_1131_; lean_object* v___x_1132_; lean_object* v_bs_x27_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
v_v_1131_ = lean_array_uget(v_bs_1129_, v_i_1128_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v_bs_x27_1133_ = lean_array_uset(v_bs_1129_, v_i_1128_, v___x_1132_);
v___x_1134_ = l_Lean_Name_toString(v_v_1131_, v___x_1130_);
v___x_1135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
v___x_1136_ = ((size_t)1ULL);
v___x_1137_ = lean_usize_add(v_i_1128_, v___x_1136_);
v___x_1138_ = lean_array_uset(v_bs_x27_1133_, v_i_1128_, v___x_1135_);
v_i_1128_ = v___x_1137_;
v_bs_1129_ = v___x_1138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0___boxed(lean_object* v_sz_1140_, lean_object* v_i_1141_, lean_object* v_bs_1142_){
_start:
{
size_t v_sz_boxed_1143_; size_t v_i_boxed_1144_; lean_object* v_res_1145_; 
v_sz_boxed_1143_ = lean_unbox_usize(v_sz_1140_);
lean_dec(v_sz_1140_);
v_i_boxed_1144_ = lean_unbox_usize(v_i_1141_);
lean_dec(v_i_1141_);
v_res_1145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_boxed_1143_, v_i_boxed_1144_, v_bs_1142_);
return v_res_1145_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(4u);
v___x_1165_ = l_Lean_JsonNumber_fromNat(v___x_1164_);
return v___x_1165_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12);
v___x_1167_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13);
v___x_1169_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v___x_1168_);
return v___x_1170_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__20));
v___x_1186_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14);
v___x_1187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___x_1185_);
return v___x_1187_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21);
v___x_1189_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10));
v___x_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v___x_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(lean_object* v_configHandle_1194_, lean_object* v_solutionExport_1195_, lean_object* v_kernelName_1196_, lean_object* v___x_1197_, lean_object* v_kernelCommand_1198_, lean_object* v_configPath_1199_, lean_object* v_solutionHandle_1200_, lean_object* v_solutionPath_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_a_1205_; lean_object* v_legalAxioms_1232_; uint8_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; size_t v_sz_1239_; size_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v_legalAxioms_1232_ = lean_ctor_get(v___y_1202_, 5);
v___x_1233_ = 0;
v___x_1234_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5));
v___x_1235_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6));
lean_inc_ref(v_solutionPath_1201_);
v___x_1236_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_solutionPath_1201_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7));
v_sz_1239_ = lean_array_size(v_legalAxioms_1232_);
v___x_1240_ = ((size_t)0ULL);
lean_inc_ref(v_legalAxioms_1232_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_1239_, v___x_1240_, v_legalAxioms_1232_);
v___x_1242_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1238_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = 1;
v___x_1245_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22);
v___x_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1243_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1237_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1234_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = l_Lean_Json_mkObj(v___x_1248_);
lean_dec_ref_known(v___x_1248_, 2);
v___x_1250_ = l_Lean_Json_compress(v___x_1249_);
v___x_1251_ = lean_io_prim_handle_put_str(v_configHandle_1194_, v___x_1250_);
lean_dec_ref(v___x_1250_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref_known(v___x_1251_, 1);
v___x_1252_ = lean_io_prim_handle_flush(v_configHandle_1194_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v___x_1253_; 
lean_dec_ref_known(v___x_1252_, 1);
v___x_1253_ = lean_io_prim_handle_put_str(v_solutionHandle_1200_, v_solutionExport_1195_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v___x_1254_; 
lean_dec_ref_known(v___x_1253_, 1);
v___x_1254_ = lean_io_prim_handle_flush(v_solutionHandle_1200_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_kernelArgs_1256_; lean_object* v___y_1257_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
lean_dec_ref_known(v___x_1254_, 1);
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = lean_array_get_size(v_kernelCommand_1198_);
lean_inc_ref(v_kernelCommand_1198_);
v___x_1321_ = l_Array_toSubarray___redArg(v_kernelCommand_1198_, v___x_1319_, v___x_1320_);
v___x_1322_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18));
v___x_1323_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v___x_1321_, v___x_1322_);
lean_inc_ref(v_kernelName_1196_);
v___x_1324_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_1196_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
lean_inc_ref(v_solutionPath_1201_);
v___x_1325_ = lean_array_push(v___x_1323_, v_solutionPath_1201_);
v_kernelArgs_1256_ = v___x_1325_;
v___y_1257_ = v___y_1202_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1326_; 
lean_inc_ref(v_configPath_1199_);
v___x_1326_ = lean_array_push(v___x_1323_, v_configPath_1199_);
v_kernelArgs_1256_ = v___x_1326_;
v___y_1257_ = v___y_1202_;
goto v___jp_1255_;
}
v___jp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v_projectDir_1266_; lean_object* v_whichLandrun_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_array_get(v___x_1197_, v_kernelCommand_1198_, v___x_1258_);
lean_dec_ref(v_kernelCommand_1198_);
v___x_1260_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18));
v___x_1261_ = lean_unsigned_to_nat(2u);
v___x_1262_ = lean_mk_empty_array_with_capacity(v___x_1261_);
v___x_1263_ = lean_array_push(v___x_1262_, v_configPath_1199_);
v___x_1264_ = lean_array_push(v___x_1263_, v_solutionPath_1201_);
v___x_1265_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1259_);
lean_ctor_set(v___x_1265_, 1, v_kernelArgs_1256_);
lean_ctor_set(v___x_1265_, 2, v___x_1260_);
lean_ctor_set(v___x_1265_, 3, v___x_1260_);
lean_ctor_set(v___x_1265_, 4, v___x_1264_);
lean_ctor_set(v___x_1265_, 5, v___x_1260_);
lean_ctor_set(v___x_1265_, 6, v___x_1260_);
v_projectDir_1266_ = lean_ctor_get(v___y_1257_, 0);
v_whichLandrun_1267_ = lean_ctor_get(v___y_1257_, 8);
v___x_1268_ = l___private_Lake_CLI_Check_0__Lake_Check_buildLandrunArgs(v___x_1265_);
v___x_1269_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
lean_inc_ref(v_projectDir_1266_);
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_projectDir_1266_);
lean_inc_ref(v_whichLandrun_1267_);
v___x_1271_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set(v___x_1271_, 1, v_whichLandrun_1267_);
lean_ctor_set(v___x_1271_, 2, v___x_1268_);
lean_ctor_set(v___x_1271_, 3, v___x_1270_);
lean_ctor_set(v___x_1271_, 4, v___x_1260_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*5, v___x_1244_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*5 + 1, v___x_1233_);
v___x_1272_ = lean_io_process_spawn(v___x_1271_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = lean_io_process_child_wait(v___x_1269_, v_a_1273_);
lean_dec(v_a_1273_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1316_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1316_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1316_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
uint32_t v___x_1279_; uint32_t v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = 0;
v___x_1280_ = lean_unbox_uint32(v_a_1275_);
v___x_1281_ = lean_uint32_dec_eq(v___x_1280_, v___x_1279_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23));
lean_inc_ref(v_kernelName_1196_);
v___x_1283_ = lean_string_append(v_kernelName_1196_, v___x_1282_);
v___x_1284_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1283_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1300_; 
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v___x_1284_, 0);
lean_dec(v_unused_1301_);
v___x_1286_ = v___x_1284_;
v_isShared_1287_ = v_isSharedCheck_1300_;
goto v_resetjp_1285_;
}
else
{
lean_dec(v___x_1284_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1300_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; uint32_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1288_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24));
v___x_1289_ = lean_string_append(v_kernelName_1196_, v___x_1288_);
v___x_1290_ = lean_unbox_uint32(v_a_1275_);
lean_dec(v_a_1275_);
v___x_1291_ = lean_uint32_to_nat(v___x_1290_);
v___x_1292_ = l_Nat_reprFast(v___x_1291_);
v___x_1293_ = lean_string_append(v___x_1289_, v___x_1292_);
lean_dec_ref(v___x_1292_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 1);
lean_ctor_set(v___x_1277_, 0, v___x_1293_);
v___x_1295_ = v___x_1277_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1297_; 
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1295_);
v___x_1297_ = v___x_1286_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
else
{
lean_object* v_a_1302_; 
lean_del_object(v___x_1277_);
lean_dec(v_a_1275_);
v_a_1302_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1284_, 1);
v_a_1205_ = v_a_1302_;
goto v___jp_1204_;
}
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_del_object(v___x_1277_);
lean_dec(v_a_1275_);
v___x_1303_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25));
lean_inc_ref(v_kernelName_1196_);
v___x_1304_ = lean_string_append(v_kernelName_1196_, v___x_1303_);
v___x_1305_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1304_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v_kernelName_1196_);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; 
v_unused_1314_ = lean_ctor_get(v___x_1305_, 0);
lean_dec(v_unused_1314_);
v___x_1307_ = v___x_1305_;
v_isShared_1308_ = v_isSharedCheck_1313_;
goto v_resetjp_1306_;
}
else
{
lean_dec(v___x_1305_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1313_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1309_ = lean_box(0);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1309_);
v___x_1311_ = v___x_1307_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
else
{
lean_object* v_a_1315_; 
v_a_1315_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1305_, 1);
v_a_1205_ = v_a_1315_;
goto v___jp_1204_;
}
}
}
}
else
{
lean_object* v_a_1317_; 
v_a_1317_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1274_, 1);
v_a_1205_ = v_a_1317_;
goto v___jp_1204_;
}
}
else
{
lean_object* v_a_1318_; 
v_a_1318_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1272_, 1);
v_a_1205_ = v_a_1318_;
goto v___jp_1204_;
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_solutionPath_1201_);
lean_dec_ref(v_configPath_1199_);
lean_dec_ref(v_kernelCommand_1198_);
lean_dec_ref(v_kernelName_1196_);
v_a_1327_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1254_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1254_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref(v_solutionPath_1201_);
lean_dec_ref(v_configPath_1199_);
lean_dec_ref(v_kernelCommand_1198_);
lean_dec_ref(v_kernelName_1196_);
v_a_1335_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1253_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1253_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v_solutionPath_1201_);
lean_dec_ref(v_configPath_1199_);
lean_dec_ref(v_kernelCommand_1198_);
lean_dec_ref(v_kernelName_1196_);
v_a_1343_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1252_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1252_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_solutionPath_1201_);
lean_dec_ref(v_configPath_1199_);
lean_dec_ref(v_kernelCommand_1198_);
lean_dec_ref(v_kernelName_1196_);
v_a_1351_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1251_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1251_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
v___jp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1206_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__0));
v___x_1207_ = lean_string_append(v___x_1206_, v_kernelName_1196_);
lean_dec_ref(v_kernelName_1196_);
v___x_1208_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__1));
lean_inc_ref(v___x_1207_);
v___x_1209_ = lean_string_append(v___x_1207_, v___x_1208_);
v___x_1210_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1209_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1222_; 
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v___x_1210_, 0);
lean_dec(v_unused_1223_);
v___x_1212_ = v___x_1210_;
v_isShared_1213_ = v_isSharedCheck_1222_;
goto v_resetjp_1211_;
}
else
{
lean_dec(v___x_1210_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1222_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1214_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__2));
v___x_1215_ = lean_string_append(v___x_1207_, v___x_1214_);
v___x_1216_ = lean_io_error_to_string(v_a_1205_);
v___x_1217_ = lean_string_append(v___x_1215_, v___x_1216_);
lean_dec_ref(v___x_1216_);
v___x_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1218_);
v___x_1220_ = v___x_1212_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec_ref(v___x_1207_);
lean_dec(v_a_1205_);
v_a_1224_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1210_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1210_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed(lean_object* v_configHandle_1359_, lean_object* v_solutionExport_1360_, lean_object* v_kernelName_1361_, lean_object* v___x_1362_, lean_object* v_kernelCommand_1363_, lean_object* v_configPath_1364_, lean_object* v_solutionHandle_1365_, lean_object* v_solutionPath_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(v_configHandle_1359_, v_solutionExport_1360_, v_kernelName_1361_, v___x_1362_, v_kernelCommand_1363_, v_configPath_1364_, v_solutionHandle_1365_, v_solutionPath_1366_, v___y_1367_);
lean_dec_ref(v___y_1367_);
lean_dec(v_solutionHandle_1365_);
lean_dec_ref(v___x_1362_);
lean_dec_ref(v_solutionExport_1360_);
lean_dec(v_configHandle_1359_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__1(lean_object* v_solutionExport_1370_, lean_object* v_kernelName_1371_, lean_object* v___x_1372_, lean_object* v_kernelCommand_1373_, lean_object* v_configHandle_1374_, lean_object* v_configPath_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___f_1378_; lean_object* v___x_1379_; 
v___f_1378_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed), 10, 6);
lean_closure_set(v___f_1378_, 0, v_configHandle_1374_);
lean_closure_set(v___f_1378_, 1, v_solutionExport_1370_);
lean_closure_set(v___f_1378_, 2, v_kernelName_1371_);
lean_closure_set(v___f_1378_, 3, v___x_1372_);
lean_closure_set(v___f_1378_, 4, v_kernelCommand_1373_);
lean_closure_set(v___f_1378_, 5, v_configPath_1375_);
v___x_1379_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg(v___f_1378_, v___y_1376_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__1___boxed(lean_object* v_solutionExport_1380_, lean_object* v_kernelName_1381_, lean_object* v___x_1382_, lean_object* v_kernelCommand_1383_, lean_object* v_configHandle_1384_, lean_object* v_configPath_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__1(v_solutionExport_1380_, v_kernelName_1381_, v___x_1382_, v_kernelCommand_1383_, v_configHandle_1384_, v_configPath_1385_, v___y_1386_);
lean_dec_ref(v___y_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(lean_object* v_kernelName_1391_, lean_object* v_kernelCommand_1392_, lean_object* v_solutionExport_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1396_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0));
v___x_1397_ = lean_string_append(v___x_1396_, v_kernelName_1391_);
v___x_1398_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1));
v___x_1399_ = lean_string_append(v___x_1397_, v___x_1398_);
v___x_1400_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1399_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v___x_1401_; lean_object* v___f_1402_; lean_object* v___x_1403_; 
lean_dec_ref_known(v___x_1400_, 1);
v___x_1401_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__17));
v___f_1402_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1402_, 0, v_solutionExport_1393_);
lean_closure_set(v___f_1402_, 1, v_kernelName_1391_);
lean_closure_set(v___f_1402_, 2, v___x_1401_);
lean_closure_set(v___f_1402_, 3, v_kernelCommand_1392_);
v___x_1403_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__2___redArg(v___f_1402_, v_a_1394_);
return v___x_1403_;
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec_ref(v_solutionExport_1393_);
lean_dec_ref(v_kernelCommand_1392_);
lean_dec_ref(v_kernelName_1391_);
v_a_1404_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1400_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1400_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___boxed(lean_object* v_kernelName_1412_, lean_object* v_kernelCommand_1413_, lean_object* v_solutionExport_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_kernelName_1412_, v_kernelCommand_1413_, v_solutionExport_1414_, v_a_1415_);
lean_dec_ref(v_a_1415_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1(lean_object* v_inst_1418_, lean_object* v_R_1419_, lean_object* v_a_1420_, lean_object* v_b_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v_a_1420_, v_b_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__0___redArg(lean_object* v_a_1423_, lean_object* v_x_1424_){
_start:
{
if (lean_obj_tag(v_x_1424_) == 0)
{
uint8_t v___x_1425_; 
v___x_1425_ = 0;
return v___x_1425_;
}
else
{
lean_object* v_key_1426_; lean_object* v_tail_1427_; uint8_t v___x_1428_; 
v_key_1426_ = lean_ctor_get(v_x_1424_, 0);
v_tail_1427_ = lean_ctor_get(v_x_1424_, 2);
v___x_1428_ = lean_name_eq(v_key_1426_, v_a_1423_);
if (v___x_1428_ == 0)
{
v_x_1424_ = v_tail_1427_;
goto _start;
}
else
{
return v___x_1428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__0___redArg___boxed(lean_object* v_a_1430_, lean_object* v_x_1431_){
_start:
{
uint8_t v_res_1432_; lean_object* v_r_1433_; 
v_res_1432_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__0___redArg(v_a_1430_, v_x_1431_);
lean_dec(v_x_1431_);
lean_dec(v_a_1430_);
v_r_1433_ = lean_box(v_res_1432_);
return v_r_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__1___redArg(lean_object* v_a_1434_, lean_object* v_x_1435_){
_start:
{
if (lean_obj_tag(v_x_1435_) == 0)
{
return v_x_1435_;
}
else
{
lean_object* v_key_1436_; lean_object* v_value_1437_; lean_object* v_tail_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1447_; 
v_key_1436_ = lean_ctor_get(v_x_1435_, 0);
v_value_1437_ = lean_ctor_get(v_x_1435_, 1);
v_tail_1438_ = lean_ctor_get(v_x_1435_, 2);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_x_1435_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1440_ = v_x_1435_;
v_isShared_1441_ = v_isSharedCheck_1447_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_tail_1438_);
lean_inc(v_value_1437_);
lean_inc(v_key_1436_);
lean_dec(v_x_1435_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1447_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
uint8_t v___x_1442_; 
v___x_1442_ = lean_name_eq(v_key_1436_, v_a_1434_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__1___redArg(v_a_1434_, v_tail_1438_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 2, v___x_1443_);
v___x_1445_ = v___x_1440_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_key_1436_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_value_1437_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
else
{
lean_del_object(v___x_1440_);
lean_dec(v_value_1437_);
lean_dec(v_key_1436_);
return v_tail_1438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__1___redArg___boxed(lean_object* v_a_1448_, lean_object* v_x_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__1___redArg(v_a_1448_, v_x_1449_);
lean_dec(v_a_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0___redArg(lean_object* v_m_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v_size_1453_; lean_object* v_buckets_1454_; lean_object* v___x_1455_; uint64_t v___y_1457_; 
v_size_1453_ = lean_ctor_get(v_m_1451_, 0);
v_buckets_1454_ = lean_ctor_get(v_m_1451_, 1);
v___x_1455_ = lean_array_get_size(v_buckets_1454_);
if (lean_obj_tag(v_a_1452_) == 0)
{
uint64_t v___x_1486_; 
v___x_1486_ = 1723ULL;
v___y_1457_ = v___x_1486_;
goto v___jp_1456_;
}
else
{
uint64_t v_hash_1487_; 
v_hash_1487_ = lean_ctor_get_uint64(v_a_1452_, sizeof(void*)*2);
v___y_1457_ = v_hash_1487_;
goto v___jp_1456_;
}
v___jp_1456_:
{
uint64_t v___x_1458_; uint64_t v___x_1459_; uint64_t v_fold_1460_; uint64_t v___x_1461_; uint64_t v___x_1462_; uint64_t v___x_1463_; size_t v___x_1464_; size_t v___x_1465_; size_t v___x_1466_; size_t v___x_1467_; size_t v___x_1468_; lean_object* v_bkt_1469_; uint8_t v___x_1470_; 
v___x_1458_ = 32ULL;
v___x_1459_ = lean_uint64_shift_right(v___y_1457_, v___x_1458_);
v_fold_1460_ = lean_uint64_xor(v___y_1457_, v___x_1459_);
v___x_1461_ = 16ULL;
v___x_1462_ = lean_uint64_shift_right(v_fold_1460_, v___x_1461_);
v___x_1463_ = lean_uint64_xor(v_fold_1460_, v___x_1462_);
v___x_1464_ = lean_uint64_to_usize(v___x_1463_);
v___x_1465_ = lean_usize_of_nat(v___x_1455_);
v___x_1466_ = ((size_t)1ULL);
v___x_1467_ = lean_usize_sub(v___x_1465_, v___x_1466_);
v___x_1468_ = lean_usize_land(v___x_1464_, v___x_1467_);
v_bkt_1469_ = lean_array_uget_borrowed(v_buckets_1454_, v___x_1468_);
v___x_1470_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__0___redArg(v_a_1452_, v_bkt_1469_);
if (v___x_1470_ == 0)
{
return v_m_1451_;
}
else
{
lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1483_; 
lean_inc(v_bkt_1469_);
lean_inc_ref(v_buckets_1454_);
lean_inc(v_size_1453_);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_m_1451_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; lean_object* v_unused_1485_; 
v_unused_1484_ = lean_ctor_get(v_m_1451_, 1);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_m_1451_, 0);
lean_dec(v_unused_1485_);
v___x_1472_ = v_m_1451_;
v_isShared_1473_ = v_isSharedCheck_1483_;
goto v_resetjp_1471_;
}
else
{
lean_dec(v_m_1451_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1483_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v_buckets_x27_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1474_ = lean_box(0);
v_buckets_x27_1475_ = lean_array_uset(v_buckets_1454_, v___x_1468_, v___x_1474_);
v___x_1476_ = lean_unsigned_to_nat(1u);
v___x_1477_ = lean_nat_sub(v_size_1453_, v___x_1476_);
lean_dec(v_size_1453_);
v___x_1478_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__1___redArg(v_a_1452_, v_bkt_1469_);
v___x_1479_ = lean_array_uset(v_buckets_x27_1475_, v___x_1468_, v___x_1478_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v___x_1479_);
lean_ctor_set(v___x_1472_, 0, v___x_1477_);
v___x_1481_ = v___x_1472_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0___redArg___boxed(lean_object* v_m_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0___redArg(v_m_1488_, v_a_1489_);
lean_dec(v_a_1489_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__1(lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
if (lean_obj_tag(v_x_1492_) == 0)
{
return v_x_1491_;
}
else
{
lean_object* v_head_1493_; lean_object* v_tail_1494_; lean_object* v___x_1495_; 
v_head_1493_ = lean_ctor_get(v_x_1492_, 0);
v_tail_1494_ = lean_ctor_get(v_x_1492_, 1);
v___x_1495_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0___redArg(v_x_1491_, v_head_1493_);
v_x_1491_ = v___x_1495_;
v_x_1492_ = v_tail_1494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__1___boxed(lean_object* v_x_1497_, lean_object* v_x_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_List_foldl___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__1(v_x_1497_, v_x_1498_);
lean_dec(v_x_1498_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2_spec__4___redArg(lean_object* v_a_1500_, lean_object* v_x_1501_){
_start:
{
if (lean_obj_tag(v_x_1501_) == 0)
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_box(0);
return v___x_1502_;
}
else
{
lean_object* v_key_1503_; lean_object* v_value_1504_; lean_object* v_tail_1505_; uint8_t v___x_1506_; 
v_key_1503_ = lean_ctor_get(v_x_1501_, 0);
v_value_1504_ = lean_ctor_get(v_x_1501_, 1);
v_tail_1505_ = lean_ctor_get(v_x_1501_, 2);
v___x_1506_ = lean_name_eq(v_key_1503_, v_a_1500_);
if (v___x_1506_ == 0)
{
v_x_1501_ = v_tail_1505_;
goto _start;
}
else
{
lean_object* v___x_1508_; 
lean_inc(v_value_1504_);
v___x_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_value_1504_);
return v___x_1508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2_spec__4___redArg___boxed(lean_object* v_a_1509_, lean_object* v_x_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2_spec__4___redArg(v_a_1509_, v_x_1510_);
lean_dec(v_x_1510_);
lean_dec(v_a_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2___redArg(lean_object* v_m_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v_buckets_1514_; lean_object* v___x_1515_; uint64_t v___y_1517_; 
v_buckets_1514_ = lean_ctor_get(v_m_1512_, 1);
v___x_1515_ = lean_array_get_size(v_buckets_1514_);
if (lean_obj_tag(v_a_1513_) == 0)
{
uint64_t v___x_1531_; 
v___x_1531_ = 1723ULL;
v___y_1517_ = v___x_1531_;
goto v___jp_1516_;
}
else
{
uint64_t v_hash_1532_; 
v_hash_1532_ = lean_ctor_get_uint64(v_a_1513_, sizeof(void*)*2);
v___y_1517_ = v_hash_1532_;
goto v___jp_1516_;
}
v___jp_1516_:
{
uint64_t v___x_1518_; uint64_t v___x_1519_; uint64_t v_fold_1520_; uint64_t v___x_1521_; uint64_t v___x_1522_; uint64_t v___x_1523_; size_t v___x_1524_; size_t v___x_1525_; size_t v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1518_ = 32ULL;
v___x_1519_ = lean_uint64_shift_right(v___y_1517_, v___x_1518_);
v_fold_1520_ = lean_uint64_xor(v___y_1517_, v___x_1519_);
v___x_1521_ = 16ULL;
v___x_1522_ = lean_uint64_shift_right(v_fold_1520_, v___x_1521_);
v___x_1523_ = lean_uint64_xor(v_fold_1520_, v___x_1522_);
v___x_1524_ = lean_uint64_to_usize(v___x_1523_);
v___x_1525_ = lean_usize_of_nat(v___x_1515_);
v___x_1526_ = ((size_t)1ULL);
v___x_1527_ = lean_usize_sub(v___x_1525_, v___x_1526_);
v___x_1528_ = lean_usize_land(v___x_1524_, v___x_1527_);
v___x_1529_ = lean_array_uget_borrowed(v_buckets_1514_, v___x_1528_);
v___x_1530_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2_spec__4___redArg(v_a_1513_, v___x_1529_);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2___redArg___boxed(lean_object* v_m_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2___redArg(v_m_1533_, v_a_1534_);
lean_dec(v_a_1534_);
lean_dec_ref(v_m_1533_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg(lean_object* v___x_1538_, lean_object* v_a_1539_, lean_object* v_as_x27_1540_, lean_object* v_b_1541_){
_start:
{
if (lean_obj_tag(v_as_x27_1540_) == 0)
{
lean_object* v___x_1543_; 
lean_dec_ref(v_a_1539_);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_b_1541_);
return v___x_1543_;
}
else
{
lean_object* v_head_1544_; lean_object* v_tail_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_head_1544_ = lean_ctor_get(v_as_x27_1540_, 0);
v_tail_1545_ = lean_ctor_get(v_as_x27_1540_, 1);
v___x_1546_ = lean_box(0);
v___x_1547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2___redArg(v___x_1538_, v_head_1544_);
if (lean_obj_tag(v___x_1547_) == 1)
{
lean_object* v_val_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1578_; 
v_val_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1578_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_val_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1578_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; 
lean_inc(v_head_1544_);
lean_inc_ref(v_a_1539_);
v___x_1552_ = lean_environment_find(v_a_1539_, v_head_1544_);
if (lean_obj_tag(v___x_1552_) == 1)
{
lean_object* v_val_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1569_; 
v_val_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1569_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_val_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1569_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
uint8_t v___x_1557_; 
v___x_1557_ = l_Lake_Check_Compare_instBEqConstantInfo__lake_beq(v_val_1548_, v_val_1553_);
lean_dec(v_val_1553_);
lean_dec(v_val_1548_);
if (v___x_1557_ == 0)
{
uint8_t v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
lean_dec_ref(v_a_1539_);
v___x_1558_ = 1;
v___x_1559_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg___closed__0));
lean_inc(v_head_1544_);
v___x_1560_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1544_, v___x_1558_);
v___x_1561_ = lean_string_append(v___x_1559_, v___x_1560_);
lean_dec_ref(v___x_1560_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 18);
lean_ctor_set(v___x_1555_, 0, v___x_1561_);
v___x_1563_ = v___x_1555_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1565_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1563_);
v___x_1565_ = v___x_1550_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
else
{
lean_del_object(v___x_1555_);
lean_del_object(v___x_1550_);
v_as_x27_1540_ = v_tail_1545_;
v_b_1541_ = v___x_1546_;
goto _start;
}
}
}
else
{
lean_object* v___x_1570_; uint8_t v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
lean_dec(v___x_1552_);
lean_dec(v_val_1548_);
lean_dec_ref(v_a_1539_);
v___x_1570_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg___closed__1));
v___x_1571_ = 1;
lean_inc(v_head_1544_);
v___x_1572_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1544_, v___x_1571_);
v___x_1573_ = lean_string_append(v___x_1570_, v___x_1572_);
lean_dec_ref(v___x_1572_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set_tag(v___x_1550_, 18);
lean_ctor_set(v___x_1550_, 0, v___x_1573_);
v___x_1575_ = v___x_1550_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
}
}
}
else
{
lean_dec(v___x_1547_);
v_as_x27_1540_ = v_tail_1545_;
v_b_1541_ = v___x_1546_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg___boxed(lean_object* v___x_1580_, lean_object* v_a_1581_, lean_object* v_as_x27_1582_, lean_object* v_b_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg(v___x_1580_, v_a_1581_, v_as_x27_1582_, v_b_1583_);
lean_dec(v_as_x27_1582_);
lean_dec_ref(v___x_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(lean_object* v_solution_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_a_1621_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_1643_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1642_);
if (lean_obj_tag(v___x_1643_) == 0)
{
uint32_t v___x_1644_; lean_object* v___x_1645_; 
lean_dec_ref_known(v___x_1643_, 1);
v___x_1644_ = 0;
v___x_1645_ = l_Lean_mkEmptyEnvironment(v___x_1644_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v_constMap_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v_constMap_1647_ = lean_ctor_get(v_solution_1617_, 0);
lean_inc_ref_n(v_constMap_1647_, 2);
lean_dec_ref(v_solution_1617_);
v___x_1648_ = lean_elab_environment_to_kernel_env(v_a_1646_);
v___x_1649_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__11));
v___x_1650_ = l_List_foldl___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__1(v_constMap_1647_, v___x_1649_);
v___x_1651_ = l_Lean_Kernel_Environment_replay(v___x_1650_, v___x_1648_);
lean_dec_ref(v___x_1650_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1653_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__12));
v___x_1654_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1653_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1693_; 
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; 
v_unused_1694_ = lean_ctor_get(v___x_1654_, 0);
lean_dec(v_unused_1694_);
v___x_1656_ = v___x_1654_;
v_isShared_1657_ = v_isSharedCheck_1693_;
goto v_resetjp_1655_;
}
else
{
lean_dec(v___x_1654_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1693_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__14));
v___x_1659_ = lean_box(0);
v___x_1660_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg(v_constMap_1647_, v_a_1652_, v___x_1658_, v___x_1659_);
lean_dec_ref(v_constMap_1647_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1668_; 
lean_del_object(v___x_1656_);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; 
v_unused_1669_ = lean_ctor_get(v___x_1660_, 0);
lean_dec(v_unused_1669_);
v___x_1662_ = v___x_1660_;
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
else
{
lean_dec(v___x_1660_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1668_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1664_ = lean_box(0);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1664_);
v___x_1666_ = v___x_1662_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_a_1670_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1660_, 1);
v___x_1671_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__15));
v___x_1672_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1671_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1683_; 
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1683_ == 0)
{
lean_object* v_unused_1684_; 
v_unused_1684_ = lean_ctor_get(v___x_1672_, 0);
lean_dec(v_unused_1684_);
v___x_1674_ = v___x_1672_;
v_isShared_1675_ = v_isSharedCheck_1683_;
goto v_resetjp_1673_;
}
else
{
lean_dec(v___x_1672_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1683_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = lean_io_error_to_string(v_a_1670_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set_tag(v___x_1656_, 1);
lean_ctor_set(v___x_1656_, 0, v___x_1676_);
v___x_1678_ = v___x_1656_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1678_);
v___x_1680_ = v___x_1674_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_a_1670_);
lean_del_object(v___x_1656_);
v_a_1685_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1672_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1672_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
}
else
{
lean_object* v_a_1695_; 
lean_dec(v_a_1652_);
lean_dec_ref(v_constMap_1647_);
v_a_1695_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1654_, 1);
v_a_1621_ = v_a_1695_;
goto v___jp_1620_;
}
}
else
{
lean_object* v_a_1696_; 
lean_dec_ref(v_constMap_1647_);
v_a_1696_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1651_, 1);
v_a_1621_ = v_a_1696_;
goto v___jp_1620_;
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v_solution_1617_);
v_a_1697_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1645_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1645_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec_ref(v_solution_1617_);
v_a_1705_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1643_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1643_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
v___jp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0));
v___x_1623_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1622_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1632_; 
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; 
v_unused_1633_ = lean_ctor_get(v___x_1623_, 0);
lean_dec(v_unused_1633_);
v___x_1625_ = v___x_1623_;
v_isShared_1626_ = v_isSharedCheck_1632_;
goto v_resetjp_1624_;
}
else
{
lean_dec(v___x_1623_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1632_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1627_ = lean_io_error_to_string(v_a_1621_);
v___x_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1628_);
v___x_1630_ = v___x_1625_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec(v_a_1621_);
v_a_1634_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1623_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1623_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___boxed(lean_object* v_solution_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_solution_1713_, v_a_1714_);
lean_dec_ref(v_a_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0(lean_object* v_00_u03b2_1717_, lean_object* v_m_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0___redArg(v_m_1718_, v_a_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0___boxed(lean_object* v_00_u03b2_1721_, lean_object* v_m_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0(v_00_u03b2_1721_, v_m_1722_, v_a_1723_);
lean_dec(v_a_1723_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2(lean_object* v_00_u03b2_1725_, lean_object* v_m_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2___redArg(v_m_1726_, v_a_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2___boxed(lean_object* v_00_u03b2_1729_, lean_object* v_m_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2(v_00_u03b2_1729_, v_m_1730_, v_a_1731_);
lean_dec(v_a_1731_);
lean_dec_ref(v_m_1730_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3(lean_object* v___x_1733_, lean_object* v_a_1734_, lean_object* v_as_1735_, lean_object* v_as_x27_1736_, lean_object* v_b_1737_, lean_object* v_a_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___redArg(v___x_1733_, v_a_1734_, v_as_x27_1736_, v_b_1737_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3___boxed(lean_object* v___x_1742_, lean_object* v_a_1743_, lean_object* v_as_1744_, lean_object* v_as_x27_1745_, lean_object* v_b_1746_, lean_object* v_a_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__3(v___x_1742_, v_a_1743_, v_as_1744_, v_as_x27_1745_, v_b_1746_, v_a_1747_, v___y_1748_);
lean_dec_ref(v___y_1748_);
lean_dec(v_as_x27_1745_);
lean_dec(v_as_1744_);
lean_dec_ref(v___x_1742_);
return v_res_1750_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__0(lean_object* v_00_u03b2_1751_, lean_object* v_a_1752_, lean_object* v_x_1753_){
_start:
{
uint8_t v___x_1754_; 
v___x_1754_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__0___redArg(v_a_1752_, v_x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1755_, lean_object* v_a_1756_, lean_object* v_x_1757_){
_start:
{
uint8_t v_res_1758_; lean_object* v_r_1759_; 
v_res_1758_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__0(v_00_u03b2_1755_, v_a_1756_, v_x_1757_);
lean_dec(v_x_1757_);
lean_dec(v_a_1756_);
v_r_1759_ = lean_box(v_res_1758_);
return v_r_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__1(lean_object* v_00_u03b2_1760_, lean_object* v_a_1761_, lean_object* v_x_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__1___redArg(v_a_1761_, v_x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1764_, lean_object* v_a_1765_, lean_object* v_x_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__0_spec__1(v_00_u03b2_1764_, v_a_1765_, v_x_1766_);
lean_dec(v_a_1765_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2_spec__4(lean_object* v_00_u03b2_1768_, lean_object* v_a_1769_, lean_object* v_x_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2_spec__4___redArg(v_a_1769_, v_x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1772_, lean_object* v_a_1773_, lean_object* v_x_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_spec__2_spec__4(v_00_u03b2_1772_, v_a_1773_, v_x_1774_);
lean_dec(v_x_1774_);
lean_dec(v_a_1773_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg(){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__51));
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___boxed(lean_object* v_a_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(lean_object* v_a_1929_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___boxed(lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(v_a_1932_);
lean_dec_ref(v_a_1932_);
return v_res_1934_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(lean_object* v_a_1935_, lean_object* v_as_1936_, size_t v_i_1937_, size_t v_stop_1938_){
_start:
{
uint8_t v___x_1939_; 
v___x_1939_ = lean_usize_dec_eq(v_i_1937_, v_stop_1938_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1940_ = lean_array_uget_borrowed(v_as_1936_, v_i_1937_);
v___x_1941_ = lean_name_eq(v_a_1935_, v___x_1940_);
if (v___x_1941_ == 0)
{
size_t v___x_1942_; size_t v___x_1943_; 
v___x_1942_ = ((size_t)1ULL);
v___x_1943_ = lean_usize_add(v_i_1937_, v___x_1942_);
v_i_1937_ = v___x_1943_;
goto _start;
}
else
{
return v___x_1941_;
}
}
else
{
uint8_t v___x_1945_; 
v___x_1945_ = 0;
return v___x_1945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0___boxed(lean_object* v_a_1946_, lean_object* v_as_1947_, lean_object* v_i_1948_, lean_object* v_stop_1949_){
_start:
{
size_t v_i_boxed_1950_; size_t v_stop_boxed_1951_; uint8_t v_res_1952_; lean_object* v_r_1953_; 
v_i_boxed_1950_ = lean_unbox_usize(v_i_1948_);
lean_dec(v_i_1948_);
v_stop_boxed_1951_ = lean_unbox_usize(v_stop_1949_);
lean_dec(v_stop_1949_);
v_res_1952_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_1946_, v_as_1947_, v_i_boxed_1950_, v_stop_boxed_1951_);
lean_dec_ref(v_as_1947_);
lean_dec(v_a_1946_);
v_r_1953_ = lean_box(v_res_1952_);
return v_r_1953_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(lean_object* v_as_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = lean_array_get_size(v_as_1954_);
v___x_1958_ = lean_nat_dec_lt(v___x_1956_, v___x_1957_);
if (v___x_1958_ == 0)
{
return v___x_1958_;
}
else
{
if (v___x_1958_ == 0)
{
return v___x_1958_;
}
else
{
size_t v___x_1959_; size_t v___x_1960_; uint8_t v___x_1961_; 
v___x_1959_ = ((size_t)0ULL);
v___x_1960_ = lean_usize_of_nat(v___x_1957_);
v___x_1961_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_1955_, v_as_1954_, v___x_1959_, v___x_1960_);
return v___x_1961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0___boxed(lean_object* v_as_1962_, lean_object* v_a_1963_){
_start:
{
uint8_t v_res_1964_; lean_object* v_r_1965_; 
v_res_1964_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_as_1962_, v_a_1963_);
lean_dec(v_a_1963_);
lean_dec_ref(v_as_1962_);
v_r_1965_ = lean_box(v_res_1964_);
return v_r_1965_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__4(void){
_start:
{
lean_object* v___x_1982_; lean_object* v_additional_1983_; lean_object* v___x_1984_; 
v___x_1982_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3));
v_additional_1983_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_1984_ = l_Array_append___redArg(v_additional_1983_, v___x_1982_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(lean_object* v_a_1985_){
_start:
{
lean_object* v_legalAxioms_1987_; lean_object* v_additional_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v_legalAxioms_1987_ = lean_ctor_get(v_a_1985_, 5);
v_additional_1988_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_1989_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__2));
v___x_1990_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_legalAxioms_1987_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; 
v___x_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1991_, 0, v_additional_1988_);
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__4, &l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__4_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__4);
v___x_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
return v___x_1993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___boxed(lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_1994_);
lean_dec_ref(v_a_1994_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_stringStream(lean_object* v_s_1997_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_1999_ = lean_string_to_utf8(v_s_1997_);
v___x_2000_ = lean_unsigned_to_nat(0u);
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = lean_st_mk_ref(v___x_2001_);
v___x_2003_ = l_IO_FS_Stream_ofBuffer(v___x_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_stringStream___boxed(lean_object* v_s_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l___private_Lake_CLI_Check_0__Lake_Check_stringStream(v_s_2004_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg(lean_object* v_e_2007_){
_start:
{
if (lean_obj_tag(v_e_2007_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2017_; 
v_a_2009_ = lean_ctor_get(v_e_2007_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_e_2007_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2011_ = v_e_2007_;
v_isShared_2012_ = v_isSharedCheck_2017_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v_e_2007_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2017_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2013_ = lean_mk_io_user_error(v_a_2009_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set_tag(v___x_2011_, 1);
lean_ctor_set(v___x_2011_, 0, v___x_2013_);
v___x_2015_ = v___x_2011_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
v_a_2018_ = lean_ctor_get(v_e_2007_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_e_2007_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v_e_2007_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v_e_2007_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set_tag(v___x_2020_, 0);
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg___boxed(lean_object* v_e_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg(v_e_2026_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0(lean_object* v_00_u03b1_2029_, lean_object* v_e_2030_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg(v_e_2030_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___boxed(lean_object* v_00_u03b1_2033_, lean_object* v_e_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0(v_00_u03b1_2033_, v_e_2034_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__1(lean_object* v_solutionExport_2037_, lean_object* v_init_2038_, lean_object* v_x_2039_, lean_object* v___y_2040_){
_start:
{
if (lean_obj_tag(v_x_2039_) == 0)
{
lean_object* v_k_2042_; lean_object* v_v_2043_; lean_object* v_l_2044_; lean_object* v_r_2045_; lean_object* v___x_2046_; 
v_k_2042_ = lean_ctor_get(v_x_2039_, 1);
lean_inc(v_k_2042_);
v_v_2043_ = lean_ctor_get(v_x_2039_, 2);
lean_inc(v_v_2043_);
v_l_2044_ = lean_ctor_get(v_x_2039_, 3);
lean_inc(v_l_2044_);
v_r_2045_ = lean_ctor_get(v_x_2039_, 4);
lean_inc(v_r_2045_);
lean_dec_ref_known(v_x_2039_, 5);
lean_inc_ref(v_solutionExport_2037_);
v___x_2046_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__1(v_solutionExport_2037_, v_init_2038_, v_l_2044_, v___y_2040_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v_a_2048_; lean_object* v___x_2049_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v_a_2048_ = lean_ctor_get(v_a_2047_, 0);
lean_inc(v_a_2048_);
lean_dec(v_a_2047_);
lean_inc_ref(v_solutionExport_2037_);
v___x_2049_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_k_2042_, v_v_2043_, v_solutionExport_2037_, v___y_2040_);
if (lean_obj_tag(v___x_2049_) == 0)
{
if (lean_obj_tag(v_a_2048_) == 0)
{
lean_object* v_a_2050_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v_init_2038_ = v_a_2050_;
v_x_2039_ = v_r_2045_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_2049_, 1);
v_init_2038_ = v_a_2048_;
v_x_2039_ = v_r_2045_;
goto _start;
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_a_2048_);
lean_dec(v_r_2045_);
lean_dec_ref(v_solutionExport_2037_);
v_a_2053_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2049_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2049_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_dec(v_r_2045_);
lean_dec(v_v_2043_);
lean_dec(v_k_2042_);
lean_dec_ref(v_solutionExport_2037_);
return v___x_2046_;
}
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_dec_ref(v_solutionExport_2037_);
v___x_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2061_, 0, v_init_2038_);
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__1___boxed(lean_object* v_solutionExport_2063_, lean_object* v_init_2064_, lean_object* v_x_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__1(v_solutionExport_2063_, v_init_2064_, v_x_2065_, v___y_2066_);
lean_dec_ref(v___y_2066_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(lean_object* v_challengeExport_2069_, lean_object* v_solutionExport_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_val_2074_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = l___private_Lake_CLI_Check_0__Lake_Check_stringStream(v_challengeExport_2069_);
v___x_2078_ = l_LeanExport_parseStream(v___x_2077_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2078_, 1);
lean_inc_ref(v_solutionExport_2070_);
v___x_2080_ = l___private_Lake_CLI_Check_0__Lake_Check_stringStream(v_solutionExport_2070_);
v___x_2081_ = l_LeanExport_parseStream(v___x_2080_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2083_; lean_object* v_a_2084_; lean_object* v_theoremNames_2085_; lean_object* v_definitionNames_2086_; lean_object* v_legalAxioms_2087_; lean_object* v_externalKernels_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc_n(v_a_2082_, 2);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2083_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2083_);
v_theoremNames_2085_ = lean_ctor_get(v_a_2071_, 3);
v_definitionNames_2086_ = lean_ctor_get(v_a_2071_, 4);
v_legalAxioms_2087_ = lean_ctor_get(v_a_2071_, 5);
v_externalKernels_2088_ = lean_ctor_get(v_a_2071_, 11);
lean_inc_ref(v_theoremNames_2085_);
v___x_2089_ = l_Array_append___redArg(v_theoremNames_2085_, v_legalAxioms_2087_);
v___x_2090_ = l_Lake_Check_compareAt(v_a_2079_, v_a_2082_, v___x_2089_, v_definitionNames_2086_, v_a_2084_);
lean_dec_ref(v___x_2089_);
v___x_2091_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg(v___x_2090_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec_ref_known(v___x_2091_, 1);
lean_inc(v_a_2082_);
v___x_2092_ = l_Lake_Check_checkAxioms(v_a_2082_, v_theoremNames_2085_, v_definitionNames_2086_, v_legalAxioms_2087_);
v___x_2093_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__0___redArg(v___x_2092_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec_ref_known(v___x_2093_, 1);
v___x_2094_ = lean_box(0);
lean_inc(v_externalKernels_2088_);
v___x_2095_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_spec__1(v_solutionExport_2070_, v___x_2094_, v_externalKernels_2088_, v_a_2071_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v_a_2098_; lean_object* v_a_2119_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v_a_2119_ = lean_ctor_get(v_a_2096_, 0);
lean_inc(v_a_2119_);
lean_dec(v_a_2096_);
v_a_2098_ = v_a_2119_;
goto v___jp_2097_;
v___jp_2097_:
{
lean_object* v___x_2099_; 
v___x_2099_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_a_2082_, v_a_2071_);
if (lean_obj_tag(v___x_2099_) == 0)
{
if (lean_obj_tag(v_a_2098_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2109_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2109_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2109_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
if (lean_obj_tag(v_a_2100_) == 1)
{
lean_object* v_val_2104_; 
lean_del_object(v___x_2102_);
v_val_2104_ = lean_ctor_get(v_a_2100_, 0);
lean_inc(v_val_2104_);
lean_dec_ref_known(v_a_2100_, 1);
v_val_2074_ = v_val_2104_;
goto v___jp_2073_;
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
lean_dec(v_a_2100_);
v___x_2105_ = lean_box(0);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2105_);
v___x_2107_ = v___x_2102_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_val_2110_; 
lean_dec_ref_known(v___x_2099_, 1);
v_val_2110_ = lean_ctor_get(v_a_2098_, 0);
lean_inc(v_val_2110_);
lean_dec_ref_known(v_a_2098_, 1);
v_val_2074_ = v_val_2110_;
goto v___jp_2073_;
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v_a_2098_);
v_a_2111_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2099_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2099_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_a_2082_);
v_a_2120_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2095_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2095_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_dec(v_a_2082_);
lean_dec_ref(v_solutionExport_2070_);
return v___x_2093_;
}
}
else
{
lean_dec(v_a_2082_);
lean_dec_ref(v_solutionExport_2070_);
return v___x_2091_;
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec(v_a_2079_);
lean_dec_ref(v_solutionExport_2070_);
v_a_2128_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2081_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2081_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v_solutionExport_2070_);
v_a_2136_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2078_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2078_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
v___jp_2073_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_mk_io_user_error(v_val_2074_);
v___x_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
return v___x_2076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch___boxed(lean_object* v_challengeExport_2144_, lean_object* v_solutionExport_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExport_2144_, v_solutionExport_2145_, v_a_2146_);
lean_dec_ref(v_a_2146_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt(lean_object* v_a_2150_){
_start:
{
lean_object* v___x_2152_; lean_object* v_a_2153_; lean_object* v___x_2154_; lean_object* v_a_2155_; lean_object* v_challengeModule_2156_; lean_object* v_solutionModule_2157_; lean_object* v_theoremNames_2158_; lean_object* v_definitionNames_2159_; lean_object* v_legalAxioms_2160_; lean_object* v___x_2161_; 
v___x_2152_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_2150_);
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref(v___x_2152_);
v___x_2154_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2154_);
v_challengeModule_2156_ = lean_ctor_get(v_a_2150_, 1);
v_solutionModule_2157_ = lean_ctor_get(v_a_2150_, 2);
v_theoremNames_2158_ = lean_ctor_get(v_a_2150_, 3);
v_definitionNames_2159_ = lean_ctor_get(v_a_2150_, 4);
v_legalAxioms_2160_ = lean_ctor_get(v_a_2150_, 5);
lean_inc(v_challengeModule_2156_);
v___x_2161_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v_challengeModule_2156_, v_a_2150_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec_ref_known(v___x_2161_, 1);
v___x_2162_ = l_Array_append___redArg(v_a_2153_, v_theoremNames_2158_);
v___x_2163_ = l_Array_append___redArg(v___x_2162_, v_legalAxioms_2160_);
v___x_2164_ = l_Array_append___redArg(v___x_2163_, v_a_2155_);
lean_dec(v_a_2155_);
v___x_2165_ = l_Array_append___redArg(v___x_2164_, v_definitionNames_2159_);
lean_inc_ref(v___x_2165_);
lean_inc(v_challengeModule_2156_);
v___x_2166_ = l___private_Lake_CLI_Check_0__Lake_Check_safeExport(v_challengeModule_2156_, v___x_2165_, v_a_2150_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2168_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
lean_inc(v_solutionModule_2157_);
v___x_2168_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v_solutionModule_2157_, v_a_2150_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v___x_2169_; 
lean_dec_ref_known(v___x_2168_, 1);
lean_inc(v_solutionModule_2157_);
v___x_2169_ = l___private_Lake_CLI_Check_0__Lake_Check_safeExport(v_solutionModule_2157_, v___x_2165_, v_a_2150_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_a_2167_, v_a_2170_, v_a_2150_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec_ref_known(v___x_2171_, 1);
v___x_2172_ = ((lean_object*)(l_Lake_Check_compareIt___closed__0));
v___x_2173_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2172_);
return v___x_2173_;
}
else
{
return v___x_2171_;
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_a_2167_);
v_a_2174_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2169_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2169_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_dec(v_a_2167_);
lean_dec_ref(v___x_2165_);
return v___x_2168_;
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec_ref(v___x_2165_);
v_a_2182_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2166_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2166_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_dec(v_a_2155_);
lean_dec(v_a_2153_);
return v___x_2161_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___boxed(lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lake_Check_compareIt(v_a_2190_);
lean_dec_ref(v_a_2190_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(lean_object* v_j_2193_, lean_object* v_k_2194_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = l_Lean_Json_getObjValD(v_j_2193_, v_k_2194_);
v___x_2196_ = l_Lean_Json_getStr_x3f(v___x_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0___boxed(lean_object* v_j_2197_, lean_object* v_k_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_j_2197_, v_k_2198_);
lean_dec_ref(v_k_2198_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(size_t v_sz_2200_, size_t v_i_2201_, lean_object* v_bs_2202_){
_start:
{
uint8_t v___x_2203_; 
v___x_2203_ = lean_usize_dec_lt(v_i_2201_, v_sz_2200_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v_bs_2202_);
return v___x_2204_;
}
else
{
lean_object* v_v_2205_; lean_object* v___x_2206_; 
v_v_2205_ = lean_array_uget_borrowed(v_bs_2202_, v_i_2201_);
lean_inc(v_v_2205_);
v___x_2206_ = l_Lean_Json_getStr_x3f(v_v_2205_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec_ref(v_bs_2202_);
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2216_; lean_object* v_bs_x27_2217_; size_t v___x_2218_; size_t v___x_2219_; lean_object* v___x_2220_; 
v_a_2215_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2206_, 1);
v___x_2216_ = lean_unsigned_to_nat(0u);
v_bs_x27_2217_ = lean_array_uset(v_bs_2202_, v_i_2201_, v___x_2216_);
v___x_2218_ = ((size_t)1ULL);
v___x_2219_ = lean_usize_add(v_i_2201_, v___x_2218_);
v___x_2220_ = lean_array_uset(v_bs_x27_2217_, v_i_2201_, v_a_2215_);
v_i_2201_ = v___x_2219_;
v_bs_2202_ = v___x_2220_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2222_, lean_object* v_i_2223_, lean_object* v_bs_2224_){
_start:
{
size_t v_sz_boxed_2225_; size_t v_i_boxed_2226_; lean_object* v_res_2227_; 
v_sz_boxed_2225_ = lean_unbox_usize(v_sz_2222_);
lean_dec(v_sz_2222_);
v_i_boxed_2226_ = lean_unbox_usize(v_i_2223_);
lean_dec(v_i_2223_);
v_res_2227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_2225_, v_i_boxed_2226_, v_bs_2224_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(lean_object* v_x_2230_){
_start:
{
if (lean_obj_tag(v_x_2230_) == 4)
{
lean_object* v_elems_2231_; size_t v_sz_2232_; size_t v___x_2233_; lean_object* v___x_2234_; 
v_elems_2231_ = lean_ctor_get(v_x_2230_, 0);
lean_inc_ref(v_elems_2231_);
lean_dec_ref_known(v_x_2230_, 1);
v_sz_2232_ = lean_array_size(v_elems_2231_);
v___x_2233_ = ((size_t)0ULL);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_2232_, v___x_2233_, v_elems_2231_);
return v___x_2234_;
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2235_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__0));
v___x_2236_ = lean_unsigned_to_nat(80u);
v___x_2237_ = l_Lean_Json_pretty(v_x_2230_, v___x_2236_);
v___x_2238_ = lean_string_append(v___x_2235_, v___x_2237_);
lean_dec_ref(v___x_2237_);
v___x_2239_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_2240_ = lean_string_append(v___x_2238_, v___x_2239_);
v___x_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
return v___x_2241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(lean_object* v_x_2244_){
_start:
{
if (lean_obj_tag(v_x_2244_) == 0)
{
lean_object* v___x_2245_; 
v___x_2245_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3___closed__0));
return v___x_2245_;
}
else
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_x_2244_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2263_; 
v_a_2255_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2257_ = v___x_2246_;
v_isShared_2258_ = v_isSharedCheck_2263_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2246_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2263_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2259_, 0, v_a_2255_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v___x_2259_);
v___x_2261_ = v___x_2257_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(lean_object* v_j_2264_, lean_object* v_k_2265_){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = l_Lean_Json_getObjValD(v_j_2264_, v_k_2265_);
v___x_2267_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(v___x_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2___boxed(lean_object* v_j_2268_, lean_object* v_k_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_j_2268_, v_k_2269_);
lean_dec_ref(v_k_2269_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(lean_object* v_x_2273_){
_start:
{
if (lean_obj_tag(v_x_2273_) == 0)
{
lean_object* v___x_2274_; 
v___x_2274_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___closed__0));
return v___x_2274_;
}
else
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Json_getBool_x3f(v_x_2273_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2275_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2292_; 
v_a_2284_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2286_ = v___x_2275_;
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2275_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2288_, 0, v_a_2284_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2288_);
v___x_2290_ = v___x_2286_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___boxed(lean_object* v_x_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v_x_2293_);
lean_dec(v_x_2293_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(lean_object* v_j_2295_, lean_object* v_k_2296_){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = l_Lean_Json_getObjValD(v_j_2295_, v_k_2296_);
v___x_2298_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v___x_2297_);
lean_dec(v___x_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3___boxed(lean_object* v_j_2299_, lean_object* v_k_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_j_2299_, v_k_2300_);
lean_dec_ref(v_k_2300_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_cmp_2302_, lean_object* v_k_2303_, lean_object* v_v_2304_, lean_object* v_t_2305_){
_start:
{
if (lean_obj_tag(v_t_2305_) == 0)
{
lean_object* v_size_2306_; lean_object* v_k_2307_; lean_object* v_v_2308_; lean_object* v_l_2309_; lean_object* v_r_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2591_; 
v_size_2306_ = lean_ctor_get(v_t_2305_, 0);
v_k_2307_ = lean_ctor_get(v_t_2305_, 1);
v_v_2308_ = lean_ctor_get(v_t_2305_, 2);
v_l_2309_ = lean_ctor_get(v_t_2305_, 3);
v_r_2310_ = lean_ctor_get(v_t_2305_, 4);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_t_2305_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2312_ = v_t_2305_;
v_isShared_2313_ = v_isSharedCheck_2591_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_r_2310_);
lean_inc(v_l_2309_);
lean_inc(v_v_2308_);
lean_inc(v_k_2307_);
lean_inc(v_size_2306_);
lean_dec(v_t_2305_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2591_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; uint8_t v___x_2315_; 
lean_inc_ref(v_cmp_2302_);
lean_inc(v_k_2307_);
lean_inc_ref(v_k_2303_);
v___x_2314_ = lean_apply_2(v_cmp_2302_, v_k_2303_, v_k_2307_);
v___x_2315_ = lean_unbox(v___x_2314_);
switch(v___x_2315_)
{
case 0:
{
lean_object* v_impl_2316_; lean_object* v___x_2317_; 
lean_dec(v_size_2306_);
v_impl_2316_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_2302_, v_k_2303_, v_v_2304_, v_l_2309_);
v___x_2317_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2310_) == 0)
{
lean_object* v_size_2318_; lean_object* v_size_2319_; lean_object* v_k_2320_; lean_object* v_v_2321_; lean_object* v_l_2322_; lean_object* v_r_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_size_2318_ = lean_ctor_get(v_r_2310_, 0);
v_size_2319_ = lean_ctor_get(v_impl_2316_, 0);
lean_inc(v_size_2319_);
v_k_2320_ = lean_ctor_get(v_impl_2316_, 1);
lean_inc(v_k_2320_);
v_v_2321_ = lean_ctor_get(v_impl_2316_, 2);
lean_inc(v_v_2321_);
v_l_2322_ = lean_ctor_get(v_impl_2316_, 3);
lean_inc(v_l_2322_);
v_r_2323_ = lean_ctor_get(v_impl_2316_, 4);
lean_inc(v_r_2323_);
v___x_2324_ = lean_unsigned_to_nat(3u);
v___x_2325_ = lean_nat_mul(v___x_2324_, v_size_2318_);
v___x_2326_ = lean_nat_dec_lt(v___x_2325_, v_size_2319_);
lean_dec(v___x_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
lean_dec(v_r_2323_);
lean_dec(v_l_2322_);
lean_dec(v_v_2321_);
lean_dec(v_k_2320_);
v___x_2327_ = lean_nat_add(v___x_2317_, v_size_2319_);
lean_dec(v_size_2319_);
v___x_2328_ = lean_nat_add(v___x_2327_, v_size_2318_);
lean_dec(v___x_2327_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 3, v_impl_2316_);
lean_ctor_set(v___x_2312_, 0, v___x_2328_);
v___x_2330_ = v___x_2312_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2331_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2331_, 3, v_impl_2316_);
lean_ctor_set(v_reuseFailAlloc_2331_, 4, v_r_2310_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
else
{
lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2397_; 
v_isSharedCheck_2397_ = !lean_is_exclusive(v_impl_2316_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; lean_object* v_unused_2399_; lean_object* v_unused_2400_; lean_object* v_unused_2401_; lean_object* v_unused_2402_; 
v_unused_2398_ = lean_ctor_get(v_impl_2316_, 4);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_impl_2316_, 3);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_impl_2316_, 2);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_impl_2316_, 1);
lean_dec(v_unused_2401_);
v_unused_2402_ = lean_ctor_get(v_impl_2316_, 0);
lean_dec(v_unused_2402_);
v___x_2333_ = v_impl_2316_;
v_isShared_2334_ = v_isSharedCheck_2397_;
goto v_resetjp_2332_;
}
else
{
lean_dec(v_impl_2316_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2397_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v_size_2335_; lean_object* v_size_2336_; lean_object* v_k_2337_; lean_object* v_v_2338_; lean_object* v_l_2339_; lean_object* v_r_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v_size_2335_ = lean_ctor_get(v_l_2322_, 0);
v_size_2336_ = lean_ctor_get(v_r_2323_, 0);
v_k_2337_ = lean_ctor_get(v_r_2323_, 1);
v_v_2338_ = lean_ctor_get(v_r_2323_, 2);
v_l_2339_ = lean_ctor_get(v_r_2323_, 3);
v_r_2340_ = lean_ctor_get(v_r_2323_, 4);
v___x_2341_ = lean_unsigned_to_nat(2u);
v___x_2342_ = lean_nat_mul(v___x_2341_, v_size_2335_);
v___x_2343_ = lean_nat_dec_lt(v_size_2336_, v___x_2342_);
lean_dec(v___x_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2372_; 
lean_inc(v_r_2340_);
lean_inc(v_l_2339_);
lean_inc(v_v_2338_);
lean_inc(v_k_2337_);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_r_2323_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; lean_object* v_unused_2374_; lean_object* v_unused_2375_; lean_object* v_unused_2376_; lean_object* v_unused_2377_; 
v_unused_2373_ = lean_ctor_get(v_r_2323_, 4);
lean_dec(v_unused_2373_);
v_unused_2374_ = lean_ctor_get(v_r_2323_, 3);
lean_dec(v_unused_2374_);
v_unused_2375_ = lean_ctor_get(v_r_2323_, 2);
lean_dec(v_unused_2375_);
v_unused_2376_ = lean_ctor_get(v_r_2323_, 1);
lean_dec(v_unused_2376_);
v_unused_2377_ = lean_ctor_get(v_r_2323_, 0);
lean_dec(v_unused_2377_);
v___x_2345_ = v_r_2323_;
v_isShared_2346_ = v_isSharedCheck_2372_;
goto v_resetjp_2344_;
}
else
{
lean_dec(v_r_2323_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2372_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___x_2360_; lean_object* v___y_2362_; 
v___x_2347_ = lean_nat_add(v___x_2317_, v_size_2319_);
lean_dec(v_size_2319_);
v___x_2348_ = lean_nat_add(v___x_2347_, v_size_2318_);
lean_dec(v___x_2347_);
v___x_2360_ = lean_nat_add(v___x_2317_, v_size_2335_);
if (lean_obj_tag(v_l_2339_) == 0)
{
lean_object* v_size_2370_; 
v_size_2370_ = lean_ctor_get(v_l_2339_, 0);
lean_inc(v_size_2370_);
v___y_2362_ = v_size_2370_;
goto v___jp_2361_;
}
else
{
lean_object* v___x_2371_; 
v___x_2371_ = lean_unsigned_to_nat(0u);
v___y_2362_ = v___x_2371_;
goto v___jp_2361_;
}
v___jp_2349_:
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2353_ = lean_nat_add(v___y_2350_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec(v___y_2350_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 4, v_r_2310_);
lean_ctor_set(v___x_2345_, 3, v_r_2340_);
lean_ctor_set(v___x_2345_, 2, v_v_2308_);
lean_ctor_set(v___x_2345_, 1, v_k_2307_);
lean_ctor_set(v___x_2345_, 0, v___x_2353_);
v___x_2355_ = v___x_2345_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2359_, 3, v_r_2340_);
lean_ctor_set(v_reuseFailAlloc_2359_, 4, v_r_2310_);
v___x_2355_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2357_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 4, v___x_2355_);
lean_ctor_set(v___x_2333_, 3, v___y_2351_);
lean_ctor_set(v___x_2333_, 2, v_v_2338_);
lean_ctor_set(v___x_2333_, 1, v_k_2337_);
lean_ctor_set(v___x_2333_, 0, v___x_2348_);
v___x_2357_ = v___x_2333_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_k_2337_);
lean_ctor_set(v_reuseFailAlloc_2358_, 2, v_v_2338_);
lean_ctor_set(v_reuseFailAlloc_2358_, 3, v___y_2351_);
lean_ctor_set(v_reuseFailAlloc_2358_, 4, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
v___jp_2361_:
{
lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2363_ = lean_nat_add(v___x_2360_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec(v___x_2360_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 4, v_l_2339_);
lean_ctor_set(v___x_2312_, 3, v_l_2322_);
lean_ctor_set(v___x_2312_, 2, v_v_2321_);
lean_ctor_set(v___x_2312_, 1, v_k_2320_);
lean_ctor_set(v___x_2312_, 0, v___x_2363_);
v___x_2365_ = v___x_2312_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_k_2320_);
lean_ctor_set(v_reuseFailAlloc_2369_, 2, v_v_2321_);
lean_ctor_set(v_reuseFailAlloc_2369_, 3, v_l_2322_);
lean_ctor_set(v_reuseFailAlloc_2369_, 4, v_l_2339_);
v___x_2365_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_nat_add(v___x_2317_, v_size_2318_);
if (lean_obj_tag(v_r_2340_) == 0)
{
lean_object* v_size_2367_; 
v_size_2367_ = lean_ctor_get(v_r_2340_, 0);
lean_inc(v_size_2367_);
v___y_2350_ = v___x_2366_;
v___y_2351_ = v___x_2365_;
v___y_2352_ = v_size_2367_;
goto v___jp_2349_;
}
else
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_unsigned_to_nat(0u);
v___y_2350_ = v___x_2366_;
v___y_2351_ = v___x_2365_;
v___y_2352_ = v___x_2368_;
goto v___jp_2349_;
}
}
}
}
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
lean_del_object(v___x_2312_);
v___x_2378_ = lean_nat_add(v___x_2317_, v_size_2319_);
lean_dec(v_size_2319_);
v___x_2379_ = lean_nat_add(v___x_2378_, v_size_2318_);
lean_dec(v___x_2378_);
v___x_2380_ = lean_nat_add(v___x_2317_, v_size_2318_);
v___x_2381_ = lean_nat_add(v___x_2380_, v_size_2336_);
lean_dec(v___x_2380_);
lean_inc_ref(v_r_2310_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 4, v_r_2310_);
lean_ctor_set(v___x_2333_, 3, v_r_2323_);
lean_ctor_set(v___x_2333_, 2, v_v_2308_);
lean_ctor_set(v___x_2333_, 1, v_k_2307_);
lean_ctor_set(v___x_2333_, 0, v___x_2381_);
v___x_2383_ = v___x_2333_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2396_, 3, v_r_2323_);
lean_ctor_set(v_reuseFailAlloc_2396_, 4, v_r_2310_);
v___x_2383_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
v_isSharedCheck_2390_ = !lean_is_exclusive(v_r_2310_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; lean_object* v_unused_2392_; lean_object* v_unused_2393_; lean_object* v_unused_2394_; lean_object* v_unused_2395_; 
v_unused_2391_ = lean_ctor_get(v_r_2310_, 4);
lean_dec(v_unused_2391_);
v_unused_2392_ = lean_ctor_get(v_r_2310_, 3);
lean_dec(v_unused_2392_);
v_unused_2393_ = lean_ctor_get(v_r_2310_, 2);
lean_dec(v_unused_2393_);
v_unused_2394_ = lean_ctor_get(v_r_2310_, 1);
lean_dec(v_unused_2394_);
v_unused_2395_ = lean_ctor_get(v_r_2310_, 0);
lean_dec(v_unused_2395_);
v___x_2385_ = v_r_2310_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_dec(v_r_2310_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 4, v___x_2383_);
lean_ctor_set(v___x_2385_, 3, v_l_2322_);
lean_ctor_set(v___x_2385_, 2, v_v_2321_);
lean_ctor_set(v___x_2385_, 1, v_k_2320_);
lean_ctor_set(v___x_2385_, 0, v___x_2379_);
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2379_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_k_2320_);
lean_ctor_set(v_reuseFailAlloc_2389_, 2, v_v_2321_);
lean_ctor_set(v_reuseFailAlloc_2389_, 3, v_l_2322_);
lean_ctor_set(v_reuseFailAlloc_2389_, 4, v___x_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2403_; 
v_l_2403_ = lean_ctor_get(v_impl_2316_, 3);
lean_inc(v_l_2403_);
if (lean_obj_tag(v_l_2403_) == 0)
{
lean_object* v_r_2404_; lean_object* v_k_2405_; lean_object* v_v_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2417_; 
v_r_2404_ = lean_ctor_get(v_impl_2316_, 4);
v_k_2405_ = lean_ctor_get(v_impl_2316_, 1);
v_v_2406_ = lean_ctor_get(v_impl_2316_, 2);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_impl_2316_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; lean_object* v_unused_2419_; 
v_unused_2418_ = lean_ctor_get(v_impl_2316_, 3);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v_impl_2316_, 0);
lean_dec(v_unused_2419_);
v___x_2408_ = v_impl_2316_;
v_isShared_2409_ = v_isSharedCheck_2417_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_r_2404_);
lean_inc(v_v_2406_);
lean_inc(v_k_2405_);
lean_dec(v_impl_2316_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2417_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2410_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2404_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 3, v_r_2404_);
lean_ctor_set(v___x_2408_, 2, v_v_2308_);
lean_ctor_set(v___x_2408_, 1, v_k_2307_);
lean_ctor_set(v___x_2408_, 0, v___x_2317_);
v___x_2412_ = v___x_2408_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2416_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2416_, 3, v_r_2404_);
lean_ctor_set(v_reuseFailAlloc_2416_, 4, v_r_2404_);
v___x_2412_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
lean_object* v___x_2414_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 4, v___x_2412_);
lean_ctor_set(v___x_2312_, 3, v_l_2403_);
lean_ctor_set(v___x_2312_, 2, v_v_2406_);
lean_ctor_set(v___x_2312_, 1, v_k_2405_);
lean_ctor_set(v___x_2312_, 0, v___x_2410_);
v___x_2414_ = v___x_2312_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_k_2405_);
lean_ctor_set(v_reuseFailAlloc_2415_, 2, v_v_2406_);
lean_ctor_set(v_reuseFailAlloc_2415_, 3, v_l_2403_);
lean_ctor_set(v_reuseFailAlloc_2415_, 4, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_object* v_r_2420_; 
v_r_2420_ = lean_ctor_get(v_impl_2316_, 4);
lean_inc(v_r_2420_);
if (lean_obj_tag(v_r_2420_) == 0)
{
lean_object* v_k_2421_; lean_object* v_v_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2445_; 
v_k_2421_ = lean_ctor_get(v_impl_2316_, 1);
v_v_2422_ = lean_ctor_get(v_impl_2316_, 2);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_impl_2316_);
if (v_isSharedCheck_2445_ == 0)
{
lean_object* v_unused_2446_; lean_object* v_unused_2447_; lean_object* v_unused_2448_; 
v_unused_2446_ = lean_ctor_get(v_impl_2316_, 4);
lean_dec(v_unused_2446_);
v_unused_2447_ = lean_ctor_get(v_impl_2316_, 3);
lean_dec(v_unused_2447_);
v_unused_2448_ = lean_ctor_get(v_impl_2316_, 0);
lean_dec(v_unused_2448_);
v___x_2424_ = v_impl_2316_;
v_isShared_2425_ = v_isSharedCheck_2445_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_v_2422_);
lean_inc(v_k_2421_);
lean_dec(v_impl_2316_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2445_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v_k_2426_; lean_object* v_v_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2441_; 
v_k_2426_ = lean_ctor_get(v_r_2420_, 1);
v_v_2427_ = lean_ctor_get(v_r_2420_, 2);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_r_2420_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; lean_object* v_unused_2443_; lean_object* v_unused_2444_; 
v_unused_2442_ = lean_ctor_get(v_r_2420_, 4);
lean_dec(v_unused_2442_);
v_unused_2443_ = lean_ctor_get(v_r_2420_, 3);
lean_dec(v_unused_2443_);
v_unused_2444_ = lean_ctor_get(v_r_2420_, 0);
lean_dec(v_unused_2444_);
v___x_2429_ = v_r_2420_;
v_isShared_2430_ = v_isSharedCheck_2441_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_v_2427_);
lean_inc(v_k_2426_);
lean_dec(v_r_2420_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2441_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2431_ = lean_unsigned_to_nat(3u);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 4, v_l_2403_);
lean_ctor_set(v___x_2429_, 3, v_l_2403_);
lean_ctor_set(v___x_2429_, 2, v_v_2422_);
lean_ctor_set(v___x_2429_, 1, v_k_2421_);
lean_ctor_set(v___x_2429_, 0, v___x_2317_);
v___x_2433_ = v___x_2429_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_k_2421_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v_v_2422_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v_l_2403_);
lean_ctor_set(v_reuseFailAlloc_2440_, 4, v_l_2403_);
v___x_2433_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2435_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 4, v_l_2403_);
lean_ctor_set(v___x_2424_, 2, v_v_2308_);
lean_ctor_set(v___x_2424_, 1, v_k_2307_);
lean_ctor_set(v___x_2424_, 0, v___x_2317_);
v___x_2435_ = v___x_2424_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2439_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2439_, 3, v_l_2403_);
lean_ctor_set(v_reuseFailAlloc_2439_, 4, v_l_2403_);
v___x_2435_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2437_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 4, v___x_2435_);
lean_ctor_set(v___x_2312_, 3, v___x_2433_);
lean_ctor_set(v___x_2312_, 2, v_v_2427_);
lean_ctor_set(v___x_2312_, 1, v_k_2426_);
lean_ctor_set(v___x_2312_, 0, v___x_2431_);
v___x_2437_ = v___x_2312_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_k_2426_);
lean_ctor_set(v_reuseFailAlloc_2438_, 2, v_v_2427_);
lean_ctor_set(v_reuseFailAlloc_2438_, 3, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2438_, 4, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
}
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2449_ = lean_unsigned_to_nat(2u);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 4, v_r_2420_);
lean_ctor_set(v___x_2312_, 3, v_impl_2316_);
lean_ctor_set(v___x_2312_, 0, v___x_2449_);
v___x_2451_ = v___x_2312_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v_impl_2316_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v_r_2420_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2454_; 
lean_dec(v_v_2308_);
lean_dec(v_k_2307_);
lean_dec_ref(v_cmp_2302_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 2, v_v_2304_);
lean_ctor_set(v___x_2312_, 1, v_k_2303_);
v___x_2454_ = v___x_2312_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_size_2306_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_k_2303_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_v_2304_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v_l_2309_);
lean_ctor_set(v_reuseFailAlloc_2455_, 4, v_r_2310_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
default: 
{
lean_object* v_impl_2456_; lean_object* v___x_2457_; 
lean_dec(v_size_2306_);
v_impl_2456_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_2302_, v_k_2303_, v_v_2304_, v_r_2310_);
v___x_2457_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2309_) == 0)
{
lean_object* v_size_2458_; lean_object* v_size_2459_; lean_object* v_k_2460_; lean_object* v_v_2461_; lean_object* v_l_2462_; lean_object* v_r_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; 
v_size_2458_ = lean_ctor_get(v_l_2309_, 0);
v_size_2459_ = lean_ctor_get(v_impl_2456_, 0);
lean_inc(v_size_2459_);
v_k_2460_ = lean_ctor_get(v_impl_2456_, 1);
lean_inc(v_k_2460_);
v_v_2461_ = lean_ctor_get(v_impl_2456_, 2);
lean_inc(v_v_2461_);
v_l_2462_ = lean_ctor_get(v_impl_2456_, 3);
lean_inc(v_l_2462_);
v_r_2463_ = lean_ctor_get(v_impl_2456_, 4);
lean_inc(v_r_2463_);
v___x_2464_ = lean_unsigned_to_nat(3u);
v___x_2465_ = lean_nat_mul(v___x_2464_, v_size_2458_);
v___x_2466_ = lean_nat_dec_lt(v___x_2465_, v_size_2459_);
lean_dec(v___x_2465_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
lean_dec(v_r_2463_);
lean_dec(v_l_2462_);
lean_dec(v_v_2461_);
lean_dec(v_k_2460_);
v___x_2467_ = lean_nat_add(v___x_2457_, v_size_2458_);
v___x_2468_ = lean_nat_add(v___x_2467_, v_size_2459_);
lean_dec(v_size_2459_);
lean_dec(v___x_2467_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 4, v_impl_2456_);
lean_ctor_set(v___x_2312_, 0, v___x_2468_);
v___x_2470_ = v___x_2312_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2471_, 3, v_l_2309_);
lean_ctor_set(v_reuseFailAlloc_2471_, 4, v_impl_2456_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
else
{
lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2535_; 
v_isSharedCheck_2535_ = !lean_is_exclusive(v_impl_2456_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; lean_object* v_unused_2537_; lean_object* v_unused_2538_; lean_object* v_unused_2539_; lean_object* v_unused_2540_; 
v_unused_2536_ = lean_ctor_get(v_impl_2456_, 4);
lean_dec(v_unused_2536_);
v_unused_2537_ = lean_ctor_get(v_impl_2456_, 3);
lean_dec(v_unused_2537_);
v_unused_2538_ = lean_ctor_get(v_impl_2456_, 2);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v_impl_2456_, 1);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_impl_2456_, 0);
lean_dec(v_unused_2540_);
v___x_2473_ = v_impl_2456_;
v_isShared_2474_ = v_isSharedCheck_2535_;
goto v_resetjp_2472_;
}
else
{
lean_dec(v_impl_2456_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2535_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v_size_2475_; lean_object* v_k_2476_; lean_object* v_v_2477_; lean_object* v_l_2478_; lean_object* v_r_2479_; lean_object* v_size_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v_size_2475_ = lean_ctor_get(v_l_2462_, 0);
v_k_2476_ = lean_ctor_get(v_l_2462_, 1);
v_v_2477_ = lean_ctor_get(v_l_2462_, 2);
v_l_2478_ = lean_ctor_get(v_l_2462_, 3);
v_r_2479_ = lean_ctor_get(v_l_2462_, 4);
v_size_2480_ = lean_ctor_get(v_r_2463_, 0);
v___x_2481_ = lean_unsigned_to_nat(2u);
v___x_2482_ = lean_nat_mul(v___x_2481_, v_size_2480_);
v___x_2483_ = lean_nat_dec_lt(v_size_2475_, v___x_2482_);
lean_dec(v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2511_; 
lean_inc(v_r_2479_);
lean_inc(v_l_2478_);
lean_inc(v_v_2477_);
lean_inc(v_k_2476_);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_l_2462_);
if (v_isSharedCheck_2511_ == 0)
{
lean_object* v_unused_2512_; lean_object* v_unused_2513_; lean_object* v_unused_2514_; lean_object* v_unused_2515_; lean_object* v_unused_2516_; 
v_unused_2512_ = lean_ctor_get(v_l_2462_, 4);
lean_dec(v_unused_2512_);
v_unused_2513_ = lean_ctor_get(v_l_2462_, 3);
lean_dec(v_unused_2513_);
v_unused_2514_ = lean_ctor_get(v_l_2462_, 2);
lean_dec(v_unused_2514_);
v_unused_2515_ = lean_ctor_get(v_l_2462_, 1);
lean_dec(v_unused_2515_);
v_unused_2516_ = lean_ctor_get(v_l_2462_, 0);
lean_dec(v_unused_2516_);
v___x_2485_ = v_l_2462_;
v_isShared_2486_ = v_isSharedCheck_2511_;
goto v_resetjp_2484_;
}
else
{
lean_dec(v_l_2462_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2511_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2501_; 
v___x_2487_ = lean_nat_add(v___x_2457_, v_size_2458_);
v___x_2488_ = lean_nat_add(v___x_2487_, v_size_2459_);
lean_dec(v_size_2459_);
if (lean_obj_tag(v_l_2478_) == 0)
{
lean_object* v_size_2509_; 
v_size_2509_ = lean_ctor_get(v_l_2478_, 0);
lean_inc(v_size_2509_);
v___y_2501_ = v_size_2509_;
goto v___jp_2500_;
}
else
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_unsigned_to_nat(0u);
v___y_2501_ = v___x_2510_;
goto v___jp_2500_;
}
v___jp_2489_:
{
lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2493_ = lean_nat_add(v___y_2490_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec(v___y_2490_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 4, v_r_2463_);
lean_ctor_set(v___x_2485_, 3, v_r_2479_);
lean_ctor_set(v___x_2485_, 2, v_v_2461_);
lean_ctor_set(v___x_2485_, 1, v_k_2460_);
lean_ctor_set(v___x_2485_, 0, v___x_2493_);
v___x_2495_ = v___x_2485_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_k_2460_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_v_2461_);
lean_ctor_set(v_reuseFailAlloc_2499_, 3, v_r_2479_);
lean_ctor_set(v_reuseFailAlloc_2499_, 4, v_r_2463_);
v___x_2495_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2497_; 
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 4, v___x_2495_);
lean_ctor_set(v___x_2473_, 3, v___y_2491_);
lean_ctor_set(v___x_2473_, 2, v_v_2477_);
lean_ctor_set(v___x_2473_, 1, v_k_2476_);
lean_ctor_set(v___x_2473_, 0, v___x_2488_);
v___x_2497_ = v___x_2473_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_k_2476_);
lean_ctor_set(v_reuseFailAlloc_2498_, 2, v_v_2477_);
lean_ctor_set(v_reuseFailAlloc_2498_, 3, v___y_2491_);
lean_ctor_set(v_reuseFailAlloc_2498_, 4, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
v___jp_2500_:
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2502_ = lean_nat_add(v___x_2487_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec(v___x_2487_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 4, v_l_2478_);
lean_ctor_set(v___x_2312_, 0, v___x_2502_);
v___x_2504_ = v___x_2312_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2508_, 3, v_l_2309_);
lean_ctor_set(v_reuseFailAlloc_2508_, 4, v_l_2478_);
v___x_2504_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_nat_add(v___x_2457_, v_size_2480_);
if (lean_obj_tag(v_r_2479_) == 0)
{
lean_object* v_size_2506_; 
v_size_2506_ = lean_ctor_get(v_r_2479_, 0);
lean_inc(v_size_2506_);
v___y_2490_ = v___x_2505_;
v___y_2491_ = v___x_2504_;
v___y_2492_ = v_size_2506_;
goto v___jp_2489_;
}
else
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_unsigned_to_nat(0u);
v___y_2490_ = v___x_2505_;
v___y_2491_ = v___x_2504_;
v___y_2492_ = v___x_2507_;
goto v___jp_2489_;
}
}
}
}
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
lean_del_object(v___x_2312_);
v___x_2517_ = lean_nat_add(v___x_2457_, v_size_2458_);
v___x_2518_ = lean_nat_add(v___x_2517_, v_size_2459_);
lean_dec(v_size_2459_);
v___x_2519_ = lean_nat_add(v___x_2517_, v_size_2475_);
lean_dec(v___x_2517_);
lean_inc_ref(v_l_2309_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 4, v_l_2462_);
lean_ctor_set(v___x_2473_, 3, v_l_2309_);
lean_ctor_set(v___x_2473_, 2, v_v_2308_);
lean_ctor_set(v___x_2473_, 1, v_k_2307_);
lean_ctor_set(v___x_2473_, 0, v___x_2519_);
v___x_2521_ = v___x_2473_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2534_, 3, v_l_2309_);
lean_ctor_set(v_reuseFailAlloc_2534_, 4, v_l_2462_);
v___x_2521_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
v_isSharedCheck_2528_ = !lean_is_exclusive(v_l_2309_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; lean_object* v_unused_2530_; lean_object* v_unused_2531_; lean_object* v_unused_2532_; lean_object* v_unused_2533_; 
v_unused_2529_ = lean_ctor_get(v_l_2309_, 4);
lean_dec(v_unused_2529_);
v_unused_2530_ = lean_ctor_get(v_l_2309_, 3);
lean_dec(v_unused_2530_);
v_unused_2531_ = lean_ctor_get(v_l_2309_, 2);
lean_dec(v_unused_2531_);
v_unused_2532_ = lean_ctor_get(v_l_2309_, 1);
lean_dec(v_unused_2532_);
v_unused_2533_ = lean_ctor_get(v_l_2309_, 0);
lean_dec(v_unused_2533_);
v___x_2523_ = v_l_2309_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_dec(v_l_2309_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 4, v_r_2463_);
lean_ctor_set(v___x_2523_, 3, v___x_2521_);
lean_ctor_set(v___x_2523_, 2, v_v_2461_);
lean_ctor_set(v___x_2523_, 1, v_k_2460_);
lean_ctor_set(v___x_2523_, 0, v___x_2518_);
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v_k_2460_);
lean_ctor_set(v_reuseFailAlloc_2527_, 2, v_v_2461_);
lean_ctor_set(v_reuseFailAlloc_2527_, 3, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2527_, 4, v_r_2463_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2541_; 
v_l_2541_ = lean_ctor_get(v_impl_2456_, 3);
lean_inc(v_l_2541_);
if (lean_obj_tag(v_l_2541_) == 0)
{
lean_object* v_r_2542_; lean_object* v_k_2543_; lean_object* v_v_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2567_; 
v_r_2542_ = lean_ctor_get(v_impl_2456_, 4);
v_k_2543_ = lean_ctor_get(v_impl_2456_, 1);
v_v_2544_ = lean_ctor_get(v_impl_2456_, 2);
v_isSharedCheck_2567_ = !lean_is_exclusive(v_impl_2456_);
if (v_isSharedCheck_2567_ == 0)
{
lean_object* v_unused_2568_; lean_object* v_unused_2569_; 
v_unused_2568_ = lean_ctor_get(v_impl_2456_, 3);
lean_dec(v_unused_2568_);
v_unused_2569_ = lean_ctor_get(v_impl_2456_, 0);
lean_dec(v_unused_2569_);
v___x_2546_ = v_impl_2456_;
v_isShared_2547_ = v_isSharedCheck_2567_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_r_2542_);
lean_inc(v_v_2544_);
lean_inc(v_k_2543_);
lean_dec(v_impl_2456_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2567_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v_k_2548_; lean_object* v_v_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2563_; 
v_k_2548_ = lean_ctor_get(v_l_2541_, 1);
v_v_2549_ = lean_ctor_get(v_l_2541_, 2);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_l_2541_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; lean_object* v_unused_2565_; lean_object* v_unused_2566_; 
v_unused_2564_ = lean_ctor_get(v_l_2541_, 4);
lean_dec(v_unused_2564_);
v_unused_2565_ = lean_ctor_get(v_l_2541_, 3);
lean_dec(v_unused_2565_);
v_unused_2566_ = lean_ctor_get(v_l_2541_, 0);
lean_dec(v_unused_2566_);
v___x_2551_ = v_l_2541_;
v_isShared_2552_ = v_isSharedCheck_2563_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_v_2549_);
lean_inc(v_k_2548_);
lean_dec(v_l_2541_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2563_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2553_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2542_, 2);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 4, v_r_2542_);
lean_ctor_set(v___x_2551_, 3, v_r_2542_);
lean_ctor_set(v___x_2551_, 2, v_v_2308_);
lean_ctor_set(v___x_2551_, 1, v_k_2307_);
lean_ctor_set(v___x_2551_, 0, v___x_2457_);
v___x_2555_ = v___x_2551_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_r_2542_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_r_2542_);
v___x_2555_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2557_; 
lean_inc(v_r_2542_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 3, v_r_2542_);
lean_ctor_set(v___x_2546_, 0, v___x_2457_);
v___x_2557_ = v___x_2546_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_k_2543_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_v_2544_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_r_2542_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v_r_2542_);
v___x_2557_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2559_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 4, v___x_2557_);
lean_ctor_set(v___x_2312_, 3, v___x_2555_);
lean_ctor_set(v___x_2312_, 2, v_v_2549_);
lean_ctor_set(v___x_2312_, 1, v_k_2548_);
lean_ctor_set(v___x_2312_, 0, v___x_2553_);
v___x_2559_ = v___x_2312_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2553_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_k_2548_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v_v_2549_);
lean_ctor_set(v_reuseFailAlloc_2560_, 3, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2560_, 4, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
}
else
{
lean_object* v_r_2570_; 
v_r_2570_ = lean_ctor_get(v_impl_2456_, 4);
lean_inc(v_r_2570_);
if (lean_obj_tag(v_r_2570_) == 0)
{
lean_object* v_k_2571_; lean_object* v_v_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2583_; 
v_k_2571_ = lean_ctor_get(v_impl_2456_, 1);
v_v_2572_ = lean_ctor_get(v_impl_2456_, 2);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_impl_2456_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; lean_object* v_unused_2585_; lean_object* v_unused_2586_; 
v_unused_2584_ = lean_ctor_get(v_impl_2456_, 4);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_impl_2456_, 3);
lean_dec(v_unused_2585_);
v_unused_2586_ = lean_ctor_get(v_impl_2456_, 0);
lean_dec(v_unused_2586_);
v___x_2574_ = v_impl_2456_;
v_isShared_2575_ = v_isSharedCheck_2583_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_v_2572_);
lean_inc(v_k_2571_);
lean_dec(v_impl_2456_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2583_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = lean_unsigned_to_nat(3u);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 4, v_l_2541_);
lean_ctor_set(v___x_2574_, 2, v_v_2308_);
lean_ctor_set(v___x_2574_, 1, v_k_2307_);
lean_ctor_set(v___x_2574_, 0, v___x_2457_);
v___x_2578_ = v___x_2574_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2582_, 3, v_l_2541_);
lean_ctor_set(v_reuseFailAlloc_2582_, 4, v_l_2541_);
v___x_2578_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2580_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 4, v_r_2570_);
lean_ctor_set(v___x_2312_, 3, v___x_2578_);
lean_ctor_set(v___x_2312_, 2, v_v_2572_);
lean_ctor_set(v___x_2312_, 1, v_k_2571_);
lean_ctor_set(v___x_2312_, 0, v___x_2576_);
v___x_2580_ = v___x_2312_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_k_2571_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_v_2572_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v_r_2570_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2587_ = lean_unsigned_to_nat(2u);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 4, v_impl_2456_);
lean_ctor_set(v___x_2312_, 3, v_r_2570_);
lean_ctor_set(v___x_2312_, 0, v___x_2587_);
v___x_2589_ = v___x_2312_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2590_, 3, v_r_2570_);
lean_ctor_set(v_reuseFailAlloc_2590_, 4, v_impl_2456_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
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
lean_object* v___x_2592_; lean_object* v___x_2593_; 
lean_dec_ref(v_cmp_2302_);
v___x_2592_ = lean_unsigned_to_nat(1u);
v___x_2593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
lean_ctor_set(v___x_2593_, 1, v_k_2303_);
lean_ctor_set(v___x_2593_, 2, v_v_2304_);
lean_ctor_set(v___x_2593_, 3, v_t_2305_);
lean_ctor_set(v___x_2593_, 4, v_t_2305_);
return v___x_2593_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(lean_object* v_cmp_2594_, lean_object* v_init_2595_, lean_object* v_x_2596_){
_start:
{
if (lean_obj_tag(v_x_2596_) == 0)
{
lean_object* v_k_2597_; lean_object* v_v_2598_; lean_object* v_l_2599_; lean_object* v_r_2600_; lean_object* v___x_2601_; 
v_k_2597_ = lean_ctor_get(v_x_2596_, 1);
lean_inc(v_k_2597_);
v_v_2598_ = lean_ctor_get(v_x_2596_, 2);
lean_inc(v_v_2598_);
v_l_2599_ = lean_ctor_get(v_x_2596_, 3);
lean_inc(v_l_2599_);
v_r_2600_ = lean_ctor_get(v_x_2596_, 4);
lean_inc(v_r_2600_);
lean_dec_ref_known(v_x_2596_, 5);
lean_inc_ref(v_cmp_2594_);
v___x_2601_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_2594_, v_init_2595_, v_l_2599_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_dec(v_r_2600_);
lean_dec(v_v_2598_);
lean_dec(v_k_2597_);
lean_dec_ref(v_cmp_2594_);
return v___x_2601_;
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2603_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2603_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_v_2598_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v_a_2602_);
lean_dec(v_r_2600_);
lean_dec(v_k_2597_);
lean_dec_ref(v_cmp_2594_);
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
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
lean_object* v_a_2612_; lean_object* v___x_2613_; 
v_a_2612_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2603_, 1);
lean_inc_ref(v_cmp_2594_);
v___x_2613_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_2594_, v_k_2597_, v_a_2612_, v_a_2602_);
v_init_2595_ = v___x_2613_;
v_x_2596_ = v_r_2600_;
goto _start;
}
}
}
else
{
lean_object* v___x_2615_; 
lean_dec_ref(v_cmp_2594_);
v___x_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2615_, 0, v_init_2595_);
return v___x_2615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(lean_object* v_cmp_2616_, lean_object* v_j_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_Json_getObj_x3f(v_j_2617_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec_ref(v_cmp_2616_);
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v_a_2627_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2628_ = lean_box(1);
v___x_2629_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_2616_, v___x_2628_, v_a_2627_);
return v___x_2629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(lean_object* v_x_2633_){
_start:
{
if (lean_obj_tag(v_x_2633_) == 0)
{
lean_object* v___x_2634_; 
v___x_2634_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__0));
return v___x_2634_;
}
else
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__1));
v___x_2636_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(v___x_2635_, v_x_2633_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2653_; 
v_a_2645_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2647_ = v___x_2636_;
v_isShared_2648_ = v_isSharedCheck_2653_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2636_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2653_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2649_, 0, v_a_2645_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(lean_object* v_j_2654_, lean_object* v_k_2655_){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = l_Lean_Json_getObjValD(v_j_2654_, v_k_2655_);
v___x_2657_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(v___x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4___boxed(lean_object* v_j_2658_, lean_object* v_k_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_j_2658_, v_k_2659_);
lean_dec_ref(v_k_2659_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(lean_object* v_j_2661_, lean_object* v_k_2662_){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = l_Lean_Json_getObjValD(v_j_2661_, v_k_2662_);
v___x_2664_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v___x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1___boxed(lean_object* v_j_2665_, lean_object* v_k_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_j_2665_, v_k_2666_);
lean_dec_ref(v_k_2666_);
return v_res_2667_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5(void){
_start:
{
uint8_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = 1;
v___x_2677_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__4));
v___x_2678_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2677_, v___x_2676_);
return v___x_2678_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__6));
v___x_2681_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__5, &l_Lake_Check_instFromJsonConfig_fromJson___closed__5_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5);
v___x_2682_ = lean_string_append(v___x_2681_, v___x_2680_);
return v___x_2682_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9(void){
_start:
{
uint8_t v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2685_ = 1;
v___x_2686_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__8));
v___x_2687_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2686_, v___x_2685_);
return v___x_2687_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2688_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__9, &l_Lake_Check_instFromJsonConfig_fromJson___closed__9_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9);
v___x_2689_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2690_ = lean_string_append(v___x_2689_, v___x_2688_);
return v___x_2690_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2693_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__10, &l_Lake_Check_instFromJsonConfig_fromJson___closed__10_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10);
v___x_2694_ = lean_string_append(v___x_2693_, v___x_2692_);
return v___x_2694_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15(void){
_start:
{
uint8_t v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = 1;
v___x_2699_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__14));
v___x_2700_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2699_, v___x_2698_);
return v___x_2700_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__15, &l_Lake_Check_instFromJsonConfig_fromJson___closed__15_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15);
v___x_2702_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2703_ = lean_string_append(v___x_2702_, v___x_2701_);
return v___x_2703_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2705_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__16, &l_Lake_Check_instFromJsonConfig_fromJson___closed__16_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16);
v___x_2706_ = lean_string_append(v___x_2705_, v___x_2704_);
return v___x_2706_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20(void){
_start:
{
uint8_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2710_ = 1;
v___x_2711_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__19));
v___x_2712_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2711_, v___x_2710_);
return v___x_2712_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__20, &l_Lake_Check_instFromJsonConfig_fromJson___closed__20_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20);
v___x_2714_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2715_ = lean_string_append(v___x_2714_, v___x_2713_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2717_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__21, &l_Lake_Check_instFromJsonConfig_fromJson___closed__21_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21);
v___x_2718_ = lean_string_append(v___x_2717_, v___x_2716_);
return v___x_2718_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25(void){
_start:
{
uint8_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2722_ = 1;
v___x_2723_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__24));
v___x_2724_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2723_, v___x_2722_);
return v___x_2724_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2725_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__25, &l_Lake_Check_instFromJsonConfig_fromJson___closed__25_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25);
v___x_2726_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2727_ = lean_string_append(v___x_2726_, v___x_2725_);
return v___x_2727_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2728_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2729_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__26, &l_Lake_Check_instFromJsonConfig_fromJson___closed__26_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26);
v___x_2730_ = lean_string_append(v___x_2729_, v___x_2728_);
return v___x_2730_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29(void){
_start:
{
uint8_t v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = 1;
v___x_2734_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__28));
v___x_2735_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2734_, v___x_2733_);
return v___x_2735_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__29, &l_Lake_Check_instFromJsonConfig_fromJson___closed__29_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29);
v___x_2737_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2738_ = lean_string_append(v___x_2737_, v___x_2736_);
return v___x_2738_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31(void){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2739_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2740_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__30, &l_Lake_Check_instFromJsonConfig_fromJson___closed__30_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30);
v___x_2741_ = lean_string_append(v___x_2740_, v___x_2739_);
return v___x_2741_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35(void){
_start:
{
uint8_t v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2746_ = 1;
v___x_2747_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__34));
v___x_2748_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2747_, v___x_2746_);
return v___x_2748_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2749_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__35, &l_Lake_Check_instFromJsonConfig_fromJson___closed__35_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35);
v___x_2750_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2751_ = lean_string_append(v___x_2750_, v___x_2749_);
return v___x_2751_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2752_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2753_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__36, &l_Lake_Check_instFromJsonConfig_fromJson___closed__36_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36);
v___x_2754_ = lean_string_append(v___x_2753_, v___x_2752_);
return v___x_2754_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41(void){
_start:
{
uint8_t v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2759_ = 1;
v___x_2760_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__40));
v___x_2761_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2760_, v___x_2759_);
return v___x_2761_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2762_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__41, &l_Lake_Check_instFromJsonConfig_fromJson___closed__41_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41);
v___x_2763_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_2764_ = lean_string_append(v___x_2763_, v___x_2762_);
return v___x_2764_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2765_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_2766_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__42, &l_Lake_Check_instFromJsonConfig_fromJson___closed__42_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42);
v___x_2767_ = lean_string_append(v___x_2766_, v___x_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instFromJsonConfig_fromJson(lean_object* v_json_2768_){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
lean_inc(v_json_2768_);
v___x_2770_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_2768_, v___x_2769_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2780_; 
lean_dec(v_json_2768_);
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2780_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2780_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2775_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__12, &l_Lake_Check_instFromJsonConfig_fromJson___closed__12_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12);
v___x_2776_ = lean_string_append(v___x_2775_, v_a_2771_);
lean_dec(v_a_2771_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 0, v___x_2776_);
v___x_2778_ = v___x_2773_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
else
{
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_json_2768_);
v_a_2781_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2770_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2770_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set_tag(v___x_2783_, 0);
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_a_2789_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2770_, 1);
v___x_2790_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
lean_inc(v_json_2768_);
v___x_2791_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_2768_, v___x_2790_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2801_; 
lean_dec(v_a_2789_);
lean_dec(v_json_2768_);
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2794_ = v___x_2791_;
v_isShared_2795_ = v_isSharedCheck_2801_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2791_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2801_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2796_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__17, &l_Lake_Check_instFromJsonConfig_fromJson___closed__17_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17);
v___x_2797_ = lean_string_append(v___x_2796_, v_a_2792_);
lean_dec(v_a_2792_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v___x_2797_);
v___x_2799_ = v___x_2794_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
else
{
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_a_2789_);
lean_dec(v_json_2768_);
v_a_2802_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2791_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2791_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set_tag(v___x_2804_, 0);
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v_a_2810_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v___x_2791_, 1);
v___x_2811_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
lean_inc(v_json_2768_);
v___x_2812_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_2768_, v___x_2811_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2822_; 
lean_dec(v_a_2810_);
lean_dec(v_a_2789_);
lean_dec(v_json_2768_);
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2822_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2822_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2820_; 
v___x_2817_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__22, &l_Lake_Check_instFromJsonConfig_fromJson___closed__22_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22);
v___x_2818_ = lean_string_append(v___x_2817_, v_a_2813_);
lean_dec(v_a_2813_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2818_);
v___x_2820_ = v___x_2815_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
else
{
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec(v_a_2810_);
lean_dec(v_a_2789_);
lean_dec(v_json_2768_);
v_a_2823_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2812_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2812_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set_tag(v___x_2825_, 0);
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v_a_2831_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2812_, 1);
v___x_2832_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
lean_inc(v_json_2768_);
v___x_2833_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_json_2768_, v___x_2832_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2843_; 
lean_dec(v_a_2831_);
lean_dec(v_a_2810_);
lean_dec(v_a_2789_);
lean_dec(v_json_2768_);
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2843_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2843_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2838_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__27, &l_Lake_Check_instFromJsonConfig_fromJson___closed__27_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27);
v___x_2839_ = lean_string_append(v___x_2838_, v_a_2834_);
lean_dec(v_a_2834_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2839_);
v___x_2841_ = v___x_2836_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
else
{
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec(v_a_2831_);
lean_dec(v_a_2810_);
lean_dec(v_a_2789_);
lean_dec(v_json_2768_);
v_a_2844_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2833_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2833_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set_tag(v___x_2846_, 0);
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_a_2852_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2852_);
lean_dec_ref_known(v___x_2833_, 1);
v___x_2853_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7));
lean_inc(v_json_2768_);
v___x_2854_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_2768_, v___x_2853_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2864_; 
lean_dec(v_a_2852_);
lean_dec(v_a_2831_);
lean_dec(v_a_2810_);
lean_dec(v_a_2789_);
lean_dec(v_json_2768_);
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2864_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2864_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
v___x_2859_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__31, &l_Lake_Check_instFromJsonConfig_fromJson___closed__31_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31);
v___x_2860_ = lean_string_append(v___x_2859_, v_a_2855_);
lean_dec(v_a_2855_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2860_);
v___x_2862_ = v___x_2857_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2860_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
else
{
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v_a_2852_);
lean_dec(v_a_2831_);
lean_dec(v_a_2810_);
lean_dec(v_a_2789_);
lean_dec(v_json_2768_);
v_a_2865_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2854_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2854_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
lean_ctor_set_tag(v___x_2867_, 0);
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_a_2873_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2854_, 1);
v___x_2874_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
lean_inc(v_json_2768_);
v___x_2875_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_json_2768_, v___x_2874_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2885_; 
lean_dec(v_a_2873_);
lean_dec(v_a_2852_);
lean_dec(v_a_2831_);
lean_dec(v_a_2810_);
lean_dec(v_a_2789_);
lean_dec(v_json_2768_);
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2885_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2885_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2880_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__37, &l_Lake_Check_instFromJsonConfig_fromJson___closed__37_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37);
v___x_2881_ = lean_string_append(v___x_2880_, v_a_2876_);
lean_dec(v_a_2876_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2881_);
v___x_2883_ = v___x_2878_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
else
{
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec(v_a_2873_);
lean_dec(v_a_2852_);
lean_dec(v_a_2831_);
lean_dec(v_a_2810_);
lean_dec(v_a_2789_);
lean_dec(v_json_2768_);
v_a_2886_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2875_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2875_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
lean_ctor_set_tag(v___x_2888_, 0);
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_a_2894_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2875_, 1);
v___x_2895_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_2896_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_json_2768_, v___x_2895_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2906_; 
lean_dec(v_a_2894_);
lean_dec(v_a_2873_);
lean_dec(v_a_2852_);
lean_dec(v_a_2831_);
lean_dec(v_a_2810_);
lean_dec(v_a_2789_);
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2899_ = v___x_2896_;
v_isShared_2900_ = v_isSharedCheck_2906_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2896_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2906_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v___x_2901_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__43, &l_Lake_Check_instFromJsonConfig_fromJson___closed__43_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43);
v___x_2902_ = lean_string_append(v___x_2901_, v_a_2897_);
lean_dec(v_a_2897_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v___x_2902_);
v___x_2904_ = v___x_2899_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
else
{
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec(v_a_2894_);
lean_dec(v_a_2873_);
lean_dec(v_a_2852_);
lean_dec(v_a_2831_);
lean_dec(v_a_2810_);
lean_dec(v_a_2789_);
v_a_2907_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2896_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2896_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set_tag(v___x_2909_, 0);
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2923_; 
v_a_2915_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2917_ = v___x_2896_;
v_isShared_2918_ = v_isSharedCheck_2923_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2896_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2923_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2919_; lean_object* v___x_2921_; 
v___x_2919_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2919_, 0, v_a_2789_);
lean_ctor_set(v___x_2919_, 1, v_a_2810_);
lean_ctor_set(v___x_2919_, 2, v_a_2831_);
lean_ctor_set(v___x_2919_, 3, v_a_2852_);
lean_ctor_set(v___x_2919_, 4, v_a_2873_);
lean_ctor_set(v___x_2919_, 5, v_a_2894_);
lean_ctor_set(v___x_2919_, 6, v_a_2915_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v___x_2919_);
v___x_2921_ = v___x_2917_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2919_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10(lean_object* v_cmp_2924_, lean_object* v_00_u03b2_2925_, lean_object* v_k_2926_, lean_object* v_v_2927_, lean_object* v_t_2928_, lean_object* v_hl_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_2924_, v_k_2926_, v_v_2927_, v_t_2928_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(lean_object* v_k_2933_, lean_object* v_x_2934_){
_start:
{
if (lean_obj_tag(v_x_2934_) == 0)
{
lean_object* v___x_2935_; 
lean_dec_ref(v_k_2933_);
v___x_2935_ = lean_box(0);
return v___x_2935_;
}
else
{
lean_object* v_val_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_val_2936_ = lean_ctor_get(v_x_2934_, 0);
v___x_2937_ = lean_alloc_ctor(1, 0, 1);
v___x_2938_ = lean_unbox(v_val_2936_);
lean_ctor_set_uint8(v___x_2937_, 0, v___x_2938_);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v_k_2933_);
lean_ctor_set(v___x_2939_, 1, v___x_2937_);
v___x_2940_ = lean_box(0);
v___x_2941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2939_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
return v___x_2941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2___boxed(lean_object* v_k_2942_, lean_object* v_x_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v_k_2942_, v_x_2943_);
lean_dec(v_x_2943_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(size_t v_sz_2945_, size_t v_i_2946_, lean_object* v_bs_2947_){
_start:
{
uint8_t v___x_2948_; 
v___x_2948_ = lean_usize_dec_lt(v_i_2946_, v_sz_2945_);
if (v___x_2948_ == 0)
{
return v_bs_2947_;
}
else
{
lean_object* v_v_2949_; lean_object* v___x_2950_; lean_object* v_bs_x27_2951_; lean_object* v___x_2952_; size_t v___x_2953_; size_t v___x_2954_; lean_object* v___x_2955_; 
v_v_2949_ = lean_array_uget(v_bs_2947_, v_i_2946_);
v___x_2950_ = lean_unsigned_to_nat(0u);
v_bs_x27_2951_ = lean_array_uset(v_bs_2947_, v_i_2946_, v___x_2950_);
v___x_2952_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2952_, 0, v_v_2949_);
v___x_2953_ = ((size_t)1ULL);
v___x_2954_ = lean_usize_add(v_i_2946_, v___x_2953_);
v___x_2955_ = lean_array_uset(v_bs_x27_2951_, v_i_2946_, v___x_2952_);
v_i_2946_ = v___x_2954_;
v_bs_2947_ = v___x_2955_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0___boxed(lean_object* v_sz_2957_, lean_object* v_i_2958_, lean_object* v_bs_2959_){
_start:
{
size_t v_sz_boxed_2960_; size_t v_i_boxed_2961_; lean_object* v_res_2962_; 
v_sz_boxed_2960_ = lean_unbox_usize(v_sz_2957_);
lean_dec(v_sz_2957_);
v_i_boxed_2961_ = lean_unbox_usize(v_i_2958_);
lean_dec(v_i_2958_);
v_res_2962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_boxed_2960_, v_i_boxed_2961_, v_bs_2959_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(lean_object* v_a_2963_){
_start:
{
size_t v_sz_2964_; size_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_sz_2964_ = lean_array_size(v_a_2963_);
v___x_2965_ = ((size_t)0ULL);
v___x_2966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_2964_, v___x_2965_, v_a_2963_);
v___x_2967_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(lean_object* v_x_2968_){
_start:
{
if (lean_obj_tag(v_x_2968_) == 0)
{
lean_object* v___x_2969_; 
v___x_2969_ = lean_box(0);
return v___x_2969_;
}
else
{
lean_object* v_val_2970_; lean_object* v___x_2971_; 
v_val_2970_ = lean_ctor_get(v_x_2968_, 0);
lean_inc(v_val_2970_);
lean_dec_ref_known(v_x_2968_, 1);
v___x_2971_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_val_2970_);
return v___x_2971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
if (lean_obj_tag(v_a_2972_) == 0)
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_array_to_list(v_a_2973_);
return v___x_2974_;
}
else
{
lean_object* v_head_2975_; lean_object* v_tail_2976_; lean_object* v___x_2977_; 
v_head_2975_ = lean_ctor_get(v_a_2972_, 0);
lean_inc(v_head_2975_);
v_tail_2976_ = lean_ctor_get(v_a_2972_, 1);
lean_inc(v_tail_2976_);
lean_dec_ref_known(v_a_2972_, 2);
v___x_2977_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2973_, v_head_2975_);
v_a_2972_ = v_tail_2976_;
v_a_2973_ = v___x_2977_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(lean_object* v_t_2979_){
_start:
{
if (lean_obj_tag(v_t_2979_) == 0)
{
lean_object* v_size_2980_; lean_object* v_k_2981_; lean_object* v_v_2982_; lean_object* v_l_2983_; lean_object* v_r_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2994_; 
v_size_2980_ = lean_ctor_get(v_t_2979_, 0);
v_k_2981_ = lean_ctor_get(v_t_2979_, 1);
v_v_2982_ = lean_ctor_get(v_t_2979_, 2);
v_l_2983_ = lean_ctor_get(v_t_2979_, 3);
v_r_2984_ = lean_ctor_get(v_t_2979_, 4);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_t_2979_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2986_ = v_t_2979_;
v_isShared_2987_ = v_isSharedCheck_2994_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_r_2984_);
lean_inc(v_l_2983_);
lean_inc(v_v_2982_);
lean_inc(v_k_2981_);
lean_inc(v_size_2980_);
lean_dec(v_t_2979_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2994_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2992_; 
v___x_2988_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_v_2982_);
v___x_2989_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_l_2983_);
v___x_2990_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_r_2984_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 4, v___x_2990_);
lean_ctor_set(v___x_2986_, 3, v___x_2989_);
lean_ctor_set(v___x_2986_, 2, v___x_2988_);
v___x_2992_ = v___x_2986_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_size_2980_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_k_2981_);
lean_ctor_set(v_reuseFailAlloc_2993_, 2, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_2993_, 3, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_2993_, 4, v___x_2990_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
else
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_box(1);
return v___x_2995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(lean_object* v_map_2996_){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_map_2996_);
v___x_2998_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(lean_object* v_k_2999_, lean_object* v_x_3000_){
_start:
{
if (lean_obj_tag(v_x_3000_) == 0)
{
lean_object* v___x_3001_; 
lean_dec_ref(v_k_2999_);
v___x_3001_ = lean_box(0);
return v___x_3001_;
}
else
{
lean_object* v_val_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_val_3002_ = lean_ctor_get(v_x_3000_, 0);
lean_inc(v_val_3002_);
lean_dec_ref_known(v_x_3000_, 1);
v___x_3003_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(v_val_3002_);
v___x_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3004_, 0, v_k_2999_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = lean_box(0);
v___x_3006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3004_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
return v___x_3006_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instToJsonConfig_toJson(lean_object* v_x_3009_){
_start:
{
lean_object* v_challenge__module_3010_; lean_object* v_solution__module_3011_; lean_object* v_theorem__names_3012_; lean_object* v_definition__names_3013_; lean_object* v_permitted__axioms_3014_; lean_object* v_enable__nanoda_x3f_3015_; lean_object* v_external__kernels_x3f_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v_challenge__module_3010_ = lean_ctor_get(v_x_3009_, 0);
lean_inc_ref(v_challenge__module_3010_);
v_solution__module_3011_ = lean_ctor_get(v_x_3009_, 1);
lean_inc_ref(v_solution__module_3011_);
v_theorem__names_3012_ = lean_ctor_get(v_x_3009_, 2);
lean_inc_ref(v_theorem__names_3012_);
v_definition__names_3013_ = lean_ctor_get(v_x_3009_, 3);
lean_inc(v_definition__names_3013_);
v_permitted__axioms_3014_ = lean_ctor_get(v_x_3009_, 4);
lean_inc_ref(v_permitted__axioms_3014_);
v_enable__nanoda_x3f_3015_ = lean_ctor_get(v_x_3009_, 5);
lean_inc(v_enable__nanoda_x3f_3015_);
v_external__kernels_x3f_3016_ = lean_ctor_get(v_x_3009_, 6);
lean_inc(v_external__kernels_x3f_3016_);
lean_dec_ref(v_x_3009_);
v___x_3017_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
v___x_3018_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3018_, 0, v_challenge__module_3010_);
v___x_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3017_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = lean_box(0);
v___x_3021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
v___x_3022_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
v___x_3023_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3023_, 0, v_solution__module_3011_);
v___x_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3022_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
lean_ctor_set(v___x_3025_, 1, v___x_3020_);
v___x_3026_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
v___x_3027_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_theorem__names_3012_);
v___x_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3026_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v___x_3020_);
v___x_3030_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
v___x_3031_ = l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(v_definition__names_3013_);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set(v___x_3033_, 1, v___x_3020_);
v___x_3034_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7));
v___x_3035_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_permitted__axioms_3014_);
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3020_);
v___x_3038_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
v___x_3039_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v___x_3038_, v_enable__nanoda_x3f_3015_);
lean_dec(v_enable__nanoda_x3f_3015_);
v___x_3040_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_3041_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(v___x_3040_, v_external__kernels_x3f_3016_);
v___x_3042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
lean_ctor_set(v___x_3042_, 1, v___x_3020_);
v___x_3043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3039_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3037_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3033_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3029_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3025_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3021_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = ((lean_object*)(l_Lake_Check_instToJsonConfig_toJson___closed__0));
v___x_3050_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(v___x_3048_, v___x_3049_);
v___x_3051_ = l_Lean_Json_mkObj(v___x_3050_);
lean_dec(v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(lean_object* v_x_3060_, lean_object* v_x_3061_){
_start:
{
if (lean_obj_tag(v_x_3060_) == 0)
{
lean_object* v___x_3062_; 
v___x_3062_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3062_;
}
else
{
lean_object* v_val_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v_val_3063_ = lean_ctor_get(v_x_3060_, 0);
v___x_3064_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3065_ = lean_unbox(v_val_3063_);
v___x_3066_ = l_Bool_repr___redArg(v___x_3065_);
v___x_3067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3064_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = l_Repr_addAppParen(v___x_3067_, v_x_3061_);
return v___x_3068_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___boxed(lean_object* v_x_3069_, lean_object* v_x_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_x_3069_, v_x_3070_);
lean_dec(v_x_3070_);
lean_dec(v_x_3069_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_Check_instReprConfig_repr_spec__4(lean_object* v_a_3072_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = lean_nat_to_int(v_a_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(lean_object* v_x_3074_, lean_object* v_x_3075_, lean_object* v_x_3076_){
_start:
{
if (lean_obj_tag(v_x_3076_) == 0)
{
lean_dec(v_x_3074_);
return v_x_3075_;
}
else
{
lean_object* v_head_3077_; lean_object* v_tail_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3089_; 
v_head_3077_ = lean_ctor_get(v_x_3076_, 0);
v_tail_3078_ = lean_ctor_get(v_x_3076_, 1);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_x_3076_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3080_ = v_x_3076_;
v_isShared_3081_ = v_isSharedCheck_3089_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_tail_3078_);
lean_inc(v_head_3077_);
lean_dec(v_x_3076_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3089_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
lean_inc(v_x_3074_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set_tag(v___x_3080_, 5);
lean_ctor_set(v___x_3080_, 1, v_x_3074_);
lean_ctor_set(v___x_3080_, 0, v_x_3075_);
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_x_3075_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_x_3074_);
v___x_3083_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = l_String_quote(v_head_3077_);
v___x_3085_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
v___x_3086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3083_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
v_x_3075_ = v___x_3086_;
v_x_3076_ = v_tail_3078_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_3090_, lean_object* v_x_3091_, lean_object* v_x_3092_){
_start:
{
if (lean_obj_tag(v_x_3092_) == 0)
{
lean_dec(v_x_3090_);
return v_x_3091_;
}
else
{
lean_object* v_head_3093_; lean_object* v_tail_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3105_; 
v_head_3093_ = lean_ctor_get(v_x_3092_, 0);
v_tail_3094_ = lean_ctor_get(v_x_3092_, 1);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_x_3092_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3096_ = v_x_3092_;
v_isShared_3097_ = v_isSharedCheck_3105_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_tail_3094_);
lean_inc(v_head_3093_);
lean_dec(v_x_3092_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3105_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
lean_inc(v_x_3090_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set_tag(v___x_3096_, 5);
lean_ctor_set(v___x_3096_, 1, v_x_3090_);
lean_ctor_set(v___x_3096_, 0, v_x_3091_);
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_x_3091_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_x_3090_);
v___x_3099_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3100_ = l_String_quote(v_head_3093_);
v___x_3101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
v___x_3102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3099_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(v_x_3090_, v___x_3102_, v_tail_3094_);
return v___x_3103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(lean_object* v___y_3106_){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = l_String_quote(v___y_3106_);
v___x_3108_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(lean_object* v_x_3109_, lean_object* v_x_3110_){
_start:
{
if (lean_obj_tag(v_x_3109_) == 0)
{
lean_object* v___x_3111_; 
lean_dec(v_x_3110_);
v___x_3111_ = lean_box(0);
return v___x_3111_;
}
else
{
lean_object* v_tail_3112_; 
v_tail_3112_ = lean_ctor_get(v_x_3109_, 1);
if (lean_obj_tag(v_tail_3112_) == 0)
{
lean_object* v_head_3113_; lean_object* v___x_3114_; 
lean_dec(v_x_3110_);
v_head_3113_ = lean_ctor_get(v_x_3109_, 0);
lean_inc(v_head_3113_);
lean_dec_ref_known(v_x_3109_, 2);
v___x_3114_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3113_);
return v___x_3114_;
}
else
{
lean_object* v_head_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_inc(v_tail_3112_);
v_head_3115_ = lean_ctor_get(v_x_3109_, 0);
lean_inc(v_head_3115_);
lean_dec_ref_known(v_x_3109_, 2);
v___x_3116_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3115_);
v___x_3117_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(v_x_3110_, v___x_3116_, v_tail_3112_);
return v___x_3117_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__0));
v___x_3126_ = lean_string_length(v___x_3125_);
return v___x_3126_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4);
v___x_3128_ = lean_nat_to_int(v___x_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(lean_object* v_xs_3136_){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3137_ = lean_array_get_size(v_xs_3136_);
v___x_3138_ = lean_unsigned_to_nat(0u);
v___x_3139_ = lean_nat_dec_eq(v___x_3137_, v___x_3138_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3140_ = lean_array_to_list(v_xs_3136_);
v___x_3141_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3142_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(v___x_3140_, v___x_3141_);
v___x_3143_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5);
v___x_3144_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__6));
v___x_3145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
lean_ctor_set(v___x_3145_, 1, v___x_3142_);
v___x_3146_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_3147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3145_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3143_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = l_Std_Format_fill(v___x_3148_);
return v___x_3149_;
}
else
{
lean_object* v___x_3150_; 
lean_dec_ref(v_xs_3136_);
v___x_3150_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__9));
return v___x_3150_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(lean_object* v_x_3151_, lean_object* v_x_3152_){
_start:
{
if (lean_obj_tag(v_x_3151_) == 0)
{
lean_object* v___x_3153_; 
v___x_3153_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3153_;
}
else
{
lean_object* v_val_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v_val_3154_ = lean_ctor_get(v_x_3151_, 0);
lean_inc(v_val_3154_);
lean_dec_ref_known(v_x_3151_, 1);
v___x_3155_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3156_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_val_3154_);
v___x_3157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3155_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = l_Repr_addAppParen(v___x_3157_, v_x_3152_);
return v___x_3158_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1___boxed(lean_object* v_x_3159_, lean_object* v_x_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_x_3159_, v_x_3160_);
lean_dec(v_x_3160_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(lean_object* v_init_3162_, lean_object* v_x_3163_){
_start:
{
if (lean_obj_tag(v_x_3163_) == 0)
{
lean_object* v_k_3164_; lean_object* v_v_3165_; lean_object* v_l_3166_; lean_object* v_r_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v_k_3164_ = lean_ctor_get(v_x_3163_, 1);
v_v_3165_ = lean_ctor_get(v_x_3163_, 2);
v_l_3166_ = lean_ctor_get(v_x_3163_, 3);
v_r_3167_ = lean_ctor_get(v_x_3163_, 4);
v___x_3168_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_3162_, v_r_3167_);
lean_inc(v_v_3165_);
lean_inc(v_k_3164_);
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v_k_3164_);
lean_ctor_set(v___x_3169_, 1, v_v_3165_);
v___x_3170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3168_);
v_init_3162_ = v___x_3170_;
v_x_3163_ = v_l_3166_;
goto _start;
}
else
{
return v_init_3162_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4___boxed(lean_object* v_init_3172_, lean_object* v_x_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_3172_, v_x_3173_);
lean_dec(v_x_3173_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(lean_object* v_x_3175_, lean_object* v_x_3176_, lean_object* v_x_3177_){
_start:
{
if (lean_obj_tag(v_x_3177_) == 0)
{
lean_dec(v_x_3175_);
return v_x_3176_;
}
else
{
lean_object* v_head_3178_; lean_object* v_tail_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3188_; 
v_head_3178_ = lean_ctor_get(v_x_3177_, 0);
v_tail_3179_ = lean_ctor_get(v_x_3177_, 1);
v_isSharedCheck_3188_ = !lean_is_exclusive(v_x_3177_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3181_ = v_x_3177_;
v_isShared_3182_ = v_isSharedCheck_3188_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_tail_3179_);
lean_inc(v_head_3178_);
lean_dec(v_x_3177_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3188_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
lean_inc(v_x_3175_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set_tag(v___x_3181_, 5);
lean_ctor_set(v___x_3181_, 1, v_x_3175_);
lean_ctor_set(v___x_3181_, 0, v_x_3176_);
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_x_3176_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_x_3175_);
v___x_3184_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
lean_object* v___x_3185_; 
v___x_3185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
lean_ctor_set(v___x_3185_, 1, v_head_3178_);
v_x_3176_ = v___x_3185_;
v_x_3177_ = v_tail_3179_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(lean_object* v_x_3189_, lean_object* v_x_3190_){
_start:
{
if (lean_obj_tag(v_x_3189_) == 0)
{
lean_object* v___x_3191_; 
lean_dec(v_x_3190_);
v___x_3191_ = lean_box(0);
return v___x_3191_;
}
else
{
lean_object* v_tail_3192_; 
v_tail_3192_ = lean_ctor_get(v_x_3189_, 1);
if (lean_obj_tag(v_tail_3192_) == 0)
{
lean_object* v_head_3193_; 
lean_dec(v_x_3190_);
v_head_3193_ = lean_ctor_get(v_x_3189_, 0);
lean_inc(v_head_3193_);
lean_dec_ref_known(v_x_3189_, 2);
return v_head_3193_;
}
else
{
lean_object* v_head_3194_; lean_object* v___x_3195_; 
lean_inc(v_tail_3192_);
v_head_3194_ = lean_ctor_get(v_x_3189_, 0);
lean_inc(v_head_3194_);
lean_dec_ref_known(v_x_3189_, 2);
v___x_3195_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(v_x_3190_, v_head_3194_, v_tail_3192_);
return v___x_3195_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__0));
v___x_3199_ = lean_string_length(v___x_3198_);
return v___x_3199_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2);
v___x_3201_ = lean_nat_to_int(v___x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(lean_object* v_x_3206_){
_start:
{
lean_object* v_fst_3207_; lean_object* v_snd_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3231_; 
v_fst_3207_ = lean_ctor_get(v_x_3206_, 0);
v_snd_3208_ = lean_ctor_get(v_x_3206_, 1);
v_isSharedCheck_3231_ = !lean_is_exclusive(v_x_3206_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3210_ = v_x_3206_;
v_isShared_3211_ = v_isSharedCheck_3231_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_snd_3208_);
lean_inc(v_fst_3207_);
lean_dec(v_x_3206_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3231_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3212_ = l_String_quote(v_fst_3207_);
v___x_3213_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
v___x_3214_ = lean_box(0);
if (v_isShared_3211_ == 0)
{
lean_ctor_set_tag(v___x_3210_, 1);
lean_ctor_set(v___x_3210_, 1, v___x_3214_);
lean_ctor_set(v___x_3210_, 0, v___x_3213_);
v___x_3216_ = v___x_3210_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; lean_object* v___x_3229_; 
v___x_3217_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_snd_3208_);
v___x_3218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
lean_ctor_set(v___x_3218_, 1, v___x_3216_);
v___x_3219_ = l_List_reverse___redArg(v___x_3218_);
v___x_3220_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3221_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(v___x_3219_, v___x_3220_);
v___x_3222_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3);
v___x_3223_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__4));
v___x_3224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v___x_3221_);
v___x_3225_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__5));
v___x_3226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3224_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3222_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = 0;
v___x_3229_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3229_, 0, v___x_3227_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*1, v___x_3228_);
return v___x_3229_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(lean_object* v_x_3232_, lean_object* v_x_3233_, lean_object* v_x_3234_){
_start:
{
if (lean_obj_tag(v_x_3234_) == 0)
{
lean_dec(v_x_3232_);
return v_x_3233_;
}
else
{
lean_object* v_head_3235_; lean_object* v_tail_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3246_; 
v_head_3235_ = lean_ctor_get(v_x_3234_, 0);
v_tail_3236_ = lean_ctor_get(v_x_3234_, 1);
v_isSharedCheck_3246_ = !lean_is_exclusive(v_x_3234_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3238_ = v_x_3234_;
v_isShared_3239_ = v_isSharedCheck_3246_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_tail_3236_);
lean_inc(v_head_3235_);
lean_dec(v_x_3234_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3246_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
lean_inc(v_x_3232_);
if (v_isShared_3239_ == 0)
{
lean_ctor_set_tag(v___x_3238_, 5);
lean_ctor_set(v___x_3238_, 1, v_x_3232_);
lean_ctor_set(v___x_3238_, 0, v_x_3233_);
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_x_3233_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_x_3232_);
v___x_3241_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3235_);
v___x_3243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v_x_3233_ = v___x_3243_;
v_x_3234_ = v_tail_3236_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(lean_object* v_x_3247_, lean_object* v_x_3248_, lean_object* v_x_3249_){
_start:
{
if (lean_obj_tag(v_x_3249_) == 0)
{
lean_dec(v_x_3247_);
return v_x_3248_;
}
else
{
lean_object* v_head_3250_; lean_object* v_tail_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3261_; 
v_head_3250_ = lean_ctor_get(v_x_3249_, 0);
v_tail_3251_ = lean_ctor_get(v_x_3249_, 1);
v_isSharedCheck_3261_ = !lean_is_exclusive(v_x_3249_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3253_ = v_x_3249_;
v_isShared_3254_ = v_isSharedCheck_3261_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_tail_3251_);
lean_inc(v_head_3250_);
lean_dec(v_x_3249_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3261_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
lean_inc(v_x_3247_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set_tag(v___x_3253_, 5);
lean_ctor_set(v___x_3253_, 1, v_x_3247_);
lean_ctor_set(v___x_3253_, 0, v_x_3248_);
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_x_3248_);
lean_ctor_set(v_reuseFailAlloc_3260_, 1, v_x_3247_);
v___x_3256_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3250_);
v___x_3258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3256_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v___x_3259_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(v_x_3247_, v___x_3258_, v_tail_3251_);
return v___x_3259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(lean_object* v_x_3262_, lean_object* v_x_3263_){
_start:
{
if (lean_obj_tag(v_x_3262_) == 0)
{
lean_object* v___x_3264_; 
lean_dec(v_x_3263_);
v___x_3264_ = lean_box(0);
return v___x_3264_;
}
else
{
lean_object* v_tail_3265_; 
v_tail_3265_ = lean_ctor_get(v_x_3262_, 1);
if (lean_obj_tag(v_tail_3265_) == 0)
{
lean_object* v_head_3266_; lean_object* v___x_3267_; 
lean_dec(v_x_3263_);
v_head_3266_ = lean_ctor_get(v_x_3262_, 0);
lean_inc(v_head_3266_);
lean_dec_ref_known(v_x_3262_, 2);
v___x_3267_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3266_);
return v___x_3267_;
}
else
{
lean_object* v_head_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
lean_inc(v_tail_3265_);
v_head_3268_ = lean_ctor_get(v_x_3262_, 0);
lean_inc(v_head_3268_);
lean_dec_ref_known(v_x_3262_, 2);
v___x_3269_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3268_);
v___x_3270_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(v_x_3263_, v___x_3269_, v_tail_3265_);
return v___x_3270_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_safeExport_spec__0___closed__1));
v___x_3274_ = lean_string_length(v___x_3273_);
return v___x_3274_;
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1);
v___x_3276_ = lean_nat_to_int(v___x_3275_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(lean_object* v_a_3279_){
_start:
{
if (lean_obj_tag(v_a_3279_) == 0)
{
lean_object* v___x_3280_; 
v___x_3280_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0));
return v___x_3280_;
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; uint8_t v___x_3289_; lean_object* v___x_3290_; 
v___x_3281_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3282_ = l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(v_a_3279_, v___x_3281_);
v___x_3283_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2);
v___x_3284_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__3));
v___x_3285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
lean_ctor_set(v___x_3285_, 1, v___x_3282_);
v___x_3286_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_3287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3283_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = 0;
v___x_3290_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set_uint8(v___x_3290_, sizeof(void*)*1, v___x_3289_);
return v___x_3290_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(lean_object* v_x_3294_, lean_object* v_x_3295_){
_start:
{
if (lean_obj_tag(v_x_3294_) == 0)
{
lean_object* v___x_3296_; 
v___x_3296_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3296_;
}
else
{
lean_object* v_val_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_val_3297_ = lean_ctor_get(v_x_3294_, 0);
v___x_3298_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3299_ = lean_unsigned_to_nat(1024u);
v___x_3300_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__1));
v___x_3301_ = lean_box(0);
v___x_3302_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v___x_3301_, v_val_3297_);
v___x_3303_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v___x_3302_);
v___x_3304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3300_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = l_Repr_addAppParen(v___x_3304_, v___x_3299_);
v___x_3306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3298_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = l_Repr_addAppParen(v___x_3306_, v_x_3295_);
return v___x_3307_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___boxed(lean_object* v_x_3308_, lean_object* v_x_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_x_3308_, v_x_3309_);
lean_dec(v_x_3309_);
lean_dec(v_x_3308_);
return v_res_3310_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = lean_unsigned_to_nat(20u);
v___x_3324_ = lean_nat_to_int(v___x_3323_);
return v___x_3324_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = lean_unsigned_to_nat(19u);
v___x_3328_ = lean_nat_to_int(v___x_3327_);
return v___x_3328_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = lean_unsigned_to_nat(17u);
v___x_3332_ = lean_nat_to_int(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = lean_unsigned_to_nat(18u);
v___x_3340_ = lean_nat_to_int(v___x_3339_);
return v___x_3340_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = lean_unsigned_to_nat(21u);
v___x_3344_ = lean_nat_to_int(v___x_3343_);
return v___x_3344_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__0));
v___x_3347_ = lean_string_length(v___x_3346_);
return v___x_3347_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__18, &l_Lake_Check_instReprConfig_repr___redArg___closed__18_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18);
v___x_3349_ = lean_nat_to_int(v___x_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___redArg(lean_object* v_x_3354_){
_start:
{
lean_object* v_challenge__module_3355_; lean_object* v_solution__module_3356_; lean_object* v_theorem__names_3357_; lean_object* v_definition__names_3358_; lean_object* v_permitted__axioms_3359_; lean_object* v_enable__nanoda_x3f_3360_; lean_object* v_external__kernels_x3f_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v_challenge__module_3355_ = lean_ctor_get(v_x_3354_, 0);
lean_inc_ref(v_challenge__module_3355_);
v_solution__module_3356_ = lean_ctor_get(v_x_3354_, 1);
lean_inc_ref(v_solution__module_3356_);
v_theorem__names_3357_ = lean_ctor_get(v_x_3354_, 2);
lean_inc_ref(v_theorem__names_3357_);
v_definition__names_3358_ = lean_ctor_get(v_x_3354_, 3);
lean_inc(v_definition__names_3358_);
v_permitted__axioms_3359_ = lean_ctor_get(v_x_3354_, 4);
lean_inc_ref(v_permitted__axioms_3359_);
v_enable__nanoda_x3f_3360_ = lean_ctor_get(v_x_3354_, 5);
lean_inc(v_enable__nanoda_x3f_3360_);
v_external__kernels_x3f_3361_ = lean_ctor_get(v_x_3354_, 6);
lean_inc(v_external__kernels_x3f_3361_);
lean_dec_ref(v_x_3354_);
v___x_3362_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__4));
v___x_3363_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__5));
v___x_3364_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__6, &l_Lake_Check_instReprConfig_repr___redArg___closed__6_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6);
v___x_3365_ = l_String_quote(v_challenge__module_3355_);
v___x_3366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
v___x_3367_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3364_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = 0;
v___x_3369_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3369_, 0, v___x_3367_);
lean_ctor_set_uint8(v___x_3369_, sizeof(void*)*1, v___x_3368_);
v___x_3370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3363_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
v___x_3371_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__2));
v___x_3372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3370_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = lean_box(1);
v___x_3374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__7));
v___x_3376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3374_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
lean_ctor_set(v___x_3377_, 1, v___x_3362_);
v___x_3378_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__8, &l_Lake_Check_instReprConfig_repr___redArg___closed__8_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8);
v___x_3379_ = l_String_quote(v_solution__module_3356_);
v___x_3380_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
v___x_3381_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3378_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
lean_ctor_set_uint8(v___x_3382_, sizeof(void*)*1, v___x_3368_);
v___x_3383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3377_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3383_);
lean_ctor_set(v___x_3384_, 1, v___x_3371_);
v___x_3385_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
lean_ctor_set(v___x_3385_, 1, v___x_3373_);
v___x_3386_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__9));
v___x_3387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3385_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
lean_ctor_set(v___x_3388_, 1, v___x_3362_);
v___x_3389_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__10, &l_Lake_Check_instReprConfig_repr___redArg___closed__10_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10);
v___x_3390_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_theorem__names_3357_);
v___x_3391_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3389_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v___x_3392_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*1, v___x_3368_);
v___x_3393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3388_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
lean_ctor_set(v___x_3394_, 1, v___x_3371_);
v___x_3395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v___x_3373_);
v___x_3396_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__11));
v___x_3397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3395_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
v___x_3398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
lean_ctor_set(v___x_3398_, 1, v___x_3362_);
v___x_3399_ = lean_unsigned_to_nat(0u);
v___x_3400_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_definition__names_3358_, v___x_3399_);
v___x_3401_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3364_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set_uint8(v___x_3402_, sizeof(void*)*1, v___x_3368_);
v___x_3403_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3398_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
v___x_3404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
lean_ctor_set(v___x_3404_, 1, v___x_3371_);
v___x_3405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
lean_ctor_set(v___x_3405_, 1, v___x_3373_);
v___x_3406_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__12));
v___x_3407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3405_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___x_3408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
lean_ctor_set(v___x_3408_, 1, v___x_3362_);
v___x_3409_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_permitted__axioms_3359_);
v___x_3410_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3364_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
v___x_3411_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
lean_ctor_set_uint8(v___x_3411_, sizeof(void*)*1, v___x_3368_);
v___x_3412_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3408_);
lean_ctor_set(v___x_3412_, 1, v___x_3411_);
v___x_3413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v___x_3371_);
v___x_3414_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
lean_ctor_set(v___x_3414_, 1, v___x_3373_);
v___x_3415_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__13));
v___x_3416_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3414_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
lean_ctor_set(v___x_3417_, 1, v___x_3362_);
v___x_3418_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__14, &l_Lake_Check_instReprConfig_repr___redArg___closed__14_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14);
v___x_3419_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_enable__nanoda_x3f_3360_, v___x_3399_);
lean_dec(v_enable__nanoda_x3f_3360_);
v___x_3420_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
lean_ctor_set_uint8(v___x_3421_, sizeof(void*)*1, v___x_3368_);
v___x_3422_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3417_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v___x_3423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
lean_ctor_set(v___x_3423_, 1, v___x_3371_);
v___x_3424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
lean_ctor_set(v___x_3424_, 1, v___x_3373_);
v___x_3425_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__15));
v___x_3426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3424_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
lean_ctor_set(v___x_3427_, 1, v___x_3362_);
v___x_3428_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__16, &l_Lake_Check_instReprConfig_repr___redArg___closed__16_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16);
v___x_3429_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_external__kernels_x3f_3361_, v___x_3399_);
lean_dec(v_external__kernels_x3f_3361_);
v___x_3430_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*1, v___x_3368_);
v___x_3432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3427_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__19, &l_Lake_Check_instReprConfig_repr___redArg___closed__19_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19);
v___x_3434_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__20));
v___x_3435_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
lean_ctor_set(v___x_3435_, 1, v___x_3432_);
v___x_3436_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__21));
v___x_3437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3435_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3433_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
lean_ctor_set_uint8(v___x_3439_, sizeof(void*)*1, v___x_3368_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr(lean_object* v_x_3440_, lean_object* v_prec_3441_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Lake_Check_instReprConfig_repr___redArg(v_x_3440_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___boxed(lean_object* v_x_3443_, lean_object* v_prec_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Lake_Check_instReprConfig_repr(v_x_3443_, v_prec_3444_);
lean_dec(v_prec_3444_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(lean_object* v_a_3446_, lean_object* v_n_3447_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v_a_3446_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___boxed(lean_object* v_a_3449_, lean_object* v_n_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(v_a_3449_, v_n_3450_);
lean_dec(v_n_3450_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(lean_object* v_x_3452_, lean_object* v_x_3453_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_x_3452_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___boxed(lean_object* v_x_3455_, lean_object* v_x_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(v_x_3455_, v_x_3456_);
lean_dec(v_x_3456_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(lean_object* v_s_3460_){
_start:
{
uint32_t v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3462_ = 10;
v___x_3463_ = lean_string_push(v_s_3460_, v___x_3462_);
v___x_3464_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_spec__0(v___x_3463_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0___boxed(lean_object* v_s_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v_s_3465_);
return v_res_3467_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1(void){
_start:
{
uint32_t v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = 2;
v___x_3470_ = lean_box_uint32(v___x_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(lean_object* v_msg_3471_){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3473_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_3474_ = lean_string_append(v___x_3473_, v_msg_3471_);
v___x_3475_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_3474_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3483_; 
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3483_ == 0)
{
lean_object* v_unused_3484_; 
v_unused_3484_ = lean_ctor_get(v___x_3475_, 0);
lean_dec(v_unused_3484_);
v___x_3477_ = v___x_3475_;
v_isShared_3478_ = v_isSharedCheck_3483_;
goto v_resetjp_3476_;
}
else
{
lean_dec(v___x_3475_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3483_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3479_; lean_object* v___x_3481_; 
v___x_3479_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1;
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v___x_3479_);
v___x_3481_ = v___x_3477_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3479_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
v_a_3485_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3475_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3475_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed(lean_object* v_msg_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v_msg_3493_);
lean_dec_ref(v_msg_3493_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(lean_object* v_cmd_3499_, lean_object* v_projectDir_3500_){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v___x_3502_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__0));
lean_inc_ref(v_projectDir_3500_);
v___x_3503_ = l_System_FilePath_join(v_projectDir_3500_, v___x_3502_);
v___x_3504_ = l_System_FilePath_pathExists(v___x_3503_);
lean_dec_ref(v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3505_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_3506_ = lean_string_append(v___x_3505_, v_projectDir_3500_);
lean_dec_ref(v_projectDir_3500_);
v___x_3507_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__1));
v___x_3508_ = lean_string_append(v___x_3506_, v___x_3507_);
v___x_3509_ = lean_string_append(v___x_3508_, v_cmd_3499_);
v___x_3510_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__2));
v___x_3511_ = lean_string_append(v___x_3509_, v___x_3510_);
v___x_3512_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3511_);
lean_dec_ref(v___x_3511_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3521_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3521_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3521_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
v___x_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_a_3513_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3517_);
v___x_3519_ = v___x_3515_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
v_a_3522_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3512_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3512_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
lean_dec_ref(v_projectDir_3500_);
v___x_3530_ = lean_box(0);
v___x_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
return v___x_3531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___boxed(lean_object* v_cmd_3532_, lean_object* v_projectDir_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v_cmd_3532_, v_projectDir_3533_);
lean_dec_ref(v_cmd_3532_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext(lean_object* v_cmd_3542_, lean_object* v_lean_3543_, lean_object* v_lake_3544_, lean_object* v_projectDir_3545_){
_start:
{
uint8_t v___x_3547_; 
v___x_3547_ = l_System_Platform_isLinux;
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
lean_dec_ref(v_projectDir_3545_);
lean_dec_ref(v_lean_3543_);
v___x_3548_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__0));
v___x_3549_ = lean_string_append(v___x_3548_, v_cmd_3542_);
v___x_3550_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0));
v___x_3551_ = lean_string_append(v___x_3549_, v___x_3550_);
v___x_3552_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3551_);
lean_dec_ref(v___x_3551_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3561_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3555_ = v___x_3552_;
v_isShared_3556_ = v_isSharedCheck_3561_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3561_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3557_, 0, v_a_3553_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v___x_3557_);
v___x_3559_ = v___x_3555_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
v_a_3562_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3552_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3552_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
else
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___y_3573_; 
v___x_3570_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1));
v___x_3571_ = lean_io_getenv(v___x_3570_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v___x_3669_; 
v___x_3669_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5));
v___y_3573_ = v___x_3669_;
goto v___jp_3572_;
}
else
{
lean_object* v_val_3670_; 
v_val_3670_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_val_3670_);
lean_dec_ref_known(v___x_3571_, 1);
v___y_3573_ = v_val_3670_;
goto v___jp_3572_;
}
v___jp_3572_:
{
lean_object* v___x_3574_; lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3668_; 
lean_inc_ref(v___y_3573_);
v___x_3574_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___y_3573_);
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3577_ = v___x_3574_;
v_isShared_3578_ = v_isSharedCheck_3668_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3668_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
if (lean_obj_tag(v_a_3575_) == 1)
{
lean_object* v_val_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3646_; 
lean_del_object(v___x_3577_);
lean_dec_ref(v___y_3573_);
v_val_3579_ = lean_ctor_get(v_a_3575_, 0);
lean_inc(v_val_3579_);
lean_dec_ref_known(v_a_3575_, 1);
v___x_3580_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2));
v___x_3581_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_3580_);
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3584_ = v___x_3581_;
v_isShared_3585_ = v_isSharedCheck_3646_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3581_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3646_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
if (lean_obj_tag(v_a_3582_) == 1)
{
lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3620_; 
lean_del_object(v___x_3584_);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_a_3582_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; 
v_unused_3621_ = lean_ctor_get(v_a_3582_, 0);
lean_dec(v_unused_3621_);
v___x_3587_ = v_a_3582_;
v_isShared_3588_ = v_isSharedCheck_3620_;
goto v_resetjp_3586_;
}
else
{
lean_dec(v_a_3582_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3620_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3589_; 
v___x_3589_ = lean_io_realpath(v_projectDir_3545_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3611_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3592_ = v___x_3589_;
v_isShared_3593_ = v_isSharedCheck_3611_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3611_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v_binDir_3594_; lean_object* v_lake_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3606_; 
v_binDir_3594_ = lean_ctor_get(v_lean_3543_, 6);
lean_inc_ref(v_binDir_3594_);
lean_dec_ref(v_lean_3543_);
v_lake_3595_ = lean_ctor_get(v_lake_3544_, 5);
v___x_3596_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3));
v___x_3597_ = l_System_FilePath_join(v_binDir_3594_, v___x_3596_);
v___x_3598_ = l_System_FilePath_exeExtension;
v___x_3599_ = l_System_FilePath_addExtension(v___x_3597_, v___x_3598_);
v___x_3600_ = lean_box(0);
v___x_3601_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_3602_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__17));
v___x_3603_ = lean_box(1);
lean_inc_ref(v_lake_3595_);
v___x_3604_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3604_, 0, v_a_3590_);
lean_ctor_set(v___x_3604_, 1, v___x_3600_);
lean_ctor_set(v___x_3604_, 2, v___x_3600_);
lean_ctor_set(v___x_3604_, 3, v___x_3601_);
lean_ctor_set(v___x_3604_, 4, v___x_3601_);
lean_ctor_set(v___x_3604_, 5, v___x_3601_);
lean_ctor_set(v___x_3604_, 6, v___x_3602_);
lean_ctor_set(v___x_3604_, 7, v___x_3602_);
lean_ctor_set(v___x_3604_, 8, v_val_3579_);
lean_ctor_set(v___x_3604_, 9, v_lake_3595_);
lean_ctor_set(v___x_3604_, 10, v___x_3599_);
lean_ctor_set(v___x_3604_, 11, v___x_3603_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 0, v___x_3604_);
v___x_3606_ = v___x_3587_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3608_; 
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v___x_3606_);
v___x_3608_ = v___x_3592_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_del_object(v___x_3587_);
lean_dec(v_val_3579_);
lean_dec_ref(v_lean_3543_);
v_a_3612_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3589_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3589_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
}
else
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
lean_dec(v_a_3582_);
lean_dec(v_val_3579_);
lean_dec_ref(v_projectDir_3545_);
lean_dec_ref(v_lean_3543_);
v___x_3622_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError___closed__0));
v___x_3623_ = lean_string_append(v___x_3622_, v_cmd_3542_);
v___x_3624_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4));
v___x_3625_ = lean_string_append(v___x_3623_, v___x_3624_);
v___x_3626_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3625_);
lean_dec_ref(v___x_3625_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3637_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3629_ = v___x_3626_;
v_isShared_3630_ = v_isSharedCheck_3637_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3637_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v_a_3627_);
v___x_3632_ = v___x_3584_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3634_; 
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3632_);
v___x_3634_ = v___x_3629_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3632_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_del_object(v___x_3584_);
v_a_3638_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3626_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3626_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
}
}
else
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
lean_dec(v_a_3575_);
lean_dec_ref(v_projectDir_3545_);
lean_dec_ref(v_lean_3543_);
v___x_3647_ = l___private_Lake_CLI_Check_0__Lake_Check_missingLandrunError(v_cmd_3542_, v___y_3573_);
lean_dec_ref(v___y_3573_);
v___x_3648_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3647_);
lean_dec_ref(v___x_3647_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3659_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3651_ = v___x_3648_;
v_isShared_3652_ = v_isSharedCheck_3659_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3648_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3659_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 0, v_a_3649_);
v___x_3654_ = v___x_3577_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3649_);
v___x_3654_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3656_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v___x_3654_);
v___x_3656_ = v___x_3651_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_del_object(v___x_3577_);
v_a_3660_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3648_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3648_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___boxed(lean_object* v_cmd_3671_, lean_object* v_lean_3672_, lean_object* v_lake_3673_, lean_object* v_projectDir_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v_cmd_3671_, v_lean_3672_, v_lake_3673_, v_projectDir_3674_);
lean_dec_ref(v_lake_3673_);
lean_dec_ref(v_cmd_3671_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(lean_object* v_init_3683_, lean_object* v_x_3684_){
_start:
{
lean_object* v_d_3687_; 
if (lean_obj_tag(v_x_3684_) == 0)
{
lean_object* v_k_3690_; lean_object* v_v_3691_; lean_object* v_l_3692_; lean_object* v_r_3693_; lean_object* v___x_3694_; 
v_k_3690_ = lean_ctor_get(v_x_3684_, 1);
v_v_3691_ = lean_ctor_get(v_x_3684_, 2);
v_l_3692_ = lean_ctor_get(v_x_3684_, 3);
v_r_3693_ = lean_ctor_get(v_x_3684_, 4);
v___x_3694_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_3683_, v_l_3692_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3694_, 1);
if (lean_obj_tag(v_a_3695_) == 0)
{
lean_object* v_a_3696_; 
v_a_3696_ = lean_ctor_get(v_a_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v_a_3695_, 1);
v_d_3687_ = v_a_3696_;
goto v___jp_3686_;
}
else
{
lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3736_; 
v_isSharedCheck_3736_ = !lean_is_exclusive(v_a_3695_);
if (v_isSharedCheck_3736_ == 0)
{
lean_object* v_unused_3737_; 
v_unused_3737_ = lean_ctor_get(v_a_3695_, 0);
lean_dec(v_unused_3737_);
v___x_3698_ = v_a_3695_;
v_isShared_3699_ = v_isSharedCheck_3736_;
goto v_resetjp_3697_;
}
else
{
lean_dec(v_a_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3736_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3735_; 
v___x_3700_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__17));
v___x_3701_ = lean_unsigned_to_nat(0u);
v___x_3702_ = lean_array_get_borrowed(v___x_3700_, v_v_3691_, v___x_3701_);
lean_inc(v___x_3702_);
v___x_3703_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_3702_);
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3706_ = v___x_3703_;
v_isShared_3707_ = v_isSharedCheck_3735_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3703_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3735_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3708_; 
v___x_3708_ = lean_box(0);
if (lean_obj_tag(v_a_3704_) == 0)
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3709_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_3710_ = lean_string_append(v___x_3709_, v_k_3690_);
v___x_3711_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1));
v___x_3712_ = lean_string_append(v___x_3710_, v___x_3711_);
v___x_3713_ = lean_string_append(v___x_3712_, v___x_3702_);
v___x_3714_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2));
v___x_3715_ = lean_string_append(v___x_3713_, v___x_3714_);
v___x_3716_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3715_);
lean_dec_ref(v___x_3715_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3719_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3717_);
lean_dec_ref_known(v___x_3716_, 1);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 0, v_a_3717_);
v___x_3719_ = v___x_3706_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3717_);
v___x_3719_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3721_; 
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3719_);
v___x_3721_ = v___x_3698_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
lean_ctor_set(v___x_3722_, 1, v___x_3708_);
v_d_3687_ = v___x_3722_;
goto v___jp_3686_;
}
}
}
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_del_object(v___x_3706_);
lean_del_object(v___x_3698_);
v_a_3725_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3716_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3716_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
else
{
lean_object* v___x_3733_; 
lean_dec_ref_known(v_a_3704_, 1);
lean_del_object(v___x_3706_);
lean_del_object(v___x_3698_);
v___x_3733_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v_init_3683_ = v___x_3733_;
v_x_3684_ = v_r_3693_;
goto _start;
}
}
}
}
}
else
{
return v___x_3694_;
}
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3738_, 0, v_init_3683_);
v___x_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
return v___x_3739_;
}
v___jp_3686_:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3688_, 0, v_d_3687_);
v___x_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
return v___x_3689_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___boxed(lean_object* v_init_3740_, lean_object* v_x_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_3740_, v_x_3741_);
lean_dec(v_x_3741_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(lean_object* v_init_3745_, lean_object* v_x_3746_){
_start:
{
lean_object* v_d_3749_; 
if (lean_obj_tag(v_x_3746_) == 0)
{
lean_object* v_k_3752_; lean_object* v_v_3753_; lean_object* v_l_3754_; lean_object* v_r_3755_; lean_object* v___x_3756_; 
v_k_3752_ = lean_ctor_get(v_x_3746_, 1);
v_v_3753_ = lean_ctor_get(v_x_3746_, 2);
v_l_3754_ = lean_ctor_get(v_x_3746_, 3);
v_r_3755_ = lean_ctor_get(v_x_3746_, 4);
v___x_3756_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(v_init_3745_, v_l_3754_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3794_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3794_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3794_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
if (lean_obj_tag(v_a_3757_) == 0)
{
lean_object* v_a_3761_; 
lean_del_object(v___x_3759_);
v_a_3761_ = lean_ctor_get(v_a_3757_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v_a_3757_, 1);
v_d_3749_ = v_a_3761_;
goto v___jp_3748_;
}
else
{
lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3792_; 
v_isSharedCheck_3792_ = !lean_is_exclusive(v_a_3757_);
if (v_isSharedCheck_3792_ == 0)
{
lean_object* v_unused_3793_; 
v_unused_3793_ = lean_ctor_get(v_a_3757_, 0);
lean_dec(v_unused_3793_);
v___x_3763_ = v_a_3757_;
v_isShared_3764_ = v_isSharedCheck_3792_;
goto v_resetjp_3762_;
}
else
{
lean_dec(v_a_3757_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3792_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; uint8_t v___x_3768_; 
v___x_3765_ = lean_box(0);
v___x_3766_ = lean_array_get_size(v_v_3753_);
v___x_3767_ = lean_unsigned_to_nat(0u);
v___x_3768_ = lean_nat_dec_eq(v___x_3766_, v___x_3767_);
if (v___x_3768_ == 0)
{
lean_object* v___x_3769_; 
lean_del_object(v___x_3763_);
lean_del_object(v___x_3759_);
v___x_3769_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v_init_3745_ = v___x_3769_;
v_x_3746_ = v_r_3755_;
goto _start;
}
else
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3771_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_3772_ = lean_string_append(v___x_3771_, v_k_3752_);
v___x_3773_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___closed__0));
v___x_3774_ = lean_string_append(v___x_3772_, v___x_3773_);
v___x_3775_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3774_);
lean_dec_ref(v___x_3774_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3778_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref_known(v___x_3775_, 1);
if (v_isShared_3764_ == 0)
{
lean_ctor_set_tag(v___x_3763_, 0);
lean_ctor_set(v___x_3763_, 0, v_a_3776_);
v___x_3778_ = v___x_3763_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3776_);
v___x_3778_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3780_; 
if (v_isShared_3760_ == 0)
{
lean_ctor_set_tag(v___x_3759_, 1);
lean_ctor_set(v___x_3759_, 0, v___x_3778_);
v___x_3780_ = v___x_3759_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3778_);
v___x_3780_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3780_);
lean_ctor_set(v___x_3781_, 1, v___x_3765_);
v_d_3749_ = v___x_3781_;
goto v___jp_3748_;
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_del_object(v___x_3763_);
lean_del_object(v___x_3759_);
v_a_3784_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3775_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3775_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
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
return v___x_3756_;
}
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3795_, 0, v_init_3745_);
v___x_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
return v___x_3796_;
}
v___jp_3748_:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3750_, 0, v_d_3749_);
v___x_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
return v___x_3751_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___boxed(lean_object* v_init_3797_, lean_object* v_x_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(v_init_3797_, v_x_3798_);
lean_dec(v_x_3798_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(lean_object* v_k_3801_, lean_object* v_v_3802_, lean_object* v_t_3803_){
_start:
{
if (lean_obj_tag(v_t_3803_) == 0)
{
lean_object* v_size_3804_; lean_object* v_k_3805_; lean_object* v_v_3806_; lean_object* v_l_3807_; lean_object* v_r_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_4088_; 
v_size_3804_ = lean_ctor_get(v_t_3803_, 0);
v_k_3805_ = lean_ctor_get(v_t_3803_, 1);
v_v_3806_ = lean_ctor_get(v_t_3803_, 2);
v_l_3807_ = lean_ctor_get(v_t_3803_, 3);
v_r_3808_ = lean_ctor_get(v_t_3803_, 4);
v_isSharedCheck_4088_ = !lean_is_exclusive(v_t_3803_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_3810_ = v_t_3803_;
v_isShared_3811_ = v_isSharedCheck_4088_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_r_3808_);
lean_inc(v_l_3807_);
lean_inc(v_v_3806_);
lean_inc(v_k_3805_);
lean_inc(v_size_3804_);
lean_dec(v_t_3803_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_4088_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
uint8_t v___x_3812_; 
v___x_3812_ = lean_string_compare(v_k_3801_, v_k_3805_);
switch(v___x_3812_)
{
case 0:
{
lean_object* v_impl_3813_; lean_object* v___x_3814_; 
lean_dec(v_size_3804_);
v_impl_3813_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(v_k_3801_, v_v_3802_, v_l_3807_);
v___x_3814_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3808_) == 0)
{
lean_object* v_size_3815_; lean_object* v_size_3816_; lean_object* v_k_3817_; lean_object* v_v_3818_; lean_object* v_l_3819_; lean_object* v_r_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v_size_3815_ = lean_ctor_get(v_r_3808_, 0);
v_size_3816_ = lean_ctor_get(v_impl_3813_, 0);
lean_inc(v_size_3816_);
v_k_3817_ = lean_ctor_get(v_impl_3813_, 1);
lean_inc(v_k_3817_);
v_v_3818_ = lean_ctor_get(v_impl_3813_, 2);
lean_inc(v_v_3818_);
v_l_3819_ = lean_ctor_get(v_impl_3813_, 3);
lean_inc(v_l_3819_);
v_r_3820_ = lean_ctor_get(v_impl_3813_, 4);
lean_inc(v_r_3820_);
v___x_3821_ = lean_unsigned_to_nat(3u);
v___x_3822_ = lean_nat_mul(v___x_3821_, v_size_3815_);
v___x_3823_ = lean_nat_dec_lt(v___x_3822_, v_size_3816_);
lean_dec(v___x_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3827_; 
lean_dec(v_r_3820_);
lean_dec(v_l_3819_);
lean_dec(v_v_3818_);
lean_dec(v_k_3817_);
v___x_3824_ = lean_nat_add(v___x_3814_, v_size_3816_);
lean_dec(v_size_3816_);
v___x_3825_ = lean_nat_add(v___x_3824_, v_size_3815_);
lean_dec(v___x_3824_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 3, v_impl_3813_);
lean_ctor_set(v___x_3810_, 0, v___x_3825_);
v___x_3827_ = v___x_3810_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3825_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_3828_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_3828_, 3, v_impl_3813_);
lean_ctor_set(v_reuseFailAlloc_3828_, 4, v_r_3808_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
else
{
lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3894_; 
v_isSharedCheck_3894_ = !lean_is_exclusive(v_impl_3813_);
if (v_isSharedCheck_3894_ == 0)
{
lean_object* v_unused_3895_; lean_object* v_unused_3896_; lean_object* v_unused_3897_; lean_object* v_unused_3898_; lean_object* v_unused_3899_; 
v_unused_3895_ = lean_ctor_get(v_impl_3813_, 4);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_impl_3813_, 3);
lean_dec(v_unused_3896_);
v_unused_3897_ = lean_ctor_get(v_impl_3813_, 2);
lean_dec(v_unused_3897_);
v_unused_3898_ = lean_ctor_get(v_impl_3813_, 1);
lean_dec(v_unused_3898_);
v_unused_3899_ = lean_ctor_get(v_impl_3813_, 0);
lean_dec(v_unused_3899_);
v___x_3830_ = v_impl_3813_;
v_isShared_3831_ = v_isSharedCheck_3894_;
goto v_resetjp_3829_;
}
else
{
lean_dec(v_impl_3813_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3894_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v_size_3832_; lean_object* v_size_3833_; lean_object* v_k_3834_; lean_object* v_v_3835_; lean_object* v_l_3836_; lean_object* v_r_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; 
v_size_3832_ = lean_ctor_get(v_l_3819_, 0);
v_size_3833_ = lean_ctor_get(v_r_3820_, 0);
v_k_3834_ = lean_ctor_get(v_r_3820_, 1);
v_v_3835_ = lean_ctor_get(v_r_3820_, 2);
v_l_3836_ = lean_ctor_get(v_r_3820_, 3);
v_r_3837_ = lean_ctor_get(v_r_3820_, 4);
v___x_3838_ = lean_unsigned_to_nat(2u);
v___x_3839_ = lean_nat_mul(v___x_3838_, v_size_3832_);
v___x_3840_ = lean_nat_dec_lt(v_size_3833_, v___x_3839_);
lean_dec(v___x_3839_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3869_; 
lean_inc(v_r_3837_);
lean_inc(v_l_3836_);
lean_inc(v_v_3835_);
lean_inc(v_k_3834_);
v_isSharedCheck_3869_ = !lean_is_exclusive(v_r_3820_);
if (v_isSharedCheck_3869_ == 0)
{
lean_object* v_unused_3870_; lean_object* v_unused_3871_; lean_object* v_unused_3872_; lean_object* v_unused_3873_; lean_object* v_unused_3874_; 
v_unused_3870_ = lean_ctor_get(v_r_3820_, 4);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_r_3820_, 3);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_r_3820_, 2);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_r_3820_, 1);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_r_3820_, 0);
lean_dec(v_unused_3874_);
v___x_3842_ = v_r_3820_;
v_isShared_3843_ = v_isSharedCheck_3869_;
goto v_resetjp_3841_;
}
else
{
lean_dec(v_r_3820_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3869_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___x_3857_; lean_object* v___y_3859_; 
v___x_3844_ = lean_nat_add(v___x_3814_, v_size_3816_);
lean_dec(v_size_3816_);
v___x_3845_ = lean_nat_add(v___x_3844_, v_size_3815_);
lean_dec(v___x_3844_);
v___x_3857_ = lean_nat_add(v___x_3814_, v_size_3832_);
if (lean_obj_tag(v_l_3836_) == 0)
{
lean_object* v_size_3867_; 
v_size_3867_ = lean_ctor_get(v_l_3836_, 0);
lean_inc(v_size_3867_);
v___y_3859_ = v_size_3867_;
goto v___jp_3858_;
}
else
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_unsigned_to_nat(0u);
v___y_3859_ = v___x_3868_;
goto v___jp_3858_;
}
v___jp_3846_:
{
lean_object* v___x_3850_; lean_object* v___x_3852_; 
v___x_3850_ = lean_nat_add(v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec(v___y_3848_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 4, v_r_3808_);
lean_ctor_set(v___x_3842_, 3, v_r_3837_);
lean_ctor_set(v___x_3842_, 2, v_v_3806_);
lean_ctor_set(v___x_3842_, 1, v_k_3805_);
lean_ctor_set(v___x_3842_, 0, v___x_3850_);
v___x_3852_ = v___x_3842_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_3856_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_3856_, 3, v_r_3837_);
lean_ctor_set(v_reuseFailAlloc_3856_, 4, v_r_3808_);
v___x_3852_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3854_; 
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 4, v___x_3852_);
lean_ctor_set(v___x_3830_, 3, v___y_3847_);
lean_ctor_set(v___x_3830_, 2, v_v_3835_);
lean_ctor_set(v___x_3830_, 1, v_k_3834_);
lean_ctor_set(v___x_3830_, 0, v___x_3845_);
v___x_3854_ = v___x_3830_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3845_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_k_3834_);
lean_ctor_set(v_reuseFailAlloc_3855_, 2, v_v_3835_);
lean_ctor_set(v_reuseFailAlloc_3855_, 3, v___y_3847_);
lean_ctor_set(v_reuseFailAlloc_3855_, 4, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
v___jp_3858_:
{
lean_object* v___x_3860_; lean_object* v___x_3862_; 
v___x_3860_ = lean_nat_add(v___x_3857_, v___y_3859_);
lean_dec(v___y_3859_);
lean_dec(v___x_3857_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 4, v_l_3836_);
lean_ctor_set(v___x_3810_, 3, v_l_3819_);
lean_ctor_set(v___x_3810_, 2, v_v_3818_);
lean_ctor_set(v___x_3810_, 1, v_k_3817_);
lean_ctor_set(v___x_3810_, 0, v___x_3860_);
v___x_3862_ = v___x_3810_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3866_, 1, v_k_3817_);
lean_ctor_set(v_reuseFailAlloc_3866_, 2, v_v_3818_);
lean_ctor_set(v_reuseFailAlloc_3866_, 3, v_l_3819_);
lean_ctor_set(v_reuseFailAlloc_3866_, 4, v_l_3836_);
v___x_3862_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_nat_add(v___x_3814_, v_size_3815_);
if (lean_obj_tag(v_r_3837_) == 0)
{
lean_object* v_size_3864_; 
v_size_3864_ = lean_ctor_get(v_r_3837_, 0);
lean_inc(v_size_3864_);
v___y_3847_ = v___x_3862_;
v___y_3848_ = v___x_3863_;
v___y_3849_ = v_size_3864_;
goto v___jp_3846_;
}
else
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_unsigned_to_nat(0u);
v___y_3847_ = v___x_3862_;
v___y_3848_ = v___x_3863_;
v___y_3849_ = v___x_3865_;
goto v___jp_3846_;
}
}
}
}
}
else
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3880_; 
lean_del_object(v___x_3810_);
v___x_3875_ = lean_nat_add(v___x_3814_, v_size_3816_);
lean_dec(v_size_3816_);
v___x_3876_ = lean_nat_add(v___x_3875_, v_size_3815_);
lean_dec(v___x_3875_);
v___x_3877_ = lean_nat_add(v___x_3814_, v_size_3815_);
v___x_3878_ = lean_nat_add(v___x_3877_, v_size_3833_);
lean_dec(v___x_3877_);
lean_inc_ref(v_r_3808_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 4, v_r_3808_);
lean_ctor_set(v___x_3830_, 3, v_r_3820_);
lean_ctor_set(v___x_3830_, 2, v_v_3806_);
lean_ctor_set(v___x_3830_, 1, v_k_3805_);
lean_ctor_set(v___x_3830_, 0, v___x_3878_);
v___x_3880_ = v___x_3830_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3878_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_3893_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_3893_, 3, v_r_3820_);
lean_ctor_set(v_reuseFailAlloc_3893_, 4, v_r_3808_);
v___x_3880_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
v_isSharedCheck_3887_ = !lean_is_exclusive(v_r_3808_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; lean_object* v_unused_3889_; lean_object* v_unused_3890_; lean_object* v_unused_3891_; lean_object* v_unused_3892_; 
v_unused_3888_ = lean_ctor_get(v_r_3808_, 4);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_r_3808_, 3);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_r_3808_, 2);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_r_3808_, 1);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_r_3808_, 0);
lean_dec(v_unused_3892_);
v___x_3882_ = v_r_3808_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_dec(v_r_3808_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 4, v___x_3880_);
lean_ctor_set(v___x_3882_, 3, v_l_3819_);
lean_ctor_set(v___x_3882_, 2, v_v_3818_);
lean_ctor_set(v___x_3882_, 1, v_k_3817_);
lean_ctor_set(v___x_3882_, 0, v___x_3876_);
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3876_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v_k_3817_);
lean_ctor_set(v_reuseFailAlloc_3886_, 2, v_v_3818_);
lean_ctor_set(v_reuseFailAlloc_3886_, 3, v_l_3819_);
lean_ctor_set(v_reuseFailAlloc_3886_, 4, v___x_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3900_; 
v_l_3900_ = lean_ctor_get(v_impl_3813_, 3);
lean_inc(v_l_3900_);
if (lean_obj_tag(v_l_3900_) == 0)
{
lean_object* v_r_3901_; lean_object* v_k_3902_; lean_object* v_v_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3914_; 
v_r_3901_ = lean_ctor_get(v_impl_3813_, 4);
v_k_3902_ = lean_ctor_get(v_impl_3813_, 1);
v_v_3903_ = lean_ctor_get(v_impl_3813_, 2);
v_isSharedCheck_3914_ = !lean_is_exclusive(v_impl_3813_);
if (v_isSharedCheck_3914_ == 0)
{
lean_object* v_unused_3915_; lean_object* v_unused_3916_; 
v_unused_3915_ = lean_ctor_get(v_impl_3813_, 3);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_impl_3813_, 0);
lean_dec(v_unused_3916_);
v___x_3905_ = v_impl_3813_;
v_isShared_3906_ = v_isSharedCheck_3914_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_r_3901_);
lean_inc(v_v_3903_);
lean_inc(v_k_3902_);
lean_dec(v_impl_3813_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3914_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3907_; lean_object* v___x_3909_; 
v___x_3907_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3901_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 3, v_r_3901_);
lean_ctor_set(v___x_3905_, 2, v_v_3806_);
lean_ctor_set(v___x_3905_, 1, v_k_3805_);
lean_ctor_set(v___x_3905_, 0, v___x_3814_);
v___x_3909_ = v___x_3905_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3913_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_3913_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_3913_, 3, v_r_3901_);
lean_ctor_set(v_reuseFailAlloc_3913_, 4, v_r_3901_);
v___x_3909_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
lean_object* v___x_3911_; 
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 4, v___x_3909_);
lean_ctor_set(v___x_3810_, 3, v_l_3900_);
lean_ctor_set(v___x_3810_, 2, v_v_3903_);
lean_ctor_set(v___x_3810_, 1, v_k_3902_);
lean_ctor_set(v___x_3810_, 0, v___x_3907_);
v___x_3911_ = v___x_3810_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3907_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v_k_3902_);
lean_ctor_set(v_reuseFailAlloc_3912_, 2, v_v_3903_);
lean_ctor_set(v_reuseFailAlloc_3912_, 3, v_l_3900_);
lean_ctor_set(v_reuseFailAlloc_3912_, 4, v___x_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
else
{
lean_object* v_r_3917_; 
v_r_3917_ = lean_ctor_get(v_impl_3813_, 4);
lean_inc(v_r_3917_);
if (lean_obj_tag(v_r_3917_) == 0)
{
lean_object* v_k_3918_; lean_object* v_v_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3942_; 
v_k_3918_ = lean_ctor_get(v_impl_3813_, 1);
v_v_3919_ = lean_ctor_get(v_impl_3813_, 2);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_impl_3813_);
if (v_isSharedCheck_3942_ == 0)
{
lean_object* v_unused_3943_; lean_object* v_unused_3944_; lean_object* v_unused_3945_; 
v_unused_3943_ = lean_ctor_get(v_impl_3813_, 4);
lean_dec(v_unused_3943_);
v_unused_3944_ = lean_ctor_get(v_impl_3813_, 3);
lean_dec(v_unused_3944_);
v_unused_3945_ = lean_ctor_get(v_impl_3813_, 0);
lean_dec(v_unused_3945_);
v___x_3921_ = v_impl_3813_;
v_isShared_3922_ = v_isSharedCheck_3942_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_v_3919_);
lean_inc(v_k_3918_);
lean_dec(v_impl_3813_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3942_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v_k_3923_; lean_object* v_v_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3938_; 
v_k_3923_ = lean_ctor_get(v_r_3917_, 1);
v_v_3924_ = lean_ctor_get(v_r_3917_, 2);
v_isSharedCheck_3938_ = !lean_is_exclusive(v_r_3917_);
if (v_isSharedCheck_3938_ == 0)
{
lean_object* v_unused_3939_; lean_object* v_unused_3940_; lean_object* v_unused_3941_; 
v_unused_3939_ = lean_ctor_get(v_r_3917_, 4);
lean_dec(v_unused_3939_);
v_unused_3940_ = lean_ctor_get(v_r_3917_, 3);
lean_dec(v_unused_3940_);
v_unused_3941_ = lean_ctor_get(v_r_3917_, 0);
lean_dec(v_unused_3941_);
v___x_3926_ = v_r_3917_;
v_isShared_3927_ = v_isSharedCheck_3938_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_v_3924_);
lean_inc(v_k_3923_);
lean_dec(v_r_3917_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3938_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3928_; lean_object* v___x_3930_; 
v___x_3928_ = lean_unsigned_to_nat(3u);
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 4, v_l_3900_);
lean_ctor_set(v___x_3926_, 3, v_l_3900_);
lean_ctor_set(v___x_3926_, 2, v_v_3919_);
lean_ctor_set(v___x_3926_, 1, v_k_3918_);
lean_ctor_set(v___x_3926_, 0, v___x_3814_);
v___x_3930_ = v___x_3926_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_k_3918_);
lean_ctor_set(v_reuseFailAlloc_3937_, 2, v_v_3919_);
lean_ctor_set(v_reuseFailAlloc_3937_, 3, v_l_3900_);
lean_ctor_set(v_reuseFailAlloc_3937_, 4, v_l_3900_);
v___x_3930_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3932_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v_l_3900_);
lean_ctor_set(v___x_3921_, 2, v_v_3806_);
lean_ctor_set(v___x_3921_, 1, v_k_3805_);
lean_ctor_set(v___x_3921_, 0, v___x_3814_);
v___x_3932_ = v___x_3921_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_3936_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_3936_, 3, v_l_3900_);
lean_ctor_set(v_reuseFailAlloc_3936_, 4, v_l_3900_);
v___x_3932_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
lean_object* v___x_3934_; 
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 4, v___x_3932_);
lean_ctor_set(v___x_3810_, 3, v___x_3930_);
lean_ctor_set(v___x_3810_, 2, v_v_3924_);
lean_ctor_set(v___x_3810_, 1, v_k_3923_);
lean_ctor_set(v___x_3810_, 0, v___x_3928_);
v___x_3934_ = v___x_3810_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3928_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_k_3923_);
lean_ctor_set(v_reuseFailAlloc_3935_, 2, v_v_3924_);
lean_ctor_set(v_reuseFailAlloc_3935_, 3, v___x_3930_);
lean_ctor_set(v_reuseFailAlloc_3935_, 4, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
}
}
else
{
lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3946_ = lean_unsigned_to_nat(2u);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 4, v_r_3917_);
lean_ctor_set(v___x_3810_, 3, v_impl_3813_);
lean_ctor_set(v___x_3810_, 0, v___x_3946_);
v___x_3948_ = v___x_3810_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3946_);
lean_ctor_set(v_reuseFailAlloc_3949_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_3949_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_3949_, 3, v_impl_3813_);
lean_ctor_set(v_reuseFailAlloc_3949_, 4, v_r_3917_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3951_; 
lean_dec(v_v_3806_);
lean_dec(v_k_3805_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 2, v_v_3802_);
lean_ctor_set(v___x_3810_, 1, v_k_3801_);
v___x_3951_ = v___x_3810_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_size_3804_);
lean_ctor_set(v_reuseFailAlloc_3952_, 1, v_k_3801_);
lean_ctor_set(v_reuseFailAlloc_3952_, 2, v_v_3802_);
lean_ctor_set(v_reuseFailAlloc_3952_, 3, v_l_3807_);
lean_ctor_set(v_reuseFailAlloc_3952_, 4, v_r_3808_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
default: 
{
lean_object* v_impl_3953_; lean_object* v___x_3954_; 
lean_dec(v_size_3804_);
v_impl_3953_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(v_k_3801_, v_v_3802_, v_r_3808_);
v___x_3954_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3807_) == 0)
{
lean_object* v_size_3955_; lean_object* v_size_3956_; lean_object* v_k_3957_; lean_object* v_v_3958_; lean_object* v_l_3959_; lean_object* v_r_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; uint8_t v___x_3963_; 
v_size_3955_ = lean_ctor_get(v_l_3807_, 0);
v_size_3956_ = lean_ctor_get(v_impl_3953_, 0);
lean_inc(v_size_3956_);
v_k_3957_ = lean_ctor_get(v_impl_3953_, 1);
lean_inc(v_k_3957_);
v_v_3958_ = lean_ctor_get(v_impl_3953_, 2);
lean_inc(v_v_3958_);
v_l_3959_ = lean_ctor_get(v_impl_3953_, 3);
lean_inc(v_l_3959_);
v_r_3960_ = lean_ctor_get(v_impl_3953_, 4);
lean_inc(v_r_3960_);
v___x_3961_ = lean_unsigned_to_nat(3u);
v___x_3962_ = lean_nat_mul(v___x_3961_, v_size_3955_);
v___x_3963_ = lean_nat_dec_lt(v___x_3962_, v_size_3956_);
lean_dec(v___x_3962_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3967_; 
lean_dec(v_r_3960_);
lean_dec(v_l_3959_);
lean_dec(v_v_3958_);
lean_dec(v_k_3957_);
v___x_3964_ = lean_nat_add(v___x_3954_, v_size_3955_);
v___x_3965_ = lean_nat_add(v___x_3964_, v_size_3956_);
lean_dec(v_size_3956_);
lean_dec(v___x_3964_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 4, v_impl_3953_);
lean_ctor_set(v___x_3810_, 0, v___x_3965_);
v___x_3967_ = v___x_3810_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3965_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_3968_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_3968_, 3, v_l_3807_);
lean_ctor_set(v_reuseFailAlloc_3968_, 4, v_impl_3953_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
else
{
lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_4032_; 
v_isSharedCheck_4032_ = !lean_is_exclusive(v_impl_3953_);
if (v_isSharedCheck_4032_ == 0)
{
lean_object* v_unused_4033_; lean_object* v_unused_4034_; lean_object* v_unused_4035_; lean_object* v_unused_4036_; lean_object* v_unused_4037_; 
v_unused_4033_ = lean_ctor_get(v_impl_3953_, 4);
lean_dec(v_unused_4033_);
v_unused_4034_ = lean_ctor_get(v_impl_3953_, 3);
lean_dec(v_unused_4034_);
v_unused_4035_ = lean_ctor_get(v_impl_3953_, 2);
lean_dec(v_unused_4035_);
v_unused_4036_ = lean_ctor_get(v_impl_3953_, 1);
lean_dec(v_unused_4036_);
v_unused_4037_ = lean_ctor_get(v_impl_3953_, 0);
lean_dec(v_unused_4037_);
v___x_3970_ = v_impl_3953_;
v_isShared_3971_ = v_isSharedCheck_4032_;
goto v_resetjp_3969_;
}
else
{
lean_dec(v_impl_3953_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_4032_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v_size_3972_; lean_object* v_k_3973_; lean_object* v_v_3974_; lean_object* v_l_3975_; lean_object* v_r_3976_; lean_object* v_size_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; uint8_t v___x_3980_; 
v_size_3972_ = lean_ctor_get(v_l_3959_, 0);
v_k_3973_ = lean_ctor_get(v_l_3959_, 1);
v_v_3974_ = lean_ctor_get(v_l_3959_, 2);
v_l_3975_ = lean_ctor_get(v_l_3959_, 3);
v_r_3976_ = lean_ctor_get(v_l_3959_, 4);
v_size_3977_ = lean_ctor_get(v_r_3960_, 0);
v___x_3978_ = lean_unsigned_to_nat(2u);
v___x_3979_ = lean_nat_mul(v___x_3978_, v_size_3977_);
v___x_3980_ = lean_nat_dec_lt(v_size_3972_, v___x_3979_);
lean_dec(v___x_3979_);
if (v___x_3980_ == 0)
{
lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4008_; 
lean_inc(v_r_3976_);
lean_inc(v_l_3975_);
lean_inc(v_v_3974_);
lean_inc(v_k_3973_);
v_isSharedCheck_4008_ = !lean_is_exclusive(v_l_3959_);
if (v_isSharedCheck_4008_ == 0)
{
lean_object* v_unused_4009_; lean_object* v_unused_4010_; lean_object* v_unused_4011_; lean_object* v_unused_4012_; lean_object* v_unused_4013_; 
v_unused_4009_ = lean_ctor_get(v_l_3959_, 4);
lean_dec(v_unused_4009_);
v_unused_4010_ = lean_ctor_get(v_l_3959_, 3);
lean_dec(v_unused_4010_);
v_unused_4011_ = lean_ctor_get(v_l_3959_, 2);
lean_dec(v_unused_4011_);
v_unused_4012_ = lean_ctor_get(v_l_3959_, 1);
lean_dec(v_unused_4012_);
v_unused_4013_ = lean_ctor_get(v_l_3959_, 0);
lean_dec(v_unused_4013_);
v___x_3982_ = v_l_3959_;
v_isShared_3983_ = v_isSharedCheck_4008_;
goto v_resetjp_3981_;
}
else
{
lean_dec(v_l_3959_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4008_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3998_; 
v___x_3984_ = lean_nat_add(v___x_3954_, v_size_3955_);
v___x_3985_ = lean_nat_add(v___x_3984_, v_size_3956_);
lean_dec(v_size_3956_);
if (lean_obj_tag(v_l_3975_) == 0)
{
lean_object* v_size_4006_; 
v_size_4006_ = lean_ctor_get(v_l_3975_, 0);
lean_inc(v_size_4006_);
v___y_3998_ = v_size_4006_;
goto v___jp_3997_;
}
else
{
lean_object* v___x_4007_; 
v___x_4007_ = lean_unsigned_to_nat(0u);
v___y_3998_ = v___x_4007_;
goto v___jp_3997_;
}
v___jp_3986_:
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3990_ = lean_nat_add(v___y_3987_, v___y_3989_);
lean_dec(v___y_3989_);
lean_dec(v___y_3987_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 4, v_r_3960_);
lean_ctor_set(v___x_3982_, 3, v_r_3976_);
lean_ctor_set(v___x_3982_, 2, v_v_3958_);
lean_ctor_set(v___x_3982_, 1, v_k_3957_);
lean_ctor_set(v___x_3982_, 0, v___x_3990_);
v___x_3992_ = v___x_3982_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3990_);
lean_ctor_set(v_reuseFailAlloc_3996_, 1, v_k_3957_);
lean_ctor_set(v_reuseFailAlloc_3996_, 2, v_v_3958_);
lean_ctor_set(v_reuseFailAlloc_3996_, 3, v_r_3976_);
lean_ctor_set(v_reuseFailAlloc_3996_, 4, v_r_3960_);
v___x_3992_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3994_; 
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 4, v___x_3992_);
lean_ctor_set(v___x_3970_, 3, v___y_3988_);
lean_ctor_set(v___x_3970_, 2, v_v_3974_);
lean_ctor_set(v___x_3970_, 1, v_k_3973_);
lean_ctor_set(v___x_3970_, 0, v___x_3985_);
v___x_3994_ = v___x_3970_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3985_);
lean_ctor_set(v_reuseFailAlloc_3995_, 1, v_k_3973_);
lean_ctor_set(v_reuseFailAlloc_3995_, 2, v_v_3974_);
lean_ctor_set(v_reuseFailAlloc_3995_, 3, v___y_3988_);
lean_ctor_set(v_reuseFailAlloc_3995_, 4, v___x_3992_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
v___jp_3997_:
{
lean_object* v___x_3999_; lean_object* v___x_4001_; 
v___x_3999_ = lean_nat_add(v___x_3984_, v___y_3998_);
lean_dec(v___y_3998_);
lean_dec(v___x_3984_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 4, v_l_3975_);
lean_ctor_set(v___x_3810_, 0, v___x_3999_);
v___x_4001_ = v___x_3810_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_3999_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_4005_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_4005_, 3, v_l_3807_);
lean_ctor_set(v_reuseFailAlloc_4005_, 4, v_l_3975_);
v___x_4001_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
lean_object* v___x_4002_; 
v___x_4002_ = lean_nat_add(v___x_3954_, v_size_3977_);
if (lean_obj_tag(v_r_3976_) == 0)
{
lean_object* v_size_4003_; 
v_size_4003_ = lean_ctor_get(v_r_3976_, 0);
lean_inc(v_size_4003_);
v___y_3987_ = v___x_4002_;
v___y_3988_ = v___x_4001_;
v___y_3989_ = v_size_4003_;
goto v___jp_3986_;
}
else
{
lean_object* v___x_4004_; 
v___x_4004_ = lean_unsigned_to_nat(0u);
v___y_3987_ = v___x_4002_;
v___y_3988_ = v___x_4001_;
v___y_3989_ = v___x_4004_;
goto v___jp_3986_;
}
}
}
}
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4018_; 
lean_del_object(v___x_3810_);
v___x_4014_ = lean_nat_add(v___x_3954_, v_size_3955_);
v___x_4015_ = lean_nat_add(v___x_4014_, v_size_3956_);
lean_dec(v_size_3956_);
v___x_4016_ = lean_nat_add(v___x_4014_, v_size_3972_);
lean_dec(v___x_4014_);
lean_inc_ref(v_l_3807_);
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 4, v_l_3959_);
lean_ctor_set(v___x_3970_, 3, v_l_3807_);
lean_ctor_set(v___x_3970_, 2, v_v_3806_);
lean_ctor_set(v___x_3970_, 1, v_k_3805_);
lean_ctor_set(v___x_3970_, 0, v___x_4016_);
v___x_4018_ = v___x_3970_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4016_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_4031_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_4031_, 3, v_l_3807_);
lean_ctor_set(v_reuseFailAlloc_4031_, 4, v_l_3959_);
v___x_4018_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
v_isSharedCheck_4025_ = !lean_is_exclusive(v_l_3807_);
if (v_isSharedCheck_4025_ == 0)
{
lean_object* v_unused_4026_; lean_object* v_unused_4027_; lean_object* v_unused_4028_; lean_object* v_unused_4029_; lean_object* v_unused_4030_; 
v_unused_4026_ = lean_ctor_get(v_l_3807_, 4);
lean_dec(v_unused_4026_);
v_unused_4027_ = lean_ctor_get(v_l_3807_, 3);
lean_dec(v_unused_4027_);
v_unused_4028_ = lean_ctor_get(v_l_3807_, 2);
lean_dec(v_unused_4028_);
v_unused_4029_ = lean_ctor_get(v_l_3807_, 1);
lean_dec(v_unused_4029_);
v_unused_4030_ = lean_ctor_get(v_l_3807_, 0);
lean_dec(v_unused_4030_);
v___x_4020_ = v_l_3807_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_dec(v_l_3807_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 4, v_r_3960_);
lean_ctor_set(v___x_4020_, 3, v___x_4018_);
lean_ctor_set(v___x_4020_, 2, v_v_3958_);
lean_ctor_set(v___x_4020_, 1, v_k_3957_);
lean_ctor_set(v___x_4020_, 0, v___x_4015_);
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v___x_4015_);
lean_ctor_set(v_reuseFailAlloc_4024_, 1, v_k_3957_);
lean_ctor_set(v_reuseFailAlloc_4024_, 2, v_v_3958_);
lean_ctor_set(v_reuseFailAlloc_4024_, 3, v___x_4018_);
lean_ctor_set(v_reuseFailAlloc_4024_, 4, v_r_3960_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4038_; 
v_l_4038_ = lean_ctor_get(v_impl_3953_, 3);
lean_inc(v_l_4038_);
if (lean_obj_tag(v_l_4038_) == 0)
{
lean_object* v_r_4039_; lean_object* v_k_4040_; lean_object* v_v_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4064_; 
v_r_4039_ = lean_ctor_get(v_impl_3953_, 4);
v_k_4040_ = lean_ctor_get(v_impl_3953_, 1);
v_v_4041_ = lean_ctor_get(v_impl_3953_, 2);
v_isSharedCheck_4064_ = !lean_is_exclusive(v_impl_3953_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; lean_object* v_unused_4066_; 
v_unused_4065_ = lean_ctor_get(v_impl_3953_, 3);
lean_dec(v_unused_4065_);
v_unused_4066_ = lean_ctor_get(v_impl_3953_, 0);
lean_dec(v_unused_4066_);
v___x_4043_ = v_impl_3953_;
v_isShared_4044_ = v_isSharedCheck_4064_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_r_4039_);
lean_inc(v_v_4041_);
lean_inc(v_k_4040_);
lean_dec(v_impl_3953_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4064_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v_k_4045_; lean_object* v_v_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4060_; 
v_k_4045_ = lean_ctor_get(v_l_4038_, 1);
v_v_4046_ = lean_ctor_get(v_l_4038_, 2);
v_isSharedCheck_4060_ = !lean_is_exclusive(v_l_4038_);
if (v_isSharedCheck_4060_ == 0)
{
lean_object* v_unused_4061_; lean_object* v_unused_4062_; lean_object* v_unused_4063_; 
v_unused_4061_ = lean_ctor_get(v_l_4038_, 4);
lean_dec(v_unused_4061_);
v_unused_4062_ = lean_ctor_get(v_l_4038_, 3);
lean_dec(v_unused_4062_);
v_unused_4063_ = lean_ctor_get(v_l_4038_, 0);
lean_dec(v_unused_4063_);
v___x_4048_ = v_l_4038_;
v_isShared_4049_ = v_isSharedCheck_4060_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_v_4046_);
lean_inc(v_k_4045_);
lean_dec(v_l_4038_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4060_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4050_; lean_object* v___x_4052_; 
v___x_4050_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4039_, 2);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 4, v_r_4039_);
lean_ctor_set(v___x_4048_, 3, v_r_4039_);
lean_ctor_set(v___x_4048_, 2, v_v_3806_);
lean_ctor_set(v___x_4048_, 1, v_k_3805_);
lean_ctor_set(v___x_4048_, 0, v___x_3954_);
v___x_4052_ = v___x_4048_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_3954_);
lean_ctor_set(v_reuseFailAlloc_4059_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_4059_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_4059_, 3, v_r_4039_);
lean_ctor_set(v_reuseFailAlloc_4059_, 4, v_r_4039_);
v___x_4052_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4054_; 
lean_inc(v_r_4039_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 3, v_r_4039_);
lean_ctor_set(v___x_4043_, 0, v___x_3954_);
v___x_4054_ = v___x_4043_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v___x_3954_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v_k_4040_);
lean_ctor_set(v_reuseFailAlloc_4058_, 2, v_v_4041_);
lean_ctor_set(v_reuseFailAlloc_4058_, 3, v_r_4039_);
lean_ctor_set(v_reuseFailAlloc_4058_, 4, v_r_4039_);
v___x_4054_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
lean_object* v___x_4056_; 
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 4, v___x_4054_);
lean_ctor_set(v___x_3810_, 3, v___x_4052_);
lean_ctor_set(v___x_3810_, 2, v_v_4046_);
lean_ctor_set(v___x_3810_, 1, v_k_4045_);
lean_ctor_set(v___x_3810_, 0, v___x_4050_);
v___x_4056_ = v___x_3810_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4050_);
lean_ctor_set(v_reuseFailAlloc_4057_, 1, v_k_4045_);
lean_ctor_set(v_reuseFailAlloc_4057_, 2, v_v_4046_);
lean_ctor_set(v_reuseFailAlloc_4057_, 3, v___x_4052_);
lean_ctor_set(v_reuseFailAlloc_4057_, 4, v___x_4054_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
}
}
else
{
lean_object* v_r_4067_; 
v_r_4067_ = lean_ctor_get(v_impl_3953_, 4);
lean_inc(v_r_4067_);
if (lean_obj_tag(v_r_4067_) == 0)
{
lean_object* v_k_4068_; lean_object* v_v_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4080_; 
v_k_4068_ = lean_ctor_get(v_impl_3953_, 1);
v_v_4069_ = lean_ctor_get(v_impl_3953_, 2);
v_isSharedCheck_4080_ = !lean_is_exclusive(v_impl_3953_);
if (v_isSharedCheck_4080_ == 0)
{
lean_object* v_unused_4081_; lean_object* v_unused_4082_; lean_object* v_unused_4083_; 
v_unused_4081_ = lean_ctor_get(v_impl_3953_, 4);
lean_dec(v_unused_4081_);
v_unused_4082_ = lean_ctor_get(v_impl_3953_, 3);
lean_dec(v_unused_4082_);
v_unused_4083_ = lean_ctor_get(v_impl_3953_, 0);
lean_dec(v_unused_4083_);
v___x_4071_ = v_impl_3953_;
v_isShared_4072_ = v_isSharedCheck_4080_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_v_4069_);
lean_inc(v_k_4068_);
lean_dec(v_impl_3953_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4080_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4073_; lean_object* v___x_4075_; 
v___x_4073_ = lean_unsigned_to_nat(3u);
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 4, v_l_4038_);
lean_ctor_set(v___x_4071_, 2, v_v_3806_);
lean_ctor_set(v___x_4071_, 1, v_k_3805_);
lean_ctor_set(v___x_4071_, 0, v___x_3954_);
v___x_4075_ = v___x_4071_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_3954_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_4079_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_4079_, 3, v_l_4038_);
lean_ctor_set(v_reuseFailAlloc_4079_, 4, v_l_4038_);
v___x_4075_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4077_; 
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 4, v_r_4067_);
lean_ctor_set(v___x_3810_, 3, v___x_4075_);
lean_ctor_set(v___x_3810_, 2, v_v_4069_);
lean_ctor_set(v___x_3810_, 1, v_k_4068_);
lean_ctor_set(v___x_3810_, 0, v___x_4073_);
v___x_4077_ = v___x_3810_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4073_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v_k_4068_);
lean_ctor_set(v_reuseFailAlloc_4078_, 2, v_v_4069_);
lean_ctor_set(v_reuseFailAlloc_4078_, 3, v___x_4075_);
lean_ctor_set(v_reuseFailAlloc_4078_, 4, v_r_4067_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
}
else
{
lean_object* v___x_4084_; lean_object* v___x_4086_; 
v___x_4084_ = lean_unsigned_to_nat(2u);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 4, v_impl_3953_);
lean_ctor_set(v___x_3810_, 3, v_r_4067_);
lean_ctor_set(v___x_3810_, 0, v___x_4084_);
v___x_4086_ = v___x_3810_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4084_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_k_3805_);
lean_ctor_set(v_reuseFailAlloc_4087_, 2, v_v_3806_);
lean_ctor_set(v_reuseFailAlloc_4087_, 3, v_r_4067_);
lean_ctor_set(v_reuseFailAlloc_4087_, 4, v_impl_3953_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
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
lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4089_ = lean_unsigned_to_nat(1u);
v___x_4090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
lean_ctor_set(v___x_4090_, 1, v_k_3801_);
lean_ctor_set(v___x_4090_, 2, v_v_3802_);
lean_ctor_set(v___x_4090_, 3, v_t_3803_);
lean_ctor_set(v___x_4090_, 4, v_t_3803_);
return v___x_4090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(lean_object* v_cfg_4098_){
_start:
{
lean_object* v___y_4101_; lean_object* v_a_4102_; lean_object* v___y_4115_; lean_object* v_externalKernels_4116_; lean_object* v___y_4129_; lean_object* v___y_4130_; uint8_t v___y_4131_; lean_object* v_a_4132_; lean_object* v___y_4146_; uint8_t v___y_4147_; lean_object* v_enable__nanoda_x3f_4160_; lean_object* v_external__kernels_x3f_4161_; lean_object* v___y_4163_; 
v_enable__nanoda_x3f_4160_ = lean_ctor_get(v_cfg_4098_, 5);
lean_inc(v_enable__nanoda_x3f_4160_);
v_external__kernels_x3f_4161_ = lean_ctor_get(v_cfg_4098_, 6);
lean_inc(v_external__kernels_x3f_4161_);
lean_dec_ref(v_cfg_4098_);
if (lean_obj_tag(v_external__kernels_x3f_4161_) == 0)
{
lean_object* v___x_4194_; 
v___x_4194_ = lean_box(1);
v___y_4163_ = v___x_4194_;
goto v___jp_4162_;
}
else
{
lean_object* v_val_4195_; 
v_val_4195_ = lean_ctor_get(v_external__kernels_x3f_4161_, 0);
lean_inc(v_val_4195_);
lean_dec_ref_known(v_external__kernels_x3f_4161_, 1);
v___y_4163_ = v_val_4195_;
goto v___jp_4162_;
}
v___jp_4100_:
{
lean_object* v_fst_4103_; 
v_fst_4103_ = lean_ctor_get(v_a_4102_, 0);
lean_inc(v_fst_4103_);
lean_dec_ref(v_a_4102_);
if (lean_obj_tag(v_fst_4103_) == 0)
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4104_, 0, v___y_4101_);
v___x_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4104_);
return v___x_4105_;
}
else
{
lean_object* v_val_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4113_; 
lean_dec(v___y_4101_);
v_val_4106_ = lean_ctor_get(v_fst_4103_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v_fst_4103_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4108_ = v_fst_4103_;
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_val_4106_);
lean_dec(v_fst_4103_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4111_; 
if (v_isShared_4109_ == 0)
{
lean_ctor_set_tag(v___x_4108_, 0);
v___x_4111_ = v___x_4108_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_val_4106_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
v___jp_4114_:
{
lean_object* v___x_4117_; 
v___x_4117_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v___y_4115_, v_externalKernels_4116_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v_a_4119_; 
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_a_4118_);
lean_dec_ref_known(v___x_4117_, 1);
v_a_4119_ = lean_ctor_get(v_a_4118_, 0);
lean_inc(v_a_4119_);
lean_dec(v_a_4118_);
v___y_4101_ = v_externalKernels_4116_;
v_a_4102_ = v_a_4119_;
goto v___jp_4100_;
}
else
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
lean_dec(v_externalKernels_4116_);
v_a_4120_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4117_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4117_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
v___jp_4128_:
{
lean_object* v_fst_4133_; 
v_fst_4133_ = lean_ctor_get(v_a_4132_, 0);
lean_inc(v_fst_4133_);
lean_dec_ref(v_a_4132_);
if (lean_obj_tag(v_fst_4133_) == 0)
{
if (v___y_4131_ == 0)
{
v___y_4115_ = v___y_4129_;
v_externalKernels_4116_ = v___y_4130_;
goto v___jp_4114_;
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4134_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0));
v___x_4135_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__2));
v___x_4136_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(v___x_4134_, v___x_4135_, v___y_4130_);
v___y_4115_ = v___y_4129_;
v_externalKernels_4116_ = v___x_4136_;
goto v___jp_4114_;
}
}
else
{
lean_object* v_val_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
v_val_4137_ = lean_ctor_get(v_fst_4133_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_fst_4133_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v_fst_4133_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_val_4137_);
lean_dec(v_fst_4133_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
lean_ctor_set_tag(v___x_4139_, 0);
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_val_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
v___jp_4145_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v___x_4149_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(v___x_4148_, v___y_4146_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v_a_4151_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref_known(v___x_4149_, 1);
v_a_4151_ = lean_ctor_get(v_a_4150_, 0);
lean_inc(v_a_4151_);
lean_dec(v_a_4150_);
v___y_4129_ = v___x_4148_;
v___y_4130_ = v___y_4146_;
v___y_4131_ = v___y_4147_;
v_a_4132_ = v_a_4151_;
goto v___jp_4128_;
}
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
lean_dec(v___y_4146_);
v_a_4152_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4149_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4149_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
v___jp_4162_:
{
if (lean_obj_tag(v_enable__nanoda_x3f_4160_) == 0)
{
uint8_t v___x_4164_; 
v___x_4164_ = 0;
v___y_4146_ = v___y_4163_;
v___y_4147_ = v___x_4164_;
goto v___jp_4145_;
}
else
{
lean_object* v_val_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4193_; 
v_val_4165_ = lean_ctor_get(v_enable__nanoda_x3f_4160_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v_enable__nanoda_x3f_4160_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4167_ = v_enable__nanoda_x3f_4160_;
v_isShared_4168_ = v_isSharedCheck_4193_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_val_4165_);
lean_dec(v_enable__nanoda_x3f_4160_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4193_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
uint8_t v___x_4169_; 
v___x_4169_ = lean_unbox(v_val_4165_);
if (v___x_4169_ == 0)
{
uint8_t v___x_4170_; 
lean_del_object(v___x_4167_);
v___x_4170_ = lean_unbox(v_val_4165_);
lean_dec(v_val_4165_);
v___y_4146_ = v___y_4163_;
v___y_4147_ = v___x_4170_;
goto v___jp_4145_;
}
else
{
if (lean_obj_tag(v___y_4163_) == 0)
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
lean_dec_ref_known(v___y_4163_, 5);
lean_dec(v_val_4165_);
v___x_4171_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__3));
v___x_4172_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4171_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4183_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4175_ = v___x_4172_;
v_isShared_4176_ = v_isSharedCheck_4183_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4172_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4183_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4178_; 
if (v_isShared_4168_ == 0)
{
lean_ctor_set_tag(v___x_4167_, 0);
lean_ctor_set(v___x_4167_, 0, v_a_4173_);
v___x_4178_ = v___x_4167_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4173_);
v___x_4178_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
lean_object* v___x_4180_; 
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v___x_4178_);
v___x_4180_ = v___x_4175_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4178_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
lean_del_object(v___x_4167_);
v_a_4184_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4172_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4172_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
else
{
uint8_t v___x_4192_; 
lean_del_object(v___x_4167_);
v___x_4192_ = lean_unbox(v_val_4165_);
lean_dec(v_val_4165_);
v___y_4146_ = v___y_4163_;
v___y_4147_ = v___x_4192_;
goto v___jp_4145_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___boxed(lean_object* v_cfg_4196_, lean_object* v_a_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v_cfg_4196_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(lean_object* v_00_u03b2_4199_, lean_object* v_k_4200_, lean_object* v_v_4201_, lean_object* v_t_4202_, lean_object* v_hl_4203_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(v_k_4200_, v_v_4201_, v_t_4202_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(size_t v_sz_4205_, size_t v_i_4206_, lean_object* v_bs_4207_){
_start:
{
uint8_t v___x_4208_; 
v___x_4208_ = lean_usize_dec_lt(v_i_4206_, v_sz_4205_);
if (v___x_4208_ == 0)
{
return v_bs_4207_;
}
else
{
lean_object* v_v_4209_; lean_object* v___x_4210_; lean_object* v_bs_x27_4211_; lean_object* v___x_4212_; size_t v___x_4213_; size_t v___x_4214_; lean_object* v___x_4215_; 
v_v_4209_ = lean_array_uget(v_bs_4207_, v_i_4206_);
v___x_4210_ = lean_unsigned_to_nat(0u);
v_bs_x27_4211_ = lean_array_uset(v_bs_4207_, v_i_4206_, v___x_4210_);
v___x_4212_ = l_String_toName(v_v_4209_);
v___x_4213_ = ((size_t)1ULL);
v___x_4214_ = lean_usize_add(v_i_4206_, v___x_4213_);
v___x_4215_ = lean_array_uset(v_bs_x27_4211_, v_i_4206_, v___x_4212_);
v_i_4206_ = v___x_4214_;
v_bs_4207_ = v___x_4215_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0___boxed(lean_object* v_sz_4217_, lean_object* v_i_4218_, lean_object* v_bs_4219_){
_start:
{
size_t v_sz_boxed_4220_; size_t v_i_boxed_4221_; lean_object* v_res_4222_; 
v_sz_boxed_4220_ = lean_unbox_usize(v_sz_4217_);
lean_dec(v_sz_4217_);
v_i_boxed_4221_ = lean_unbox_usize(v_i_4218_);
lean_dec(v_i_4218_);
v_res_4222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_boxed_4220_, v_i_boxed_4221_, v_bs_4219_);
return v_res_4222_;
}
}
static lean_object* _init_l_Lake_Check_runChallenge___boxed__const__1(void){
_start:
{
uint32_t v___x_4229_; lean_object* v___x_4230_; 
v___x_4229_ = 1;
v___x_4230_ = lean_box_uint32(v___x_4229_);
return v___x_4230_;
}
}
static lean_object* _init_l_Lake_Check_runChallenge___boxed__const__2(void){
_start:
{
uint32_t v___x_4231_; lean_object* v___x_4232_; 
v___x_4231_ = 0;
v___x_4232_ = lean_box_uint32(v___x_4231_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runChallenge(lean_object* v_configFile_x3f_4233_, lean_object* v_lean_4234_, lean_object* v_lake_4235_, lean_object* v_projectDir_4236_){
_start:
{
lean_object* v_a_4239_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4261_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__0));
v___x_4262_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_4261_, v_lean_4234_, v_lake_4235_, v_projectDir_4236_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4396_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4265_ = v___x_4262_;
v_isShared_4266_ = v_isSharedCheck_4396_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4262_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4396_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
if (lean_obj_tag(v_a_4263_) == 0)
{
lean_object* v_a_4267_; lean_object* v___x_4269_; 
v_a_4267_ = lean_ctor_get(v_a_4263_, 0);
lean_inc(v_a_4267_);
lean_dec_ref_known(v_a_4263_, 1);
if (v_isShared_4266_ == 0)
{
lean_ctor_set(v___x_4265_, 0, v_a_4267_);
v___x_4269_ = v___x_4265_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4267_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
else
{
lean_del_object(v___x_4265_);
if (lean_obj_tag(v_configFile_x3f_4233_) == 1)
{
lean_object* v_a_4271_; lean_object* v_val_4272_; lean_object* v___x_4273_; 
v_a_4271_ = lean_ctor_get(v_a_4263_, 0);
lean_inc(v_a_4271_);
lean_dec_ref_known(v_a_4263_, 1);
v_val_4272_ = lean_ctor_get(v_configFile_x3f_4233_, 0);
v___x_4273_ = l_IO_FS_readFile(v_val_4272_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v_a_4276_; lean_object* v___x_4283_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4274_);
lean_dec_ref_known(v___x_4273_, 1);
v___x_4283_ = l_Lean_Json_parse(v_a_4274_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v_a_4284_; 
lean_dec(v_a_4271_);
v_a_4284_ = lean_ctor_get(v___x_4283_, 0);
lean_inc(v_a_4284_);
lean_dec_ref_known(v___x_4283_, 1);
v_a_4276_ = v_a_4284_;
goto v___jp_4275_;
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4286_; 
v_a_4285_ = lean_ctor_get(v___x_4283_, 0);
lean_inc(v_a_4285_);
lean_dec_ref_known(v___x_4283_, 1);
v___x_4286_ = l_Lake_Check_instFromJsonConfig_fromJson(v_a_4285_);
if (lean_obj_tag(v___x_4286_) == 0)
{
lean_object* v_a_4287_; 
lean_dec(v_a_4271_);
v_a_4287_ = lean_ctor_get(v___x_4286_, 0);
lean_inc(v_a_4287_);
lean_dec_ref_known(v___x_4286_, 1);
v_a_4276_ = v_a_4287_;
goto v___jp_4275_;
}
else
{
lean_object* v_a_4288_; lean_object* v_challenge__module_4289_; lean_object* v_solution__module_4290_; lean_object* v_theorem__names_4291_; lean_object* v_definition__names_4292_; lean_object* v_permitted__axioms_4293_; size_t v_sz_4294_; size_t v___x_4295_; lean_object* v___x_4296_; lean_object* v___y_4298_; lean_object* v___y_4377_; 
v_a_4288_ = lean_ctor_get(v___x_4286_, 0);
lean_inc(v_a_4288_);
lean_dec_ref_known(v___x_4286_, 1);
v_challenge__module_4289_ = lean_ctor_get(v_a_4288_, 0);
lean_inc_ref(v_challenge__module_4289_);
v_solution__module_4290_ = lean_ctor_get(v_a_4288_, 1);
lean_inc_ref(v_solution__module_4290_);
v_theorem__names_4291_ = lean_ctor_get(v_a_4288_, 2);
v_definition__names_4292_ = lean_ctor_get(v_a_4288_, 3);
v_permitted__axioms_4293_ = lean_ctor_get(v_a_4288_, 4);
lean_inc_ref(v_permitted__axioms_4293_);
v_sz_4294_ = lean_array_size(v_theorem__names_4291_);
v___x_4295_ = ((size_t)0ULL);
lean_inc_ref(v_theorem__names_4291_);
v___x_4296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_4294_, v___x_4295_, v_theorem__names_4291_);
if (lean_obj_tag(v_definition__names_4292_) == 0)
{
lean_object* v___x_4387_; 
v___x_4387_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__18));
v___y_4377_ = v___x_4387_;
goto v___jp_4376_;
}
else
{
lean_object* v_val_4388_; 
v_val_4388_ = lean_ctor_get(v_definition__names_4292_, 0);
lean_inc(v_val_4388_);
v___y_4377_ = v_val_4388_;
goto v___jp_4376_;
}
v___jp_4297_:
{
lean_object* v___x_4299_; 
v___x_4299_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v_a_4288_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4367_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4302_ = v___x_4299_;
v_isShared_4303_ = v_isSharedCheck_4367_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4299_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4367_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
if (lean_obj_tag(v_a_4300_) == 0)
{
lean_object* v_a_4304_; lean_object* v___x_4306_; 
lean_dec_ref(v___y_4298_);
lean_dec_ref(v___x_4296_);
lean_dec_ref(v_permitted__axioms_4293_);
lean_dec_ref(v_solution__module_4290_);
lean_dec_ref(v_challenge__module_4289_);
lean_dec(v_a_4271_);
v_a_4304_ = lean_ctor_get(v_a_4300_, 0);
lean_inc(v_a_4304_);
lean_dec_ref_known(v_a_4300_, 1);
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 0, v_a_4304_);
v___x_4306_ = v___x_4302_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4304_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
else
{
lean_object* v_a_4308_; lean_object* v_projectDir_4309_; lean_object* v_leanPath_4310_; lean_object* v_binPath_4311_; lean_object* v_whichLandrun_4312_; lean_object* v_whichLake_4313_; lean_object* v_whichLean4Export_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4360_; 
lean_del_object(v___x_4302_);
v_a_4308_ = lean_ctor_get(v_a_4300_, 0);
lean_inc(v_a_4308_);
lean_dec_ref_known(v_a_4300_, 1);
v_projectDir_4309_ = lean_ctor_get(v_a_4271_, 0);
v_leanPath_4310_ = lean_ctor_get(v_a_4271_, 6);
v_binPath_4311_ = lean_ctor_get(v_a_4271_, 7);
v_whichLandrun_4312_ = lean_ctor_get(v_a_4271_, 8);
v_whichLake_4313_ = lean_ctor_get(v_a_4271_, 9);
v_whichLean4Export_4314_ = lean_ctor_get(v_a_4271_, 10);
v_isSharedCheck_4360_ = !lean_is_exclusive(v_a_4271_);
if (v_isSharedCheck_4360_ == 0)
{
lean_object* v_unused_4361_; lean_object* v_unused_4362_; lean_object* v_unused_4363_; lean_object* v_unused_4364_; lean_object* v_unused_4365_; lean_object* v_unused_4366_; 
v_unused_4361_ = lean_ctor_get(v_a_4271_, 11);
lean_dec(v_unused_4361_);
v_unused_4362_ = lean_ctor_get(v_a_4271_, 5);
lean_dec(v_unused_4362_);
v_unused_4363_ = lean_ctor_get(v_a_4271_, 4);
lean_dec(v_unused_4363_);
v_unused_4364_ = lean_ctor_get(v_a_4271_, 3);
lean_dec(v_unused_4364_);
v_unused_4365_ = lean_ctor_get(v_a_4271_, 2);
lean_dec(v_unused_4365_);
v_unused_4366_ = lean_ctor_get(v_a_4271_, 1);
lean_dec(v_unused_4366_);
v___x_4316_ = v_a_4271_;
v_isShared_4317_ = v_isSharedCheck_4360_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_whichLean4Export_4314_);
lean_inc(v_whichLake_4313_);
lean_inc(v_whichLandrun_4312_);
lean_inc(v_binPath_4311_);
lean_inc(v_leanPath_4310_);
lean_inc(v_projectDir_4309_);
lean_dec(v_a_4271_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4360_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4318_; 
lean_inc_ref(v_projectDir_4309_);
v___x_4318_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_4261_, v_projectDir_4309_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4351_; 
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4321_ = v___x_4318_;
v_isShared_4322_ = v_isSharedCheck_4351_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4318_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4351_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
if (lean_obj_tag(v_a_4319_) == 1)
{
lean_object* v_val_4323_; lean_object* v___x_4325_; 
lean_del_object(v___x_4316_);
lean_dec_ref(v_whichLean4Export_4314_);
lean_dec_ref(v_whichLake_4313_);
lean_dec_ref(v_whichLandrun_4312_);
lean_dec_ref(v_binPath_4311_);
lean_dec_ref(v_leanPath_4310_);
lean_dec_ref(v_projectDir_4309_);
lean_dec(v_a_4308_);
lean_dec_ref(v___y_4298_);
lean_dec_ref(v___x_4296_);
lean_dec_ref(v_permitted__axioms_4293_);
lean_dec_ref(v_solution__module_4290_);
lean_dec_ref(v_challenge__module_4289_);
v_val_4323_ = lean_ctor_get(v_a_4319_, 0);
lean_inc(v_val_4323_);
lean_dec_ref_known(v_a_4319_, 1);
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 0, v_val_4323_);
v___x_4325_ = v___x_4321_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_val_4323_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
else
{
lean_object* v___x_4327_; lean_object* v___x_4328_; size_t v_sz_4329_; lean_object* v___x_4330_; lean_object* v___x_4332_; 
lean_del_object(v___x_4321_);
lean_dec(v_a_4319_);
v___x_4327_ = l_String_toName(v_challenge__module_4289_);
v___x_4328_ = l_String_toName(v_solution__module_4290_);
v_sz_4329_ = lean_array_size(v_permitted__axioms_4293_);
v___x_4330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_4329_, v___x_4295_, v_permitted__axioms_4293_);
lean_inc(v_a_4308_);
lean_inc_ref(v_whichLean4Export_4314_);
lean_inc_ref(v_whichLake_4313_);
lean_inc_ref(v_whichLandrun_4312_);
lean_inc_ref(v___x_4330_);
lean_inc_ref(v___y_4298_);
lean_inc_ref(v___x_4296_);
lean_inc(v___x_4328_);
lean_inc(v___x_4327_);
lean_inc_ref(v_projectDir_4309_);
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 11, v_a_4308_);
lean_ctor_set(v___x_4316_, 5, v___x_4330_);
lean_ctor_set(v___x_4316_, 4, v___y_4298_);
lean_ctor_set(v___x_4316_, 3, v___x_4296_);
lean_ctor_set(v___x_4316_, 2, v___x_4328_);
lean_ctor_set(v___x_4316_, 1, v___x_4327_);
v___x_4332_ = v___x_4316_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_projectDir_4309_);
lean_ctor_set(v_reuseFailAlloc_4350_, 1, v___x_4327_);
lean_ctor_set(v_reuseFailAlloc_4350_, 2, v___x_4328_);
lean_ctor_set(v_reuseFailAlloc_4350_, 3, v___x_4296_);
lean_ctor_set(v_reuseFailAlloc_4350_, 4, v___y_4298_);
lean_ctor_set(v_reuseFailAlloc_4350_, 5, v___x_4330_);
lean_ctor_set(v_reuseFailAlloc_4350_, 6, v_leanPath_4310_);
lean_ctor_set(v_reuseFailAlloc_4350_, 7, v_binPath_4311_);
lean_ctor_set(v_reuseFailAlloc_4350_, 8, v_whichLandrun_4312_);
lean_ctor_set(v_reuseFailAlloc_4350_, 9, v_whichLake_4313_);
lean_ctor_set(v_reuseFailAlloc_4350_, 10, v_whichLean4Export_4314_);
lean_ctor_set(v_reuseFailAlloc_4350_, 11, v_a_4308_);
v___x_4332_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
lean_object* v___x_4333_; 
v___x_4333_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v___x_4332_);
lean_dec_ref(v___x_4332_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v_fst_4335_; lean_object* v_snd_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
lean_dec_ref_known(v___x_4333_, 1);
v_fst_4335_ = lean_ctor_get(v_a_4334_, 0);
lean_inc(v_fst_4335_);
v_snd_4336_ = lean_ctor_get(v_a_4334_, 1);
lean_inc(v_snd_4336_);
lean_dec(v_a_4334_);
v___x_4337_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4337_, 0, v_projectDir_4309_);
lean_ctor_set(v___x_4337_, 1, v___x_4327_);
lean_ctor_set(v___x_4337_, 2, v___x_4328_);
lean_ctor_set(v___x_4337_, 3, v___x_4296_);
lean_ctor_set(v___x_4337_, 4, v___y_4298_);
lean_ctor_set(v___x_4337_, 5, v___x_4330_);
lean_ctor_set(v___x_4337_, 6, v_fst_4335_);
lean_ctor_set(v___x_4337_, 7, v_snd_4336_);
lean_ctor_set(v___x_4337_, 8, v_whichLandrun_4312_);
lean_ctor_set(v___x_4337_, 9, v_whichLake_4313_);
lean_ctor_set(v___x_4337_, 10, v_whichLean4Export_4314_);
lean_ctor_set(v___x_4337_, 11, v_a_4308_);
v___x_4338_ = l_Lake_Check_compareIt(v___x_4337_);
lean_dec_ref_known(v___x_4337_, 12);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4346_; 
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4346_ == 0)
{
lean_object* v_unused_4347_; 
v_unused_4347_ = lean_ctor_get(v___x_4338_, 0);
lean_dec(v_unused_4347_);
v___x_4340_ = v___x_4338_;
v_isShared_4341_ = v_isSharedCheck_4346_;
goto v_resetjp_4339_;
}
else
{
lean_dec(v___x_4338_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4346_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4342_; lean_object* v___x_4344_; 
v___x_4342_ = l_Lake_Check_runChallenge___boxed__const__2;
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 0, v___x_4342_);
v___x_4344_ = v___x_4340_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4342_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
else
{
lean_object* v_a_4348_; 
v_a_4348_ = lean_ctor_get(v___x_4338_, 0);
lean_inc(v_a_4348_);
lean_dec_ref_known(v___x_4338_, 1);
v_a_4239_ = v_a_4348_;
goto v___jp_4238_;
}
}
else
{
lean_object* v_a_4349_; 
lean_dec_ref(v___x_4330_);
lean_dec(v___x_4328_);
lean_dec(v___x_4327_);
lean_dec_ref(v_whichLean4Export_4314_);
lean_dec_ref(v_whichLake_4313_);
lean_dec_ref(v_whichLandrun_4312_);
lean_dec_ref(v_projectDir_4309_);
lean_dec(v_a_4308_);
lean_dec_ref(v___y_4298_);
lean_dec_ref(v___x_4296_);
v_a_4349_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4349_);
lean_dec_ref_known(v___x_4333_, 1);
v_a_4239_ = v_a_4349_;
goto v___jp_4238_;
}
}
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
lean_del_object(v___x_4316_);
lean_dec_ref(v_whichLean4Export_4314_);
lean_dec_ref(v_whichLake_4313_);
lean_dec_ref(v_whichLandrun_4312_);
lean_dec_ref(v_binPath_4311_);
lean_dec_ref(v_leanPath_4310_);
lean_dec_ref(v_projectDir_4309_);
lean_dec(v_a_4308_);
lean_dec_ref(v___y_4298_);
lean_dec_ref(v___x_4296_);
lean_dec_ref(v_permitted__axioms_4293_);
lean_dec_ref(v_solution__module_4290_);
lean_dec_ref(v_challenge__module_4289_);
v_a_4352_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4318_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4318_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
lean_dec_ref(v___y_4298_);
lean_dec_ref(v___x_4296_);
lean_dec_ref(v_permitted__axioms_4293_);
lean_dec_ref(v_solution__module_4290_);
lean_dec_ref(v_challenge__module_4289_);
lean_dec(v_a_4271_);
v_a_4368_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4370_ = v___x_4299_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4299_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
}
v___jp_4376_:
{
size_t v_sz_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; uint8_t v___x_4382_; 
v_sz_4378_ = lean_array_size(v___y_4377_);
v___x_4379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_4378_, v___x_4295_, v___y_4377_);
v___x_4380_ = lean_array_get_size(v___x_4296_);
v___x_4381_ = lean_unsigned_to_nat(0u);
v___x_4382_ = lean_nat_dec_eq(v___x_4380_, v___x_4381_);
if (v___x_4382_ == 0)
{
v___y_4298_ = v___x_4379_;
goto v___jp_4297_;
}
else
{
lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4383_ = lean_array_get_size(v___x_4379_);
v___x_4384_ = lean_nat_dec_eq(v___x_4383_, v___x_4381_);
if (v___x_4384_ == 0)
{
v___y_4298_ = v___x_4379_;
goto v___jp_4297_;
}
else
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
lean_dec_ref(v___x_4379_);
lean_dec_ref(v___x_4296_);
lean_dec_ref(v_permitted__axioms_4293_);
lean_dec_ref(v_solution__module_4290_);
lean_dec_ref(v_challenge__module_4289_);
lean_dec(v_a_4288_);
lean_dec(v_a_4271_);
v___x_4385_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__3));
v___x_4386_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4385_);
return v___x_4386_;
}
}
}
}
}
v___jp_4275_:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4277_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__1));
v___x_4278_ = lean_string_append(v___x_4277_, v_val_4272_);
v___x_4279_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__2));
v___x_4280_ = lean_string_append(v___x_4278_, v___x_4279_);
v___x_4281_ = lean_string_append(v___x_4280_, v_a_4276_);
lean_dec_ref(v_a_4276_);
v___x_4282_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4281_);
lean_dec_ref(v___x_4281_);
return v___x_4282_;
}
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
lean_dec(v_a_4271_);
v_a_4389_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4273_, 1);
v___x_4390_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__4));
v___x_4391_ = lean_io_error_to_string(v_a_4389_);
v___x_4392_ = lean_string_append(v___x_4390_, v___x_4391_);
lean_dec_ref(v___x_4391_);
v___x_4393_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4392_);
lean_dec_ref(v___x_4392_);
return v___x_4393_;
}
}
else
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
lean_dec_ref_known(v_a_4263_, 1);
v___x_4394_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__5));
v___x_4395_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4394_);
return v___x_4395_;
}
}
}
}
else
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
v_a_4397_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4399_ = v___x_4262_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4262_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_a_4397_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
v___jp_4238_:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4240_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_4241_ = lean_io_error_to_string(v_a_4239_);
v___x_4242_ = lean_string_append(v___x_4240_, v___x_4241_);
lean_dec_ref(v___x_4241_);
v___x_4243_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_4242_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4251_; 
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4251_ == 0)
{
lean_object* v_unused_4252_; 
v_unused_4252_ = lean_ctor_get(v___x_4243_, 0);
lean_dec(v_unused_4252_);
v___x_4245_ = v___x_4243_;
v_isShared_4246_ = v_isSharedCheck_4251_;
goto v_resetjp_4244_;
}
else
{
lean_dec(v___x_4243_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4251_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4247_; lean_object* v___x_4249_; 
v___x_4247_ = l_Lake_Check_runChallenge___boxed__const__1;
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v___x_4247_);
v___x_4249_ = v___x_4245_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4247_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
v_a_4253_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4243_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4243_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runChallenge___boxed(lean_object* v_configFile_x3f_4405_, lean_object* v_lean_4406_, lean_object* v_lake_4407_, lean_object* v_projectDir_4408_, lean_object* v_a_4409_){
_start:
{
lean_object* v_res_4410_; 
v_res_4410_ = l_Lake_Check_runChallenge(v_configFile_x3f_4405_, v_lean_4406_, v_lake_4407_, v_projectDir_4408_);
lean_dec_ref(v_lake_4407_);
lean_dec(v_configFile_x3f_4405_);
return v_res_4410_;
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
