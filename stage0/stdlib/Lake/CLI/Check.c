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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_get_stdout();
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
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
lean_object* lean_io_prim_handle_read(lean_object*, size_t);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_task_get_own(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* l_LeanExport_parseStream(lean_object*);
lean_object* l_Lake_Check_compareAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Check_checkAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_io_create_dir(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_String_compare___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lake_Check_usedAxioms(lean_object*);
extern uint8_t l_System_Platform_isLinux;
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLeanPrefix(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLeanPrefix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLakeHome(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLakeHome___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "`lake "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` needs `"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 431, .m_capacity = 431, .m_length = 430, .m_data = "` to sandbox the code it checks, and it was not found.\n\n  Install `bubblewrap` from your distribution and put `bwrap` on PATH, or set\n  COMPARATOR_BWRAP to its full path. It needs either unprivileged user\n  namespaces or a `bwrap` installed setuid root, which is how distributions\n  that disable them ship it.\n\n  There is no unsandboxed mode: the code being checked is untrusted, and it\n  is built and exported inside the sandbox."};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--tmpfs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--ro-bind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--bind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--setenv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "/home"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__1_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__8 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__8_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--chdir"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__10 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__10_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "/root"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__12 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__12_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "/run/user"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__15 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__15_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "/tmp"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__16 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__16_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "--dir"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__17 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__17_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "/tmp/home"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__18 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__18_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HOME"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__19 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__19_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--unshare-all"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__20 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__20_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "--die-with-parent"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__21 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__21_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--new-session"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__22 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__22_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__0_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__19_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__18_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__20_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__21_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__22_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__23 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__23_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "--share-net"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__24 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__24_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__24_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__25 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__25_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "--dev"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__26 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__26_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "/dev"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__27 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__27_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--proc"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__28 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__28_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "/proc"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__29 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__29_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "--clearenv"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__30 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__30_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-i"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__0_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Child exited with "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0;
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
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "LEAN_ABORT_ON_PANIC"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__9 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__9_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__9_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__10 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__10_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__10_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__15 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__15_value;
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
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__19_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "/run"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "/var"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths___closed__1_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths___closed__0_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths___closed__1_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths___closed__2_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths___closed__2_value;
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "check"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__0_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "LAKE_CHECK_EXPORT"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__2_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__10_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__3_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__3_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Building and exporting"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LEAN_PATH"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__0_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__0_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1_value;
static const lean_string_object l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Exporting "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " from "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__7_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__16_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " kernel rejected the solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " exited with "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " kernel accepts the solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__3_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "export_file_path"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "permitted_axioms"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unpermitted_axiom_hard_error"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "num_threads"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "nat_extension"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__20 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__20_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__20_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "string_extension"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__27;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Running "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " kernel on solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--silent"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--from-export"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean default"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2_value;
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Check_compareIt___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Your solution is okay!"};
static const lean_object* l_Lake_Check_compareIt___lam__0___closed__0 = (const lean_object*)&l_Lake_Check_compareIt___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lake_Check_instFromJsonConfig_fromJson___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(67, 66, 102, 170, 71, 166, 115, 173)}};
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
static const lean_ctor_object l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__2_value)}};
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
static const lean_ctor_object l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__0_value)}};
static const lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1;
static lean_once_cell_t l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2;
static const lean_ctor_object l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1_value)}};
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
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12_value)}};
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
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 153, .m_capacity = 153, .m_length = 152, .m_data = "` sandboxes the code it checks with `bwrap`, which needs Linux namespaces. There is no unsandboxed mode, so the command is unavailable on this platform."};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "COMPARATOR_BWRAP"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leanexport"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leanchecker"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` needs `env` on PATH to build inside the sandbox"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` needs `git` on PATH to build inside the sandbox"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "bwrap"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` kernel `"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` was not found"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` has an empty command"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Check_0__Lake_Check_checkProject___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_checkProject___closed__0_value;
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
v_externalKernels_3_ = lean_ctor_get(v_a_1_, 15);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLeanPrefix(lean_object* v_a_29_){
_start:
{
lean_object* v_leanPrefix_31_; lean_object* v___x_32_; 
v_leanPrefix_31_ = lean_ctor_get(v_a_29_, 6);
lean_inc_ref(v_leanPrefix_31_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v_leanPrefix_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLeanPrefix___boxed(lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l___private_Lake_CLI_Check_0__Lake_Check_getLeanPrefix(v_a_33_);
lean_dec_ref(v_a_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLakeHome(lean_object* v_a_36_){
_start:
{
lean_object* v_lakeHome_38_; lean_object* v___x_39_; 
v_lakeHome_38_ = lean_ctor_get(v_a_36_, 11);
lean_inc_ref(v_lakeHome_38_);
v___x_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_39_, 0, v_lakeHome_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLakeHome___boxed(lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Lake_CLI_Check_0__Lake_Check_getLakeHome(v_a_40_);
lean_dec_ref(v_a_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule(lean_object* v_a_43_){
_start:
{
lean_object* v_challengeModule_45_; lean_object* v___x_46_; 
v_challengeModule_45_ = lean_ctor_get(v_a_43_, 1);
lean_inc(v_challengeModule_45_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v_challengeModule_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule___boxed(lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule(v_a_47_);
lean_dec_ref(v_a_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule(lean_object* v_a_50_){
_start:
{
lean_object* v_solutionModule_52_; lean_object* v___x_53_; 
v_solutionModule_52_ = lean_ctor_get(v_a_50_, 2);
lean_inc(v_solutionModule_52_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v_solutionModule_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule___boxed(lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule(v_a_54_);
lean_dec_ref(v_a_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms(lean_object* v_a_57_){
_start:
{
lean_object* v_legalAxioms_59_; lean_object* v___x_60_; 
v_legalAxioms_59_ = lean_ctor_get(v_a_57_, 5);
lean_inc_ref(v_legalAxioms_59_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v_legalAxioms_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms___boxed(lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms(v_a_61_);
lean_dec_ref(v_a_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_whichExe(lean_object* v_exe_69_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_71_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v___x_72_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__1));
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_mk_empty_array_with_capacity(v___x_73_);
v___x_75_ = lean_array_push(v___x_74_, v_exe_69_);
v___x_76_ = lean_box(0);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__2));
v___x_79_ = 1;
v___x_80_ = 0;
v___x_81_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_81_, 0, v___x_71_);
lean_ctor_set(v___x_81_, 1, v___x_72_);
lean_ctor_set(v___x_81_, 2, v___x_75_);
lean_ctor_set(v___x_81_, 3, v___x_76_);
lean_ctor_set(v___x_81_, 4, v___x_78_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*5, v___x_79_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*5 + 1, v___x_80_);
v___x_82_ = l_IO_Process_output(v___x_81_, v___x_76_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_107_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_107_ == 0)
{
v___x_85_ = v___x_82_;
v_isShared_86_ = v_isSharedCheck_107_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_107_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
uint32_t v_exitCode_87_; lean_object* v_stdout_88_; uint32_t v___x_89_; uint8_t v___x_90_; 
v_exitCode_87_ = lean_ctor_get_uint32(v_a_83_, sizeof(void*)*2);
v_stdout_88_ = lean_ctor_get(v_a_83_, 0);
lean_inc_ref(v_stdout_88_);
lean_dec(v_a_83_);
v___x_89_ = 0;
v___x_90_ = lean_uint32_dec_eq(v_exitCode_87_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_92_; 
lean_dec_ref(v_stdout_88_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_76_);
v___x_92_ = v___x_85_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_76_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_94_ = lean_string_utf8_byte_size(v_stdout_88_);
v___x_95_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_95_, 0, v_stdout_88_);
lean_ctor_set(v___x_95_, 1, v___x_77_);
lean_ctor_set(v___x_95_, 2, v___x_94_);
v___x_96_ = l_String_Slice_trimAscii(v___x_95_);
v___x_97_ = l_String_Slice_toString(v___x_96_);
lean_dec_ref(v___x_96_);
v___x_98_ = lean_string_utf8_byte_size(v___x_97_);
v___x_99_ = lean_nat_dec_eq(v___x_98_, v___x_77_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_97_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_100_);
v___x_102_ = v___x_85_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_100_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
else
{
lean_object* v___x_105_; 
lean_dec_ref(v___x_97_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_76_);
v___x_105_ = v___x_85_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_76_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
else
{
lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_114_ == 0)
{
lean_object* v_unused_115_; 
v_unused_115_ = lean_ctor_get(v___x_82_, 0);
lean_dec(v_unused_115_);
v___x_109_ = v___x_82_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_dec(v___x_82_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 0);
lean_ctor_set(v___x_109_, 0, v___x_76_);
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_76_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_whichExe___boxed(lean_object* v_exe_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v_exe_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError(lean_object* v_cmd_122_, lean_object* v_exe_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_124_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_125_ = lean_string_append(v___x_124_, v_cmd_122_);
v___x_126_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__1));
v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
v___x_128_ = lean_string_append(v___x_127_, v_exe_123_);
v___x_129_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__2));
v___x_130_ = lean_string_append(v___x_128_, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___boxed(lean_object* v_cmd_131_, lean_object* v_exe_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError(v_cmd_131_, v_exe_132_);
lean_dec_ref(v_exe_132_);
lean_dec_ref(v_cmd_131_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1(lean_object* v_as_134_, size_t v_sz_135_, size_t v_i_136_, lean_object* v_b_137_){
_start:
{
lean_object* v_a_140_; uint8_t v___x_144_; 
v___x_144_ = lean_usize_dec_lt(v_i_136_, v_sz_135_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; 
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v_b_137_);
return v___x_145_;
}
else
{
lean_object* v_a_146_; lean_object* v___x_147_; 
v_a_146_ = lean_array_uget_borrowed(v_as_134_, v_i_136_);
v___x_147_ = lean_io_getenv(v_a_146_);
if (lean_obj_tag(v___x_147_) == 1)
{
lean_object* v_val_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_val_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_val_148_);
lean_dec_ref_known(v___x_147_, 1);
lean_inc(v_a_146_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v_a_146_);
lean_ctor_set(v___x_149_, 1, v_val_148_);
v___x_150_ = lean_array_push(v_b_137_, v___x_149_);
v_a_140_ = v___x_150_;
goto v___jp_139_;
}
else
{
lean_dec(v___x_147_);
v_a_140_ = v_b_137_;
goto v___jp_139_;
}
}
v___jp_139_:
{
size_t v___x_141_; size_t v___x_142_; 
v___x_141_ = ((size_t)1ULL);
v___x_142_ = lean_usize_add(v_i_136_, v___x_141_);
v_i_136_ = v___x_142_;
v_b_137_ = v_a_140_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1___boxed(lean_object* v_as_151_, lean_object* v_sz_152_, lean_object* v_i_153_, lean_object* v_b_154_, lean_object* v___y_155_){
_start:
{
size_t v_sz_boxed_156_; size_t v_i_boxed_157_; lean_object* v_res_158_; 
v_sz_boxed_156_ = lean_unbox_usize(v_sz_152_);
lean_dec(v_sz_152_);
v_i_boxed_157_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1(v_as_151_, v_sz_boxed_156_, v_i_boxed_157_, v_b_154_);
lean_dec_ref(v_as_151_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(lean_object* v_fst_159_, lean_object* v_as_160_, size_t v_i_161_, size_t v_stop_162_, lean_object* v_b_163_){
_start:
{
lean_object* v___y_165_; uint8_t v___x_169_; 
v___x_169_ = lean_usize_dec_eq(v_i_161_, v_stop_162_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v_fst_171_; uint8_t v___x_172_; 
v___x_170_ = lean_array_uget_borrowed(v_as_160_, v_i_161_);
v_fst_171_ = lean_ctor_get(v___x_170_, 0);
v___x_172_ = lean_string_dec_eq(v_fst_171_, v_fst_159_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
lean_inc(v___x_170_);
v___x_173_ = lean_array_push(v_b_163_, v___x_170_);
v___y_165_ = v___x_173_;
goto v___jp_164_;
}
else
{
v___y_165_ = v_b_163_;
goto v___jp_164_;
}
}
else
{
return v_b_163_;
}
v___jp_164_:
{
size_t v___x_166_; size_t v___x_167_; 
v___x_166_ = ((size_t)1ULL);
v___x_167_ = lean_usize_add(v_i_161_, v___x_166_);
v_i_161_ = v___x_167_;
v_b_163_ = v___y_165_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0___boxed(lean_object* v_fst_174_, lean_object* v_as_175_, lean_object* v_i_176_, lean_object* v_stop_177_, lean_object* v_b_178_){
_start:
{
size_t v_i_boxed_179_; size_t v_stop_boxed_180_; lean_object* v_res_181_; 
v_i_boxed_179_ = lean_unbox_usize(v_i_176_);
lean_dec(v_i_176_);
v_stop_boxed_180_ = lean_unbox_usize(v_stop_177_);
lean_dec(v_stop_177_);
v_res_181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(v_fst_174_, v_as_175_, v_i_boxed_179_, v_stop_boxed_180_, v_b_178_);
lean_dec_ref(v_as_175_);
lean_dec_ref(v_fst_174_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2(lean_object* v_as_184_, size_t v_sz_185_, size_t v_i_186_, lean_object* v_b_187_){
_start:
{
lean_object* v_a_190_; uint8_t v___x_194_; 
v___x_194_ = lean_usize_dec_lt(v_i_186_, v_sz_185_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v_b_187_);
return v___x_195_;
}
else
{
lean_object* v_a_196_; lean_object* v_fst_197_; lean_object* v_snd_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_220_; 
v_a_196_ = lean_array_uget(v_as_184_, v_i_186_);
v_fst_197_ = lean_ctor_get(v_a_196_, 0);
v_snd_198_ = lean_ctor_get(v_a_196_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_a_196_);
if (v_isSharedCheck_220_ == 0)
{
v___x_200_ = v_a_196_;
v_isShared_201_ = v_isSharedCheck_220_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_snd_198_);
lean_inc(v_fst_197_);
lean_dec(v_a_196_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_220_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___y_203_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_array_get_size(v_b_187_);
v___x_211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___closed__0));
v___x_212_ = lean_nat_dec_lt(v___x_209_, v___x_210_);
if (v___x_212_ == 0)
{
lean_dec_ref(v_b_187_);
v___y_203_ = v___x_211_;
goto v___jp_202_;
}
else
{
uint8_t v___x_213_; 
v___x_213_ = lean_nat_dec_le(v___x_210_, v___x_210_);
if (v___x_213_ == 0)
{
if (v___x_212_ == 0)
{
lean_dec_ref(v_b_187_);
v___y_203_ = v___x_211_;
goto v___jp_202_;
}
else
{
size_t v___x_214_; size_t v___x_215_; lean_object* v___x_216_; 
v___x_214_ = ((size_t)0ULL);
v___x_215_ = lean_usize_of_nat(v___x_210_);
v___x_216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(v_fst_197_, v_b_187_, v___x_214_, v___x_215_, v___x_211_);
lean_dec_ref(v_b_187_);
v___y_203_ = v___x_216_;
goto v___jp_202_;
}
}
else
{
size_t v___x_217_; size_t v___x_218_; lean_object* v___x_219_; 
v___x_217_ = ((size_t)0ULL);
v___x_218_ = lean_usize_of_nat(v___x_210_);
v___x_219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(v_fst_197_, v_b_187_, v___x_217_, v___x_218_, v___x_211_);
lean_dec_ref(v_b_187_);
v___y_203_ = v___x_219_;
goto v___jp_202_;
}
}
v___jp_202_:
{
if (lean_obj_tag(v_snd_198_) == 1)
{
lean_object* v_val_204_; lean_object* v___x_206_; 
v_val_204_ = lean_ctor_get(v_snd_198_, 0);
lean_inc(v_val_204_);
lean_dec_ref_known(v_snd_198_, 1);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 1, v_val_204_);
v___x_206_ = v___x_200_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_fst_197_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_val_204_);
v___x_206_ = v_reuseFailAlloc_208_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; 
v___x_207_ = lean_array_push(v___y_203_, v___x_206_);
v_a_190_ = v___x_207_;
goto v___jp_189_;
}
}
else
{
lean_del_object(v___x_200_);
lean_dec(v_snd_198_);
lean_dec(v_fst_197_);
v_a_190_ = v___y_203_;
goto v___jp_189_;
}
}
}
}
v___jp_189_:
{
size_t v___x_191_; size_t v___x_192_; 
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_add(v_i_186_, v___x_191_);
v_i_186_ = v___x_192_;
v_b_187_ = v_a_190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___boxed(lean_object* v_as_221_, lean_object* v_sz_222_, lean_object* v_i_223_, lean_object* v_b_224_, lean_object* v___y_225_){
_start:
{
size_t v_sz_boxed_226_; size_t v_i_boxed_227_; lean_object* v_res_228_; 
v_sz_boxed_226_ = lean_unbox_usize(v_sz_222_);
lean_dec(v_sz_222_);
v_i_boxed_227_ = lean_unbox_usize(v_i_223_);
lean_dec(v_i_223_);
v_res_228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2(v_as_221_, v_sz_boxed_226_, v_i_boxed_227_, v_b_224_);
lean_dec_ref(v_as_221_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(lean_object* v_spawnArgs_229_){
_start:
{
lean_object* v_envPass_231_; lean_object* v_envOverride_232_; lean_object* v_env_233_; size_t v_sz_234_; size_t v___x_235_; lean_object* v___x_236_; 
v_envPass_231_ = lean_ctor_get(v_spawnArgs_229_, 2);
v_envOverride_232_ = lean_ctor_get(v_spawnArgs_229_, 3);
v_env_233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___closed__0));
v_sz_234_ = lean_array_size(v_envPass_231_);
v___x_235_ = ((size_t)0ULL);
v___x_236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1(v_envPass_231_, v_sz_234_, v___x_235_, v_env_233_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; size_t v_sz_238_; lean_object* v___x_239_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_236_, 1);
v_sz_238_ = lean_array_size(v_envOverride_232_);
v___x_239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2(v_envOverride_232_, v_sz_238_, v___x_235_, v_a_237_);
return v___x_239_;
}
else
{
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv___boxed(lean_object* v_spawnArgs_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(v_spawnArgs_240_);
lean_dec_ref(v_spawnArgs_240_);
return v_res_242_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_245_ = lean_unsigned_to_nat(2u);
v___x_246_ = lean_mk_empty_array_with_capacity(v___x_245_);
v___x_247_ = lean_array_push(v___x_246_, v___x_244_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(lean_object* v_as_248_, size_t v_i_249_, size_t v_stop_250_, lean_object* v_b_251_){
_start:
{
uint8_t v___x_252_; 
v___x_252_ = lean_usize_dec_eq(v_i_249_, v_stop_250_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; size_t v___x_257_; size_t v___x_258_; 
v___x_253_ = lean_array_uget_borrowed(v_as_248_, v_i_249_);
v___x_254_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1);
lean_inc(v___x_253_);
v___x_255_ = lean_array_push(v___x_254_, v___x_253_);
v___x_256_ = l_Array_append___redArg(v_b_251_, v___x_255_);
lean_dec_ref(v___x_255_);
v___x_257_ = ((size_t)1ULL);
v___x_258_ = lean_usize_add(v_i_249_, v___x_257_);
v_i_249_ = v___x_258_;
v_b_251_ = v___x_256_;
goto _start;
}
else
{
return v_b_251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___boxed(lean_object* v_as_260_, lean_object* v_i_261_, lean_object* v_stop_262_, lean_object* v_b_263_){
_start:
{
size_t v_i_boxed_264_; size_t v_stop_boxed_265_; lean_object* v_res_266_; 
v_i_boxed_264_ = lean_unbox_usize(v_i_261_);
lean_dec(v_i_261_);
v_stop_boxed_265_ = lean_unbox_usize(v_stop_262_);
lean_dec(v_stop_262_);
v_res_266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(v_as_260_, v_i_boxed_264_, v_stop_boxed_265_, v_b_263_);
lean_dec_ref(v_as_260_);
return v_res_266_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__0));
v___x_269_ = lean_unsigned_to_nat(3u);
v___x_270_ = lean_mk_empty_array_with_capacity(v___x_269_);
v___x_271_ = lean_array_push(v___x_270_, v___x_268_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(lean_object* v_as_272_, size_t v_i_273_, size_t v_stop_274_, lean_object* v_b_275_){
_start:
{
uint8_t v___x_276_; 
v___x_276_ = lean_usize_dec_eq(v_i_273_, v_stop_274_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; size_t v___x_282_; size_t v___x_283_; 
v___x_277_ = lean_array_uget_borrowed(v_as_272_, v_i_273_);
v___x_278_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1);
lean_inc_n(v___x_277_, 2);
v___x_279_ = lean_array_push(v___x_278_, v___x_277_);
v___x_280_ = lean_array_push(v___x_279_, v___x_277_);
v___x_281_ = l_Array_append___redArg(v_b_275_, v___x_280_);
lean_dec_ref(v___x_280_);
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_add(v_i_273_, v___x_282_);
v_i_273_ = v___x_283_;
v_b_275_ = v___x_281_;
goto _start;
}
else
{
return v_b_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___boxed(lean_object* v_as_285_, lean_object* v_i_286_, lean_object* v_stop_287_, lean_object* v_b_288_){
_start:
{
size_t v_i_boxed_289_; size_t v_stop_boxed_290_; lean_object* v_res_291_; 
v_i_boxed_289_ = lean_unbox_usize(v_i_286_);
lean_dec(v_i_286_);
v_stop_boxed_290_ = lean_unbox_usize(v_stop_287_);
lean_dec(v_stop_287_);
v_res_291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(v_as_285_, v_i_boxed_289_, v_stop_boxed_290_, v_b_288_);
lean_dec_ref(v_as_285_);
return v_res_291_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__0));
v___x_294_ = lean_unsigned_to_nat(3u);
v___x_295_ = lean_mk_empty_array_with_capacity(v___x_294_);
v___x_296_ = lean_array_push(v___x_295_, v___x_293_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(lean_object* v_as_297_, size_t v_i_298_, size_t v_stop_299_, lean_object* v_b_300_){
_start:
{
uint8_t v___x_301_; 
v___x_301_ = lean_usize_dec_eq(v_i_298_, v_stop_299_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; size_t v___x_307_; size_t v___x_308_; 
v___x_302_ = lean_array_uget_borrowed(v_as_297_, v_i_298_);
v___x_303_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1);
lean_inc_n(v___x_302_, 2);
v___x_304_ = lean_array_push(v___x_303_, v___x_302_);
v___x_305_ = lean_array_push(v___x_304_, v___x_302_);
v___x_306_ = l_Array_append___redArg(v_b_300_, v___x_305_);
lean_dec_ref(v___x_305_);
v___x_307_ = ((size_t)1ULL);
v___x_308_ = lean_usize_add(v_i_298_, v___x_307_);
v_i_298_ = v___x_308_;
v_b_300_ = v___x_306_;
goto _start;
}
else
{
return v_b_300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___boxed(lean_object* v_as_310_, lean_object* v_i_311_, lean_object* v_stop_312_, lean_object* v_b_313_){
_start:
{
size_t v_i_boxed_314_; size_t v_stop_boxed_315_; lean_object* v_res_316_; 
v_i_boxed_314_ = lean_unbox_usize(v_i_311_);
lean_dec(v_i_311_);
v_stop_boxed_315_ = lean_unbox_usize(v_stop_312_);
lean_dec(v_stop_312_);
v_res_316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(v_as_310_, v_i_boxed_314_, v_stop_boxed_315_, v_b_313_);
lean_dec_ref(v_as_310_);
return v_res_316_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__0));
v___x_319_ = lean_unsigned_to_nat(3u);
v___x_320_ = lean_mk_empty_array_with_capacity(v___x_319_);
v___x_321_ = lean_array_push(v___x_320_, v___x_318_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(lean_object* v_as_322_, size_t v_i_323_, size_t v_stop_324_, lean_object* v_b_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_usize_dec_eq(v_i_323_, v_stop_324_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; size_t v___x_334_; size_t v___x_335_; 
v___x_327_ = lean_array_uget_borrowed(v_as_322_, v_i_323_);
v_fst_328_ = lean_ctor_get(v___x_327_, 0);
v_snd_329_ = lean_ctor_get(v___x_327_, 1);
v___x_330_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1);
lean_inc(v_fst_328_);
v___x_331_ = lean_array_push(v___x_330_, v_fst_328_);
lean_inc(v_snd_329_);
v___x_332_ = lean_array_push(v___x_331_, v_snd_329_);
v___x_333_ = l_Array_append___redArg(v_b_325_, v___x_332_);
lean_dec_ref(v___x_332_);
v___x_334_ = ((size_t)1ULL);
v___x_335_ = lean_usize_add(v_i_323_, v___x_334_);
v_i_323_ = v___x_335_;
v_b_325_ = v___x_333_;
goto _start;
}
else
{
return v_b_325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___boxed(lean_object* v_as_337_, lean_object* v_i_338_, lean_object* v_stop_339_, lean_object* v_b_340_){
_start:
{
size_t v_i_boxed_341_; size_t v_stop_boxed_342_; lean_object* v_res_343_; 
v_i_boxed_341_ = lean_unbox_usize(v_i_338_);
lean_dec(v_i_338_);
v_stop_boxed_342_ = lean_unbox_usize(v_stop_339_);
lean_dec(v_stop_339_);
v_res_343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(v_as_337_, v_i_boxed_341_, v_stop_boxed_342_, v_b_340_);
lean_dec_ref(v_as_337_);
return v_res_343_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__0));
v___x_347_ = lean_unsigned_to_nat(18u);
v___x_348_ = lean_mk_empty_array_with_capacity(v___x_347_);
v___x_349_ = lean_array_push(v___x_348_, v___x_346_);
return v___x_349_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__0));
v___x_351_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2);
v___x_352_ = lean_array_push(v___x_351_, v___x_350_);
return v___x_352_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__0));
v___x_354_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3);
v___x_355_ = lean_array_push(v___x_354_, v___x_353_);
return v___x_355_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_357_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4);
v___x_358_ = lean_array_push(v___x_357_, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__1));
v___x_360_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5);
v___x_361_ = lean_array_push(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_363_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6);
v___x_364_ = lean_array_push(v___x_363_, v___x_362_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_366_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__8));
v___x_367_ = lean_unsigned_to_nat(2u);
v___x_368_ = lean_mk_empty_array_with_capacity(v___x_367_);
v___x_369_ = lean_array_push(v___x_368_, v___x_366_);
return v___x_369_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_371_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__10));
v___x_372_ = lean_unsigned_to_nat(2u);
v___x_373_ = lean_mk_empty_array_with_capacity(v___x_372_);
v___x_374_ = lean_array_push(v___x_373_, v___x_371_);
return v___x_374_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__12));
v___x_377_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7);
v___x_378_ = lean_array_push(v___x_377_, v___x_376_);
return v___x_378_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_380_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13);
v___x_381_ = lean_array_push(v___x_380_, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__15));
v___x_415_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14);
v___x_416_ = lean_array_push(v___x_415_, v___x_414_);
return v___x_416_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_418_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31);
v___x_419_ = lean_array_push(v___x_418_, v___x_417_);
return v___x_419_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__16));
v___x_421_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32);
v___x_422_ = lean_array_push(v___x_421_, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__17));
v___x_424_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33);
v___x_425_ = lean_array_push(v___x_424_, v___x_423_);
return v___x_425_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__18));
v___x_427_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34);
v___x_428_ = lean_array_push(v___x_427_, v___x_426_);
return v___x_428_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__26));
v___x_430_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35);
v___x_431_ = lean_array_push(v___x_430_, v___x_429_);
return v___x_431_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__27));
v___x_433_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36);
v___x_434_ = lean_array_push(v___x_433_, v___x_432_);
return v___x_434_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__28));
v___x_436_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37);
v___x_437_ = lean_array_push(v___x_436_, v___x_435_);
return v___x_437_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__29));
v___x_439_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38);
v___x_440_ = lean_array_push(v___x_439_, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_args_443_; 
v___x_441_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__30));
v___x_442_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39);
v_args_443_ = lean_array_push(v___x_442_, v___x_441_);
return v_args_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs(lean_object* v_spawnArgs_444_, lean_object* v_env_445_, lean_object* v_projectDir_446_){
_start:
{
lean_object* v_cmd_447_; lean_object* v_args_448_; lean_object* v_readablePaths_449_; lean_object* v_writablePaths_450_; lean_object* v_tmpfsPaths_451_; uint8_t v_network_452_; lean_object* v_cwd_453_; lean_object* v___y_455_; lean_object* v___y_461_; lean_object* v___y_470_; lean_object* v_args_475_; lean_object* v___x_476_; lean_object* v___y_478_; lean_object* v___y_489_; lean_object* v___y_500_; lean_object* v___x_510_; uint8_t v___x_511_; 
v_cmd_447_ = lean_ctor_get(v_spawnArgs_444_, 0);
lean_inc_ref(v_cmd_447_);
v_args_448_ = lean_ctor_get(v_spawnArgs_444_, 1);
lean_inc_ref(v_args_448_);
v_readablePaths_449_ = lean_ctor_get(v_spawnArgs_444_, 4);
lean_inc_ref(v_readablePaths_449_);
v_writablePaths_450_ = lean_ctor_get(v_spawnArgs_444_, 5);
lean_inc_ref(v_writablePaths_450_);
v_tmpfsPaths_451_ = lean_ctor_get(v_spawnArgs_444_, 6);
lean_inc_ref(v_tmpfsPaths_451_);
v_network_452_ = lean_ctor_get_uint8(v_spawnArgs_444_, sizeof(void*)*8);
v_cwd_453_ = lean_ctor_get(v_spawnArgs_444_, 7);
lean_inc(v_cwd_453_);
lean_dec_ref(v_spawnArgs_444_);
v_args_475_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_510_ = lean_array_get_size(v_tmpfsPaths_451_);
v___x_511_ = lean_nat_dec_lt(v___x_476_, v___x_510_);
if (v___x_511_ == 0)
{
lean_dec_ref(v_tmpfsPaths_451_);
v___y_500_ = v_args_475_;
goto v___jp_499_;
}
else
{
uint8_t v___x_512_; 
v___x_512_ = lean_nat_dec_le(v___x_510_, v___x_510_);
if (v___x_512_ == 0)
{
if (v___x_511_ == 0)
{
lean_dec_ref(v_tmpfsPaths_451_);
v___y_500_ = v_args_475_;
goto v___jp_499_;
}
else
{
size_t v___x_513_; size_t v___x_514_; lean_object* v___x_515_; 
v___x_513_ = ((size_t)0ULL);
v___x_514_ = lean_usize_of_nat(v___x_510_);
v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(v_tmpfsPaths_451_, v___x_513_, v___x_514_, v_args_475_);
lean_dec_ref(v_tmpfsPaths_451_);
v___y_500_ = v___x_515_;
goto v___jp_499_;
}
}
else
{
size_t v___x_516_; size_t v___x_517_; lean_object* v___x_518_; 
v___x_516_ = ((size_t)0ULL);
v___x_517_ = lean_usize_of_nat(v___x_510_);
v___x_518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(v_tmpfsPaths_451_, v___x_516_, v___x_517_, v_args_475_);
lean_dec_ref(v_tmpfsPaths_451_);
v___y_500_ = v___x_518_;
goto v___jp_499_;
}
}
v___jp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_456_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9);
v___x_457_ = lean_array_push(v___x_456_, v_cmd_447_);
v___x_458_ = l_Array_append___redArg(v___y_455_, v___x_457_);
lean_dec_ref(v___x_457_);
v___x_459_ = l_Array_append___redArg(v___x_458_, v_args_448_);
lean_dec_ref(v_args_448_);
return v___x_459_;
}
v___jp_460_:
{
if (lean_obj_tag(v_cwd_453_) == 1)
{
lean_object* v_val_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec_ref(v_projectDir_446_);
v_val_462_ = lean_ctor_get(v_cwd_453_, 0);
lean_inc(v_val_462_);
lean_dec_ref_known(v_cwd_453_, 1);
v___x_463_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11);
v___x_464_ = lean_array_push(v___x_463_, v_val_462_);
v___x_465_ = l_Array_append___redArg(v___y_461_, v___x_464_);
lean_dec_ref(v___x_464_);
v___y_455_ = v___x_465_;
goto v___jp_454_;
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v_cwd_453_);
v___x_466_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11);
v___x_467_ = lean_array_push(v___x_466_, v_projectDir_446_);
v___x_468_ = l_Array_append___redArg(v___y_461_, v___x_467_);
lean_dec_ref(v___x_467_);
v___y_455_ = v___x_468_;
goto v___jp_454_;
}
}
v___jp_469_:
{
lean_object* v___x_471_; lean_object* v_args_472_; 
v___x_471_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__23));
v_args_472_ = l_Array_append___redArg(v___y_470_, v___x_471_);
if (v_network_452_ == 0)
{
v___y_461_ = v_args_472_;
goto v___jp_460_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__25));
v___x_474_ = l_Array_append___redArg(v_args_472_, v___x_473_);
v___y_461_ = v___x_474_;
goto v___jp_460_;
}
}
v___jp_477_:
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_array_get_size(v_env_445_);
v___x_480_ = lean_nat_dec_lt(v___x_476_, v___x_479_);
if (v___x_480_ == 0)
{
v___y_470_ = v___y_478_;
goto v___jp_469_;
}
else
{
uint8_t v___x_481_; 
v___x_481_ = lean_nat_dec_le(v___x_479_, v___x_479_);
if (v___x_481_ == 0)
{
if (v___x_480_ == 0)
{
v___y_470_ = v___y_478_;
goto v___jp_469_;
}
else
{
size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
v___x_482_ = ((size_t)0ULL);
v___x_483_ = lean_usize_of_nat(v___x_479_);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(v_env_445_, v___x_482_, v___x_483_, v___y_478_);
v___y_470_ = v___x_484_;
goto v___jp_469_;
}
}
else
{
size_t v___x_485_; size_t v___x_486_; lean_object* v___x_487_; 
v___x_485_ = ((size_t)0ULL);
v___x_486_ = lean_usize_of_nat(v___x_479_);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(v_env_445_, v___x_485_, v___x_486_, v___y_478_);
v___y_470_ = v___x_487_;
goto v___jp_469_;
}
}
}
v___jp_488_:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_array_get_size(v_writablePaths_450_);
v___x_491_ = lean_nat_dec_lt(v___x_476_, v___x_490_);
if (v___x_491_ == 0)
{
lean_dec_ref(v_writablePaths_450_);
v___y_478_ = v___y_489_;
goto v___jp_477_;
}
else
{
uint8_t v___x_492_; 
v___x_492_ = lean_nat_dec_le(v___x_490_, v___x_490_);
if (v___x_492_ == 0)
{
if (v___x_491_ == 0)
{
lean_dec_ref(v_writablePaths_450_);
v___y_478_ = v___y_489_;
goto v___jp_477_;
}
else
{
size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v___x_493_ = ((size_t)0ULL);
v___x_494_ = lean_usize_of_nat(v___x_490_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(v_writablePaths_450_, v___x_493_, v___x_494_, v___y_489_);
lean_dec_ref(v_writablePaths_450_);
v___y_478_ = v___x_495_;
goto v___jp_477_;
}
}
else
{
size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; 
v___x_496_ = ((size_t)0ULL);
v___x_497_ = lean_usize_of_nat(v___x_490_);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(v_writablePaths_450_, v___x_496_, v___x_497_, v___y_489_);
lean_dec_ref(v_writablePaths_450_);
v___y_478_ = v___x_498_;
goto v___jp_477_;
}
}
}
v___jp_499_:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_array_get_size(v_readablePaths_449_);
v___x_502_ = lean_nat_dec_lt(v___x_476_, v___x_501_);
if (v___x_502_ == 0)
{
lean_dec_ref(v_readablePaths_449_);
v___y_489_ = v___y_500_;
goto v___jp_488_;
}
else
{
uint8_t v___x_503_; 
v___x_503_ = lean_nat_dec_le(v___x_501_, v___x_501_);
if (v___x_503_ == 0)
{
if (v___x_502_ == 0)
{
lean_dec_ref(v_readablePaths_449_);
v___y_489_ = v___y_500_;
goto v___jp_488_;
}
else
{
size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v___x_504_ = ((size_t)0ULL);
v___x_505_ = lean_usize_of_nat(v___x_501_);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(v_readablePaths_449_, v___x_504_, v___x_505_, v___y_500_);
lean_dec_ref(v_readablePaths_449_);
v___y_489_ = v___x_506_;
goto v___jp_488_;
}
}
else
{
size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; 
v___x_507_ = ((size_t)0ULL);
v___x_508_ = lean_usize_of_nat(v___x_501_);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(v_readablePaths_449_, v___x_507_, v___x_508_, v___y_500_);
lean_dec_ref(v_readablePaths_449_);
v___y_489_ = v___x_509_;
goto v___jp_488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___boxed(lean_object* v_spawnArgs_519_, lean_object* v_env_520_, lean_object* v_projectDir_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs(v_spawnArgs_519_, v_env_520_, v_projectDir_521_);
lean_dec_ref(v_env_520_);
return v_res_522_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__0));
v___x_525_ = lean_unsigned_to_nat(2u);
v___x_526_ = lean_mk_empty_array_with_capacity(v___x_525_);
v___x_527_ = lean_array_push(v___x_526_, v___x_524_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(lean_object* v_spawnArgs_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(v_spawnArgs_528_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_552_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_552_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_552_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_552_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_projectDir_536_; lean_object* v_whichSandbox_537_; lean_object* v_whichEnvBin_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v_projectDir_536_ = lean_ctor_get(v_a_529_, 0);
v_whichSandbox_537_ = lean_ctor_get(v_a_529_, 9);
v_whichEnvBin_538_ = lean_ctor_get(v_a_529_, 14);
v___x_539_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v___x_540_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1, &l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1);
lean_inc_ref(v_whichSandbox_537_);
v___x_541_ = lean_array_push(v___x_540_, v_whichSandbox_537_);
lean_inc_ref_n(v_projectDir_536_, 2);
v___x_542_ = l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs(v_spawnArgs_528_, v_a_532_, v_projectDir_536_);
lean_dec(v_a_532_);
v___x_543_ = l_Array_append___redArg(v___x_541_, v___x_542_);
lean_dec_ref(v___x_542_);
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v_projectDir_536_);
v___x_545_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__2));
v___x_546_ = 1;
v___x_547_ = 0;
lean_inc_ref(v_whichEnvBin_538_);
v___x_548_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_548_, 0, v___x_539_);
lean_ctor_set(v___x_548_, 1, v_whichEnvBin_538_);
lean_ctor_set(v___x_548_, 2, v___x_543_);
lean_ctor_set(v___x_548_, 3, v___x_544_);
lean_ctor_set(v___x_548_, 4, v___x_545_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*5, v___x_546_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*5 + 1, v___x_547_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_548_);
v___x_550_ = v___x_534_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec_ref(v_spawnArgs_528_);
v_a_553_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_531_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_531_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___boxed(lean_object* v_spawnArgs_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_561_, v_a_562_);
lean_dec_ref(v_a_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(lean_object* v_handle_565_, lean_object* v_child_566_){
_start:
{
lean_object* v_stdout_568_; size_t v___x_569_; lean_object* v___x_570_; 
v_stdout_568_ = lean_ctor_get(v_child_566_, 1);
v___x_569_ = ((size_t)4096ULL);
v___x_570_ = lean_io_prim_handle_read(v_stdout_568_, v___x_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; uint8_t v___x_572_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
v___x_572_ = l_ByteArray_isEmpty(v_a_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
v___x_573_ = lean_io_prim_handle_write(v_handle_565_, v_a_571_);
lean_dec(v_a_571_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_dec_ref_known(v___x_573_, 1);
goto _start;
}
else
{
return v___x_573_;
}
}
else
{
lean_object* v___x_575_; 
lean_dec(v_a_571_);
v___x_575_ = lean_io_prim_handle_flush(v_handle_565_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_583_; 
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; 
v_unused_584_ = lean_ctor_get(v___x_575_, 0);
lean_dec(v_unused_584_);
v___x_577_ = v___x_575_;
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
else
{
lean_dec(v___x_575_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_box(0);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_579_);
v___x_581_ = v___x_577_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
else
{
return v___x_575_;
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
v_a_585_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_570_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_570_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg___boxed(lean_object* v_handle_593_, lean_object* v_child_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(v_handle_593_, v_child_594_);
lean_dec_ref(v_child_594_);
lean_dec(v_handle_593_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop(lean_object* v_handle_597_, lean_object* v_args_598_, lean_object* v_child_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(v_handle_597_, v_child_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___boxed(lean_object* v_handle_602_, lean_object* v_args_603_, lean_object* v_child_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop(v_handle_602_, v_args_603_, v_child_604_);
lean_dec_ref(v_child_604_);
lean_dec_ref(v_args_603_);
lean_dec(v_handle_602_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(lean_object* v_e_607_){
_start:
{
if (lean_obj_tag(v_e_607_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_618_; 
v_a_609_ = lean_ctor_get(v_e_607_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v_e_607_);
if (v_isSharedCheck_618_ == 0)
{
v___x_611_ = v_e_607_;
v_isShared_612_ = v_isSharedCheck_618_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v_e_607_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_618_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_613_ = lean_io_error_to_string(v_a_609_);
v___x_614_ = lean_mk_io_user_error(v___x_613_);
if (v_isShared_612_ == 0)
{
lean_ctor_set_tag(v___x_611_, 1);
lean_ctor_set(v___x_611_, 0, v___x_614_);
v___x_616_ = v___x_611_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
v_a_619_ = lean_ctor_get(v_e_607_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_e_607_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v_e_607_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v_e_607_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set_tag(v___x_621_, 0);
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg___boxed(lean_object* v_e_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(v_e_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0(lean_object* v_00_u03b1_630_, lean_object* v_e_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(v_e_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___boxed(lean_object* v_00_u03b1_634_, lean_object* v_e_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0(v_00_u03b1_634_, v_e_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0(lean_object* v_handle_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(v_handle_638_, v_a_639_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 1);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
v_a_650_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_641_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_641_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set_tag(v___x_652_, 0);
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0___boxed(lean_object* v_handle_658_, lean_object* v_a_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0(v_handle_658_, v_a_659_);
lean_dec_ref(v_a_659_);
lean_dec(v_handle_658_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(lean_object* v_handle_665_, lean_object* v_args_666_){
_start:
{
lean_object* v___x_668_; lean_object* v_cmd_669_; lean_object* v_args_670_; lean_object* v_cwd_671_; lean_object* v_env_672_; uint8_t v_inheritEnv_673_; uint8_t v_setsid_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_734_; 
v___x_668_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___closed__0));
v_cmd_669_ = lean_ctor_get(v_args_666_, 1);
v_args_670_ = lean_ctor_get(v_args_666_, 2);
v_cwd_671_ = lean_ctor_get(v_args_666_, 3);
v_env_672_ = lean_ctor_get(v_args_666_, 4);
v_inheritEnv_673_ = lean_ctor_get_uint8(v_args_666_, sizeof(void*)*5);
v_setsid_674_ = lean_ctor_get_uint8(v_args_666_, sizeof(void*)*5 + 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_args_666_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v_args_666_, 0);
lean_dec(v_unused_735_);
v___x_676_ = v_args_666_;
v_isShared_677_ = v_isSharedCheck_734_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_env_672_);
lean_inc(v_cwd_671_);
lean_inc(v_args_670_);
lean_inc(v_cmd_669_);
lean_dec(v_args_666_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_734_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_668_);
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_cmd_669_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_args_670_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v_cwd_671_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v_env_672_);
lean_ctor_set_uint8(v_reuseFailAlloc_733_, sizeof(void*)*5, v_inheritEnv_673_);
lean_ctor_set_uint8(v_reuseFailAlloc_733_, sizeof(void*)*5 + 1, v_setsid_674_);
v___x_679_ = v_reuseFailAlloc_733_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; 
v___x_680_ = lean_io_process_spawn(v___x_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___f_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v_stderr_685_; lean_object* v___x_686_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc_n(v_a_681_, 2);
lean_dec_ref_known(v___x_680_, 1);
v___f_682_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0___boxed), 3, 2);
lean_closure_set(v___f_682_, 0, v_handle_665_);
lean_closure_set(v___f_682_, 1, v_a_681_);
v___x_683_ = lean_unsigned_to_nat(9u);
v___x_684_ = lean_io_as_task(v___f_682_, v___x_683_);
v_stderr_685_ = lean_ctor_get(v_a_681_, 2);
v___x_686_ = l_IO_FS_Handle_readToEnd(v_stderr_685_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = lean_io_process_child_wait(v___x_668_, v_a_681_);
lean_dec(v_a_681_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_708_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_708_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_708_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_708_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_task_get_own(v___x_684_);
v___x_699_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(v___x_698_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_dec_ref_known(v___x_699_, 1);
goto v___jp_693_;
}
else
{
if (lean_obj_tag(v___x_699_) == 0)
{
lean_dec_ref_known(v___x_699_, 1);
goto v___jp_693_;
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_del_object(v___x_691_);
lean_dec(v_a_689_);
lean_dec(v_a_687_);
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
v___jp_693_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_a_687_);
lean_ctor_set(v___x_694_, 1, v_a_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_694_);
v___x_696_ = v___x_691_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v_a_687_);
lean_dec_ref(v___x_684_);
v_a_709_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_688_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_688_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec_ref(v___x_684_);
lean_dec(v_a_681_);
v_a_717_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_686_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_686_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_handle_665_);
v_a_725_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_680_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_680_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___boxed(lean_object* v_handle_736_, lean_object* v_args_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(v_handle_736_, v_args_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(lean_object* v_s_740_){
_start:
{
lean_object* v___x_742_; lean_object* v_putStr_743_; lean_object* v___x_744_; 
v___x_742_ = lean_get_stderr();
v_putStr_743_ = lean_ctor_get(v___x_742_, 4);
lean_inc_ref(v_putStr_743_);
lean_dec_ref(v___x_742_);
v___x_744_ = lean_apply_2(v_putStr_743_, v_s_740_, lean_box(0));
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0___boxed(lean_object* v_s_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v_s_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(lean_object* v_handle_749_, lean_object* v_spawnArgs_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_750_, v_a_751_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_755_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
v___x_755_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(v_handle_749_, v_a_754_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v_fst_757_; lean_object* v_snd_758_; lean_object* v___x_759_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v_fst_757_ = lean_ctor_get(v_a_756_, 0);
lean_inc(v_fst_757_);
v_snd_758_ = lean_ctor_get(v_a_756_, 1);
lean_inc(v_snd_758_);
lean_dec(v_a_756_);
v___x_759_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v_fst_757_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_779_; 
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v___x_759_, 0);
lean_dec(v_unused_780_);
v___x_761_ = v___x_759_;
v_isShared_762_ = v_isSharedCheck_779_;
goto v_resetjp_760_;
}
else
{
lean_dec(v___x_759_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_779_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
uint32_t v___x_763_; uint32_t v___x_764_; uint8_t v___x_765_; 
v___x_763_ = 0;
v___x_764_ = lean_unbox_uint32(v_snd_758_);
v___x_765_ = lean_uint32_dec_eq(v___x_764_, v___x_763_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; uint32_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_766_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0));
v___x_767_ = lean_unbox_uint32(v_snd_758_);
lean_dec(v_snd_758_);
v___x_768_ = lean_uint32_to_nat(v___x_767_);
v___x_769_ = l_Nat_reprFast(v___x_768_);
v___x_770_ = lean_string_append(v___x_766_, v___x_769_);
lean_dec_ref(v___x_769_);
v___x_771_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
if (v_isShared_762_ == 0)
{
lean_ctor_set_tag(v___x_761_, 1);
lean_ctor_set(v___x_761_, 0, v___x_771_);
v___x_773_ = v___x_761_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_777_; 
lean_dec(v_snd_758_);
v___x_775_ = lean_box(0);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_775_);
v___x_777_ = v___x_761_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
else
{
lean_dec(v_snd_758_);
return v___x_759_;
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
v_a_781_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_755_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_755_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_handle_749_);
v_a_789_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_753_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_753_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___boxed(lean_object* v_handle_797_, lean_object* v_spawnArgs_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_handle_797_, v_spawnArgs_798_, v_a_799_);
lean_dec_ref(v_a_799_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(lean_object* v_spawnArgs_802_, lean_object* v_a_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_802_, v_a_803_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
v___x_807_ = lean_box(0);
v___x_808_ = l_IO_Process_output(v_a_806_, v___x_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; uint32_t v_exitCode_810_; lean_object* v_stdout_811_; lean_object* v_stderr_812_; lean_object* v___x_813_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v_exitCode_810_ = lean_ctor_get_uint32(v_a_809_, sizeof(void*)*2);
v_stdout_811_ = lean_ctor_get(v_a_809_, 0);
lean_inc_ref(v_stdout_811_);
v_stderr_812_ = lean_ctor_get(v_a_809_, 1);
lean_inc_ref(v_stderr_812_);
lean_dec(v_a_809_);
v___x_813_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v_stderr_812_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_830_; 
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v___x_813_, 0);
lean_dec(v_unused_831_);
v___x_815_ = v___x_813_;
v_isShared_816_ = v_isSharedCheck_830_;
goto v_resetjp_814_;
}
else
{
lean_dec(v___x_813_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_830_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint32_t v___x_817_; uint8_t v___x_818_; 
v___x_817_ = 0;
v___x_818_ = lean_uint32_dec_eq(v_exitCode_810_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
lean_dec_ref(v_stdout_811_);
v___x_819_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0));
v___x_820_ = lean_uint32_to_nat(v_exitCode_810_);
v___x_821_ = l_Nat_reprFast(v___x_820_);
v___x_822_ = lean_string_append(v___x_819_, v___x_821_);
lean_dec_ref(v___x_821_);
v___x_823_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
if (v_isShared_816_ == 0)
{
lean_ctor_set_tag(v___x_815_, 1);
lean_ctor_set(v___x_815_, 0, v___x_823_);
v___x_825_ = v___x_815_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
else
{
lean_object* v___x_828_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_stdout_811_);
v___x_828_ = v___x_815_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_stdout_811_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec_ref(v_stdout_811_);
v_a_832_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_813_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_813_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
v_a_840_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_808_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_808_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_a_848_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_805_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_805_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___boxed(lean_object* v_spawnArgs_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v_spawnArgs_856_, v_a_857_);
lean_dec_ref(v_a_857_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(lean_object* v_spawnArgs_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_860_, v_a_861_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v___x_865_ = lean_io_process_spawn(v_a_864_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_865_, 1);
v___x_867_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v___x_868_ = lean_io_process_child_wait(v___x_867_, v_a_866_);
lean_dec(v_a_866_);
return v___x_868_;
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_865_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_865_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_863_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_863_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode___boxed(lean_object* v_spawnArgs_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v_spawnArgs_885_, v_a_886_);
lean_dec_ref(v_a_886_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(lean_object* v_spawnArgs_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v_spawnArgs_889_, v_a_890_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_913_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_913_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_913_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_913_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
uint32_t v___x_897_; uint32_t v___x_898_; uint8_t v___x_899_; 
v___x_897_ = 0;
v___x_898_ = lean_unbox_uint32(v_a_893_);
v___x_899_ = lean_uint32_dec_eq(v___x_898_, v___x_897_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; uint32_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_900_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0));
v___x_901_ = lean_unbox_uint32(v_a_893_);
lean_dec(v_a_893_);
v___x_902_ = lean_uint32_to_nat(v___x_901_);
v___x_903_ = l_Nat_reprFast(v___x_902_);
v___x_904_ = lean_string_append(v___x_900_, v___x_903_);
lean_dec_ref(v___x_903_);
v___x_905_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
if (v_isShared_896_ == 0)
{
lean_ctor_set_tag(v___x_895_, 1);
lean_ctor_set(v___x_895_, 0, v___x_905_);
v___x_907_ = v___x_895_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
else
{
lean_object* v___x_909_; lean_object* v___x_911_; 
lean_dec(v_a_893_);
v___x_909_ = lean_box(0);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_909_);
v___x_911_ = v___x_895_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
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
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
v_a_914_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_892_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_892_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed___boxed(lean_object* v_spawnArgs_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v_spawnArgs_922_, v_a_923_);
lean_dec_ref(v_a_923_);
return v_res_925_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0));
v___x_928_ = lean_string_utf8_byte_size(v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(lean_object* v_s_929_){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_930_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0));
v___x_931_ = lean_string_utf8_byte_size(v_s_929_);
v___x_932_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1);
v___x_933_ = lean_nat_dec_le(v___x_932_, v___x_931_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; 
lean_dec_ref(v_s_929_);
v___x_934_ = lean_box(0);
return v___x_934_;
}
else
{
lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = lean_string_memcmp(v_s_929_, v___x_930_, v___x_935_, v___x_935_, v___x_932_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
lean_dec_ref(v_s_929_);
v___x_937_ = lean_box(0);
return v___x_937_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
lean_inc_ref(v_s_929_);
v___x_938_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_938_, 0, v_s_929_);
lean_ctor_set(v___x_938_, 1, v___x_935_);
lean_ctor_set(v___x_938_, 2, v___x_931_);
v___x_939_ = l_String_Slice_pos_x21(v___x_938_, v___x_932_);
lean_dec_ref_known(v___x_938_, 3);
v___x_940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_940_, 0, v_s_929_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
lean_ctor_set(v___x_940_, 2, v___x_931_);
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(lean_object* v_s_942_, lean_object* v_pat_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_s_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___boxed(lean_object* v_s_945_, lean_object* v_pat_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(v_s_945_, v_pat_946_);
lean_dec_ref(v_pat_946_);
return v_res_947_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0));
v___x_950_ = lean_string_utf8_byte_size(v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(lean_object* v_s_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_952_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0));
v___x_953_ = lean_string_utf8_byte_size(v_s_951_);
v___x_954_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1);
v___x_955_ = lean_nat_dec_le(v___x_954_, v___x_953_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_dec_ref(v_s_951_);
v___x_956_ = lean_box(0);
return v___x_956_;
}
else
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = lean_string_memcmp(v_s_951_, v___x_952_, v___x_957_, v___x_957_, v___x_954_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; 
lean_dec_ref(v_s_951_);
v___x_959_ = lean_box(0);
return v___x_959_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
lean_inc_ref(v_s_951_);
v___x_960_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_960_, 0, v_s_951_);
lean_ctor_set(v___x_960_, 1, v___x_957_);
lean_ctor_set(v___x_960_, 2, v___x_953_);
v___x_961_ = l_String_Slice_pos_x21(v___x_960_, v___x_954_);
lean_dec_ref_known(v___x_960_, 3);
v___x_962_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_962_, 0, v_s_951_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
lean_ctor_set(v___x_962_, 2, v___x_953_);
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(lean_object* v_s_964_, lean_object* v_pat_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_s_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___boxed(lean_object* v_s_967_, lean_object* v_pat_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(v_s_967_, v_pat_968_);
lean_dec_ref(v_pat_968_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg(){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___closed__0));
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___boxed(lean_object* v___dummy_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg();
return v_res_975_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0(void){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg();
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(lean_object* v_s_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___boxed(lean_object* v_s_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(v_s_979_);
lean_dec_ref(v_s_979_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(lean_object* v_a_981_, lean_object* v___x_982_, lean_object* v___x_983_, lean_object* v_a_984_, lean_object* v_b_985_){
_start:
{
lean_object* v_it_987_; lean_object* v_startInclusive_988_; lean_object* v_endExclusive_989_; 
if (lean_obj_tag(v_a_984_) == 0)
{
lean_object* v_currPos_994_; lean_object* v_searcher_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1018_; 
v_currPos_994_ = lean_ctor_get(v_a_984_, 0);
v_searcher_995_ = lean_ctor_get(v_a_984_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_a_984_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_997_ = v_a_984_;
v_isShared_998_ = v_isSharedCheck_1018_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_searcher_995_);
lean_inc(v_currPos_994_);
lean_dec(v_a_984_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1018_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
uint8_t v_decide_999_; 
v_decide_999_ = lean_nat_dec_eq(v_searcher_995_, v___x_983_);
if (v_decide_999_ == 0)
{
uint32_t v___x_1000_; uint32_t v___x_1001_; uint8_t v___x_1002_; 
v___x_1000_ = 10;
v___x_1001_ = lean_string_utf8_get_fast(v_a_981_, v_searcher_995_);
v___x_1002_ = lean_uint32_dec_eq(v___x_1001_, v___x_1000_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_string_utf8_next_fast(v_a_981_, v_searcher_995_);
lean_dec(v_searcher_995_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___x_1003_);
v___x_1005_ = v___x_997_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_currPos_994_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
v_a_984_ = v___x_1005_;
goto _start;
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v_slice_1011_; lean_object* v_nextIt_1013_; 
v___x_1008_ = lean_string_utf8_next_fast(v_a_981_, v_searcher_995_);
v___x_1009_ = lean_nat_sub(v___x_1008_, v_searcher_995_);
v___x_1010_ = lean_nat_add(v_searcher_995_, v___x_1009_);
lean_dec(v___x_1009_);
v_slice_1011_ = l_String_Slice_subslice_x21(v___x_982_, v_currPos_994_, v_searcher_995_);
lean_inc(v___x_1010_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___x_1010_);
lean_ctor_set(v___x_997_, 0, v___x_1010_);
v_nextIt_1013_ = v___x_997_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_1010_);
v_nextIt_1013_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v_startInclusive_1014_; lean_object* v_endExclusive_1015_; 
v_startInclusive_1014_ = lean_ctor_get(v_slice_1011_, 0);
lean_inc(v_startInclusive_1014_);
v_endExclusive_1015_ = lean_ctor_get(v_slice_1011_, 1);
lean_inc(v_endExclusive_1015_);
lean_dec_ref(v_slice_1011_);
v_it_987_ = v_nextIt_1013_;
v_startInclusive_988_ = v_startInclusive_1014_;
v_endExclusive_989_ = v_endExclusive_1015_;
goto v___jp_986_;
}
}
}
else
{
lean_object* v___x_1017_; 
lean_del_object(v___x_997_);
lean_dec(v_searcher_995_);
v___x_1017_ = lean_box(1);
lean_inc(v___x_983_);
v_it_987_ = v___x_1017_;
v_startInclusive_988_ = v_currPos_994_;
v_endExclusive_989_ = v___x_983_;
goto v___jp_986_;
}
}
}
else
{
lean_dec(v___x_983_);
lean_dec_ref(v_a_981_);
return v_b_985_;
}
v___jp_986_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
lean_inc_ref(v_a_981_);
v___x_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_990_, 0, v_a_981_);
lean_ctor_set(v___x_990_, 1, v_startInclusive_988_);
lean_ctor_set(v___x_990_, 2, v_endExclusive_989_);
v___x_991_ = l_String_Slice_toString(v___x_990_);
lean_dec_ref_known(v___x_990_, 3);
v___x_992_ = lean_array_push(v_b_985_, v___x_991_);
v_a_984_ = v_it_987_;
v_b_985_ = v___x_992_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg___boxed(lean_object* v_a_1019_, lean_object* v___x_1020_, lean_object* v___x_1021_, lean_object* v_a_1022_, lean_object* v_b_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1019_, v___x_1020_, v___x_1021_, v_a_1022_, v_b_1023_);
lean_dec_ref(v___x_1020_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(lean_object* v_as_x27_1025_, lean_object* v_b_1026_){
_start:
{
if (lean_obj_tag(v_as_x27_1025_) == 0)
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v_b_1026_);
return v___x_1028_;
}
else
{
lean_object* v_head_1029_; lean_object* v_tail_1030_; lean_object* v_fst_1031_; lean_object* v_snd_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1054_; 
v_head_1029_ = lean_ctor_get(v_as_x27_1025_, 0);
v_tail_1030_ = lean_ctor_get(v_as_x27_1025_, 1);
v_fst_1031_ = lean_ctor_get(v_b_1026_, 0);
v_snd_1032_ = lean_ctor_get(v_b_1026_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_b_1026_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1034_ = v_b_1026_;
v_isShared_1035_ = v_isSharedCheck_1054_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_snd_1032_);
lean_inc(v_fst_1031_);
lean_dec(v_b_1026_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1054_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; 
lean_inc(v_head_1029_);
v___x_1036_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_head_1029_);
if (lean_obj_tag(v___x_1036_) == 1)
{
lean_object* v_val_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
lean_dec(v_fst_1031_);
v_val_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_val_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1038_ = l_String_Slice_toString(v_val_1037_);
lean_dec(v_val_1037_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1038_);
v___x_1040_ = v___x_1034_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_snd_1032_);
v___x_1040_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
v_as_x27_1025_ = v_tail_1030_;
v_b_1026_ = v___x_1040_;
goto _start;
}
}
else
{
lean_object* v___x_1043_; 
lean_dec(v___x_1036_);
lean_inc(v_head_1029_);
v___x_1043_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_head_1029_);
if (lean_obj_tag(v___x_1043_) == 1)
{
lean_object* v_val_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
lean_dec(v_snd_1032_);
v_val_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_val_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = l_String_Slice_toString(v_val_1044_);
lean_dec(v_val_1044_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v___x_1045_);
v___x_1047_ = v___x_1034_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_fst_1031_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
v_as_x27_1025_ = v_tail_1030_;
v_b_1026_ = v___x_1047_;
goto _start;
}
}
else
{
lean_object* v___x_1051_; 
lean_dec(v___x_1043_);
if (v_isShared_1035_ == 0)
{
v___x_1051_ = v___x_1034_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_fst_1031_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_snd_1032_);
v___x_1051_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
v_as_x27_1025_ = v_tail_1030_;
v_b_1026_ = v___x_1051_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg___boxed(lean_object* v_as_x27_1055_, lean_object* v_b_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_1055_, v_b_1056_);
lean_dec(v_as_x27_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(lean_object* v_s_1059_){
_start:
{
lean_object* v___x_1061_; lean_object* v_putStr_1062_; lean_object* v___x_1063_; 
v___x_1061_ = lean_get_stdout();
v_putStr_1062_ = lean_ctor_get(v___x_1061_, 4);
lean_inc_ref(v_putStr_1062_);
lean_dec_ref(v___x_1061_);
v___x_1063_ = lean_apply_2(v_putStr_1062_, v_s_1059_, lean_box(0));
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2___boxed(lean_object* v_s_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v_s_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(lean_object* v_s_1067_){
_start:
{
uint32_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = 10;
v___x_1070_ = lean_string_push(v_s_1067_, v___x_1069_);
v___x_1071_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2___boxed(lean_object* v_s_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v_s_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_1114_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1113_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_projectDir_1115_; lean_object* v_leanPrefix_1116_; lean_object* v_whichLake_1117_; lean_object* v_lakeHome_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___y_1122_; lean_object* v_leanPrefix_1123_; lean_object* v_whichLake_1124_; lean_object* v_lakeHome_1125_; uint8_t v___x_1180_; 
lean_dec_ref_known(v___x_1114_, 1);
v_projectDir_1115_ = lean_ctor_get(v_a_1108_, 0);
v_leanPrefix_1116_ = lean_ctor_get(v_a_1108_, 6);
v_whichLake_1117_ = lean_ctor_get(v_a_1108_, 10);
v_lakeHome_1118_ = lean_ctor_get(v_a_1108_, 11);
v___x_1119_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1115_);
v___x_1120_ = l_System_FilePath_join(v_projectDir_1115_, v___x_1119_);
v___x_1180_ = l_System_FilePath_pathExists(v___x_1120_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_io_create_dir(v___x_1120_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_dec_ref_known(v___x_1181_, 1);
v___y_1122_ = v_a_1108_;
v_leanPrefix_1123_ = v_leanPrefix_1116_;
v_whichLake_1124_ = v_whichLake_1117_;
v_lakeHome_1125_ = v_lakeHome_1118_;
goto v___jp_1121_;
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec_ref(v___x_1120_);
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
v___y_1122_ = v_a_1108_;
v_leanPrefix_1123_ = v_leanPrefix_1116_;
v_whichLake_1124_ = v_whichLake_1117_;
v_lakeHome_1125_ = v_lakeHome_1118_;
goto v___jp_1121_;
}
v___jp_1121_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_mk_empty_array_with_capacity(v___x_1126_);
v___x_1128_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__5));
v___x_1129_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8));
v___x_1130_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1131_ = lean_unsigned_to_nat(3u);
v___x_1132_ = lean_mk_empty_array_with_capacity(v___x_1131_);
lean_inc_ref(v_projectDir_1115_);
v___x_1133_ = lean_array_push(v___x_1132_, v_projectDir_1115_);
lean_inc_ref(v_leanPrefix_1123_);
v___x_1134_ = lean_array_push(v___x_1133_, v_leanPrefix_1123_);
lean_inc_ref(v_lakeHome_1125_);
v___x_1135_ = lean_array_push(v___x_1134_, v_lakeHome_1125_);
v___x_1136_ = lean_array_push(v___x_1127_, v___x_1120_);
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1139_ = 1;
v___x_1140_ = lean_box(0);
lean_inc_ref(v_whichLake_1124_);
v___x_1141_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1141_, 0, v_whichLake_1124_);
lean_ctor_set(v___x_1141_, 1, v___x_1128_);
lean_ctor_set(v___x_1141_, 2, v___x_1129_);
lean_ctor_set(v___x_1141_, 3, v___x_1130_);
lean_ctor_set(v___x_1141_, 4, v___x_1135_);
lean_ctor_set(v___x_1141_, 5, v___x_1136_);
lean_ctor_set(v___x_1141_, 6, v___x_1138_);
lean_ctor_set(v___x_1141_, 7, v___x_1140_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*8, v___x_1139_);
v___x_1142_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v___x_1141_, v___y_1122_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1171_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc_n(v_a_1143_, 2);
lean_dec_ref_known(v___x_1142_, 1);
v___x_1144_ = lean_string_utf8_byte_size(v_a_1143_);
v___x_1145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1145_, 0, v_a_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1137_);
lean_ctor_set(v___x_1145_, 2, v___x_1144_);
v___x_1146_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0);
v___x_1147_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1143_, v___x_1145_, v___x_1144_, v___x_1146_, v___x_1138_);
lean_dec_ref_known(v___x_1145_, 3);
v___x_1148_ = lean_array_to_list(v___x_1147_);
v___x_1149_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__15));
v___x_1150_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v___x_1148_, v___x_1149_);
lean_dec(v___x_1148_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1171_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1171_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_fst_1155_; lean_object* v_snd_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1170_; 
v_fst_1155_ = lean_ctor_get(v_a_1151_, 0);
v_snd_1156_ = lean_ctor_get(v_a_1151_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_a_1151_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1158_ = v_a_1151_;
v_isShared_1159_ = v_isSharedCheck_1170_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_snd_1156_);
lean_inc(v_fst_1155_);
lean_dec(v_a_1151_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1170_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = lean_string_utf8_byte_size(v_fst_1155_);
v___x_1161_ = lean_nat_dec_eq(v___x_1160_, v___x_1137_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_string_utf8_byte_size(v_snd_1156_);
v___x_1163_ = lean_nat_dec_eq(v___x_1162_, v___x_1137_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1165_; 
if (v_isShared_1159_ == 0)
{
v___x_1165_ = v___x_1158_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_fst_1155_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_snd_1156_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1165_);
v___x_1167_ = v___x_1153_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
else
{
lean_del_object(v___x_1158_);
lean_dec(v_snd_1156_);
lean_dec(v_fst_1155_);
lean_del_object(v___x_1153_);
goto v___jp_1110_;
}
}
else
{
lean_del_object(v___x_1158_);
lean_dec(v_snd_1156_);
lean_dec(v_fst_1155_);
lean_del_object(v___x_1153_);
goto v___jp_1110_;
}
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
v_a_1172_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1142_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1142_);
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
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
v_a_1190_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1114_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1114_);
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
v___jp_1110_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__1));
v___x_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___boxed(lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v_a_1198_);
lean_dec_ref(v_a_1198_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(lean_object* v_a_1201_, lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v_inst_1204_, lean_object* v_R_1205_, lean_object* v_a_1206_, lean_object* v_b_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1201_, v___x_1202_, v___x_1203_, v_a_1206_, v_b_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___boxed(lean_object* v_a_1209_, lean_object* v___x_1210_, lean_object* v___x_1211_, lean_object* v_inst_1212_, lean_object* v_R_1213_, lean_object* v_a_1214_, lean_object* v_b_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(v_a_1209_, v___x_1210_, v___x_1211_, v_inst_1212_, v_R_1213_, v_a_1214_, v_b_1215_);
lean_dec_ref(v___x_1210_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(lean_object* v_as_1217_, lean_object* v_as_x27_1218_, lean_object* v_b_1219_, lean_object* v_a_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_1218_, v_b_1219_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___boxed(lean_object* v_as_1224_, lean_object* v_as_x27_1225_, lean_object* v_b_1226_, lean_object* v_a_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(v_as_1224_, v_as_x27_1225_, v_b_1226_, v_a_1227_, v___y_1228_);
lean_dec_ref(v___y_1228_);
lean_dec(v_as_x27_1225_);
lean_dec(v_as_1224_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(lean_object* v_a_1244_){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_1247_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1246_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_projectDir_1248_; lean_object* v_leanPrefix_1249_; lean_object* v_whichLake_1250_; lean_object* v_lakeHome_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___y_1255_; lean_object* v_leanPrefix_1256_; lean_object* v_whichLake_1257_; lean_object* v_lakeHome_1258_; uint8_t v___x_1275_; 
lean_dec_ref_known(v___x_1247_, 1);
v_projectDir_1248_ = lean_ctor_get(v_a_1244_, 0);
v_leanPrefix_1249_ = lean_ctor_get(v_a_1244_, 6);
v_whichLake_1250_ = lean_ctor_get(v_a_1244_, 10);
v_lakeHome_1251_ = lean_ctor_get(v_a_1244_, 11);
v___x_1252_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1248_);
v___x_1253_ = l_System_FilePath_join(v_projectDir_1248_, v___x_1252_);
v___x_1275_ = l_System_FilePath_pathExists(v___x_1253_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_io_create_dir(v___x_1253_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_dec_ref_known(v___x_1276_, 1);
v___y_1255_ = v_a_1244_;
v_leanPrefix_1256_ = v_leanPrefix_1249_;
v_whichLake_1257_ = v_whichLake_1250_;
v_lakeHome_1258_ = v_lakeHome_1251_;
goto v___jp_1254_;
}
else
{
lean_dec_ref(v___x_1253_);
return v___x_1276_;
}
}
else
{
v___y_1255_ = v_a_1244_;
v_leanPrefix_1256_ = v_leanPrefix_1249_;
v_whichLake_1257_ = v_whichLake_1250_;
v_lakeHome_1258_ = v_lakeHome_1251_;
goto v___jp_1254_;
}
v___jp_1254_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_mk_empty_array_with_capacity(v___x_1259_);
v___x_1261_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__1));
v___x_1262_ = lean_unsigned_to_nat(3u);
v___x_1263_ = lean_mk_empty_array_with_capacity(v___x_1262_);
v___x_1264_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2));
v___x_1265_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
lean_inc_ref(v_projectDir_1248_);
v___x_1266_ = lean_array_push(v___x_1263_, v_projectDir_1248_);
lean_inc_ref(v_leanPrefix_1256_);
v___x_1267_ = lean_array_push(v___x_1266_, v_leanPrefix_1256_);
lean_inc_ref(v_lakeHome_1258_);
v___x_1268_ = lean_array_push(v___x_1267_, v_lakeHome_1258_);
v___x_1269_ = lean_array_push(v___x_1260_, v___x_1253_);
v___x_1270_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1271_ = 1;
v___x_1272_ = lean_box(0);
lean_inc_ref(v_whichLake_1257_);
v___x_1273_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1273_, 0, v_whichLake_1257_);
lean_ctor_set(v___x_1273_, 1, v___x_1261_);
lean_ctor_set(v___x_1273_, 2, v___x_1264_);
lean_ctor_set(v___x_1273_, 3, v___x_1265_);
lean_ctor_set(v___x_1273_, 4, v___x_1268_);
lean_ctor_set(v___x_1273_, 5, v___x_1269_);
lean_ctor_set(v___x_1273_, 6, v___x_1270_);
lean_ctor_set(v___x_1273_, 7, v___x_1272_);
lean_ctor_set_uint8(v___x_1273_, sizeof(void*)*8, v___x_1271_);
v___x_1274_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_1273_, v___y_1255_);
return v___x_1274_;
}
}
else
{
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___boxed(lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_1277_);
lean_dec_ref(v_a_1277_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg(lean_object* v_f_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v_fst_1294_; lean_object* v_snd_1295_; lean_object* v_r_1296_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1292_, 1);
v_fst_1294_ = lean_ctor_get(v_a_1293_, 0);
lean_inc(v_fst_1294_);
v_snd_1295_ = lean_ctor_get(v_a_1293_, 1);
lean_inc_n(v_snd_1295_, 2);
lean_dec(v_a_1293_);
lean_inc_ref(v___y_1290_);
v_r_1296_ = lean_apply_4(v_f_1289_, v_fst_1294_, v_snd_1295_, v___y_1290_, lean_box(0));
if (lean_obj_tag(v_r_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1298_; 
v_a_1297_ = lean_ctor_get(v_r_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v_r_1296_, 1);
v___x_1298_ = lean_io_remove_file(v_snd_1295_);
lean_dec(v_snd_1295_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1305_ == 0)
{
lean_object* v_unused_1306_; 
v_unused_1306_ = lean_ctor_get(v___x_1298_, 0);
lean_dec(v_unused_1306_);
v___x_1300_ = v___x_1298_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_dec(v___x_1298_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v_a_1297_);
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1297_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v_a_1297_);
v_a_1307_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1298_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1298_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1316_; 
v_a_1315_ = lean_ctor_get(v_r_1296_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v_r_1296_, 1);
v___x_1316_ = lean_io_remove_file(v_snd_1295_);
lean_dec(v_snd_1295_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v___x_1316_, 0);
lean_dec(v_unused_1324_);
v___x_1318_ = v___x_1316_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_dec(v___x_1316_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set_tag(v___x_1318_, 1);
lean_ctor_set(v___x_1318_, 0, v_a_1315_);
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1315_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_a_1315_);
v_a_1325_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1316_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1316_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v_f_1289_);
v_a_1333_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1292_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1292_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg___boxed(lean_object* v_f_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg(v_f_1341_, v___y_1342_);
lean_dec_ref(v___y_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0(lean_object* v_00_u03b1_1345_, lean_object* v_f_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg(v_f_1346_, v___y_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___boxed(lean_object* v_00_u03b1_1350_, lean_object* v_f_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0(v_00_u03b1_1350_, v_f_1351_, v___y_1352_);
lean_dec_ref(v___y_1352_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0(lean_object* v_projectDir_1370_, lean_object* v_f_1371_, lean_object* v_handle_1372_, lean_object* v_path_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_leanPrefix_1376_; lean_object* v_whichLake_1377_; lean_object* v_lakeHome_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_leanPrefix_1376_ = lean_ctor_get(v___y_1374_, 6);
v_whichLake_1377_ = lean_ctor_get(v___y_1374_, 10);
v_lakeHome_1378_ = lean_ctor_get(v___y_1374_, 11);
v___x_1379_ = lean_unsigned_to_nat(1u);
v___x_1380_ = lean_mk_empty_array_with_capacity(v___x_1379_);
v___x_1381_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__1));
v___x_1382_ = lean_unsigned_to_nat(3u);
v___x_1383_ = lean_mk_empty_array_with_capacity(v___x_1382_);
v___x_1384_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2));
v___x_1385_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__4));
lean_inc_ref(v_projectDir_1370_);
v___x_1386_ = lean_array_push(v___x_1383_, v_projectDir_1370_);
lean_inc_ref(v_leanPrefix_1376_);
v___x_1387_ = lean_array_push(v___x_1386_, v_leanPrefix_1376_);
lean_inc_ref(v_lakeHome_1378_);
v___x_1388_ = lean_array_push(v___x_1387_, v_lakeHome_1378_);
v___x_1389_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
v___x_1390_ = l_System_FilePath_join(v_projectDir_1370_, v___x_1389_);
v___x_1391_ = lean_array_push(v___x_1380_, v___x_1390_);
v___x_1392_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1393_ = 0;
v___x_1394_ = lean_box(0);
lean_inc_ref(v_whichLake_1377_);
v___x_1395_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1395_, 0, v_whichLake_1377_);
lean_ctor_set(v___x_1395_, 1, v___x_1381_);
lean_ctor_set(v___x_1395_, 2, v___x_1384_);
lean_ctor_set(v___x_1395_, 3, v___x_1385_);
lean_ctor_set(v___x_1395_, 4, v___x_1388_);
lean_ctor_set(v___x_1395_, 5, v___x_1391_);
lean_ctor_set(v___x_1395_, 6, v___x_1392_);
lean_ctor_set(v___x_1395_, 7, v___x_1394_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*8, v___x_1393_);
v___x_1396_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_handle_1372_, v___x_1395_, v___y_1374_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v___x_1397_; 
lean_dec_ref_known(v___x_1396_, 1);
lean_inc_ref(v___y_1374_);
v___x_1397_ = lean_apply_3(v_f_1371_, v_path_1373_, v___y_1374_, lean_box(0));
return v___x_1397_;
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v_path_1373_);
lean_dec_ref(v_f_1371_);
v_a_1398_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1396_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1396_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___boxed(lean_object* v_projectDir_1406_, lean_object* v_f_1407_, lean_object* v_handle_1408_, lean_object* v_path_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0(v_projectDir_1406_, v_f_1407_, v_handle_1408_, v_path_1409_, v___y_1410_);
lean_dec_ref(v___y_1410_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(lean_object* v_f_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___closed__0));
v___x_1418_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1417_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_projectDir_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; 
lean_dec_ref_known(v___x_1418_, 1);
v_projectDir_1419_ = lean_ctor_get(v_a_1415_, 0);
lean_inc_ref(v_projectDir_1419_);
v___f_1420_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_1420_, 0, v_projectDir_1419_);
lean_closure_set(v___f_1420_, 1, v_f_1414_);
v___x_1421_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg(v___f_1420_, v_a_1415_);
return v___x_1421_;
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec_ref(v_f_1414_);
v_a_1422_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1418_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1418_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___boxed(lean_object* v_f_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v_f_1430_, v_a_1431_);
lean_dec_ref(v_a_1431_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(lean_object* v_00_u03b1_1434_, lean_object* v_f_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v_f_1435_, v_a_1436_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___boxed(lean_object* v_00_u03b1_1439_, lean_object* v_f_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(v_00_u03b1_1439_, v_f_1440_, v_a_1441_);
lean_dec_ref(v_a_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(size_t v_sz_1444_, size_t v_i_1445_, lean_object* v_bs_1446_){
_start:
{
uint8_t v___x_1447_; 
v___x_1447_ = lean_usize_dec_lt(v_i_1445_, v_sz_1444_);
if (v___x_1447_ == 0)
{
return v_bs_1446_;
}
else
{
lean_object* v_v_1448_; lean_object* v___x_1449_; lean_object* v_bs_x27_1450_; lean_object* v___x_1451_; size_t v___x_1452_; size_t v___x_1453_; lean_object* v___x_1454_; 
v_v_1448_ = lean_array_uget(v_bs_1446_, v_i_1445_);
v___x_1449_ = lean_unsigned_to_nat(0u);
v_bs_x27_1450_ = lean_array_uset(v_bs_1446_, v_i_1445_, v___x_1449_);
v___x_1451_ = l_Lean_Name_toString(v_v_1448_, v___x_1447_);
v___x_1452_ = ((size_t)1ULL);
v___x_1453_ = lean_usize_add(v_i_1445_, v___x_1452_);
v___x_1454_ = lean_array_uset(v_bs_x27_1450_, v_i_1445_, v___x_1451_);
v_i_1445_ = v___x_1453_;
v_bs_1446_ = v___x_1454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0___boxed(lean_object* v_sz_1456_, lean_object* v_i_1457_, lean_object* v_bs_1458_){
_start:
{
size_t v_sz_boxed_1459_; size_t v_i_boxed_1460_; lean_object* v_res_1461_; 
v_sz_boxed_1459_ = lean_unbox_usize(v_sz_1456_);
lean_dec(v_sz_1456_);
v_i_boxed_1460_ = lean_unbox_usize(v_i_1457_);
lean_dec(v_i_1457_);
v_res_1461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_boxed_1459_, v_i_boxed_1460_, v_bs_1458_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(lean_object* v_targets_1469_, lean_object* v_a_1470_){
_start:
{
size_t v_sz_1472_; size_t v___x_1473_; lean_object* v_targetArgs_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v_targetList_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_sz_1472_ = lean_array_size(v_targets_1469_);
v___x_1473_ = ((size_t)0ULL);
v_targetArgs_1474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_1472_, v___x_1473_, v_targets_1469_);
v___x_1475_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
lean_inc_ref(v_targetArgs_1474_);
v___x_1476_ = lean_array_to_list(v_targetArgs_1474_);
v_targetList_1477_ = l_String_intercalate(v___x_1475_, v___x_1476_);
v___x_1478_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1));
v___x_1479_ = lean_string_append(v___x_1478_, v_targetList_1477_);
lean_dec_ref(v_targetList_1477_);
v___x_1480_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1479_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_projectDir_1481_; lean_object* v_leanPrefix_1482_; lean_object* v_whichLake_1483_; lean_object* v_lakeHome_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___y_1488_; lean_object* v_leanPrefix_1489_; lean_object* v_whichLake_1490_; lean_object* v_lakeHome_1491_; uint8_t v___x_1509_; 
lean_dec_ref_known(v___x_1480_, 1);
v_projectDir_1481_ = lean_ctor_get(v_a_1470_, 0);
v_leanPrefix_1482_ = lean_ctor_get(v_a_1470_, 6);
v_whichLake_1483_ = lean_ctor_get(v_a_1470_, 10);
v_lakeHome_1484_ = lean_ctor_get(v_a_1470_, 11);
v___x_1485_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1481_);
v___x_1486_ = l_System_FilePath_join(v_projectDir_1481_, v___x_1485_);
v___x_1509_ = l_System_FilePath_pathExists(v___x_1486_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_io_create_dir(v___x_1486_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_dec_ref_known(v___x_1510_, 1);
v___y_1488_ = v_a_1470_;
v_leanPrefix_1489_ = v_leanPrefix_1482_;
v_whichLake_1490_ = v_whichLake_1483_;
v_lakeHome_1491_ = v_lakeHome_1484_;
goto v___jp_1487_;
}
else
{
lean_dec_ref(v___x_1486_);
lean_dec_ref(v_targetArgs_1474_);
return v___x_1510_;
}
}
else
{
v___y_1488_ = v_a_1470_;
v_leanPrefix_1489_ = v_leanPrefix_1482_;
v_whichLake_1490_ = v_whichLake_1483_;
v_lakeHome_1491_ = v_lakeHome_1484_;
goto v___jp_1487_;
}
v___jp_1487_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1492_ = lean_unsigned_to_nat(1u);
v___x_1493_ = lean_mk_empty_array_with_capacity(v___x_1492_);
v___x_1494_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3));
v___x_1495_ = l_Array_append___redArg(v___x_1494_, v_targetArgs_1474_);
lean_dec_ref(v_targetArgs_1474_);
v___x_1496_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8));
v___x_1497_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1498_ = lean_unsigned_to_nat(3u);
v___x_1499_ = lean_mk_empty_array_with_capacity(v___x_1498_);
lean_inc_ref(v_projectDir_1481_);
v___x_1500_ = lean_array_push(v___x_1499_, v_projectDir_1481_);
lean_inc_ref(v_leanPrefix_1489_);
v___x_1501_ = lean_array_push(v___x_1500_, v_leanPrefix_1489_);
lean_inc_ref(v_lakeHome_1491_);
v___x_1502_ = lean_array_push(v___x_1501_, v_lakeHome_1491_);
v___x_1503_ = lean_array_push(v___x_1493_, v___x_1486_);
v___x_1504_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1505_ = 0;
v___x_1506_ = lean_box(0);
lean_inc_ref(v_whichLake_1490_);
v___x_1507_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1507_, 0, v_whichLake_1490_);
lean_ctor_set(v___x_1507_, 1, v___x_1495_);
lean_ctor_set(v___x_1507_, 2, v___x_1496_);
lean_ctor_set(v___x_1507_, 3, v___x_1497_);
lean_ctor_set(v___x_1507_, 4, v___x_1502_);
lean_ctor_set(v___x_1507_, 5, v___x_1503_);
lean_ctor_set(v___x_1507_, 6, v___x_1504_);
lean_ctor_set(v___x_1507_, 7, v___x_1506_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*8, v___x_1505_);
v___x_1508_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_1507_, v___y_1488_);
return v___x_1508_;
}
}
else
{
lean_dec_ref(v_targetArgs_1474_);
return v___x_1480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___boxed(lean_object* v_targets_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v_targets_1511_, v_a_1512_);
lean_dec_ref(v_a_1512_);
return v_res_1514_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1524_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11));
v___x_1525_ = lean_unsigned_to_nat(3u);
v___x_1526_ = lean_mk_empty_array_with_capacity(v___x_1525_);
v___x_1527_ = lean_array_push(v___x_1526_, v___x_1524_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(lean_object* v_projectDir_1528_, lean_object* v_whichLean4Export_1529_, lean_object* v_args_1530_, lean_object* v_f_1531_, lean_object* v_exportHandle_1532_, lean_object* v_exportPath_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_leanPrefix_1536_; lean_object* v_leanPath_1537_; lean_object* v_binPath_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_leanPrefix_1536_ = lean_ctor_get(v___y_1534_, 6);
v_leanPath_1537_ = lean_ctor_get(v___y_1534_, 7);
v_binPath_1538_ = lean_ctor_get(v___y_1534_, 8);
v___x_1539_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6));
v___x_1540_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__0));
v___x_1541_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__1));
lean_inc_ref(v_leanPath_1537_);
v___x_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1542_, 0, v_leanPath_1537_);
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1540_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
lean_inc_ref(v_binPath_1538_);
v___x_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_binPath_1538_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1539_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2);
v___x_1547_ = lean_array_push(v___x_1546_, v___x_1543_);
v___x_1548_ = lean_array_push(v___x_1547_, v___x_1545_);
v___x_1549_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1528_);
v___x_1550_ = l_System_FilePath_join(v_projectDir_1528_, v___x_1549_);
v___x_1551_ = lean_unsigned_to_nat(4u);
v___x_1552_ = lean_mk_empty_array_with_capacity(v___x_1551_);
v___x_1553_ = lean_array_push(v___x_1552_, v_projectDir_1528_);
v___x_1554_ = lean_array_push(v___x_1553_, v___x_1550_);
lean_inc_ref(v_leanPrefix_1536_);
v___x_1555_ = lean_array_push(v___x_1554_, v_leanPrefix_1536_);
lean_inc_ref(v_whichLean4Export_1529_);
v___x_1556_ = lean_array_push(v___x_1555_, v_whichLean4Export_1529_);
v___x_1557_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1558_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1559_ = 0;
v___x_1560_ = lean_box(0);
v___x_1561_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1561_, 0, v_whichLean4Export_1529_);
lean_ctor_set(v___x_1561_, 1, v_args_1530_);
lean_ctor_set(v___x_1561_, 2, v___x_1541_);
lean_ctor_set(v___x_1561_, 3, v___x_1548_);
lean_ctor_set(v___x_1561_, 4, v___x_1556_);
lean_ctor_set(v___x_1561_, 5, v___x_1557_);
lean_ctor_set(v___x_1561_, 6, v___x_1558_);
lean_ctor_set(v___x_1561_, 7, v___x_1560_);
lean_ctor_set_uint8(v___x_1561_, sizeof(void*)*8, v___x_1559_);
v___x_1562_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_exportHandle_1532_, v___x_1561_, v___y_1534_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1563_; 
lean_dec_ref_known(v___x_1562_, 1);
lean_inc_ref(v___y_1534_);
v___x_1563_ = lean_apply_3(v_f_1531_, v_exportPath_1533_, v___y_1534_, lean_box(0));
return v___x_1563_;
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v_exportPath_1533_);
lean_dec_ref(v_f_1531_);
v_a_1564_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1562_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1562_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___boxed(lean_object* v_projectDir_1572_, lean_object* v_whichLean4Export_1573_, lean_object* v_args_1574_, lean_object* v_f_1575_, lean_object* v_exportHandle_1576_, lean_object* v_exportPath_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(v_projectDir_1572_, v_whichLean4Export_1573_, v_args_1574_, v_f_1575_, v_exportHandle_1576_, v_exportPath_1577_, v___y_1578_);
lean_dec_ref(v___y_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(lean_object* v_args_1581_, lean_object* v_f_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v_projectDir_1585_; lean_object* v_whichLean4Export_1586_; lean_object* v___f_1587_; lean_object* v___x_1588_; 
v_projectDir_1585_ = lean_ctor_get(v_a_1583_, 0);
v_whichLean4Export_1586_ = lean_ctor_get(v_a_1583_, 12);
lean_inc_ref(v_whichLean4Export_1586_);
lean_inc_ref(v_projectDir_1585_);
v___f_1587_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_1587_, 0, v_projectDir_1585_);
lean_closure_set(v___f_1587_, 1, v_whichLean4Export_1586_);
lean_closure_set(v___f_1587_, 2, v_args_1581_);
lean_closure_set(v___f_1587_, 3, v_f_1582_);
v___x_1588_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg(v___f_1587_, v_a_1583_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___boxed(lean_object* v_args_1589_, lean_object* v_f_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v_args_1589_, v_f_1590_, v_a_1591_);
lean_dec_ref(v_a_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(lean_object* v_00_u03b1_1594_, lean_object* v_args_1595_, lean_object* v_f_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v_args_1595_, v_f_1596_, v_a_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___boxed(lean_object* v_00_u03b1_1600_, lean_object* v_args_1601_, lean_object* v_f_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(v_00_u03b1_1600_, v_args_1601_, v_f_1602_, v_a_1603_);
lean_dec_ref(v_a_1603_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0(lean_object* v_x_1607_, lean_object* v_x_1608_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 0)
{
return v_x_1607_;
}
else
{
lean_object* v_head_1609_; lean_object* v_tail_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v_head_1609_ = lean_ctor_get(v_x_1608_, 0);
lean_inc(v_head_1609_);
v_tail_1610_ = lean_ctor_get(v_x_1608_, 1);
lean_inc(v_tail_1610_);
lean_dec_ref_known(v_x_1608_, 2);
v___x_1611_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0));
v___x_1612_ = lean_string_append(v_x_1607_, v___x_1611_);
v___x_1613_ = 1;
v___x_1614_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1609_, v___x_1613_);
v___x_1615_ = lean_string_append(v___x_1612_, v___x_1614_);
lean_dec_ref(v___x_1614_);
v_x_1607_ = v___x_1615_;
v_x_1608_ = v_tail_1610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0(lean_object* v_x_1620_){
_start:
{
if (lean_obj_tag(v_x_1620_) == 0)
{
lean_object* v___x_1621_; 
v___x_1621_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__0));
return v___x_1621_;
}
else
{
lean_object* v_tail_1622_; 
v_tail_1622_ = lean_ctor_get(v_x_1620_, 1);
if (lean_obj_tag(v_tail_1622_) == 0)
{
lean_object* v_head_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_head_1623_ = lean_ctor_get(v_x_1620_, 0);
lean_inc(v_head_1623_);
lean_dec_ref_known(v_x_1620_, 2);
v___x_1624_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_1625_ = 1;
v___x_1626_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1623_, v___x_1625_);
v___x_1627_ = lean_string_append(v___x_1624_, v___x_1626_);
lean_dec_ref(v___x_1626_);
v___x_1628_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__2));
v___x_1629_ = lean_string_append(v___x_1627_, v___x_1628_);
return v___x_1629_;
}
else
{
lean_object* v_head_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint32_t v___x_1636_; lean_object* v___x_1637_; 
lean_inc(v_tail_1622_);
v_head_1630_ = lean_ctor_get(v_x_1620_, 0);
lean_inc(v_head_1630_);
lean_dec_ref_known(v_x_1620_, 2);
v___x_1631_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_1632_ = 1;
v___x_1633_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1630_, v___x_1632_);
v___x_1634_ = lean_string_append(v___x_1631_, v___x_1633_);
lean_dec_ref(v___x_1633_);
v___x_1635_ = l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0(v___x_1634_, v_tail_1622_);
v___x_1636_ = 93;
v___x_1637_ = lean_string_push(v___x_1635_, v___x_1636_);
return v___x_1637_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(size_t v_sz_1638_, size_t v_i_1639_, lean_object* v_bs_1640_){
_start:
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_usize_dec_lt(v_i_1639_, v_sz_1638_);
if (v___x_1641_ == 0)
{
return v_bs_1640_;
}
else
{
lean_object* v_v_1642_; lean_object* v___x_1643_; lean_object* v_bs_x27_1644_; lean_object* v___x_1645_; size_t v___x_1646_; size_t v___x_1647_; lean_object* v___x_1648_; 
v_v_1642_ = lean_array_uget(v_bs_1640_, v_i_1639_);
v___x_1643_ = lean_unsigned_to_nat(0u);
v_bs_x27_1644_ = lean_array_uset(v_bs_1640_, v_i_1639_, v___x_1643_);
v___x_1645_ = l_Lean_Name_toString(v_v_1642_, v___x_1641_);
v___x_1646_ = ((size_t)1ULL);
v___x_1647_ = lean_usize_add(v_i_1639_, v___x_1646_);
v___x_1648_ = lean_array_uset(v_bs_x27_1644_, v_i_1639_, v___x_1645_);
v_i_1639_ = v___x_1647_;
v_bs_1640_ = v___x_1648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1___boxed(lean_object* v_sz_1650_, lean_object* v_i_1651_, lean_object* v_bs_1652_){
_start:
{
size_t v_sz_boxed_1653_; size_t v_i_boxed_1654_; lean_object* v_res_1655_; 
v_sz_boxed_1653_ = lean_unbox_usize(v_sz_1650_);
lean_dec(v_sz_1650_);
v_i_boxed_1654_ = lean_unbox_usize(v_i_1651_);
lean_dec(v_i_1651_);
v_res_1655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(v_sz_boxed_1653_, v_i_boxed_1654_, v_bs_1652_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(lean_object* v_module_1659_, lean_object* v_decls_1660_, lean_object* v_f_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1664_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__0));
v___x_1665_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__1));
lean_inc_ref(v_decls_1660_);
v___x_1666_ = lean_array_to_list(v_decls_1660_);
v___x_1667_ = l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0(v___x_1666_);
v___x_1668_ = lean_string_append(v___x_1665_, v___x_1667_);
lean_dec_ref(v___x_1667_);
v___x_1669_ = lean_string_append(v___x_1664_, v___x_1668_);
lean_dec_ref(v___x_1668_);
v___x_1670_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__2));
v___x_1671_ = lean_string_append(v___x_1669_, v___x_1670_);
v___x_1672_ = 1;
lean_inc(v_module_1659_);
v___x_1673_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_1659_, v___x_1672_);
v___x_1674_ = lean_string_append(v___x_1671_, v___x_1673_);
lean_dec_ref(v___x_1673_);
v___x_1675_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1674_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; size_t v_sz_1682_; size_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_dec_ref_known(v___x_1675_, 1);
v___x_1676_ = l_Lean_Name_toString(v_module_1659_, v___x_1672_);
v___x_1677_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__8));
v___x_1678_ = lean_unsigned_to_nat(2u);
v___x_1679_ = lean_mk_empty_array_with_capacity(v___x_1678_);
v___x_1680_ = lean_array_push(v___x_1679_, v___x_1676_);
v___x_1681_ = lean_array_push(v___x_1680_, v___x_1677_);
v_sz_1682_ = lean_array_size(v_decls_1660_);
v___x_1683_ = ((size_t)0ULL);
v___x_1684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(v_sz_1682_, v___x_1683_, v_decls_1660_);
v___x_1685_ = l_Array_append___redArg(v___x_1681_, v___x_1684_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v___x_1685_, v_f_1661_, v_a_1662_);
return v___x_1686_;
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec_ref(v_f_1661_);
lean_dec_ref(v_decls_1660_);
lean_dec(v_module_1659_);
v_a_1687_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1675_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1675_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___boxed(lean_object* v_module_1695_, lean_object* v_decls_1696_, lean_object* v_f_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1695_, v_decls_1696_, v_f_1697_, v_a_1698_);
lean_dec_ref(v_a_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(lean_object* v_00_u03b1_1701_, lean_object* v_module_1702_, lean_object* v_decls_1703_, lean_object* v_f_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1702_, v_decls_1703_, v_f_1704_, v_a_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___boxed(lean_object* v_00_u03b1_1708_, lean_object* v_module_1709_, lean_object* v_decls_1710_, lean_object* v_f_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(v_00_u03b1_1708_, v_module_1709_, v_decls_1710_, v_f_1711_, v_a_1712_);
lean_dec_ref(v_a_1712_);
return v_res_1714_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(lean_object* v_s_1715_, lean_object* v_a_1716_, uint8_t v_b_1717_){
_start:
{
uint8_t v___x_1718_; 
v___x_1718_ = 0;
switch(lean_obj_tag(v_a_1716_))
{
case 0:
{
lean_object* v_pos_1719_; lean_object* v_startInclusive_1720_; lean_object* v_endExclusive_1721_; lean_object* v___x_1722_; uint8_t v_decide_1723_; 
v_pos_1719_ = lean_ctor_get(v_a_1716_, 0);
lean_inc(v_pos_1719_);
lean_dec_ref_known(v_a_1716_, 1);
v_startInclusive_1720_ = lean_ctor_get(v_s_1715_, 1);
v_endExclusive_1721_ = lean_ctor_get(v_s_1715_, 2);
v___x_1722_ = lean_nat_sub(v_endExclusive_1721_, v_startInclusive_1720_);
v_decide_1723_ = lean_nat_dec_eq(v_pos_1719_, v___x_1722_);
lean_dec(v___x_1722_);
lean_dec(v_pos_1719_);
if (v_decide_1723_ == 0)
{
uint8_t v___x_1724_; 
v___x_1724_ = 1;
return v___x_1724_;
}
else
{
return v_decide_1723_;
}
}
case 1:
{
lean_object* v_pos_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1738_; 
v_pos_1725_ = lean_ctor_get(v_a_1716_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_a_1716_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1727_ = v_a_1716_;
v_isShared_1728_ = v_isSharedCheck_1738_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_pos_1725_);
lean_dec(v_a_1716_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1738_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_str_1729_; lean_object* v_startInclusive_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
v_str_1729_ = lean_ctor_get(v_s_1715_, 0);
v_startInclusive_1730_ = lean_ctor_get(v_s_1715_, 1);
v___x_1731_ = lean_nat_add(v_startInclusive_1730_, v_pos_1725_);
lean_dec(v_pos_1725_);
v___x_1732_ = lean_string_utf8_next_fast(v_str_1729_, v___x_1731_);
lean_dec(v___x_1731_);
v___x_1733_ = lean_nat_sub(v___x_1732_, v_startInclusive_1730_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1733_);
v___x_1735_ = v___x_1727_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
v_a_1716_ = v___x_1735_;
v_b_1717_ = v___x_1718_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1739_; lean_object* v_table_1740_; lean_object* v_stackPos_1741_; lean_object* v_needlePos_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1797_; 
v_needle_1739_ = lean_ctor_get(v_a_1716_, 0);
v_table_1740_ = lean_ctor_get(v_a_1716_, 1);
v_stackPos_1741_ = lean_ctor_get(v_a_1716_, 2);
v_needlePos_1742_ = lean_ctor_get(v_a_1716_, 3);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_a_1716_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1744_ = v_a_1716_;
v_isShared_1745_ = v_isSharedCheck_1797_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_needlePos_1742_);
lean_inc(v_stackPos_1741_);
lean_inc(v_table_1740_);
lean_inc(v_needle_1739_);
lean_dec(v_a_1716_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1797_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v_str_1746_; lean_object* v_startInclusive_1747_; lean_object* v_endExclusive_1748_; lean_object* v_str_1749_; lean_object* v_startInclusive_1750_; lean_object* v_endExclusive_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v_str_1746_ = lean_ctor_get(v_needle_1739_, 0);
v_startInclusive_1747_ = lean_ctor_get(v_needle_1739_, 1);
v_endExclusive_1748_ = lean_ctor_get(v_needle_1739_, 2);
v_str_1749_ = lean_ctor_get(v_s_1715_, 0);
v_startInclusive_1750_ = lean_ctor_get(v_s_1715_, 1);
v_endExclusive_1751_ = lean_ctor_get(v_s_1715_, 2);
v___x_1752_ = lean_nat_sub(v_stackPos_1741_, v_needlePos_1742_);
v___x_1753_ = lean_nat_sub(v_endExclusive_1748_, v_startInclusive_1747_);
v___x_1754_ = lean_nat_add(v___x_1752_, v___x_1753_);
v___x_1755_ = lean_nat_sub(v_endExclusive_1751_, v_startInclusive_1750_);
v___x_1756_ = lean_nat_dec_le(v___x_1754_, v___x_1755_);
lean_dec(v___x_1754_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
lean_dec(v___x_1753_);
lean_del_object(v___x_1744_);
lean_dec(v_needlePos_1742_);
lean_dec(v_stackPos_1741_);
lean_dec_ref(v_table_1740_);
lean_dec_ref(v_needle_1739_);
v___x_1757_ = lean_unsigned_to_nat(1u);
v___x_1758_ = lean_nat_add(v___x_1752_, v___x_1757_);
lean_dec(v___x_1752_);
v___x_1759_ = lean_nat_dec_le(v___x_1758_, v___x_1755_);
lean_dec(v___x_1755_);
lean_dec(v___x_1758_);
if (v___x_1759_ == 0)
{
return v_b_1717_;
}
else
{
lean_object* v___x_1760_; 
v___x_1760_ = lean_box(3);
v_a_1716_ = v___x_1760_;
v_b_1717_ = v___x_1718_;
goto _start;
}
}
else
{
lean_object* v___x_1762_; uint8_t v_stackByte_1763_; lean_object* v___x_1764_; uint8_t v_patByte_1765_; uint8_t v___x_1766_; 
lean_dec(v___x_1755_);
lean_dec(v___x_1752_);
v___x_1762_ = lean_nat_add(v_startInclusive_1750_, v_stackPos_1741_);
v_stackByte_1763_ = lean_string_get_byte_fast(v_str_1749_, v___x_1762_);
v___x_1764_ = lean_nat_add(v_startInclusive_1747_, v_needlePos_1742_);
v_patByte_1765_ = lean_string_get_byte_fast(v_str_1746_, v___x_1764_);
v___x_1766_ = lean_uint8_dec_eq(v_stackByte_1763_, v_patByte_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; uint8_t v_decide_1768_; 
lean_dec(v___x_1753_);
v___x_1767_ = lean_unsigned_to_nat(0u);
v_decide_1768_ = lean_nat_dec_eq(v_needlePos_1742_, v___x_1767_);
if (v_decide_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v_newNeedlePos_1771_; uint8_t v___x_1772_; 
v___x_1769_ = lean_unsigned_to_nat(1u);
v___x_1770_ = lean_nat_sub(v_needlePos_1742_, v___x_1769_);
lean_dec(v_needlePos_1742_);
v_newNeedlePos_1771_ = lean_array_fget_borrowed(v_table_1740_, v___x_1770_);
lean_dec(v___x_1770_);
v___x_1772_ = lean_nat_dec_eq(v_newNeedlePos_1771_, v___x_1767_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1774_; 
lean_inc(v_newNeedlePos_1771_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 3, v_newNeedlePos_1771_);
v___x_1774_ = v___x_1744_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_needle_1739_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_table_1740_);
lean_ctor_set(v_reuseFailAlloc_1776_, 2, v_stackPos_1741_);
lean_ctor_set(v_reuseFailAlloc_1776_, 3, v_newNeedlePos_1771_);
v___x_1774_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
v_a_1716_ = v___x_1774_;
v_b_1717_ = v___x_1718_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1777_; lean_object* v___x_1779_; 
v_nextStackPos_1777_ = l_String_Slice_posGE___redArg(v_s_1715_, v_stackPos_1741_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 3, v___x_1767_);
lean_ctor_set(v___x_1744_, 2, v_nextStackPos_1777_);
v___x_1779_ = v___x_1744_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_needle_1739_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_table_1740_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v_nextStackPos_1777_);
lean_ctor_set(v_reuseFailAlloc_1781_, 3, v___x_1767_);
v___x_1779_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
v_a_1716_ = v___x_1779_;
v_b_1717_ = v___x_1718_;
goto _start;
}
}
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v_nextStackPos_1784_; lean_object* v___x_1786_; 
lean_dec(v_needlePos_1742_);
v___x_1782_ = lean_unsigned_to_nat(1u);
v___x_1783_ = lean_nat_add(v_stackPos_1741_, v___x_1782_);
lean_dec(v_stackPos_1741_);
v_nextStackPos_1784_ = l_String_Slice_posGE___redArg(v_s_1715_, v___x_1783_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 3, v___x_1767_);
lean_ctor_set(v___x_1744_, 2, v_nextStackPos_1784_);
v___x_1786_ = v___x_1744_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_needle_1739_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_table_1740_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_nextStackPos_1784_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v___x_1767_);
v___x_1786_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
v_a_1716_ = v___x_1786_;
v_b_1717_ = v___x_1718_;
goto _start;
}
}
}
else
{
lean_object* v___x_1789_; lean_object* v_nextNeedlePos_1790_; uint8_t v_decide_1791_; 
v___x_1789_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_1790_ = lean_nat_add(v_needlePos_1742_, v___x_1789_);
lean_dec(v_needlePos_1742_);
v_decide_1791_ = lean_nat_dec_eq(v_nextNeedlePos_1790_, v___x_1753_);
lean_dec(v___x_1753_);
if (v_decide_1791_ == 0)
{
lean_object* v_nextStackPos_1792_; lean_object* v___x_1794_; 
v_nextStackPos_1792_ = lean_nat_add(v_stackPos_1741_, v___x_1789_);
lean_dec(v_stackPos_1741_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 3, v_nextNeedlePos_1790_);
lean_ctor_set(v___x_1744_, 2, v_nextStackPos_1792_);
v___x_1794_ = v___x_1744_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_needle_1739_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_table_1740_);
lean_ctor_set(v_reuseFailAlloc_1796_, 2, v_nextStackPos_1792_);
lean_ctor_set(v_reuseFailAlloc_1796_, 3, v_nextNeedlePos_1790_);
v___x_1794_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
v_a_1716_ = v___x_1794_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_1790_);
lean_del_object(v___x_1744_);
lean_dec(v_stackPos_1741_);
lean_dec_ref(v_table_1740_);
lean_dec_ref(v_needle_1739_);
return v_decide_1791_;
}
}
}
}
}
default: 
{
return v_b_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg___boxed(lean_object* v_s_1798_, lean_object* v_a_1799_, lean_object* v_b_1800_){
_start:
{
uint8_t v_b_boxed_1801_; uint8_t v_res_1802_; lean_object* v_r_1803_; 
v_b_boxed_1801_ = lean_unbox(v_b_1800_);
v_res_1802_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_1798_, v_a_1799_, v_b_boxed_1801_);
lean_dec_ref(v_s_1798_);
v_r_1803_ = lean_box(v_res_1802_);
return v_r_1803_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0));
v___x_1806_ = lean_string_utf8_byte_size(v___x_1805_);
return v___x_1806_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1);
v___x_1809_ = lean_nat_dec_eq(v___x_1808_, v___x_1807_);
return v___x_1809_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1810_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1);
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0));
v___x_1813_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___x_1811_);
lean_ctor_set(v___x_1813_, 2, v___x_1810_);
return v___x_1813_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3);
v___x_1815_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1814_);
return v___x_1815_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4);
v___x_1818_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3);
v___x_1819_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v___x_1817_);
lean_ctor_set(v___x_1819_, 2, v___x_1816_);
lean_ctor_set(v___x_1819_, 3, v___x_1816_);
return v___x_1819_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(lean_object* v_s_1822_){
_start:
{
lean_object* v___y_1824_; uint8_t v___x_1827_; 
v___x_1827_ = lean_uint8_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5);
v___y_1824_ = v___x_1828_;
goto v___jp_1823_;
}
else
{
lean_object* v___x_1829_; 
v___x_1829_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__6));
v___y_1824_ = v___x_1829_;
goto v___jp_1823_;
}
v___jp_1823_:
{
uint8_t v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = 0;
lean_inc(v___y_1824_);
v___x_1826_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_1822_, v___y_1824_, v___x_1825_);
return v___x_1826_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___boxed(lean_object* v_s_1830_){
_start:
{
uint8_t v_res_1831_; lean_object* v_r_1832_; 
v_res_1831_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v_s_1830_);
lean_dec_ref(v_s_1830_);
v_r_1832_ = lean_box(v_res_1831_);
return v_r_1832_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(lean_object* v_kernelName_1833_){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1834_ = lean_unsigned_to_nat(0u);
v___x_1835_ = lean_string_utf8_byte_size(v_kernelName_1833_);
v___x_1836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1836_, 0, v_kernelName_1833_);
lean_ctor_set(v___x_1836_, 1, v___x_1834_);
lean_ctor_set(v___x_1836_, 2, v___x_1835_);
v___x_1837_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v___x_1836_);
lean_dec_ref_known(v___x_1836_, 3);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel___boxed(lean_object* v_kernelName_1838_){
_start:
{
uint8_t v_res_1839_; lean_object* v_r_1840_; 
v_res_1839_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_1838_);
v_r_1840_ = lean_box(v_res_1839_);
return v_r_1840_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(lean_object* v_s_1841_, lean_object* v_inst_1842_, lean_object* v_R_1843_, lean_object* v_a_1844_, uint8_t v_b_1845_, lean_object* v_c_1846_){
_start:
{
uint8_t v___x_1847_; 
v___x_1847_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_1841_, v_a_1844_, v_b_1845_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___boxed(lean_object* v_s_1848_, lean_object* v_inst_1849_, lean_object* v_R_1850_, lean_object* v_a_1851_, lean_object* v_b_1852_, lean_object* v_c_1853_){
_start:
{
uint8_t v_b_boxed_1854_; uint8_t v_res_1855_; lean_object* v_r_1856_; 
v_b_boxed_1854_ = lean_unbox(v_b_1852_);
v_res_1855_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(v_s_1848_, v_inst_1849_, v_R_1850_, v_a_1851_, v_b_boxed_1854_, v_c_1853_);
lean_dec_ref(v_s_1848_);
v_r_1856_ = lean_box(v_res_1855_);
return v_r_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(lean_object* v_a_1857_, lean_object* v_b_1858_){
_start:
{
lean_object* v_array_1859_; lean_object* v_start_1860_; lean_object* v_stop_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1874_; 
v_array_1859_ = lean_ctor_get(v_a_1857_, 0);
v_start_1860_ = lean_ctor_get(v_a_1857_, 1);
v_stop_1861_ = lean_ctor_get(v_a_1857_, 2);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_a_1857_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1863_ = v_a_1857_;
v_isShared_1864_ = v_isSharedCheck_1874_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_stop_1861_);
lean_inc(v_start_1860_);
lean_inc(v_array_1859_);
lean_dec(v_a_1857_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1874_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
uint8_t v___x_1865_; 
v___x_1865_ = lean_nat_dec_lt(v_start_1860_, v_stop_1861_);
if (v___x_1865_ == 0)
{
lean_del_object(v___x_1863_);
lean_dec(v_stop_1861_);
lean_dec(v_start_1860_);
lean_dec_ref(v_array_1859_);
return v_b_1858_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1866_ = lean_unsigned_to_nat(1u);
v___x_1867_ = lean_nat_add(v_start_1860_, v___x_1866_);
lean_inc_ref(v_array_1859_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 1, v___x_1867_);
v___x_1869_ = v___x_1863_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_array_1859_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1873_, 2, v_stop_1861_);
v___x_1869_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_array_fget(v_array_1859_, v_start_1860_);
lean_dec(v_start_1860_);
lean_dec_ref(v_array_1859_);
v___x_1871_ = lean_array_push(v_b_1858_, v___x_1870_);
v_a_1857_ = v___x_1869_;
v_b_1858_ = v___x_1871_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(size_t v_sz_1875_, size_t v_i_1876_, lean_object* v_bs_1877_){
_start:
{
uint8_t v___x_1878_; 
v___x_1878_ = lean_usize_dec_lt(v_i_1876_, v_sz_1875_);
if (v___x_1878_ == 0)
{
return v_bs_1877_;
}
else
{
lean_object* v_v_1879_; lean_object* v___x_1880_; lean_object* v_bs_x27_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; size_t v___x_1884_; size_t v___x_1885_; lean_object* v___x_1886_; 
v_v_1879_ = lean_array_uget(v_bs_1877_, v_i_1876_);
v___x_1880_ = lean_unsigned_to_nat(0u);
v_bs_x27_1881_ = lean_array_uset(v_bs_1877_, v_i_1876_, v___x_1880_);
v___x_1882_ = l_Lean_Name_toString(v_v_1879_, v___x_1878_);
v___x_1883_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
v___x_1884_ = ((size_t)1ULL);
v___x_1885_ = lean_usize_add(v_i_1876_, v___x_1884_);
v___x_1886_ = lean_array_uset(v_bs_x27_1881_, v_i_1876_, v___x_1883_);
v_i_1876_ = v___x_1885_;
v_bs_1877_ = v___x_1886_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0___boxed(lean_object* v_sz_1888_, lean_object* v_i_1889_, lean_object* v_bs_1890_){
_start:
{
size_t v_sz_boxed_1891_; size_t v_i_boxed_1892_; lean_object* v_res_1893_; 
v_sz_boxed_1891_ = lean_unbox_usize(v_sz_1888_);
lean_dec(v_sz_1888_);
v_i_boxed_1892_ = lean_unbox_usize(v_i_1889_);
lean_dec(v_i_1889_);
v_res_1893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_boxed_1891_, v_i_boxed_1892_, v_bs_1890_);
return v_res_1893_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = lean_unsigned_to_nat(4u);
v___x_1922_ = l_Lean_JsonNumber_fromNat(v___x_1921_);
return v___x_1922_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17);
v___x_1924_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
return v___x_1924_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18);
v___x_1926_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16));
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1925_);
return v___x_1927_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25));
v___x_1943_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19);
v___x_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v___x_1942_);
return v___x_1944_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__27(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26);
v___x_1946_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15));
v___x_1947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v___x_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(lean_object* v_kernelName_1948_, lean_object* v_solutionPath_1949_, lean_object* v___x_1950_, lean_object* v_kernelCommand_1951_, lean_object* v_configHandle_1952_, lean_object* v_configPath_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_a_1957_; lean_object* v_legalAxioms_1984_; uint8_t v___x_1985_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v_kernelArgs_2049_; lean_object* v___y_2050_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; size_t v_sz_2061_; size_t v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v_legalAxioms_1984_ = lean_ctor_get(v___y_1954_, 5);
v___x_1985_ = 0;
v___x_2056_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10));
v___x_2057_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
lean_inc_ref(v_solutionPath_1949_);
v___x_2058_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_solutionPath_1949_);
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12));
v_sz_2061_ = lean_array_size(v_legalAxioms_1984_);
v___x_2062_ = ((size_t)0ULL);
lean_inc_ref(v_legalAxioms_1984_);
v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_2061_, v___x_2062_, v_legalAxioms_1984_);
v___x_2064_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2060_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__27, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__27_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__27);
v___x_2067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2065_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2059_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2056_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = l_Lean_Json_mkObj(v___x_2069_);
lean_dec_ref_known(v___x_2069_, 2);
v___x_2071_ = l_Lean_Json_compress(v___x_2070_);
v___x_2072_ = lean_io_prim_handle_put_str(v_configHandle_1952_, v___x_2071_);
lean_dec_ref(v___x_2071_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v___x_2073_; 
lean_dec_ref_known(v___x_2072_, 1);
v___x_2073_ = lean_io_prim_handle_flush(v_configHandle_1952_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
lean_dec_ref_known(v___x_2073_, 1);
v___x_2074_ = lean_unsigned_to_nat(1u);
v___x_2075_ = lean_array_get_size(v_kernelCommand_1951_);
lean_inc_ref(v_kernelCommand_1951_);
v___x_2076_ = l_Array_toSubarray___redArg(v_kernelCommand_1951_, v___x_2074_, v___x_2075_);
v___x_2077_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_2078_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v___x_2076_, v___x_2077_);
lean_inc_ref(v_kernelName_1948_);
v___x_2079_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_1948_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; 
lean_inc_ref(v_solutionPath_1949_);
v___x_2080_ = lean_array_push(v___x_2078_, v_solutionPath_1949_);
v_kernelArgs_2049_ = v___x_2080_;
v___y_2050_ = v___y_1954_;
goto v___jp_2048_;
}
else
{
lean_object* v___x_2081_; 
lean_inc_ref(v_configPath_1953_);
v___x_2081_ = lean_array_push(v___x_2078_, v_configPath_1953_);
v_kernelArgs_2049_ = v___x_2081_;
v___y_2050_ = v___y_1954_;
goto v___jp_2048_;
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec_ref(v_configPath_1953_);
lean_dec_ref(v_kernelCommand_1951_);
lean_dec_ref(v_solutionPath_1949_);
lean_dec_ref(v_kernelName_1948_);
v_a_2082_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2073_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2073_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec_ref(v_configPath_1953_);
lean_dec_ref(v_kernelCommand_1951_);
lean_dec_ref(v_solutionPath_1949_);
lean_dec_ref(v_kernelName_1948_);
v_a_2090_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2072_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2072_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
v___jp_1956_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1958_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__0));
v___x_1959_ = lean_string_append(v___x_1958_, v_kernelName_1948_);
lean_dec_ref(v_kernelName_1948_);
v___x_1960_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__1));
lean_inc_ref(v___x_1959_);
v___x_1961_ = lean_string_append(v___x_1959_, v___x_1960_);
v___x_1962_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1961_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1974_; 
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v___x_1962_, 0);
lean_dec(v_unused_1975_);
v___x_1964_ = v___x_1962_;
v_isShared_1965_ = v_isSharedCheck_1974_;
goto v_resetjp_1963_;
}
else
{
lean_dec(v___x_1962_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1974_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1966_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__2));
v___x_1967_ = lean_string_append(v___x_1959_, v___x_1966_);
v___x_1968_ = lean_io_error_to_string(v_a_1957_);
v___x_1969_ = lean_string_append(v___x_1967_, v___x_1968_);
lean_dec_ref(v___x_1968_);
v___x_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1970_);
v___x_1972_ = v___x_1964_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec_ref(v___x_1959_);
lean_dec(v_a_1957_);
v_a_1976_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1962_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1962_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
v___jp_1986_:
{
lean_object* v_leanPrefix_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_leanPrefix_1991_ = lean_ctor_get(v___y_1989_, 6);
v___x_1992_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__4));
v___x_1993_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1994_ = lean_unsigned_to_nat(4u);
v___x_1995_ = lean_mk_empty_array_with_capacity(v___x_1994_);
v___x_1996_ = lean_array_push(v___x_1995_, v_configPath_1953_);
v___x_1997_ = lean_array_push(v___x_1996_, v_solutionPath_1949_);
lean_inc_ref(v___y_1990_);
v___x_1998_ = lean_array_push(v___x_1997_, v___y_1990_);
lean_inc_ref(v_leanPrefix_1991_);
v___x_1999_ = lean_array_push(v___x_1998_, v_leanPrefix_1991_);
v___x_2000_ = lean_mk_empty_array_with_capacity(v___y_1987_);
v___x_2001_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_2002_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5));
v___x_2003_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_2003_, 0, v___y_1990_);
lean_ctor_set(v___x_2003_, 1, v___y_1988_);
lean_ctor_set(v___x_2003_, 2, v___x_1992_);
lean_ctor_set(v___x_2003_, 3, v___x_1993_);
lean_ctor_set(v___x_2003_, 4, v___x_1999_);
lean_ctor_set(v___x_2003_, 5, v___x_2000_);
lean_ctor_set(v___x_2003_, 6, v___x_2001_);
lean_ctor_set(v___x_2003_, 7, v___x_2002_);
lean_ctor_set_uint8(v___x_2003_, sizeof(void*)*8, v___x_1985_);
v___x_2004_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v___x_2003_, v___y_1989_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2046_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2046_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2046_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
uint32_t v___x_2009_; uint32_t v___x_2010_; uint8_t v___x_2011_; 
v___x_2009_ = 0;
v___x_2010_ = lean_unbox_uint32(v_a_2005_);
v___x_2011_ = lean_uint32_dec_eq(v___x_2010_, v___x_2009_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6));
lean_inc_ref(v_kernelName_1948_);
v___x_2013_ = lean_string_append(v_kernelName_1948_, v___x_2012_);
v___x_2014_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2013_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2030_; 
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v___x_2014_, 0);
lean_dec(v_unused_2031_);
v___x_2016_ = v___x_2014_;
v_isShared_2017_ = v_isSharedCheck_2030_;
goto v_resetjp_2015_;
}
else
{
lean_dec(v___x_2014_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2030_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; uint32_t v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2018_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7));
v___x_2019_ = lean_string_append(v_kernelName_1948_, v___x_2018_);
v___x_2020_ = lean_unbox_uint32(v_a_2005_);
lean_dec(v_a_2005_);
v___x_2021_ = lean_uint32_to_nat(v___x_2020_);
v___x_2022_ = l_Nat_reprFast(v___x_2021_);
v___x_2023_ = lean_string_append(v___x_2019_, v___x_2022_);
lean_dec_ref(v___x_2022_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set_tag(v___x_2007_, 1);
lean_ctor_set(v___x_2007_, 0, v___x_2023_);
v___x_2025_ = v___x_2007_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2027_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2025_);
v___x_2027_ = v___x_2016_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v_a_2032_; 
lean_del_object(v___x_2007_);
lean_dec(v_a_2005_);
v_a_2032_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2014_, 1);
v_a_1957_ = v_a_2032_;
goto v___jp_1956_;
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_del_object(v___x_2007_);
lean_dec(v_a_2005_);
v___x_2033_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8));
lean_inc_ref(v_kernelName_1948_);
v___x_2034_ = lean_string_append(v_kernelName_1948_, v___x_2033_);
v___x_2035_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2034_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2043_; 
lean_dec_ref(v_kernelName_1948_);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; 
v_unused_2044_ = lean_ctor_get(v___x_2035_, 0);
lean_dec(v_unused_2044_);
v___x_2037_ = v___x_2035_;
v_isShared_2038_ = v_isSharedCheck_2043_;
goto v_resetjp_2036_;
}
else
{
lean_dec(v___x_2035_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2043_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2039_ = lean_box(0);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2039_);
v___x_2041_ = v___x_2037_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
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
lean_object* v_a_2045_; 
v_a_2045_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2035_, 1);
v_a_1957_ = v_a_2045_;
goto v___jp_1956_;
}
}
}
}
else
{
lean_object* v_a_2047_; 
v_a_2047_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2004_, 1);
v_a_1957_ = v_a_2047_;
goto v___jp_1956_;
}
}
v___jp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_a_2054_; 
v___x_2051_ = lean_unsigned_to_nat(0u);
v___x_2052_ = lean_array_get(v___x_1950_, v_kernelCommand_1951_, v___x_2051_);
lean_dec_ref(v_kernelCommand_1951_);
lean_inc(v___x_2052_);
v___x_2053_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_2052_);
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref(v___x_2053_);
if (lean_obj_tag(v_a_2054_) == 0)
{
v___y_1987_ = v___x_2051_;
v___y_1988_ = v_kernelArgs_2049_;
v___y_1989_ = v___y_2050_;
v___y_1990_ = v___x_2052_;
goto v___jp_1986_;
}
else
{
lean_object* v_val_2055_; 
lean_dec(v___x_2052_);
v_val_2055_ = lean_ctor_get(v_a_2054_, 0);
lean_inc(v_val_2055_);
lean_dec_ref_known(v_a_2054_, 1);
v___y_1987_ = v___x_2051_;
v___y_1988_ = v_kernelArgs_2049_;
v___y_1989_ = v___y_2050_;
v___y_1990_ = v_val_2055_;
goto v___jp_1986_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed(lean_object* v_kernelName_2098_, lean_object* v_solutionPath_2099_, lean_object* v___x_2100_, lean_object* v_kernelCommand_2101_, lean_object* v_configHandle_2102_, lean_object* v_configPath_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(v_kernelName_2098_, v_solutionPath_2099_, v___x_2100_, v_kernelCommand_2101_, v_configHandle_2102_, v_configPath_2103_, v___y_2104_);
lean_dec_ref(v___y_2104_);
lean_dec(v_configHandle_2102_);
lean_dec_ref(v___x_2100_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(lean_object* v_kernelName_2109_, lean_object* v_kernelCommand_2110_, lean_object* v_solutionPath_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___x_2114_; lean_object* v___f_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2114_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
lean_inc_ref(v_kernelName_2109_);
v___f_2115_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed), 8, 4);
lean_closure_set(v___f_2115_, 0, v_kernelName_2109_);
lean_closure_set(v___f_2115_, 1, v_solutionPath_2111_);
lean_closure_set(v___f_2115_, 2, v___x_2114_);
lean_closure_set(v___f_2115_, 3, v_kernelCommand_2110_);
v___x_2116_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0));
v___x_2117_ = lean_string_append(v___x_2116_, v_kernelName_2109_);
lean_dec_ref(v_kernelName_2109_);
v___x_2118_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1));
v___x_2119_ = lean_string_append(v___x_2117_, v___x_2118_);
v___x_2120_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2119_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v___x_2121_; 
lean_dec_ref_known(v___x_2120_, 1);
v___x_2121_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg(v___f_2115_, v_a_2112_);
return v___x_2121_;
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v___f_2115_);
v_a_2122_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2120_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2120_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___boxed(lean_object* v_kernelName_2130_, lean_object* v_kernelCommand_2131_, lean_object* v_solutionPath_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_kernelName_2130_, v_kernelCommand_2131_, v_solutionPath_2132_, v_a_2133_);
lean_dec_ref(v_a_2133_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1(lean_object* v_inst_2136_, lean_object* v_R_2137_, lean_object* v_a_2138_, lean_object* v_b_2139_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v_a_2138_, v_b_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(lean_object* v_solutionPath_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v_whichLeanChecker_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v_whichLeanChecker_2147_ = lean_ctor_get(v_a_2145_, 13);
v___x_2148_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0));
v___x_2149_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_2150_ = lean_unsigned_to_nat(3u);
v___x_2151_ = lean_mk_empty_array_with_capacity(v___x_2150_);
lean_inc_ref(v_whichLeanChecker_2147_);
v___x_2152_ = lean_array_push(v___x_2151_, v_whichLeanChecker_2147_);
v___x_2153_ = lean_array_push(v___x_2152_, v___x_2148_);
v___x_2154_ = lean_array_push(v___x_2153_, v___x_2149_);
v___x_2155_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2));
v___x_2156_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v___x_2155_, v___x_2154_, v_solutionPath_2144_, v_a_2145_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___boxed(lean_object* v_solutionPath_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_solutionPath_2157_, v_a_2158_);
lean_dec_ref(v_a_2158_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg(){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__52));
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___boxed(lean_object* v_a_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(lean_object* v_a_2315_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___boxed(lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(v_a_2318_);
lean_dec_ref(v_a_2318_);
return v_res_2320_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(lean_object* v_a_2321_, lean_object* v_as_2322_, size_t v_i_2323_, size_t v_stop_2324_){
_start:
{
uint8_t v___x_2325_; 
v___x_2325_ = lean_usize_dec_eq(v_i_2323_, v_stop_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2326_ = lean_array_uget_borrowed(v_as_2322_, v_i_2323_);
v___x_2327_ = lean_name_eq(v_a_2321_, v___x_2326_);
if (v___x_2327_ == 0)
{
size_t v___x_2328_; size_t v___x_2329_; 
v___x_2328_ = ((size_t)1ULL);
v___x_2329_ = lean_usize_add(v_i_2323_, v___x_2328_);
v_i_2323_ = v___x_2329_;
goto _start;
}
else
{
return v___x_2327_;
}
}
else
{
uint8_t v___x_2331_; 
v___x_2331_ = 0;
return v___x_2331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0___boxed(lean_object* v_a_2332_, lean_object* v_as_2333_, lean_object* v_i_2334_, lean_object* v_stop_2335_){
_start:
{
size_t v_i_boxed_2336_; size_t v_stop_boxed_2337_; uint8_t v_res_2338_; lean_object* v_r_2339_; 
v_i_boxed_2336_ = lean_unbox_usize(v_i_2334_);
lean_dec(v_i_2334_);
v_stop_boxed_2337_ = lean_unbox_usize(v_stop_2335_);
lean_dec(v_stop_2335_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_2332_, v_as_2333_, v_i_boxed_2336_, v_stop_boxed_2337_);
lean_dec_ref(v_as_2333_);
lean_dec(v_a_2332_);
v_r_2339_ = lean_box(v_res_2338_);
return v_r_2339_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(lean_object* v_as_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = lean_array_get_size(v_as_2340_);
v___x_2344_ = lean_nat_dec_lt(v___x_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
return v___x_2344_;
}
else
{
if (v___x_2344_ == 0)
{
return v___x_2344_;
}
else
{
size_t v___x_2345_; size_t v___x_2346_; uint8_t v___x_2347_; 
v___x_2345_ = ((size_t)0ULL);
v___x_2346_ = lean_usize_of_nat(v___x_2343_);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_2341_, v_as_2340_, v___x_2345_, v___x_2346_);
return v___x_2347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0___boxed(lean_object* v_as_2348_, lean_object* v_a_2349_){
_start:
{
uint8_t v_res_2350_; lean_object* v_r_2351_; 
v_res_2350_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_as_2348_, v_a_2349_);
lean_dec(v_a_2349_);
lean_dec_ref(v_as_2348_);
v_r_2351_ = lean_box(v_res_2350_);
return v_r_2351_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11(void){
_start:
{
lean_object* v___x_2382_; lean_object* v_additional_2383_; lean_object* v___x_2384_; 
v___x_2382_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__10));
v_additional_2383_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_2384_ = l_Array_append___redArg(v_additional_2383_, v___x_2382_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(lean_object* v_a_2385_){
_start:
{
lean_object* v_legalAxioms_2387_; lean_object* v_additional_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v_legalAxioms_2387_ = lean_ctor_get(v_a_2385_, 5);
v_additional_2388_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_2389_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3));
v___x_2390_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_legalAxioms_2387_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; 
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v_additional_2388_);
return v___x_2391_;
}
else
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11);
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
return v___x_2393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___boxed(lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_2394_);
lean_dec_ref(v_a_2394_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(lean_object* v_e_2397_){
_start:
{
if (lean_obj_tag(v_e_2397_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2407_; 
v_a_2399_ = lean_ctor_get(v_e_2397_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v_e_2397_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2401_ = v_e_2397_;
v_isShared_2402_ = v_isSharedCheck_2407_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v_e_2397_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2407_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2403_ = lean_mk_io_user_error(v_a_2399_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set_tag(v___x_2401_, 1);
lean_ctor_set(v___x_2401_, 0, v___x_2403_);
v___x_2405_ = v___x_2401_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
v_a_2408_ = lean_ctor_get(v_e_2397_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_e_2397_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v_e_2397_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v_e_2397_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set_tag(v___x_2410_, 0);
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
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg___boxed(lean_object* v_e_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v_e_2416_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(lean_object* v_00_u03b1_2419_, lean_object* v_e_2420_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v_e_2420_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___boxed(lean_object* v_00_u03b1_2423_, lean_object* v_e_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(v_00_u03b1_2423_, v_e_2424_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(lean_object* v_challengeExportPath_2427_, lean_object* v_solutionExportPath_2428_, lean_object* v_a_2429_){
_start:
{
uint8_t v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = 0;
v___x_2432_ = lean_io_prim_handle_mk(v_challengeExportPath_2427_, v___x_2431_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
v___x_2434_ = lean_stream_of_handle(v_a_2433_);
v___x_2435_ = l_LeanExport_parseStream(v___x_2434_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v___x_2437_ = lean_io_prim_handle_mk(v_solutionExportPath_2428_, v___x_2431_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = lean_stream_of_handle(v_a_2438_);
v___x_2440_ = l_LeanExport_parseStream(v___x_2439_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v_theoremNames_2442_; lean_object* v_definitionNames_2443_; lean_object* v_legalAxioms_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_a_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc_n(v_a_2441_, 2);
lean_dec_ref_known(v___x_2440_, 1);
v_theoremNames_2442_ = lean_ctor_get(v_a_2429_, 3);
v_definitionNames_2443_ = lean_ctor_get(v_a_2429_, 4);
v_legalAxioms_2444_ = lean_ctor_get(v_a_2429_, 5);
lean_inc_ref(v_theoremNames_2442_);
v___x_2445_ = l_Array_append___redArg(v_theoremNames_2442_, v_legalAxioms_2444_);
v___x_2446_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref(v___x_2446_);
v___x_2448_ = l_Lake_Check_compareAt(v_a_2436_, v_a_2441_, v___x_2445_, v_definitionNames_2443_, v_a_2447_);
lean_dec_ref(v___x_2445_);
v___x_2449_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v___x_2448_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
lean_dec_ref_known(v___x_2449_, 1);
v___x_2450_ = l_Lake_Check_checkAxioms(v_a_2441_, v_theoremNames_2442_, v_definitionNames_2443_, v_legalAxioms_2444_);
v___x_2451_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v___x_2450_);
return v___x_2451_;
}
else
{
lean_dec(v_a_2441_);
return v___x_2449_;
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v_a_2436_);
v_a_2452_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2440_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2440_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v_a_2436_);
v_a_2460_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2437_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2437_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
v_a_2468_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2435_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2435_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_a_2476_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2432_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2432_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare___boxed(lean_object* v_challengeExportPath_2484_, lean_object* v_solutionExportPath_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(v_challengeExportPath_2484_, v_solutionExportPath_2485_, v_a_2486_);
lean_dec_ref(v_a_2486_);
lean_dec_ref(v_solutionExportPath_2485_);
lean_dec_ref(v_challengeExportPath_2484_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels_spec__0(lean_object* v_solutionExportPath_2489_, lean_object* v_init_2490_, lean_object* v_x_2491_, lean_object* v___y_2492_){
_start:
{
if (lean_obj_tag(v_x_2491_) == 0)
{
lean_object* v_k_2494_; lean_object* v_v_2495_; lean_object* v_l_2496_; lean_object* v_r_2497_; lean_object* v___x_2498_; 
v_k_2494_ = lean_ctor_get(v_x_2491_, 1);
lean_inc(v_k_2494_);
v_v_2495_ = lean_ctor_get(v_x_2491_, 2);
lean_inc(v_v_2495_);
v_l_2496_ = lean_ctor_get(v_x_2491_, 3);
lean_inc(v_l_2496_);
v_r_2497_ = lean_ctor_get(v_x_2491_, 4);
lean_inc(v_r_2497_);
lean_dec_ref_known(v_x_2491_, 5);
lean_inc_ref(v_solutionExportPath_2489_);
v___x_2498_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels_spec__0(v_solutionExportPath_2489_, v_init_2490_, v_l_2496_, v___y_2492_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v_a_2500_; lean_object* v___x_2501_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v_a_2500_ = lean_ctor_get(v_a_2499_, 0);
lean_inc(v_a_2500_);
lean_dec(v_a_2499_);
lean_inc_ref(v_solutionExportPath_2489_);
v___x_2501_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_k_2494_, v_v_2495_, v_solutionExportPath_2489_, v___y_2492_);
if (lean_obj_tag(v___x_2501_) == 0)
{
if (lean_obj_tag(v_a_2500_) == 0)
{
lean_object* v_a_2502_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
v_init_2490_ = v_a_2502_;
v_x_2491_ = v_r_2497_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_2501_, 1);
v_init_2490_ = v_a_2500_;
v_x_2491_ = v_r_2497_;
goto _start;
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_a_2500_);
lean_dec(v_r_2497_);
lean_dec_ref(v_solutionExportPath_2489_);
v_a_2505_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2501_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2501_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_dec(v_r_2497_);
lean_dec(v_v_2495_);
lean_dec(v_k_2494_);
lean_dec_ref(v_solutionExportPath_2489_);
return v___x_2498_;
}
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_dec_ref(v_solutionExportPath_2489_);
v___x_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2513_, 0, v_init_2490_);
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
return v___x_2514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels_spec__0___boxed(lean_object* v_solutionExportPath_2515_, lean_object* v_init_2516_, lean_object* v_x_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels_spec__0(v_solutionExportPath_2515_, v_init_2516_, v_x_2517_, v___y_2518_);
lean_dec_ref(v___y_2518_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels(lean_object* v_solutionExportPath_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v_val_2525_; lean_object* v_a_2529_; lean_object* v_externalKernels_2550_; lean_object* v_result_2551_; lean_object* v___x_2552_; 
v_externalKernels_2550_ = lean_ctor_get(v_a_2522_, 15);
v_result_2551_ = lean_box(0);
lean_inc(v_externalKernels_2550_);
lean_inc_ref(v_solutionExportPath_2521_);
v___x_2552_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels_spec__0(v_solutionExportPath_2521_, v_result_2551_, v_externalKernels_2550_, v_a_2522_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v_a_2554_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v_a_2554_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_a_2554_);
lean_dec(v_a_2553_);
v_a_2529_ = v_a_2554_;
goto v___jp_2528_;
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref(v_solutionExportPath_2521_);
v_a_2555_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2552_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2552_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
v___jp_2524_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = lean_mk_io_user_error(v_val_2525_);
v___x_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
return v___x_2527_;
}
v___jp_2528_:
{
lean_object* v___x_2530_; 
v___x_2530_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_solutionExportPath_2521_, v_a_2522_);
if (lean_obj_tag(v___x_2530_) == 0)
{
if (lean_obj_tag(v_a_2529_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2540_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2540_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2540_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
if (lean_obj_tag(v_a_2531_) == 1)
{
lean_object* v_val_2535_; 
lean_del_object(v___x_2533_);
v_val_2535_ = lean_ctor_get(v_a_2531_, 0);
lean_inc(v_val_2535_);
lean_dec_ref_known(v_a_2531_, 1);
v_val_2525_ = v_val_2535_;
goto v___jp_2524_;
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2538_; 
lean_dec(v_a_2531_);
v___x_2536_ = lean_box(0);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2536_);
v___x_2538_ = v___x_2533_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
else
{
lean_object* v_val_2541_; 
lean_dec_ref_known(v___x_2530_, 1);
v_val_2541_ = lean_ctor_get(v_a_2529_, 0);
lean_inc(v_val_2541_);
lean_dec_ref_known(v_a_2529_, 1);
v_val_2525_ = v_val_2541_;
goto v___jp_2524_;
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_a_2529_);
v_a_2542_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2530_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2530_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels___boxed(lean_object* v_solutionExportPath_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels(v_solutionExportPath_2563_, v_a_2564_);
lean_dec_ref(v_a_2564_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(lean_object* v_challengeExportPath_2567_, lean_object* v_solutionExportPath_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(v_challengeExportPath_2567_, v_solutionExportPath_2568_, v_a_2569_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v___x_2572_; 
lean_dec_ref_known(v___x_2571_, 1);
v___x_2572_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels(v_solutionExportPath_2568_, v_a_2569_);
return v___x_2572_;
}
else
{
lean_dec_ref(v_solutionExportPath_2568_);
return v___x_2571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch___boxed(lean_object* v_challengeExportPath_2573_, lean_object* v_solutionExportPath_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExportPath_2573_, v_solutionExportPath_2574_, v_a_2575_);
lean_dec_ref(v_a_2575_);
lean_dec_ref(v_challengeExportPath_2573_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__0(lean_object* v_challengeExportPath_2579_, lean_object* v_solutionExportPath_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExportPath_2579_, v_solutionExportPath_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_dec_ref_known(v___x_2583_, 1);
v___x_2584_ = ((lean_object*)(l_Lake_Check_compareIt___lam__0___closed__0));
v___x_2585_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2584_);
return v___x_2585_;
}
else
{
return v___x_2583_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__0___boxed(lean_object* v_challengeExportPath_2586_, lean_object* v_solutionExportPath_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lake_Check_compareIt___lam__0(v_challengeExportPath_2586_, v_solutionExportPath_2587_, v___y_2588_);
lean_dec_ref(v___y_2588_);
lean_dec_ref(v_challengeExportPath_2586_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__1(lean_object* v___x_2591_, lean_object* v_challengeExportPath_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v_solutionModule_2595_; lean_object* v___f_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v_solutionModule_2595_ = lean_ctor_get(v___y_2593_, 2);
v___f_2596_ = lean_alloc_closure((void*)(l_Lake_Check_compareIt___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2596_, 0, v_challengeExportPath_2592_);
v___x_2597_ = lean_unsigned_to_nat(1u);
v___x_2598_ = lean_mk_empty_array_with_capacity(v___x_2597_);
lean_inc(v_solutionModule_2595_);
v___x_2599_ = lean_array_push(v___x_2598_, v_solutionModule_2595_);
v___x_2600_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v___x_2599_, v___y_2593_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v___x_2601_; 
lean_dec_ref_known(v___x_2600_, 1);
lean_inc(v_solutionModule_2595_);
v___x_2601_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_solutionModule_2595_, v___x_2591_, v___f_2596_, v___y_2593_);
return v___x_2601_;
}
else
{
lean_dec_ref(v___f_2596_);
lean_dec_ref(v___x_2591_);
return v___x_2600_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__1___boxed(lean_object* v___x_2602_, lean_object* v_challengeExportPath_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lake_Check_compareIt___lam__1(v___x_2602_, v_challengeExportPath_2603_, v___y_2604_);
lean_dec_ref(v___y_2604_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt(lean_object* v_a_2607_){
_start:
{
lean_object* v___x_2609_; lean_object* v_a_2610_; lean_object* v_challengeModule_2611_; lean_object* v_theoremNames_2612_; lean_object* v_definitionNames_2613_; lean_object* v_legalAxioms_2614_; lean_object* v___x_2615_; lean_object* v_a_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___f_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2609_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_2607_);
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref(v___x_2609_);
v_challengeModule_2611_ = lean_ctor_get(v_a_2607_, 1);
v_theoremNames_2612_ = lean_ctor_get(v_a_2607_, 3);
v_definitionNames_2613_ = lean_ctor_get(v_a_2607_, 4);
v_legalAxioms_2614_ = lean_ctor_get(v_a_2607_, 5);
v___x_2615_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref(v___x_2615_);
v___x_2617_ = l_Array_append___redArg(v_a_2610_, v_theoremNames_2612_);
v___x_2618_ = l_Array_append___redArg(v___x_2617_, v_legalAxioms_2614_);
v___x_2619_ = l_Array_append___redArg(v___x_2618_, v_a_2616_);
lean_dec(v_a_2616_);
v___x_2620_ = l_Array_append___redArg(v___x_2619_, v_definitionNames_2613_);
lean_inc_ref(v___x_2620_);
v___f_2621_ = lean_alloc_closure((void*)(l_Lake_Check_compareIt___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2621_, 0, v___x_2620_);
v___x_2622_ = lean_unsigned_to_nat(1u);
v___x_2623_ = lean_mk_empty_array_with_capacity(v___x_2622_);
lean_inc(v_challengeModule_2611_);
v___x_2624_ = lean_array_push(v___x_2623_, v_challengeModule_2611_);
v___x_2625_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v___x_2624_, v_a_2607_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v___x_2626_; 
lean_dec_ref_known(v___x_2625_, 1);
lean_inc(v_challengeModule_2611_);
v___x_2626_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_challengeModule_2611_, v___x_2620_, v___f_2621_, v_a_2607_);
return v___x_2626_;
}
else
{
lean_dec_ref(v___f_2621_);
lean_dec_ref(v___x_2620_);
return v___x_2625_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___boxed(lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lake_Check_compareIt(v_a_2627_);
lean_dec_ref(v_a_2627_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(lean_object* v_j_2630_, lean_object* v_k_2631_){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = l_Lean_Json_getObjValD(v_j_2630_, v_k_2631_);
v___x_2633_ = l_Lean_Json_getStr_x3f(v___x_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0___boxed(lean_object* v_j_2634_, lean_object* v_k_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_j_2634_, v_k_2635_);
lean_dec_ref(v_k_2635_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(size_t v_sz_2637_, size_t v_i_2638_, lean_object* v_bs_2639_){
_start:
{
uint8_t v___x_2640_; 
v___x_2640_ = lean_usize_dec_lt(v_i_2638_, v_sz_2637_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; 
v___x_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2641_, 0, v_bs_2639_);
return v___x_2641_;
}
else
{
lean_object* v_v_2642_; lean_object* v___x_2643_; 
v_v_2642_ = lean_array_uget_borrowed(v_bs_2639_, v_i_2638_);
lean_inc(v_v_2642_);
v___x_2643_ = l_Lean_Json_getStr_x3f(v_v_2642_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec_ref(v_bs_2639_);
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2653_; lean_object* v_bs_x27_2654_; size_t v___x_2655_; size_t v___x_2656_; lean_object* v___x_2657_; 
v_a_2652_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2653_ = lean_unsigned_to_nat(0u);
v_bs_x27_2654_ = lean_array_uset(v_bs_2639_, v_i_2638_, v___x_2653_);
v___x_2655_ = ((size_t)1ULL);
v___x_2656_ = lean_usize_add(v_i_2638_, v___x_2655_);
v___x_2657_ = lean_array_uset(v_bs_x27_2654_, v_i_2638_, v_a_2652_);
v_i_2638_ = v___x_2656_;
v_bs_2639_ = v___x_2657_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2659_, lean_object* v_i_2660_, lean_object* v_bs_2661_){
_start:
{
size_t v_sz_boxed_2662_; size_t v_i_boxed_2663_; lean_object* v_res_2664_; 
v_sz_boxed_2662_ = lean_unbox_usize(v_sz_2659_);
lean_dec(v_sz_2659_);
v_i_boxed_2663_ = lean_unbox_usize(v_i_2660_);
lean_dec(v_i_2660_);
v_res_2664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_2662_, v_i_boxed_2663_, v_bs_2661_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(lean_object* v_x_2667_){
_start:
{
if (lean_obj_tag(v_x_2667_) == 4)
{
lean_object* v_elems_2668_; size_t v_sz_2669_; size_t v___x_2670_; lean_object* v___x_2671_; 
v_elems_2668_ = lean_ctor_get(v_x_2667_, 0);
lean_inc_ref(v_elems_2668_);
lean_dec_ref_known(v_x_2667_, 1);
v_sz_2669_ = lean_array_size(v_elems_2668_);
v___x_2670_ = ((size_t)0ULL);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_2669_, v___x_2670_, v_elems_2668_);
return v___x_2671_;
}
else
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2672_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__0));
v___x_2673_ = lean_unsigned_to_nat(80u);
v___x_2674_ = l_Lean_Json_pretty(v_x_2667_, v___x_2673_);
v___x_2675_ = lean_string_append(v___x_2672_, v___x_2674_);
lean_dec_ref(v___x_2674_);
v___x_2676_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_2677_ = lean_string_append(v___x_2675_, v___x_2676_);
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
return v___x_2678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(lean_object* v_x_2681_){
_start:
{
if (lean_obj_tag(v_x_2681_) == 0)
{
lean_object* v___x_2682_; 
v___x_2682_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3___closed__0));
return v___x_2682_;
}
else
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_x_2681_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2700_; 
v_a_2692_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2694_ = v___x_2683_;
v_isShared_2695_ = v_isSharedCheck_2700_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2683_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2700_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_a_2692_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2696_);
v___x_2698_ = v___x_2694_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(lean_object* v_j_2701_, lean_object* v_k_2702_){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = l_Lean_Json_getObjValD(v_j_2701_, v_k_2702_);
v___x_2704_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(v___x_2703_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2___boxed(lean_object* v_j_2705_, lean_object* v_k_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_j_2705_, v_k_2706_);
lean_dec_ref(v_k_2706_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(lean_object* v_x_2710_){
_start:
{
if (lean_obj_tag(v_x_2710_) == 0)
{
lean_object* v___x_2711_; 
v___x_2711_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___closed__0));
return v___x_2711_;
}
else
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lean_Json_getBool_x3f(v_x_2710_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2729_; 
v_a_2721_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2723_ = v___x_2712_;
v_isShared_2724_ = v_isSharedCheck_2729_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2712_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2729_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
v___x_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2725_, 0, v_a_2721_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2725_);
v___x_2727_ = v___x_2723_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___boxed(lean_object* v_x_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v_x_2730_);
lean_dec(v_x_2730_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(lean_object* v_j_2732_, lean_object* v_k_2733_){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = l_Lean_Json_getObjValD(v_j_2732_, v_k_2733_);
v___x_2735_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v___x_2734_);
lean_dec(v___x_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3___boxed(lean_object* v_j_2736_, lean_object* v_k_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_j_2736_, v_k_2737_);
lean_dec_ref(v_k_2737_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_cmp_2739_, lean_object* v_k_2740_, lean_object* v_v_2741_, lean_object* v_t_2742_){
_start:
{
if (lean_obj_tag(v_t_2742_) == 0)
{
lean_object* v_size_2743_; lean_object* v_k_2744_; lean_object* v_v_2745_; lean_object* v_l_2746_; lean_object* v_r_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_3028_; 
v_size_2743_ = lean_ctor_get(v_t_2742_, 0);
v_k_2744_ = lean_ctor_get(v_t_2742_, 1);
v_v_2745_ = lean_ctor_get(v_t_2742_, 2);
v_l_2746_ = lean_ctor_get(v_t_2742_, 3);
v_r_2747_ = lean_ctor_get(v_t_2742_, 4);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_t_2742_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_2749_ = v_t_2742_;
v_isShared_2750_ = v_isSharedCheck_3028_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_r_2747_);
lean_inc(v_l_2746_);
lean_inc(v_v_2745_);
lean_inc(v_k_2744_);
lean_inc(v_size_2743_);
lean_dec(v_t_2742_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_3028_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; uint8_t v___x_2752_; 
lean_inc_ref(v_cmp_2739_);
lean_inc(v_k_2744_);
lean_inc_ref(v_k_2740_);
v___x_2751_ = lean_apply_2(v_cmp_2739_, v_k_2740_, v_k_2744_);
v___x_2752_ = lean_unbox(v___x_2751_);
switch(v___x_2752_)
{
case 0:
{
lean_object* v_impl_2753_; lean_object* v___x_2754_; 
lean_dec(v_size_2743_);
v_impl_2753_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_2739_, v_k_2740_, v_v_2741_, v_l_2746_);
v___x_2754_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2747_) == 0)
{
lean_object* v_size_2755_; lean_object* v_size_2756_; lean_object* v_k_2757_; lean_object* v_v_2758_; lean_object* v_l_2759_; lean_object* v_r_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v_size_2755_ = lean_ctor_get(v_r_2747_, 0);
v_size_2756_ = lean_ctor_get(v_impl_2753_, 0);
lean_inc(v_size_2756_);
v_k_2757_ = lean_ctor_get(v_impl_2753_, 1);
lean_inc(v_k_2757_);
v_v_2758_ = lean_ctor_get(v_impl_2753_, 2);
lean_inc(v_v_2758_);
v_l_2759_ = lean_ctor_get(v_impl_2753_, 3);
lean_inc(v_l_2759_);
v_r_2760_ = lean_ctor_get(v_impl_2753_, 4);
lean_inc(v_r_2760_);
v___x_2761_ = lean_unsigned_to_nat(3u);
v___x_2762_ = lean_nat_mul(v___x_2761_, v_size_2755_);
v___x_2763_ = lean_nat_dec_lt(v___x_2762_, v_size_2756_);
lean_dec(v___x_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
lean_dec(v_r_2760_);
lean_dec(v_l_2759_);
lean_dec(v_v_2758_);
lean_dec(v_k_2757_);
v___x_2764_ = lean_nat_add(v___x_2754_, v_size_2756_);
lean_dec(v_size_2756_);
v___x_2765_ = lean_nat_add(v___x_2764_, v_size_2755_);
lean_dec(v___x_2764_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 3, v_impl_2753_);
lean_ctor_set(v___x_2749_, 0, v___x_2765_);
v___x_2767_ = v___x_2749_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_k_2744_);
lean_ctor_set(v_reuseFailAlloc_2768_, 2, v_v_2745_);
lean_ctor_set(v_reuseFailAlloc_2768_, 3, v_impl_2753_);
lean_ctor_set(v_reuseFailAlloc_2768_, 4, v_r_2747_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
else
{
lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2834_; 
v_isSharedCheck_2834_ = !lean_is_exclusive(v_impl_2753_);
if (v_isSharedCheck_2834_ == 0)
{
lean_object* v_unused_2835_; lean_object* v_unused_2836_; lean_object* v_unused_2837_; lean_object* v_unused_2838_; lean_object* v_unused_2839_; 
v_unused_2835_ = lean_ctor_get(v_impl_2753_, 4);
lean_dec(v_unused_2835_);
v_unused_2836_ = lean_ctor_get(v_impl_2753_, 3);
lean_dec(v_unused_2836_);
v_unused_2837_ = lean_ctor_get(v_impl_2753_, 2);
lean_dec(v_unused_2837_);
v_unused_2838_ = lean_ctor_get(v_impl_2753_, 1);
lean_dec(v_unused_2838_);
v_unused_2839_ = lean_ctor_get(v_impl_2753_, 0);
lean_dec(v_unused_2839_);
v___x_2770_ = v_impl_2753_;
v_isShared_2771_ = v_isSharedCheck_2834_;
goto v_resetjp_2769_;
}
else
{
lean_dec(v_impl_2753_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2834_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v_size_2772_; lean_object* v_size_2773_; lean_object* v_k_2774_; lean_object* v_v_2775_; lean_object* v_l_2776_; lean_object* v_r_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v_size_2772_ = lean_ctor_get(v_l_2759_, 0);
v_size_2773_ = lean_ctor_get(v_r_2760_, 0);
v_k_2774_ = lean_ctor_get(v_r_2760_, 1);
v_v_2775_ = lean_ctor_get(v_r_2760_, 2);
v_l_2776_ = lean_ctor_get(v_r_2760_, 3);
v_r_2777_ = lean_ctor_get(v_r_2760_, 4);
v___x_2778_ = lean_unsigned_to_nat(2u);
v___x_2779_ = lean_nat_mul(v___x_2778_, v_size_2772_);
v___x_2780_ = lean_nat_dec_lt(v_size_2773_, v___x_2779_);
lean_dec(v___x_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2809_; 
lean_inc(v_r_2777_);
lean_inc(v_l_2776_);
lean_inc(v_v_2775_);
lean_inc(v_k_2774_);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_r_2760_);
if (v_isSharedCheck_2809_ == 0)
{
lean_object* v_unused_2810_; lean_object* v_unused_2811_; lean_object* v_unused_2812_; lean_object* v_unused_2813_; lean_object* v_unused_2814_; 
v_unused_2810_ = lean_ctor_get(v_r_2760_, 4);
lean_dec(v_unused_2810_);
v_unused_2811_ = lean_ctor_get(v_r_2760_, 3);
lean_dec(v_unused_2811_);
v_unused_2812_ = lean_ctor_get(v_r_2760_, 2);
lean_dec(v_unused_2812_);
v_unused_2813_ = lean_ctor_get(v_r_2760_, 1);
lean_dec(v_unused_2813_);
v_unused_2814_ = lean_ctor_get(v_r_2760_, 0);
lean_dec(v_unused_2814_);
v___x_2782_ = v_r_2760_;
v_isShared_2783_ = v_isSharedCheck_2809_;
goto v_resetjp_2781_;
}
else
{
lean_dec(v_r_2760_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2809_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___x_2797_; lean_object* v___y_2799_; 
v___x_2784_ = lean_nat_add(v___x_2754_, v_size_2756_);
lean_dec(v_size_2756_);
v___x_2785_ = lean_nat_add(v___x_2784_, v_size_2755_);
lean_dec(v___x_2784_);
v___x_2797_ = lean_nat_add(v___x_2754_, v_size_2772_);
if (lean_obj_tag(v_l_2776_) == 0)
{
lean_object* v_size_2807_; 
v_size_2807_ = lean_ctor_get(v_l_2776_, 0);
lean_inc(v_size_2807_);
v___y_2799_ = v_size_2807_;
goto v___jp_2798_;
}
else
{
lean_object* v___x_2808_; 
v___x_2808_ = lean_unsigned_to_nat(0u);
v___y_2799_ = v___x_2808_;
goto v___jp_2798_;
}
v___jp_2786_:
{
lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2790_ = lean_nat_add(v___y_2788_, v___y_2789_);
lean_dec(v___y_2789_);
lean_dec(v___y_2788_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 4, v_r_2747_);
lean_ctor_set(v___x_2782_, 3, v_r_2777_);
lean_ctor_set(v___x_2782_, 2, v_v_2745_);
lean_ctor_set(v___x_2782_, 1, v_k_2744_);
lean_ctor_set(v___x_2782_, 0, v___x_2790_);
v___x_2792_ = v___x_2782_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_k_2744_);
lean_ctor_set(v_reuseFailAlloc_2796_, 2, v_v_2745_);
lean_ctor_set(v_reuseFailAlloc_2796_, 3, v_r_2777_);
lean_ctor_set(v_reuseFailAlloc_2796_, 4, v_r_2747_);
v___x_2792_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2794_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 4, v___x_2792_);
lean_ctor_set(v___x_2770_, 3, v___y_2787_);
lean_ctor_set(v___x_2770_, 2, v_v_2775_);
lean_ctor_set(v___x_2770_, 1, v_k_2774_);
lean_ctor_set(v___x_2770_, 0, v___x_2785_);
v___x_2794_ = v___x_2770_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_k_2774_);
lean_ctor_set(v_reuseFailAlloc_2795_, 2, v_v_2775_);
lean_ctor_set(v_reuseFailAlloc_2795_, 3, v___y_2787_);
lean_ctor_set(v_reuseFailAlloc_2795_, 4, v___x_2792_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
v___jp_2798_:
{
lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2800_ = lean_nat_add(v___x_2797_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec(v___x_2797_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 4, v_l_2776_);
lean_ctor_set(v___x_2749_, 3, v_l_2759_);
lean_ctor_set(v___x_2749_, 2, v_v_2758_);
lean_ctor_set(v___x_2749_, 1, v_k_2757_);
lean_ctor_set(v___x_2749_, 0, v___x_2800_);
v___x_2802_ = v___x_2749_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2800_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_k_2757_);
lean_ctor_set(v_reuseFailAlloc_2806_, 2, v_v_2758_);
lean_ctor_set(v_reuseFailAlloc_2806_, 3, v_l_2759_);
lean_ctor_set(v_reuseFailAlloc_2806_, 4, v_l_2776_);
v___x_2802_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_nat_add(v___x_2754_, v_size_2755_);
if (lean_obj_tag(v_r_2777_) == 0)
{
lean_object* v_size_2804_; 
v_size_2804_ = lean_ctor_get(v_r_2777_, 0);
lean_inc(v_size_2804_);
v___y_2787_ = v___x_2802_;
v___y_2788_ = v___x_2803_;
v___y_2789_ = v_size_2804_;
goto v___jp_2786_;
}
else
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_unsigned_to_nat(0u);
v___y_2787_ = v___x_2802_;
v___y_2788_ = v___x_2803_;
v___y_2789_ = v___x_2805_;
goto v___jp_2786_;
}
}
}
}
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2820_; 
lean_del_object(v___x_2749_);
v___x_2815_ = lean_nat_add(v___x_2754_, v_size_2756_);
lean_dec(v_size_2756_);
v___x_2816_ = lean_nat_add(v___x_2815_, v_size_2755_);
lean_dec(v___x_2815_);
v___x_2817_ = lean_nat_add(v___x_2754_, v_size_2755_);
v___x_2818_ = lean_nat_add(v___x_2817_, v_size_2773_);
lean_dec(v___x_2817_);
lean_inc_ref(v_r_2747_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 4, v_r_2747_);
lean_ctor_set(v___x_2770_, 3, v_r_2760_);
lean_ctor_set(v___x_2770_, 2, v_v_2745_);
lean_ctor_set(v___x_2770_, 1, v_k_2744_);
lean_ctor_set(v___x_2770_, 0, v___x_2818_);
v___x_2820_ = v___x_2770_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_k_2744_);
lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_v_2745_);
lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_r_2760_);
lean_ctor_set(v_reuseFailAlloc_2833_, 4, v_r_2747_);
v___x_2820_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
v_isSharedCheck_2827_ = !lean_is_exclusive(v_r_2747_);
if (v_isSharedCheck_2827_ == 0)
{
lean_object* v_unused_2828_; lean_object* v_unused_2829_; lean_object* v_unused_2830_; lean_object* v_unused_2831_; lean_object* v_unused_2832_; 
v_unused_2828_ = lean_ctor_get(v_r_2747_, 4);
lean_dec(v_unused_2828_);
v_unused_2829_ = lean_ctor_get(v_r_2747_, 3);
lean_dec(v_unused_2829_);
v_unused_2830_ = lean_ctor_get(v_r_2747_, 2);
lean_dec(v_unused_2830_);
v_unused_2831_ = lean_ctor_get(v_r_2747_, 1);
lean_dec(v_unused_2831_);
v_unused_2832_ = lean_ctor_get(v_r_2747_, 0);
lean_dec(v_unused_2832_);
v___x_2822_ = v_r_2747_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_dec(v_r_2747_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 4, v___x_2820_);
lean_ctor_set(v___x_2822_, 3, v_l_2759_);
lean_ctor_set(v___x_2822_, 2, v_v_2758_);
lean_ctor_set(v___x_2822_, 1, v_k_2757_);
lean_ctor_set(v___x_2822_, 0, v___x_2816_);
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_k_2757_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_v_2758_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_l_2759_);
lean_ctor_set(v_reuseFailAlloc_2826_, 4, v___x_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2840_; 
v_l_2840_ = lean_ctor_get(v_impl_2753_, 3);
lean_inc(v_l_2840_);
if (lean_obj_tag(v_l_2840_) == 0)
{
lean_object* v_r_2841_; lean_object* v_k_2842_; lean_object* v_v_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2854_; 
v_r_2841_ = lean_ctor_get(v_impl_2753_, 4);
v_k_2842_ = lean_ctor_get(v_impl_2753_, 1);
v_v_2843_ = lean_ctor_get(v_impl_2753_, 2);
v_isSharedCheck_2854_ = !lean_is_exclusive(v_impl_2753_);
if (v_isSharedCheck_2854_ == 0)
{
lean_object* v_unused_2855_; lean_object* v_unused_2856_; 
v_unused_2855_ = lean_ctor_get(v_impl_2753_, 3);
lean_dec(v_unused_2855_);
v_unused_2856_ = lean_ctor_get(v_impl_2753_, 0);
lean_dec(v_unused_2856_);
v___x_2845_ = v_impl_2753_;
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_r_2841_);
lean_inc(v_v_2843_);
lean_inc(v_k_2842_);
lean_dec(v_impl_2753_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2847_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2841_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 3, v_r_2841_);
lean_ctor_set(v___x_2845_, 2, v_v_2745_);
lean_ctor_set(v___x_2845_, 1, v_k_2744_);
lean_ctor_set(v___x_2845_, 0, v___x_2754_);
v___x_2849_ = v___x_2845_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_k_2744_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_v_2745_);
lean_ctor_set(v_reuseFailAlloc_2853_, 3, v_r_2841_);
lean_ctor_set(v_reuseFailAlloc_2853_, 4, v_r_2841_);
v___x_2849_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2851_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 4, v___x_2849_);
lean_ctor_set(v___x_2749_, 3, v_l_2840_);
lean_ctor_set(v___x_2749_, 2, v_v_2843_);
lean_ctor_set(v___x_2749_, 1, v_k_2842_);
lean_ctor_set(v___x_2749_, 0, v___x_2847_);
v___x_2851_ = v___x_2749_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_k_2842_);
lean_ctor_set(v_reuseFailAlloc_2852_, 2, v_v_2843_);
lean_ctor_set(v_reuseFailAlloc_2852_, 3, v_l_2840_);
lean_ctor_set(v_reuseFailAlloc_2852_, 4, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
else
{
lean_object* v_r_2857_; 
v_r_2857_ = lean_ctor_get(v_impl_2753_, 4);
lean_inc(v_r_2857_);
if (lean_obj_tag(v_r_2857_) == 0)
{
lean_object* v_k_2858_; lean_object* v_v_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2882_; 
v_k_2858_ = lean_ctor_get(v_impl_2753_, 1);
v_v_2859_ = lean_ctor_get(v_impl_2753_, 2);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_impl_2753_);
if (v_isSharedCheck_2882_ == 0)
{
lean_object* v_unused_2883_; lean_object* v_unused_2884_; lean_object* v_unused_2885_; 
v_unused_2883_ = lean_ctor_get(v_impl_2753_, 4);
lean_dec(v_unused_2883_);
v_unused_2884_ = lean_ctor_get(v_impl_2753_, 3);
lean_dec(v_unused_2884_);
v_unused_2885_ = lean_ctor_get(v_impl_2753_, 0);
lean_dec(v_unused_2885_);
v___x_2861_ = v_impl_2753_;
v_isShared_2862_ = v_isSharedCheck_2882_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_v_2859_);
lean_inc(v_k_2858_);
lean_dec(v_impl_2753_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2882_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v_k_2863_; lean_object* v_v_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2878_; 
v_k_2863_ = lean_ctor_get(v_r_2857_, 1);
v_v_2864_ = lean_ctor_get(v_r_2857_, 2);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_r_2857_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; lean_object* v_unused_2880_; lean_object* v_unused_2881_; 
v_unused_2879_ = lean_ctor_get(v_r_2857_, 4);
lean_dec(v_unused_2879_);
v_unused_2880_ = lean_ctor_get(v_r_2857_, 3);
lean_dec(v_unused_2880_);
v_unused_2881_ = lean_ctor_get(v_r_2857_, 0);
lean_dec(v_unused_2881_);
v___x_2866_ = v_r_2857_;
v_isShared_2867_ = v_isSharedCheck_2878_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_v_2864_);
lean_inc(v_k_2863_);
lean_dec(v_r_2857_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2878_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2868_ = lean_unsigned_to_nat(3u);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 4, v_l_2840_);
lean_ctor_set(v___x_2866_, 3, v_l_2840_);
lean_ctor_set(v___x_2866_, 2, v_v_2859_);
lean_ctor_set(v___x_2866_, 1, v_k_2858_);
lean_ctor_set(v___x_2866_, 0, v___x_2754_);
v___x_2870_ = v___x_2866_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_k_2858_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v_v_2859_);
lean_ctor_set(v_reuseFailAlloc_2877_, 3, v_l_2840_);
lean_ctor_set(v_reuseFailAlloc_2877_, 4, v_l_2840_);
v___x_2870_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2872_; 
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 4, v_l_2840_);
lean_ctor_set(v___x_2861_, 2, v_v_2745_);
lean_ctor_set(v___x_2861_, 1, v_k_2744_);
lean_ctor_set(v___x_2861_, 0, v___x_2754_);
v___x_2872_ = v___x_2861_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_k_2744_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_v_2745_);
lean_ctor_set(v_reuseFailAlloc_2876_, 3, v_l_2840_);
lean_ctor_set(v_reuseFailAlloc_2876_, 4, v_l_2840_);
v___x_2872_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2874_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 4, v___x_2872_);
lean_ctor_set(v___x_2749_, 3, v___x_2870_);
lean_ctor_set(v___x_2749_, 2, v_v_2864_);
lean_ctor_set(v___x_2749_, 1, v_k_2863_);
lean_ctor_set(v___x_2749_, 0, v___x_2868_);
v___x_2874_ = v___x_2749_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_k_2863_);
lean_ctor_set(v_reuseFailAlloc_2875_, 2, v_v_2864_);
lean_ctor_set(v_reuseFailAlloc_2875_, 3, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2875_, 4, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
v___x_2886_ = lean_unsigned_to_nat(2u);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 4, v_r_2857_);
lean_ctor_set(v___x_2749_, 3, v_impl_2753_);
lean_ctor_set(v___x_2749_, 0, v___x_2886_);
v___x_2888_ = v___x_2749_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_k_2744_);
lean_ctor_set(v_reuseFailAlloc_2889_, 2, v_v_2745_);
lean_ctor_set(v_reuseFailAlloc_2889_, 3, v_impl_2753_);
lean_ctor_set(v_reuseFailAlloc_2889_, 4, v_r_2857_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2891_; 
lean_dec(v_v_2745_);
lean_dec(v_k_2744_);
lean_dec_ref(v_cmp_2739_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 2, v_v_2741_);
lean_ctor_set(v___x_2749_, 1, v_k_2740_);
v___x_2891_ = v___x_2749_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_size_2743_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_2892_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_2892_, 3, v_l_2746_);
lean_ctor_set(v_reuseFailAlloc_2892_, 4, v_r_2747_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
default: 
{
lean_object* v_impl_2893_; lean_object* v___x_2894_; 
lean_dec(v_size_2743_);
v_impl_2893_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_2739_, v_k_2740_, v_v_2741_, v_r_2747_);
v___x_2894_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2746_) == 0)
{
lean_object* v_size_2895_; lean_object* v_size_2896_; lean_object* v_k_2897_; lean_object* v_v_2898_; lean_object* v_l_2899_; lean_object* v_r_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v_size_2895_ = lean_ctor_get(v_l_2746_, 0);
v_size_2896_ = lean_ctor_get(v_impl_2893_, 0);
lean_inc(v_size_2896_);
v_k_2897_ = lean_ctor_get(v_impl_2893_, 1);
lean_inc(v_k_2897_);
v_v_2898_ = lean_ctor_get(v_impl_2893_, 2);
lean_inc(v_v_2898_);
v_l_2899_ = lean_ctor_get(v_impl_2893_, 3);
lean_inc(v_l_2899_);
v_r_2900_ = lean_ctor_get(v_impl_2893_, 4);
lean_inc(v_r_2900_);
v___x_2901_ = lean_unsigned_to_nat(3u);
v___x_2902_ = lean_nat_mul(v___x_2901_, v_size_2895_);
v___x_2903_ = lean_nat_dec_lt(v___x_2902_, v_size_2896_);
lean_dec(v___x_2902_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2907_; 
lean_dec(v_r_2900_);
lean_dec(v_l_2899_);
lean_dec(v_v_2898_);
lean_dec(v_k_2897_);
v___x_2904_ = lean_nat_add(v___x_2894_, v_size_2895_);
v___x_2905_ = lean_nat_add(v___x_2904_, v_size_2896_);
lean_dec(v_size_2896_);
lean_dec(v___x_2904_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 4, v_impl_2893_);
lean_ctor_set(v___x_2749_, 0, v___x_2905_);
v___x_2907_ = v___x_2749_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_k_2744_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v_v_2745_);
lean_ctor_set(v_reuseFailAlloc_2908_, 3, v_l_2746_);
lean_ctor_set(v_reuseFailAlloc_2908_, 4, v_impl_2893_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
else
{
lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2972_; 
v_isSharedCheck_2972_ = !lean_is_exclusive(v_impl_2893_);
if (v_isSharedCheck_2972_ == 0)
{
lean_object* v_unused_2973_; lean_object* v_unused_2974_; lean_object* v_unused_2975_; lean_object* v_unused_2976_; lean_object* v_unused_2977_; 
v_unused_2973_ = lean_ctor_get(v_impl_2893_, 4);
lean_dec(v_unused_2973_);
v_unused_2974_ = lean_ctor_get(v_impl_2893_, 3);
lean_dec(v_unused_2974_);
v_unused_2975_ = lean_ctor_get(v_impl_2893_, 2);
lean_dec(v_unused_2975_);
v_unused_2976_ = lean_ctor_get(v_impl_2893_, 1);
lean_dec(v_unused_2976_);
v_unused_2977_ = lean_ctor_get(v_impl_2893_, 0);
lean_dec(v_unused_2977_);
v___x_2910_ = v_impl_2893_;
v_isShared_2911_ = v_isSharedCheck_2972_;
goto v_resetjp_2909_;
}
else
{
lean_dec(v_impl_2893_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2972_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v_size_2912_; lean_object* v_k_2913_; lean_object* v_v_2914_; lean_object* v_l_2915_; lean_object* v_r_2916_; lean_object* v_size_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v_size_2912_ = lean_ctor_get(v_l_2899_, 0);
v_k_2913_ = lean_ctor_get(v_l_2899_, 1);
v_v_2914_ = lean_ctor_get(v_l_2899_, 2);
v_l_2915_ = lean_ctor_get(v_l_2899_, 3);
v_r_2916_ = lean_ctor_get(v_l_2899_, 4);
v_size_2917_ = lean_ctor_get(v_r_2900_, 0);
v___x_2918_ = lean_unsigned_to_nat(2u);
v___x_2919_ = lean_nat_mul(v___x_2918_, v_size_2917_);
v___x_2920_ = lean_nat_dec_lt(v_size_2912_, v___x_2919_);
lean_dec(v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2948_; 
lean_inc(v_r_2916_);
lean_inc(v_l_2915_);
lean_inc(v_v_2914_);
lean_inc(v_k_2913_);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_l_2899_);
if (v_isSharedCheck_2948_ == 0)
{
lean_object* v_unused_2949_; lean_object* v_unused_2950_; lean_object* v_unused_2951_; lean_object* v_unused_2952_; lean_object* v_unused_2953_; 
v_unused_2949_ = lean_ctor_get(v_l_2899_, 4);
lean_dec(v_unused_2949_);
v_unused_2950_ = lean_ctor_get(v_l_2899_, 3);
lean_dec(v_unused_2950_);
v_unused_2951_ = lean_ctor_get(v_l_2899_, 2);
lean_dec(v_unused_2951_);
v_unused_2952_ = lean_ctor_get(v_l_2899_, 1);
lean_dec(v_unused_2952_);
v_unused_2953_ = lean_ctor_get(v_l_2899_, 0);
lean_dec(v_unused_2953_);
v___x_2922_ = v_l_2899_;
v_isShared_2923_ = v_isSharedCheck_2948_;
goto v_resetjp_2921_;
}
else
{
lean_dec(v_l_2899_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2948_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2938_; 
v___x_2924_ = lean_nat_add(v___x_2894_, v_size_2895_);
v___x_2925_ = lean_nat_add(v___x_2924_, v_size_2896_);
lean_dec(v_size_2896_);
if (lean_obj_tag(v_l_2915_) == 0)
{
lean_object* v_size_2946_; 
v_size_2946_ = lean_ctor_get(v_l_2915_, 0);
lean_inc(v_size_2946_);
v___y_2938_ = v_size_2946_;
goto v___jp_2937_;
}
else
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_unsigned_to_nat(0u);
v___y_2938_ = v___x_2947_;
goto v___jp_2937_;
}
v___jp_2926_:
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2930_ = lean_nat_add(v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec(v___y_2928_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 4, v_r_2900_);
lean_ctor_set(v___x_2922_, 3, v_r_2916_);
lean_ctor_set(v___x_2922_, 2, v_v_2898_);
lean_ctor_set(v___x_2922_, 1, v_k_2897_);
lean_ctor_set(v___x_2922_, 0, v___x_2930_);
v___x_2932_ = v___x_2922_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_k_2897_);
lean_ctor_set(v_reuseFailAlloc_2936_, 2, v_v_2898_);
lean_ctor_set(v_reuseFailAlloc_2936_, 3, v_r_2916_);
lean_ctor_set(v_reuseFailAlloc_2936_, 4, v_r_2900_);
v___x_2932_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2934_; 
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 4, v___x_2932_);
lean_ctor_set(v___x_2910_, 3, v___y_2927_);
lean_ctor_set(v___x_2910_, 2, v_v_2914_);
lean_ctor_set(v___x_2910_, 1, v_k_2913_);
lean_ctor_set(v___x_2910_, 0, v___x_2925_);
v___x_2934_ = v___x_2910_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2925_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_k_2913_);
lean_ctor_set(v_reuseFailAlloc_2935_, 2, v_v_2914_);
lean_ctor_set(v_reuseFailAlloc_2935_, 3, v___y_2927_);
lean_ctor_set(v_reuseFailAlloc_2935_, 4, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
v___jp_2937_:
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
v___x_2939_ = lean_nat_add(v___x_2924_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec(v___x_2924_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 4, v_l_2915_);
lean_ctor_set(v___x_2749_, 0, v___x_2939_);
v___x_2941_ = v___x_2749_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_k_2744_);
lean_ctor_set(v_reuseFailAlloc_2945_, 2, v_v_2745_);
lean_ctor_set(v_reuseFailAlloc_2945_, 3, v_l_2746_);
lean_ctor_set(v_reuseFailAlloc_2945_, 4, v_l_2915_);
v___x_2941_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_nat_add(v___x_2894_, v_size_2917_);
if (lean_obj_tag(v_r_2916_) == 0)
{
lean_object* v_size_2943_; 
v_size_2943_ = lean_ctor_get(v_r_2916_, 0);
lean_inc(v_size_2943_);
v___y_2927_ = v___x_2941_;
v___y_2928_ = v___x_2942_;
v___y_2929_ = v_size_2943_;
goto v___jp_2926_;
}
else
{
lean_object* v___x_2944_; 
v___x_2944_ = lean_unsigned_to_nat(0u);
v___y_2927_ = v___x_2941_;
v___y_2928_ = v___x_2942_;
v___y_2929_ = v___x_2944_;
goto v___jp_2926_;
}
}
}
}
}
else
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
lean_del_object(v___x_2749_);
v___x_2954_ = lean_nat_add(v___x_2894_, v_size_2895_);
v___x_2955_ = lean_nat_add(v___x_2954_, v_size_2896_);
lean_dec(v_size_2896_);
v___x_2956_ = lean_nat_add(v___x_2954_, v_size_2912_);
lean_dec(v___x_2954_);
lean_inc_ref(v_l_2746_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 4, v_l_2899_);
lean_ctor_set(v___x_2910_, 3, v_l_2746_);
lean_ctor_set(v___x_2910_, 2, v_v_2745_);
lean_ctor_set(v___x_2910_, 1, v_k_2744_);
lean_ctor_set(v___x_2910_, 0, v___x_2956_);
v___x_2958_ = v___x_2910_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2956_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_k_2744_);
lean_ctor_set(v_reuseFailAlloc_2971_, 2, v_v_2745_);
lean_ctor_set(v_reuseFailAlloc_2971_, 3, v_l_2746_);
lean_ctor_set(v_reuseFailAlloc_2971_, 4, v_l_2899_);
v___x_2958_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
v_isSharedCheck_2965_ = !lean_is_exclusive(v_l_2746_);
if (v_isSharedCheck_2965_ == 0)
{
lean_object* v_unused_2966_; lean_object* v_unused_2967_; lean_object* v_unused_2968_; lean_object* v_unused_2969_; lean_object* v_unused_2970_; 
v_unused_2966_ = lean_ctor_get(v_l_2746_, 4);
lean_dec(v_unused_2966_);
v_unused_2967_ = lean_ctor_get(v_l_2746_, 3);
lean_dec(v_unused_2967_);
v_unused_2968_ = lean_ctor_get(v_l_2746_, 2);
lean_dec(v_unused_2968_);
v_unused_2969_ = lean_ctor_get(v_l_2746_, 1);
lean_dec(v_unused_2969_);
v_unused_2970_ = lean_ctor_get(v_l_2746_, 0);
lean_dec(v_unused_2970_);
v___x_2960_ = v_l_2746_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_dec(v_l_2746_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 4, v_r_2900_);
lean_ctor_set(v___x_2960_, 3, v___x_2958_);
lean_ctor_set(v___x_2960_, 2, v_v_2898_);
lean_ctor_set(v___x_2960_, 1, v_k_2897_);
lean_ctor_set(v___x_2960_, 0, v___x_2955_);
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_k_2897_);
lean_ctor_set(v_reuseFailAlloc_2964_, 2, v_v_2898_);
lean_ctor_set(v_reuseFailAlloc_2964_, 3, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_2964_, 4, v_r_2900_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2978_; 
v_l_2978_ = lean_ctor_get(v_impl_2893_, 3);
lean_inc(v_l_2978_);
if (lean_obj_tag(v_l_2978_) == 0)
{
lean_object* v_r_2979_; lean_object* v_k_2980_; lean_object* v_v_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3004_; 
v_r_2979_ = lean_ctor_get(v_impl_2893_, 4);
v_k_2980_ = lean_ctor_get(v_impl_2893_, 1);
v_v_2981_ = lean_ctor_get(v_impl_2893_, 2);
v_isSharedCheck_3004_ = !lean_is_exclusive(v_impl_2893_);
if (v_isSharedCheck_3004_ == 0)
{
lean_object* v_unused_3005_; lean_object* v_unused_3006_; 
v_unused_3005_ = lean_ctor_get(v_impl_2893_, 3);
lean_dec(v_unused_3005_);
v_unused_3006_ = lean_ctor_get(v_impl_2893_, 0);
lean_dec(v_unused_3006_);
v___x_2983_ = v_impl_2893_;
v_isShared_2984_ = v_isSharedCheck_3004_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_r_2979_);
lean_inc(v_v_2981_);
lean_inc(v_k_2980_);
lean_dec(v_impl_2893_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3004_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v_k_2985_; lean_object* v_v_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3000_; 
v_k_2985_ = lean_ctor_get(v_l_2978_, 1);
v_v_2986_ = lean_ctor_get(v_l_2978_, 2);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_l_2978_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; lean_object* v_unused_3002_; lean_object* v_unused_3003_; 
v_unused_3001_ = lean_ctor_get(v_l_2978_, 4);
lean_dec(v_unused_3001_);
v_unused_3002_ = lean_ctor_get(v_l_2978_, 3);
lean_dec(v_unused_3002_);
v_unused_3003_ = lean_ctor_get(v_l_2978_, 0);
lean_dec(v_unused_3003_);
v___x_2988_ = v_l_2978_;
v_isShared_2989_ = v_isSharedCheck_3000_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_v_2986_);
lean_inc(v_k_2985_);
lean_dec(v_l_2978_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3000_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; lean_object* v___x_2992_; 
v___x_2990_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2979_, 2);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 4, v_r_2979_);
lean_ctor_set(v___x_2988_, 3, v_r_2979_);
lean_ctor_set(v___x_2988_, 2, v_v_2745_);
lean_ctor_set(v___x_2988_, 1, v_k_2744_);
lean_ctor_set(v___x_2988_, 0, v___x_2894_);
v___x_2992_ = v___x_2988_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_k_2744_);
lean_ctor_set(v_reuseFailAlloc_2999_, 2, v_v_2745_);
lean_ctor_set(v_reuseFailAlloc_2999_, 3, v_r_2979_);
lean_ctor_set(v_reuseFailAlloc_2999_, 4, v_r_2979_);
v___x_2992_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2994_; 
lean_inc(v_r_2979_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 3, v_r_2979_);
lean_ctor_set(v___x_2983_, 0, v___x_2894_);
v___x_2994_ = v___x_2983_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_k_2980_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v_v_2981_);
lean_ctor_set(v_reuseFailAlloc_2998_, 3, v_r_2979_);
lean_ctor_set(v_reuseFailAlloc_2998_, 4, v_r_2979_);
v___x_2994_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2996_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 4, v___x_2994_);
lean_ctor_set(v___x_2749_, 3, v___x_2992_);
lean_ctor_set(v___x_2749_, 2, v_v_2986_);
lean_ctor_set(v___x_2749_, 1, v_k_2985_);
lean_ctor_set(v___x_2749_, 0, v___x_2990_);
v___x_2996_ = v___x_2749_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2990_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v_k_2985_);
lean_ctor_set(v_reuseFailAlloc_2997_, 2, v_v_2986_);
lean_ctor_set(v_reuseFailAlloc_2997_, 3, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_2997_, 4, v___x_2994_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
}
}
else
{
lean_object* v_r_3007_; 
v_r_3007_ = lean_ctor_get(v_impl_2893_, 4);
lean_inc(v_r_3007_);
if (lean_obj_tag(v_r_3007_) == 0)
{
lean_object* v_k_3008_; lean_object* v_v_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3020_; 
v_k_3008_ = lean_ctor_get(v_impl_2893_, 1);
v_v_3009_ = lean_ctor_get(v_impl_2893_, 2);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_impl_2893_);
if (v_isSharedCheck_3020_ == 0)
{
lean_object* v_unused_3021_; lean_object* v_unused_3022_; lean_object* v_unused_3023_; 
v_unused_3021_ = lean_ctor_get(v_impl_2893_, 4);
lean_dec(v_unused_3021_);
v_unused_3022_ = lean_ctor_get(v_impl_2893_, 3);
lean_dec(v_unused_3022_);
v_unused_3023_ = lean_ctor_get(v_impl_2893_, 0);
lean_dec(v_unused_3023_);
v___x_3011_ = v_impl_2893_;
v_isShared_3012_ = v_isSharedCheck_3020_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_v_3009_);
lean_inc(v_k_3008_);
lean_dec(v_impl_2893_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3020_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3015_; 
v___x_3013_ = lean_unsigned_to_nat(3u);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 4, v_l_2978_);
lean_ctor_set(v___x_3011_, 2, v_v_2745_);
lean_ctor_set(v___x_3011_, 1, v_k_2744_);
lean_ctor_set(v___x_3011_, 0, v___x_2894_);
v___x_3015_ = v___x_3011_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_k_2744_);
lean_ctor_set(v_reuseFailAlloc_3019_, 2, v_v_2745_);
lean_ctor_set(v_reuseFailAlloc_3019_, 3, v_l_2978_);
lean_ctor_set(v_reuseFailAlloc_3019_, 4, v_l_2978_);
v___x_3015_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3017_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 4, v_r_3007_);
lean_ctor_set(v___x_2749_, 3, v___x_3015_);
lean_ctor_set(v___x_2749_, 2, v_v_3009_);
lean_ctor_set(v___x_2749_, 1, v_k_3008_);
lean_ctor_set(v___x_2749_, 0, v___x_3013_);
v___x_3017_ = v___x_2749_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_k_3008_);
lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_v_3009_);
lean_ctor_set(v_reuseFailAlloc_3018_, 3, v___x_3015_);
lean_ctor_set(v_reuseFailAlloc_3018_, 4, v_r_3007_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
else
{
lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3024_ = lean_unsigned_to_nat(2u);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 4, v_impl_2893_);
lean_ctor_set(v___x_2749_, 3, v_r_3007_);
lean_ctor_set(v___x_2749_, 0, v___x_3024_);
v___x_3026_ = v___x_2749_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_k_2744_);
lean_ctor_set(v_reuseFailAlloc_3027_, 2, v_v_2745_);
lean_ctor_set(v_reuseFailAlloc_3027_, 3, v_r_3007_);
lean_ctor_set(v_reuseFailAlloc_3027_, 4, v_impl_2893_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
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
lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_dec_ref(v_cmp_2739_);
v___x_3029_ = lean_unsigned_to_nat(1u);
v___x_3030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
lean_ctor_set(v___x_3030_, 1, v_k_2740_);
lean_ctor_set(v___x_3030_, 2, v_v_2741_);
lean_ctor_set(v___x_3030_, 3, v_t_2742_);
lean_ctor_set(v___x_3030_, 4, v_t_2742_);
return v___x_3030_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(lean_object* v_cmp_3031_, lean_object* v_init_3032_, lean_object* v_x_3033_){
_start:
{
if (lean_obj_tag(v_x_3033_) == 0)
{
lean_object* v_k_3034_; lean_object* v_v_3035_; lean_object* v_l_3036_; lean_object* v_r_3037_; lean_object* v___x_3038_; 
v_k_3034_ = lean_ctor_get(v_x_3033_, 1);
lean_inc(v_k_3034_);
v_v_3035_ = lean_ctor_get(v_x_3033_, 2);
lean_inc(v_v_3035_);
v_l_3036_ = lean_ctor_get(v_x_3033_, 3);
lean_inc(v_l_3036_);
v_r_3037_ = lean_ctor_get(v_x_3033_, 4);
lean_inc(v_r_3037_);
lean_dec_ref_known(v_x_3033_, 5);
lean_inc_ref(v_cmp_3031_);
v___x_3038_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_3031_, v_init_3032_, v_l_3036_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_dec(v_r_3037_);
lean_dec(v_v_3035_);
lean_dec(v_k_3034_);
lean_dec_ref(v_cmp_3031_);
return v___x_3038_;
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3040_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
v___x_3040_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_v_3035_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec(v_a_3039_);
lean_dec(v_r_3037_);
lean_dec(v_k_3034_);
lean_dec_ref(v_cmp_3031_);
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3050_; 
v_a_3049_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3040_, 1);
lean_inc_ref(v_cmp_3031_);
v___x_3050_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3031_, v_k_3034_, v_a_3049_, v_a_3039_);
v_init_3032_ = v___x_3050_;
v_x_3033_ = v_r_3037_;
goto _start;
}
}
}
else
{
lean_object* v___x_3052_; 
lean_dec_ref(v_cmp_3031_);
v___x_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3052_, 0, v_init_3032_);
return v___x_3052_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(lean_object* v_cmp_3053_, lean_object* v_j_3054_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l_Lean_Json_getObj_x3f(v_j_3054_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec_ref(v_cmp_3053_);
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3055_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3055_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v_a_3064_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3064_);
lean_dec_ref_known(v___x_3055_, 1);
v___x_3065_ = lean_box(1);
v___x_3066_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_3053_, v___x_3065_, v_a_3064_);
return v___x_3066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(lean_object* v_x_3070_){
_start:
{
if (lean_obj_tag(v_x_3070_) == 0)
{
lean_object* v___x_3071_; 
v___x_3071_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__0));
return v___x_3071_;
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__1));
v___x_3073_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(v___x_3072_, v_x_3070_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3073_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3073_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3090_; 
v_a_3082_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3084_ = v___x_3073_;
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3073_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3086_, 0, v_a_3082_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v___x_3086_);
v___x_3088_ = v___x_3084_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(lean_object* v_j_3091_, lean_object* v_k_3092_){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = l_Lean_Json_getObjValD(v_j_3091_, v_k_3092_);
v___x_3094_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(v___x_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4___boxed(lean_object* v_j_3095_, lean_object* v_k_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_j_3095_, v_k_3096_);
lean_dec_ref(v_k_3096_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(lean_object* v_j_3098_, lean_object* v_k_3099_){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = l_Lean_Json_getObjValD(v_j_3098_, v_k_3099_);
v___x_3101_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v___x_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1___boxed(lean_object* v_j_3102_, lean_object* v_k_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_j_3102_, v_k_3103_);
lean_dec_ref(v_k_3103_);
return v_res_3104_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3113_ = 1;
v___x_3114_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__4));
v___x_3115_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3114_, v___x_3113_);
return v___x_3115_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3117_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__6));
v___x_3118_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__5, &l_Lake_Check_instFromJsonConfig_fromJson___closed__5_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5);
v___x_3119_ = lean_string_append(v___x_3118_, v___x_3117_);
return v___x_3119_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3122_ = 1;
v___x_3123_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__8));
v___x_3124_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3123_, v___x_3122_);
return v___x_3124_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3125_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__9, &l_Lake_Check_instFromJsonConfig_fromJson___closed__9_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9);
v___x_3126_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3127_ = lean_string_append(v___x_3126_, v___x_3125_);
return v___x_3127_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3129_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3130_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__10, &l_Lake_Check_instFromJsonConfig_fromJson___closed__10_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10);
v___x_3131_ = lean_string_append(v___x_3130_, v___x_3129_);
return v___x_3131_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15(void){
_start:
{
uint8_t v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = 1;
v___x_3136_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__14));
v___x_3137_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3136_, v___x_3135_);
return v___x_3137_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3138_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__15, &l_Lake_Check_instFromJsonConfig_fromJson___closed__15_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15);
v___x_3139_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3140_ = lean_string_append(v___x_3139_, v___x_3138_);
return v___x_3140_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3142_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__16, &l_Lake_Check_instFromJsonConfig_fromJson___closed__16_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16);
v___x_3143_ = lean_string_append(v___x_3142_, v___x_3141_);
return v___x_3143_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20(void){
_start:
{
uint8_t v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3147_ = 1;
v___x_3148_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__19));
v___x_3149_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3148_, v___x_3147_);
return v___x_3149_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21(void){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3150_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__20, &l_Lake_Check_instFromJsonConfig_fromJson___closed__20_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20);
v___x_3151_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3152_ = lean_string_append(v___x_3151_, v___x_3150_);
return v___x_3152_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22(void){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3153_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3154_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__21, &l_Lake_Check_instFromJsonConfig_fromJson___closed__21_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21);
v___x_3155_ = lean_string_append(v___x_3154_, v___x_3153_);
return v___x_3155_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25(void){
_start:
{
uint8_t v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = 1;
v___x_3160_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__24));
v___x_3161_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3160_, v___x_3159_);
return v___x_3161_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__25, &l_Lake_Check_instFromJsonConfig_fromJson___closed__25_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25);
v___x_3163_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3164_ = lean_string_append(v___x_3163_, v___x_3162_);
return v___x_3164_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3166_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__26, &l_Lake_Check_instFromJsonConfig_fromJson___closed__26_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26);
v___x_3167_ = lean_string_append(v___x_3166_, v___x_3165_);
return v___x_3167_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29(void){
_start:
{
uint8_t v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3170_ = 1;
v___x_3171_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__28));
v___x_3172_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3171_, v___x_3170_);
return v___x_3172_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30(void){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__29, &l_Lake_Check_instFromJsonConfig_fromJson___closed__29_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29);
v___x_3174_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3175_ = lean_string_append(v___x_3174_, v___x_3173_);
return v___x_3175_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3176_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3177_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__30, &l_Lake_Check_instFromJsonConfig_fromJson___closed__30_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30);
v___x_3178_ = lean_string_append(v___x_3177_, v___x_3176_);
return v___x_3178_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35(void){
_start:
{
uint8_t v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = 1;
v___x_3184_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__34));
v___x_3185_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3184_, v___x_3183_);
return v___x_3185_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__35, &l_Lake_Check_instFromJsonConfig_fromJson___closed__35_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35);
v___x_3187_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3188_ = lean_string_append(v___x_3187_, v___x_3186_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3190_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__36, &l_Lake_Check_instFromJsonConfig_fromJson___closed__36_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36);
v___x_3191_ = lean_string_append(v___x_3190_, v___x_3189_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41(void){
_start:
{
uint8_t v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3196_ = 1;
v___x_3197_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__40));
v___x_3198_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3197_, v___x_3196_);
return v___x_3198_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42(void){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3199_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__41, &l_Lake_Check_instFromJsonConfig_fromJson___closed__41_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41);
v___x_3200_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3201_ = lean_string_append(v___x_3200_, v___x_3199_);
return v___x_3201_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3202_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3203_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__42, &l_Lake_Check_instFromJsonConfig_fromJson___closed__42_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42);
v___x_3204_ = lean_string_append(v___x_3203_, v___x_3202_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instFromJsonConfig_fromJson(lean_object* v_json_3205_){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
lean_inc(v_json_3205_);
v___x_3207_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_3205_, v___x_3206_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v_json_3205_);
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3210_ = v___x_3207_;
v_isShared_3211_ = v_isSharedCheck_3217_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3217_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3215_; 
v___x_3212_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__12, &l_Lake_Check_instFromJsonConfig_fromJson___closed__12_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12);
v___x_3213_ = lean_string_append(v___x_3212_, v_a_3208_);
lean_dec(v_a_3208_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3213_);
v___x_3215_ = v___x_3210_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
else
{
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec(v_json_3205_);
v_a_3218_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3207_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3207_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
lean_ctor_set_tag(v___x_3220_, 0);
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v_a_3226_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3207_, 1);
v___x_3227_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
lean_inc(v_json_3205_);
v___x_3228_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_3205_, v___x_3227_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3238_; 
lean_dec(v_a_3226_);
lean_dec(v_json_3205_);
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3231_ = v___x_3228_;
v_isShared_3232_ = v_isSharedCheck_3238_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3228_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3238_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3233_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__17, &l_Lake_Check_instFromJsonConfig_fromJson___closed__17_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17);
v___x_3234_ = lean_string_append(v___x_3233_, v_a_3229_);
lean_dec(v_a_3229_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v___x_3234_);
v___x_3236_ = v___x_3231_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
else
{
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_dec(v_a_3226_);
lean_dec(v_json_3205_);
v_a_3239_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3228_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3228_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
lean_ctor_set_tag(v___x_3241_, 0);
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v_a_3247_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3228_, 1);
v___x_3248_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
lean_inc(v_json_3205_);
v___x_3249_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_3205_, v___x_3248_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3259_; 
lean_dec(v_a_3247_);
lean_dec(v_a_3226_);
lean_dec(v_json_3205_);
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3252_ = v___x_3249_;
v_isShared_3253_ = v_isSharedCheck_3259_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3259_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3254_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__22, &l_Lake_Check_instFromJsonConfig_fromJson___closed__22_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22);
v___x_3255_ = lean_string_append(v___x_3254_, v_a_3250_);
lean_dec(v_a_3250_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3255_);
v___x_3257_ = v___x_3252_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
else
{
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec(v_a_3247_);
lean_dec(v_a_3226_);
lean_dec(v_json_3205_);
v_a_3260_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3249_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3249_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
lean_ctor_set_tag(v___x_3262_, 0);
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v_a_3268_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3268_);
lean_dec_ref_known(v___x_3249_, 1);
v___x_3269_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
lean_inc(v_json_3205_);
v___x_3270_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_json_3205_, v___x_3269_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3280_; 
lean_dec(v_a_3268_);
lean_dec(v_a_3247_);
lean_dec(v_a_3226_);
lean_dec(v_json_3205_);
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3280_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3280_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3275_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__27, &l_Lake_Check_instFromJsonConfig_fromJson___closed__27_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27);
v___x_3276_ = lean_string_append(v___x_3275_, v_a_3271_);
lean_dec(v_a_3271_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3276_);
v___x_3278_ = v___x_3273_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
else
{
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec(v_a_3268_);
lean_dec(v_a_3247_);
lean_dec(v_a_3226_);
lean_dec(v_json_3205_);
v_a_3281_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3270_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3270_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
lean_ctor_set_tag(v___x_3283_, 0);
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_a_3289_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3289_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3290_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12));
lean_inc(v_json_3205_);
v___x_3291_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_3205_, v___x_3290_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3301_; 
lean_dec(v_a_3289_);
lean_dec(v_a_3268_);
lean_dec(v_a_3247_);
lean_dec(v_a_3226_);
lean_dec(v_json_3205_);
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3294_ = v___x_3291_;
v_isShared_3295_ = v_isSharedCheck_3301_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3291_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3301_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3296_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__31, &l_Lake_Check_instFromJsonConfig_fromJson___closed__31_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31);
v___x_3297_ = lean_string_append(v___x_3296_, v_a_3292_);
lean_dec(v_a_3292_);
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 0, v___x_3297_);
v___x_3299_ = v___x_3294_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
else
{
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec(v_a_3289_);
lean_dec(v_a_3268_);
lean_dec(v_a_3247_);
lean_dec(v_a_3226_);
lean_dec(v_json_3205_);
v_a_3302_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3291_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3291_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
lean_ctor_set_tag(v___x_3304_, 0);
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_a_3310_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3310_);
lean_dec_ref_known(v___x_3291_, 1);
v___x_3311_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
lean_inc(v_json_3205_);
v___x_3312_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_json_3205_, v___x_3311_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3322_; 
lean_dec(v_a_3310_);
lean_dec(v_a_3289_);
lean_dec(v_a_3268_);
lean_dec(v_a_3247_);
lean_dec(v_a_3226_);
lean_dec(v_json_3205_);
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3315_ = v___x_3312_;
v_isShared_3316_ = v_isSharedCheck_3322_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3312_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3322_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3317_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__37, &l_Lake_Check_instFromJsonConfig_fromJson___closed__37_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37);
v___x_3318_ = lean_string_append(v___x_3317_, v_a_3313_);
lean_dec(v_a_3313_);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 0, v___x_3318_);
v___x_3320_ = v___x_3315_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
else
{
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec(v_a_3310_);
lean_dec(v_a_3289_);
lean_dec(v_a_3268_);
lean_dec(v_a_3247_);
lean_dec(v_a_3226_);
lean_dec(v_json_3205_);
v_a_3323_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3312_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3312_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
lean_ctor_set_tag(v___x_3325_, 0);
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_a_3331_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v___x_3312_, 1);
v___x_3332_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_3333_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_json_3205_, v___x_3332_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3343_; 
lean_dec(v_a_3331_);
lean_dec(v_a_3310_);
lean_dec(v_a_3289_);
lean_dec(v_a_3268_);
lean_dec(v_a_3247_);
lean_dec(v_a_3226_);
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3343_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3343_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3341_; 
v___x_3338_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__43, &l_Lake_Check_instFromJsonConfig_fromJson___closed__43_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43);
v___x_3339_ = lean_string_append(v___x_3338_, v_a_3334_);
lean_dec(v_a_3334_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3339_);
v___x_3341_ = v___x_3336_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3339_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
else
{
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_dec(v_a_3331_);
lean_dec(v_a_3310_);
lean_dec(v_a_3289_);
lean_dec(v_a_3268_);
lean_dec(v_a_3247_);
lean_dec(v_a_3226_);
v_a_3344_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3333_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3333_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
lean_ctor_set_tag(v___x_3346_, 0);
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
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
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3360_; 
v_a_3352_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3354_ = v___x_3333_;
v_isShared_3355_ = v_isSharedCheck_3360_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3333_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3360_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3356_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3356_, 0, v_a_3226_);
lean_ctor_set(v___x_3356_, 1, v_a_3247_);
lean_ctor_set(v___x_3356_, 2, v_a_3268_);
lean_ctor_set(v___x_3356_, 3, v_a_3289_);
lean_ctor_set(v___x_3356_, 4, v_a_3310_);
lean_ctor_set(v___x_3356_, 5, v_a_3331_);
lean_ctor_set(v___x_3356_, 6, v_a_3352_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___x_3356_);
v___x_3358_ = v___x_3354_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10(lean_object* v_cmp_3361_, lean_object* v_00_u03b2_3362_, lean_object* v_k_3363_, lean_object* v_v_3364_, lean_object* v_t_3365_, lean_object* v_hl_3366_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3361_, v_k_3363_, v_v_3364_, v_t_3365_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(lean_object* v_k_3370_, lean_object* v_x_3371_){
_start:
{
if (lean_obj_tag(v_x_3371_) == 0)
{
lean_object* v___x_3372_; 
lean_dec_ref(v_k_3370_);
v___x_3372_ = lean_box(0);
return v___x_3372_;
}
else
{
lean_object* v_val_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_val_3373_ = lean_ctor_get(v_x_3371_, 0);
v___x_3374_ = lean_alloc_ctor(1, 0, 1);
v___x_3375_ = lean_unbox(v_val_3373_);
lean_ctor_set_uint8(v___x_3374_, 0, v___x_3375_);
v___x_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3376_, 0, v_k_3370_);
lean_ctor_set(v___x_3376_, 1, v___x_3374_);
v___x_3377_ = lean_box(0);
v___x_3378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3376_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2___boxed(lean_object* v_k_3379_, lean_object* v_x_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v_k_3379_, v_x_3380_);
lean_dec(v_x_3380_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(size_t v_sz_3382_, size_t v_i_3383_, lean_object* v_bs_3384_){
_start:
{
uint8_t v___x_3385_; 
v___x_3385_ = lean_usize_dec_lt(v_i_3383_, v_sz_3382_);
if (v___x_3385_ == 0)
{
return v_bs_3384_;
}
else
{
lean_object* v_v_3386_; lean_object* v___x_3387_; lean_object* v_bs_x27_3388_; lean_object* v___x_3389_; size_t v___x_3390_; size_t v___x_3391_; lean_object* v___x_3392_; 
v_v_3386_ = lean_array_uget(v_bs_3384_, v_i_3383_);
v___x_3387_ = lean_unsigned_to_nat(0u);
v_bs_x27_3388_ = lean_array_uset(v_bs_3384_, v_i_3383_, v___x_3387_);
v___x_3389_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3389_, 0, v_v_3386_);
v___x_3390_ = ((size_t)1ULL);
v___x_3391_ = lean_usize_add(v_i_3383_, v___x_3390_);
v___x_3392_ = lean_array_uset(v_bs_x27_3388_, v_i_3383_, v___x_3389_);
v_i_3383_ = v___x_3391_;
v_bs_3384_ = v___x_3392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3394_, lean_object* v_i_3395_, lean_object* v_bs_3396_){
_start:
{
size_t v_sz_boxed_3397_; size_t v_i_boxed_3398_; lean_object* v_res_3399_; 
v_sz_boxed_3397_ = lean_unbox_usize(v_sz_3394_);
lean_dec(v_sz_3394_);
v_i_boxed_3398_ = lean_unbox_usize(v_i_3395_);
lean_dec(v_i_3395_);
v_res_3399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_boxed_3397_, v_i_boxed_3398_, v_bs_3396_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(lean_object* v_a_3400_){
_start:
{
size_t v_sz_3401_; size_t v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v_sz_3401_ = lean_array_size(v_a_3400_);
v___x_3402_ = ((size_t)0ULL);
v___x_3403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_3401_, v___x_3402_, v_a_3400_);
v___x_3404_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(lean_object* v_x_3405_){
_start:
{
if (lean_obj_tag(v_x_3405_) == 0)
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_box(0);
return v___x_3406_;
}
else
{
lean_object* v_val_3407_; lean_object* v___x_3408_; 
v_val_3407_ = lean_ctor_get(v_x_3405_, 0);
lean_inc(v_val_3407_);
lean_dec_ref_known(v_x_3405_, 1);
v___x_3408_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_val_3407_);
return v___x_3408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(lean_object* v_a_3409_, lean_object* v_a_3410_){
_start:
{
if (lean_obj_tag(v_a_3409_) == 0)
{
lean_object* v___x_3411_; 
v___x_3411_ = lean_array_to_list(v_a_3410_);
return v___x_3411_;
}
else
{
lean_object* v_head_3412_; lean_object* v_tail_3413_; lean_object* v___x_3414_; 
v_head_3412_ = lean_ctor_get(v_a_3409_, 0);
lean_inc(v_head_3412_);
v_tail_3413_ = lean_ctor_get(v_a_3409_, 1);
lean_inc(v_tail_3413_);
lean_dec_ref_known(v_a_3409_, 2);
v___x_3414_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_3410_, v_head_3412_);
v_a_3409_ = v_tail_3413_;
v_a_3410_ = v___x_3414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(lean_object* v_t_3416_){
_start:
{
if (lean_obj_tag(v_t_3416_) == 0)
{
lean_object* v_size_3417_; lean_object* v_k_3418_; lean_object* v_v_3419_; lean_object* v_l_3420_; lean_object* v_r_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3431_; 
v_size_3417_ = lean_ctor_get(v_t_3416_, 0);
v_k_3418_ = lean_ctor_get(v_t_3416_, 1);
v_v_3419_ = lean_ctor_get(v_t_3416_, 2);
v_l_3420_ = lean_ctor_get(v_t_3416_, 3);
v_r_3421_ = lean_ctor_get(v_t_3416_, 4);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_t_3416_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3423_ = v_t_3416_;
v_isShared_3424_ = v_isSharedCheck_3431_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_r_3421_);
lean_inc(v_l_3420_);
lean_inc(v_v_3419_);
lean_inc(v_k_3418_);
lean_inc(v_size_3417_);
lean_dec(v_t_3416_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3431_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3425_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_v_3419_);
v___x_3426_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_l_3420_);
v___x_3427_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_r_3421_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 4, v___x_3427_);
lean_ctor_set(v___x_3423_, 3, v___x_3426_);
lean_ctor_set(v___x_3423_, 2, v___x_3425_);
v___x_3429_ = v___x_3423_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_size_3417_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v_k_3418_);
lean_ctor_set(v_reuseFailAlloc_3430_, 2, v___x_3425_);
lean_ctor_set(v_reuseFailAlloc_3430_, 3, v___x_3426_);
lean_ctor_set(v_reuseFailAlloc_3430_, 4, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
else
{
lean_object* v___x_3432_; 
v___x_3432_ = lean_box(1);
return v___x_3432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(lean_object* v_map_3433_){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_map_3433_);
v___x_3435_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(lean_object* v_k_3436_, lean_object* v_x_3437_){
_start:
{
if (lean_obj_tag(v_x_3437_) == 0)
{
lean_object* v___x_3438_; 
lean_dec_ref(v_k_3436_);
v___x_3438_ = lean_box(0);
return v___x_3438_;
}
else
{
lean_object* v_val_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v_val_3439_ = lean_ctor_get(v_x_3437_, 0);
lean_inc(v_val_3439_);
lean_dec_ref_known(v_x_3437_, 1);
v___x_3440_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(v_val_3439_);
v___x_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3441_, 0, v_k_3436_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
v___x_3442_ = lean_box(0);
v___x_3443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3441_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
return v___x_3443_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instToJsonConfig_toJson(lean_object* v_x_3446_){
_start:
{
lean_object* v_challenge__module_3447_; lean_object* v_solution__module_3448_; lean_object* v_theorem__names_3449_; lean_object* v_definition__names_3450_; lean_object* v_permitted__axioms_3451_; lean_object* v_enable__nanoda_x3f_3452_; lean_object* v_external__kernels_x3f_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v_challenge__module_3447_ = lean_ctor_get(v_x_3446_, 0);
lean_inc_ref(v_challenge__module_3447_);
v_solution__module_3448_ = lean_ctor_get(v_x_3446_, 1);
lean_inc_ref(v_solution__module_3448_);
v_theorem__names_3449_ = lean_ctor_get(v_x_3446_, 2);
lean_inc_ref(v_theorem__names_3449_);
v_definition__names_3450_ = lean_ctor_get(v_x_3446_, 3);
lean_inc(v_definition__names_3450_);
v_permitted__axioms_3451_ = lean_ctor_get(v_x_3446_, 4);
lean_inc_ref(v_permitted__axioms_3451_);
v_enable__nanoda_x3f_3452_ = lean_ctor_get(v_x_3446_, 5);
lean_inc(v_enable__nanoda_x3f_3452_);
v_external__kernels_x3f_3453_ = lean_ctor_get(v_x_3446_, 6);
lean_inc(v_external__kernels_x3f_3453_);
lean_dec_ref(v_x_3446_);
v___x_3454_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
v___x_3455_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3455_, 0, v_challenge__module_3447_);
v___x_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = lean_box(0);
v___x_3458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
v___x_3460_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3460_, 0, v_solution__module_3448_);
v___x_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3459_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
v___x_3462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3461_);
lean_ctor_set(v___x_3462_, 1, v___x_3457_);
v___x_3463_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
v___x_3464_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_theorem__names_3449_);
v___x_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3463_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
v___x_3466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
lean_ctor_set(v___x_3466_, 1, v___x_3457_);
v___x_3467_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
v___x_3468_ = l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(v_definition__names_3450_);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3467_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set(v___x_3470_, 1, v___x_3457_);
v___x_3471_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12));
v___x_3472_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_permitted__axioms_3451_);
v___x_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3471_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___x_3457_);
v___x_3475_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
v___x_3476_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v___x_3475_, v_enable__nanoda_x3f_3452_);
lean_dec(v_enable__nanoda_x3f_3452_);
v___x_3477_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_3478_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(v___x_3477_, v_external__kernels_x3f_3453_);
v___x_3479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
lean_ctor_set(v___x_3479_, 1, v___x_3457_);
v___x_3480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3476_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3474_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3470_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v___x_3483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3466_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3462_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
v___x_3485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3458_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = ((lean_object*)(l_Lake_Check_instToJsonConfig_toJson___closed__0));
v___x_3487_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(v___x_3485_, v___x_3486_);
v___x_3488_ = l_Lean_Json_mkObj(v___x_3487_);
lean_dec(v___x_3487_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(lean_object* v_x_3497_, lean_object* v_x_3498_){
_start:
{
if (lean_obj_tag(v_x_3497_) == 0)
{
lean_object* v___x_3499_; 
v___x_3499_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3499_;
}
else
{
lean_object* v_val_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v_val_3500_ = lean_ctor_get(v_x_3497_, 0);
v___x_3501_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3502_ = lean_unbox(v_val_3500_);
v___x_3503_ = l_Bool_repr___redArg(v___x_3502_);
v___x_3504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3501_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
v___x_3505_ = l_Repr_addAppParen(v___x_3504_, v_x_3498_);
return v___x_3505_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___boxed(lean_object* v_x_3506_, lean_object* v_x_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_x_3506_, v_x_3507_);
lean_dec(v_x_3507_);
lean_dec(v_x_3506_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_Check_instReprConfig_repr_spec__4(lean_object* v_a_3509_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = lean_nat_to_int(v_a_3509_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(lean_object* v_x_3511_, lean_object* v_x_3512_, lean_object* v_x_3513_){
_start:
{
if (lean_obj_tag(v_x_3513_) == 0)
{
lean_dec(v_x_3511_);
return v_x_3512_;
}
else
{
lean_object* v_head_3514_; lean_object* v_tail_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3526_; 
v_head_3514_ = lean_ctor_get(v_x_3513_, 0);
v_tail_3515_ = lean_ctor_get(v_x_3513_, 1);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_x_3513_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3517_ = v_x_3513_;
v_isShared_3518_ = v_isSharedCheck_3526_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_tail_3515_);
lean_inc(v_head_3514_);
lean_dec(v_x_3513_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3526_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
lean_inc(v_x_3511_);
if (v_isShared_3518_ == 0)
{
lean_ctor_set_tag(v___x_3517_, 5);
lean_ctor_set(v___x_3517_, 1, v_x_3511_);
lean_ctor_set(v___x_3517_, 0, v_x_3512_);
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_x_3512_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_x_3511_);
v___x_3520_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3521_ = l_String_quote(v_head_3514_);
v___x_3522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
v___x_3523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3520_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
v_x_3512_ = v___x_3523_;
v_x_3513_ = v_tail_3515_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_3527_, lean_object* v_x_3528_, lean_object* v_x_3529_){
_start:
{
if (lean_obj_tag(v_x_3529_) == 0)
{
lean_dec(v_x_3527_);
return v_x_3528_;
}
else
{
lean_object* v_head_3530_; lean_object* v_tail_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3542_; 
v_head_3530_ = lean_ctor_get(v_x_3529_, 0);
v_tail_3531_ = lean_ctor_get(v_x_3529_, 1);
v_isSharedCheck_3542_ = !lean_is_exclusive(v_x_3529_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3533_ = v_x_3529_;
v_isShared_3534_ = v_isSharedCheck_3542_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_tail_3531_);
lean_inc(v_head_3530_);
lean_dec(v_x_3529_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3542_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
lean_inc(v_x_3527_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set_tag(v___x_3533_, 5);
lean_ctor_set(v___x_3533_, 1, v_x_3527_);
lean_ctor_set(v___x_3533_, 0, v_x_3528_);
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_x_3528_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_x_3527_);
v___x_3536_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3537_ = l_String_quote(v_head_3530_);
v___x_3538_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
v___x_3539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3536_);
lean_ctor_set(v___x_3539_, 1, v___x_3538_);
v___x_3540_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(v_x_3527_, v___x_3539_, v_tail_3531_);
return v___x_3540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = l_String_quote(v___y_3543_);
v___x_3545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(lean_object* v_x_3546_, lean_object* v_x_3547_){
_start:
{
if (lean_obj_tag(v_x_3546_) == 0)
{
lean_object* v___x_3548_; 
lean_dec(v_x_3547_);
v___x_3548_ = lean_box(0);
return v___x_3548_;
}
else
{
lean_object* v_tail_3549_; 
v_tail_3549_ = lean_ctor_get(v_x_3546_, 1);
if (lean_obj_tag(v_tail_3549_) == 0)
{
lean_object* v_head_3550_; lean_object* v___x_3551_; 
lean_dec(v_x_3547_);
v_head_3550_ = lean_ctor_get(v_x_3546_, 0);
lean_inc(v_head_3550_);
lean_dec_ref_known(v_x_3546_, 2);
v___x_3551_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3550_);
return v___x_3551_;
}
else
{
lean_object* v_head_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
lean_inc(v_tail_3549_);
v_head_3552_ = lean_ctor_get(v_x_3546_, 0);
lean_inc(v_head_3552_);
lean_dec_ref_known(v_x_3546_, 2);
v___x_3553_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3552_);
v___x_3554_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(v_x_3547_, v___x_3553_, v_tail_3549_);
return v___x_3554_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__0));
v___x_3563_ = lean_string_length(v___x_3562_);
return v___x_3563_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4);
v___x_3565_ = lean_nat_to_int(v___x_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(lean_object* v_xs_3573_){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3574_ = lean_array_get_size(v_xs_3573_);
v___x_3575_ = lean_unsigned_to_nat(0u);
v___x_3576_ = lean_nat_dec_eq(v___x_3574_, v___x_3575_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3577_ = lean_array_to_list(v_xs_3573_);
v___x_3578_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3579_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(v___x_3577_, v___x_3578_);
v___x_3580_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5);
v___x_3581_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__6));
v___x_3582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
lean_ctor_set(v___x_3582_, 1, v___x_3579_);
v___x_3583_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_3584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3580_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = l_Std_Format_fill(v___x_3585_);
return v___x_3586_;
}
else
{
lean_object* v___x_3587_; 
lean_dec_ref(v_xs_3573_);
v___x_3587_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__9));
return v___x_3587_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(lean_object* v_x_3588_, lean_object* v_x_3589_){
_start:
{
if (lean_obj_tag(v_x_3588_) == 0)
{
lean_object* v___x_3590_; 
v___x_3590_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3590_;
}
else
{
lean_object* v_val_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_val_3591_ = lean_ctor_get(v_x_3588_, 0);
lean_inc(v_val_3591_);
lean_dec_ref_known(v_x_3588_, 1);
v___x_3592_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3593_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_val_3591_);
v___x_3594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3592_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
v___x_3595_ = l_Repr_addAppParen(v___x_3594_, v_x_3589_);
return v___x_3595_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1___boxed(lean_object* v_x_3596_, lean_object* v_x_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_x_3596_, v_x_3597_);
lean_dec(v_x_3597_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(lean_object* v_init_3599_, lean_object* v_x_3600_){
_start:
{
if (lean_obj_tag(v_x_3600_) == 0)
{
lean_object* v_k_3601_; lean_object* v_v_3602_; lean_object* v_l_3603_; lean_object* v_r_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v_k_3601_ = lean_ctor_get(v_x_3600_, 1);
v_v_3602_ = lean_ctor_get(v_x_3600_, 2);
v_l_3603_ = lean_ctor_get(v_x_3600_, 3);
v_r_3604_ = lean_ctor_get(v_x_3600_, 4);
v___x_3605_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_3599_, v_r_3604_);
lean_inc(v_v_3602_);
lean_inc(v_k_3601_);
v___x_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3606_, 0, v_k_3601_);
lean_ctor_set(v___x_3606_, 1, v_v_3602_);
v___x_3607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
lean_ctor_set(v___x_3607_, 1, v___x_3605_);
v_init_3599_ = v___x_3607_;
v_x_3600_ = v_l_3603_;
goto _start;
}
else
{
return v_init_3599_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4___boxed(lean_object* v_init_3609_, lean_object* v_x_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_3609_, v_x_3610_);
lean_dec(v_x_3610_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(lean_object* v_x_3612_, lean_object* v_x_3613_, lean_object* v_x_3614_){
_start:
{
if (lean_obj_tag(v_x_3614_) == 0)
{
lean_dec(v_x_3612_);
return v_x_3613_;
}
else
{
lean_object* v_head_3615_; lean_object* v_tail_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3625_; 
v_head_3615_ = lean_ctor_get(v_x_3614_, 0);
v_tail_3616_ = lean_ctor_get(v_x_3614_, 1);
v_isSharedCheck_3625_ = !lean_is_exclusive(v_x_3614_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3618_ = v_x_3614_;
v_isShared_3619_ = v_isSharedCheck_3625_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_tail_3616_);
lean_inc(v_head_3615_);
lean_dec(v_x_3614_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3625_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
lean_inc(v_x_3612_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set_tag(v___x_3618_, 5);
lean_ctor_set(v___x_3618_, 1, v_x_3612_);
lean_ctor_set(v___x_3618_, 0, v_x_3613_);
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_x_3613_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_x_3612_);
v___x_3621_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3622_; 
v___x_3622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
lean_ctor_set(v___x_3622_, 1, v_head_3615_);
v_x_3613_ = v___x_3622_;
v_x_3614_ = v_tail_3616_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(lean_object* v_x_3626_, lean_object* v_x_3627_){
_start:
{
if (lean_obj_tag(v_x_3626_) == 0)
{
lean_object* v___x_3628_; 
lean_dec(v_x_3627_);
v___x_3628_ = lean_box(0);
return v___x_3628_;
}
else
{
lean_object* v_tail_3629_; 
v_tail_3629_ = lean_ctor_get(v_x_3626_, 1);
if (lean_obj_tag(v_tail_3629_) == 0)
{
lean_object* v_head_3630_; 
lean_dec(v_x_3627_);
v_head_3630_ = lean_ctor_get(v_x_3626_, 0);
lean_inc(v_head_3630_);
lean_dec_ref_known(v_x_3626_, 2);
return v_head_3630_;
}
else
{
lean_object* v_head_3631_; lean_object* v___x_3632_; 
lean_inc(v_tail_3629_);
v_head_3631_ = lean_ctor_get(v_x_3626_, 0);
lean_inc(v_head_3631_);
lean_dec_ref_known(v_x_3626_, 2);
v___x_3632_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(v_x_3627_, v_head_3631_, v_tail_3629_);
return v___x_3632_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__0));
v___x_3636_ = lean_string_length(v___x_3635_);
return v___x_3636_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2);
v___x_3638_ = lean_nat_to_int(v___x_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(lean_object* v_x_3643_){
_start:
{
lean_object* v_fst_3644_; lean_object* v_snd_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3668_; 
v_fst_3644_ = lean_ctor_get(v_x_3643_, 0);
v_snd_3645_ = lean_ctor_get(v_x_3643_, 1);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_x_3643_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3647_ = v_x_3643_;
v_isShared_3648_ = v_isSharedCheck_3668_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_snd_3645_);
lean_inc(v_fst_3644_);
lean_dec(v_x_3643_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3668_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3653_; 
v___x_3649_ = l_String_quote(v_fst_3644_);
v___x_3650_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
v___x_3651_ = lean_box(0);
if (v_isShared_3648_ == 0)
{
lean_ctor_set_tag(v___x_3647_, 1);
lean_ctor_set(v___x_3647_, 1, v___x_3651_);
lean_ctor_set(v___x_3647_, 0, v___x_3650_);
v___x_3653_ = v___x_3647_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3650_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; uint8_t v___x_3665_; lean_object* v___x_3666_; 
v___x_3654_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_snd_3645_);
v___x_3655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
lean_ctor_set(v___x_3655_, 1, v___x_3653_);
v___x_3656_ = l_List_reverse___redArg(v___x_3655_);
v___x_3657_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3658_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(v___x_3656_, v___x_3657_);
v___x_3659_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3);
v___x_3660_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__4));
v___x_3661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
lean_ctor_set(v___x_3661_, 1, v___x_3658_);
v___x_3662_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__5));
v___x_3663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3661_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3659_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = 0;
v___x_3666_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3666_, 0, v___x_3664_);
lean_ctor_set_uint8(v___x_3666_, sizeof(void*)*1, v___x_3665_);
return v___x_3666_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(lean_object* v_x_3669_, lean_object* v_x_3670_, lean_object* v_x_3671_){
_start:
{
if (lean_obj_tag(v_x_3671_) == 0)
{
lean_dec(v_x_3669_);
return v_x_3670_;
}
else
{
lean_object* v_head_3672_; lean_object* v_tail_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3683_; 
v_head_3672_ = lean_ctor_get(v_x_3671_, 0);
v_tail_3673_ = lean_ctor_get(v_x_3671_, 1);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_x_3671_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3675_ = v_x_3671_;
v_isShared_3676_ = v_isSharedCheck_3683_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_tail_3673_);
lean_inc(v_head_3672_);
lean_dec(v_x_3671_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3683_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
lean_inc(v_x_3669_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set_tag(v___x_3675_, 5);
lean_ctor_set(v___x_3675_, 1, v_x_3669_);
lean_ctor_set(v___x_3675_, 0, v_x_3670_);
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_x_3670_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_x_3669_);
v___x_3678_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3672_);
v___x_3680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3678_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
v_x_3670_ = v___x_3680_;
v_x_3671_ = v_tail_3673_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(lean_object* v_x_3684_, lean_object* v_x_3685_, lean_object* v_x_3686_){
_start:
{
if (lean_obj_tag(v_x_3686_) == 0)
{
lean_dec(v_x_3684_);
return v_x_3685_;
}
else
{
lean_object* v_head_3687_; lean_object* v_tail_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3698_; 
v_head_3687_ = lean_ctor_get(v_x_3686_, 0);
v_tail_3688_ = lean_ctor_get(v_x_3686_, 1);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_x_3686_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3690_ = v_x_3686_;
v_isShared_3691_ = v_isSharedCheck_3698_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_tail_3688_);
lean_inc(v_head_3687_);
lean_dec(v_x_3686_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3698_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
lean_inc(v_x_3684_);
if (v_isShared_3691_ == 0)
{
lean_ctor_set_tag(v___x_3690_, 5);
lean_ctor_set(v___x_3690_, 1, v_x_3684_);
lean_ctor_set(v___x_3690_, 0, v_x_3685_);
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_x_3685_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_x_3684_);
v___x_3693_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3694_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3687_);
v___x_3695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(v_x_3684_, v___x_3695_, v_tail_3688_);
return v___x_3696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(lean_object* v_x_3699_, lean_object* v_x_3700_){
_start:
{
if (lean_obj_tag(v_x_3699_) == 0)
{
lean_object* v___x_3701_; 
lean_dec(v_x_3700_);
v___x_3701_ = lean_box(0);
return v___x_3701_;
}
else
{
lean_object* v_tail_3702_; 
v_tail_3702_ = lean_ctor_get(v_x_3699_, 1);
if (lean_obj_tag(v_tail_3702_) == 0)
{
lean_object* v_head_3703_; lean_object* v___x_3704_; 
lean_dec(v_x_3700_);
v_head_3703_ = lean_ctor_get(v_x_3699_, 0);
lean_inc(v_head_3703_);
lean_dec_ref_known(v_x_3699_, 2);
v___x_3704_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3703_);
return v___x_3704_;
}
else
{
lean_object* v_head_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
lean_inc(v_tail_3702_);
v_head_3705_ = lean_ctor_get(v_x_3699_, 0);
lean_inc(v_head_3705_);
lean_dec_ref_known(v_x_3699_, 2);
v___x_3706_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3705_);
v___x_3707_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(v_x_3700_, v___x_3706_, v_tail_3702_);
return v___x_3707_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_3711_ = lean_string_length(v___x_3710_);
return v___x_3711_;
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1);
v___x_3713_ = lean_nat_to_int(v___x_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(lean_object* v_a_3716_){
_start:
{
if (lean_obj_tag(v_a_3716_) == 0)
{
lean_object* v___x_3717_; 
v___x_3717_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0));
return v___x_3717_;
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; lean_object* v___x_3727_; 
v___x_3718_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3719_ = l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(v_a_3716_, v___x_3718_);
v___x_3720_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2);
v___x_3721_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__3));
v___x_3722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
lean_ctor_set(v___x_3722_, 1, v___x_3719_);
v___x_3723_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_3724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3722_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3720_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = 0;
v___x_3727_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set_uint8(v___x_3727_, sizeof(void*)*1, v___x_3726_);
return v___x_3727_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(lean_object* v_x_3731_, lean_object* v_x_3732_){
_start:
{
if (lean_obj_tag(v_x_3731_) == 0)
{
lean_object* v___x_3733_; 
v___x_3733_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3733_;
}
else
{
lean_object* v_val_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v_val_3734_ = lean_ctor_get(v_x_3731_, 0);
v___x_3735_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3736_ = lean_unsigned_to_nat(1024u);
v___x_3737_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__1));
v___x_3738_ = lean_box(0);
v___x_3739_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v___x_3738_, v_val_3734_);
v___x_3740_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v___x_3739_);
v___x_3741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3737_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = l_Repr_addAppParen(v___x_3741_, v___x_3736_);
v___x_3743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3735_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
v___x_3744_ = l_Repr_addAppParen(v___x_3743_, v_x_3732_);
return v___x_3744_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___boxed(lean_object* v_x_3745_, lean_object* v_x_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_x_3745_, v_x_3746_);
lean_dec(v_x_3746_);
lean_dec(v_x_3745_);
return v_res_3747_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3760_ = lean_unsigned_to_nat(20u);
v___x_3761_ = lean_nat_to_int(v___x_3760_);
return v___x_3761_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = lean_unsigned_to_nat(19u);
v___x_3765_ = lean_nat_to_int(v___x_3764_);
return v___x_3765_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3768_ = lean_unsigned_to_nat(17u);
v___x_3769_ = lean_nat_to_int(v___x_3768_);
return v___x_3769_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = lean_unsigned_to_nat(18u);
v___x_3777_ = lean_nat_to_int(v___x_3776_);
return v___x_3777_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3780_ = lean_unsigned_to_nat(21u);
v___x_3781_ = lean_nat_to_int(v___x_3780_);
return v___x_3781_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3783_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__0));
v___x_3784_ = lean_string_length(v___x_3783_);
return v___x_3784_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__18, &l_Lake_Check_instReprConfig_repr___redArg___closed__18_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18);
v___x_3786_ = lean_nat_to_int(v___x_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___redArg(lean_object* v_x_3791_){
_start:
{
lean_object* v_challenge__module_3792_; lean_object* v_solution__module_3793_; lean_object* v_theorem__names_3794_; lean_object* v_definition__names_3795_; lean_object* v_permitted__axioms_3796_; lean_object* v_enable__nanoda_x3f_3797_; lean_object* v_external__kernels_x3f_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; uint8_t v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_challenge__module_3792_ = lean_ctor_get(v_x_3791_, 0);
lean_inc_ref(v_challenge__module_3792_);
v_solution__module_3793_ = lean_ctor_get(v_x_3791_, 1);
lean_inc_ref(v_solution__module_3793_);
v_theorem__names_3794_ = lean_ctor_get(v_x_3791_, 2);
lean_inc_ref(v_theorem__names_3794_);
v_definition__names_3795_ = lean_ctor_get(v_x_3791_, 3);
lean_inc(v_definition__names_3795_);
v_permitted__axioms_3796_ = lean_ctor_get(v_x_3791_, 4);
lean_inc_ref(v_permitted__axioms_3796_);
v_enable__nanoda_x3f_3797_ = lean_ctor_get(v_x_3791_, 5);
lean_inc(v_enable__nanoda_x3f_3797_);
v_external__kernels_x3f_3798_ = lean_ctor_get(v_x_3791_, 6);
lean_inc(v_external__kernels_x3f_3798_);
lean_dec_ref(v_x_3791_);
v___x_3799_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__4));
v___x_3800_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__5));
v___x_3801_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__6, &l_Lake_Check_instReprConfig_repr___redArg___closed__6_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6);
v___x_3802_ = l_String_quote(v_challenge__module_3792_);
v___x_3803_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
v___x_3804_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3801_);
lean_ctor_set(v___x_3804_, 1, v___x_3803_);
v___x_3805_ = 0;
v___x_3806_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3806_, 0, v___x_3804_);
lean_ctor_set_uint8(v___x_3806_, sizeof(void*)*1, v___x_3805_);
v___x_3807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3800_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__2));
v___x_3809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = lean_box(1);
v___x_3811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__7));
v___x_3813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3811_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set(v___x_3814_, 1, v___x_3799_);
v___x_3815_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__8, &l_Lake_Check_instReprConfig_repr___redArg___closed__8_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8);
v___x_3816_ = l_String_quote(v_solution__module_3793_);
v___x_3817_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
v___x_3818_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3815_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
v___x_3819_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
lean_ctor_set_uint8(v___x_3819_, sizeof(void*)*1, v___x_3805_);
v___x_3820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3814_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
lean_ctor_set(v___x_3821_, 1, v___x_3808_);
v___x_3822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
lean_ctor_set(v___x_3822_, 1, v___x_3810_);
v___x_3823_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__9));
v___x_3824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3822_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
lean_ctor_set(v___x_3825_, 1, v___x_3799_);
v___x_3826_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__10, &l_Lake_Check_instReprConfig_repr___redArg___closed__10_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10);
v___x_3827_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_theorem__names_3794_);
v___x_3828_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3826_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
v___x_3829_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3829_, 0, v___x_3828_);
lean_ctor_set_uint8(v___x_3829_, sizeof(void*)*1, v___x_3805_);
v___x_3830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3825_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
v___x_3831_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
lean_ctor_set(v___x_3831_, 1, v___x_3808_);
v___x_3832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
lean_ctor_set(v___x_3832_, 1, v___x_3810_);
v___x_3833_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__11));
v___x_3834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3832_);
lean_ctor_set(v___x_3834_, 1, v___x_3833_);
v___x_3835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3834_);
lean_ctor_set(v___x_3835_, 1, v___x_3799_);
v___x_3836_ = lean_unsigned_to_nat(0u);
v___x_3837_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_definition__names_3795_, v___x_3836_);
v___x_3838_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3801_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
v___x_3839_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3839_, 0, v___x_3838_);
lean_ctor_set_uint8(v___x_3839_, sizeof(void*)*1, v___x_3805_);
v___x_3840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3835_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
v___x_3841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
lean_ctor_set(v___x_3841_, 1, v___x_3808_);
v___x_3842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3841_);
lean_ctor_set(v___x_3842_, 1, v___x_3810_);
v___x_3843_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__12));
v___x_3844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3842_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
v___x_3845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
lean_ctor_set(v___x_3845_, 1, v___x_3799_);
v___x_3846_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_permitted__axioms_3796_);
v___x_3847_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3801_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
lean_ctor_set_uint8(v___x_3848_, sizeof(void*)*1, v___x_3805_);
v___x_3849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3845_);
lean_ctor_set(v___x_3849_, 1, v___x_3848_);
v___x_3850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
lean_ctor_set(v___x_3850_, 1, v___x_3808_);
v___x_3851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
lean_ctor_set(v___x_3851_, 1, v___x_3810_);
v___x_3852_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__13));
v___x_3853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3851_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
v___x_3854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3853_);
lean_ctor_set(v___x_3854_, 1, v___x_3799_);
v___x_3855_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__14, &l_Lake_Check_instReprConfig_repr___redArg___closed__14_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14);
v___x_3856_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_enable__nanoda_x3f_3797_, v___x_3836_);
lean_dec(v_enable__nanoda_x3f_3797_);
v___x_3857_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3855_);
lean_ctor_set(v___x_3857_, 1, v___x_3856_);
v___x_3858_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3858_, 0, v___x_3857_);
lean_ctor_set_uint8(v___x_3858_, sizeof(void*)*1, v___x_3805_);
v___x_3859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3854_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
v___x_3860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3859_);
lean_ctor_set(v___x_3860_, 1, v___x_3808_);
v___x_3861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
lean_ctor_set(v___x_3861_, 1, v___x_3810_);
v___x_3862_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__15));
v___x_3863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3861_);
lean_ctor_set(v___x_3863_, 1, v___x_3862_);
v___x_3864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
lean_ctor_set(v___x_3864_, 1, v___x_3799_);
v___x_3865_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__16, &l_Lake_Check_instReprConfig_repr___redArg___closed__16_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16);
v___x_3866_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_external__kernels_x3f_3798_, v___x_3836_);
lean_dec(v_external__kernels_x3f_3798_);
v___x_3867_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3865_);
lean_ctor_set(v___x_3867_, 1, v___x_3866_);
v___x_3868_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
lean_ctor_set_uint8(v___x_3868_, sizeof(void*)*1, v___x_3805_);
v___x_3869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3864_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___x_3870_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__19, &l_Lake_Check_instReprConfig_repr___redArg___closed__19_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19);
v___x_3871_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__20));
v___x_3872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3871_);
lean_ctor_set(v___x_3872_, 1, v___x_3869_);
v___x_3873_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__21));
v___x_3874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3872_);
lean_ctor_set(v___x_3874_, 1, v___x_3873_);
v___x_3875_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3870_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
v___x_3876_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
lean_ctor_set_uint8(v___x_3876_, sizeof(void*)*1, v___x_3805_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr(lean_object* v_x_3877_, lean_object* v_prec_3878_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l_Lake_Check_instReprConfig_repr___redArg(v_x_3877_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___boxed(lean_object* v_x_3880_, lean_object* v_prec_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_Lake_Check_instReprConfig_repr(v_x_3880_, v_prec_3881_);
lean_dec(v_prec_3881_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(lean_object* v_a_3883_, lean_object* v_n_3884_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v_a_3883_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___boxed(lean_object* v_a_3886_, lean_object* v_n_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(v_a_3886_, v_n_3887_);
lean_dec(v_n_3887_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(lean_object* v_x_3889_, lean_object* v_x_3890_){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_x_3889_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___boxed(lean_object* v_x_3892_, lean_object* v_x_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(v_x_3892_, v_x_3893_);
lean_dec(v_x_3893_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(lean_object* v_s_3897_){
_start:
{
uint32_t v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3899_ = 10;
v___x_3900_ = lean_string_push(v_s_3897_, v___x_3899_);
v___x_3901_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v___x_3900_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0___boxed(lean_object* v_s_3902_, lean_object* v_a_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v_s_3902_);
return v_res_3904_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1(void){
_start:
{
uint32_t v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = 2;
v___x_3907_ = lean_box_uint32(v___x_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(lean_object* v_msg_3908_){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3910_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_3911_ = lean_string_append(v___x_3910_, v_msg_3908_);
v___x_3912_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_3911_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3920_; 
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3920_ == 0)
{
lean_object* v_unused_3921_; 
v_unused_3921_ = lean_ctor_get(v___x_3912_, 0);
lean_dec(v_unused_3921_);
v___x_3914_ = v___x_3912_;
v_isShared_3915_ = v_isSharedCheck_3920_;
goto v_resetjp_3913_;
}
else
{
lean_dec(v___x_3912_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3920_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3916_; lean_object* v___x_3918_; 
v___x_3916_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1;
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 0, v___x_3916_);
v___x_3918_ = v___x_3914_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
v_a_3922_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3912_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3912_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed(lean_object* v_msg_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v_msg_3930_);
lean_dec_ref(v_msg_3930_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(lean_object* v_cmd_3936_, lean_object* v_projectDir_3937_){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; uint8_t v___x_3941_; 
v___x_3939_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__0));
lean_inc_ref(v_projectDir_3937_);
v___x_3940_ = l_System_FilePath_join(v_projectDir_3937_, v___x_3939_);
v___x_3941_ = l_System_FilePath_pathExists(v___x_3940_);
lean_dec_ref(v___x_3940_);
if (v___x_3941_ == 0)
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3942_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_3943_ = lean_string_append(v___x_3942_, v_projectDir_3937_);
lean_dec_ref(v_projectDir_3937_);
v___x_3944_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__1));
v___x_3945_ = lean_string_append(v___x_3943_, v___x_3944_);
v___x_3946_ = lean_string_append(v___x_3945_, v_cmd_3936_);
v___x_3947_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__2));
v___x_3948_ = lean_string_append(v___x_3946_, v___x_3947_);
v___x_3949_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3948_);
lean_dec_ref(v___x_3948_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3958_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3952_ = v___x_3949_;
v_isShared_3953_ = v_isSharedCheck_3958_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___x_3949_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3958_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3954_; lean_object* v___x_3956_; 
v___x_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3954_, 0, v_a_3950_);
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 0, v___x_3954_);
v___x_3956_ = v___x_3952_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3954_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
v_a_3959_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3949_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3949_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
else
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
lean_dec_ref(v_projectDir_3937_);
v___x_3967_ = lean_box(0);
v___x_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
return v___x_3968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___boxed(lean_object* v_cmd_3969_, lean_object* v_projectDir_3970_, lean_object* v_a_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v_cmd_3969_, v_projectDir_3970_);
lean_dec_ref(v_cmd_3969_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext(lean_object* v_cmd_3981_, lean_object* v_lean_3982_, lean_object* v_lake_3983_, lean_object* v_projectDir_3984_){
_start:
{
uint8_t v___x_3986_; 
v___x_3986_ = l_System_Platform_isLinux;
if (v___x_3986_ == 0)
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
lean_dec_ref(v_projectDir_3984_);
lean_dec_ref(v_lean_3982_);
v___x_3987_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_3988_ = lean_string_append(v___x_3987_, v_cmd_3981_);
v___x_3989_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0));
v___x_3990_ = lean_string_append(v___x_3988_, v___x_3989_);
v___x_3991_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3990_);
lean_dec_ref(v___x_3990_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4000_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3994_ = v___x_3991_;
v_isShared_3995_ = v_isSharedCheck_4000_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3991_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4000_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3996_; lean_object* v___x_3998_; 
v___x_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3996_, 0, v_a_3992_);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 0, v___x_3996_);
v___x_3998_ = v___x_3994_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3996_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
v_a_4001_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3991_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3991_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
else
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___y_4012_; 
v___x_4009_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1));
v___x_4010_ = lean_io_getenv(v___x_4009_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v___x_4144_; 
v___x_4144_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7));
v___y_4012_ = v___x_4144_;
goto v___jp_4011_;
}
else
{
lean_object* v_val_4145_; 
v_val_4145_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_val_4145_);
lean_dec_ref_known(v___x_4010_, 1);
v___y_4012_ = v_val_4145_;
goto v___jp_4011_;
}
v___jp_4011_:
{
lean_object* v___x_4013_; lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4143_; 
lean_inc_ref(v___y_4012_);
v___x_4013_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___y_4012_);
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4016_ = v___x_4013_;
v_isShared_4017_ = v_isSharedCheck_4143_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_4013_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4143_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
if (lean_obj_tag(v_a_4014_) == 1)
{
lean_object* v_val_4018_; lean_object* v_sysroot_4019_; lean_object* v_binDir_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4121_; 
lean_del_object(v___x_4016_);
lean_dec_ref(v___y_4012_);
v_val_4018_ = lean_ctor_get(v_a_4014_, 0);
lean_inc(v_val_4018_);
lean_dec_ref_known(v_a_4014_, 1);
v_sysroot_4019_ = lean_ctor_get(v_lean_3982_, 0);
lean_inc_ref(v_sysroot_4019_);
v_binDir_4020_ = lean_ctor_get(v_lean_3982_, 6);
lean_inc_ref_n(v_binDir_4020_, 2);
lean_dec_ref(v_lean_3982_);
v___x_4021_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2));
v___x_4022_ = l_System_FilePath_join(v_binDir_4020_, v___x_4021_);
v___x_4023_ = l_System_FilePath_exeExtension;
v___x_4024_ = l_System_FilePath_addExtension(v___x_4022_, v___x_4023_);
v___x_4025_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3));
v___x_4026_ = l_System_FilePath_join(v_binDir_4020_, v___x_4025_);
v___x_4027_ = l_System_FilePath_addExtension(v___x_4026_, v___x_4023_);
v___x_4028_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4));
v___x_4029_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4028_);
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4032_ = v___x_4029_;
v_isShared_4033_ = v_isSharedCheck_4121_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4121_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
if (lean_obj_tag(v_a_4030_) == 1)
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4096_; 
lean_dec_ref_known(v_a_4030_, 1);
lean_del_object(v___x_4032_);
v___x_4034_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__4));
v___x_4035_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4034_);
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4096_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4096_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
if (lean_obj_tag(v_a_4036_) == 1)
{
lean_object* v_val_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4071_; 
lean_del_object(v___x_4038_);
v_val_4040_ = lean_ctor_get(v_a_4036_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v_a_4036_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4042_ = v_a_4036_;
v_isShared_4043_ = v_isSharedCheck_4071_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_val_4040_);
lean_dec(v_a_4036_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4071_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4044_; 
v___x_4044_ = lean_io_realpath(v_projectDir_3984_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4062_; 
v_a_4045_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4047_ = v___x_4044_;
v_isShared_4048_ = v_isSharedCheck_4062_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4044_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4062_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v_home_4049_; lean_object* v_lake_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4057_; 
v_home_4049_ = lean_ctor_get(v_lake_3983_, 0);
v_lake_4050_ = lean_ctor_get(v_lake_3983_, 5);
v___x_4051_ = lean_box(0);
v___x_4052_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_4053_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
v___x_4054_ = lean_box(1);
lean_inc_ref(v_home_4049_);
lean_inc_ref(v_lake_4050_);
v___x_4055_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_4055_, 0, v_a_4045_);
lean_ctor_set(v___x_4055_, 1, v___x_4051_);
lean_ctor_set(v___x_4055_, 2, v___x_4051_);
lean_ctor_set(v___x_4055_, 3, v___x_4052_);
lean_ctor_set(v___x_4055_, 4, v___x_4052_);
lean_ctor_set(v___x_4055_, 5, v___x_4052_);
lean_ctor_set(v___x_4055_, 6, v_sysroot_4019_);
lean_ctor_set(v___x_4055_, 7, v___x_4053_);
lean_ctor_set(v___x_4055_, 8, v___x_4053_);
lean_ctor_set(v___x_4055_, 9, v_val_4018_);
lean_ctor_set(v___x_4055_, 10, v_lake_4050_);
lean_ctor_set(v___x_4055_, 11, v_home_4049_);
lean_ctor_set(v___x_4055_, 12, v___x_4024_);
lean_ctor_set(v___x_4055_, 13, v___x_4027_);
lean_ctor_set(v___x_4055_, 14, v_val_4040_);
lean_ctor_set(v___x_4055_, 15, v___x_4054_);
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 0, v___x_4055_);
v___x_4057_ = v___x_4042_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v___x_4055_);
v___x_4057_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4059_; 
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 0, v___x_4057_);
v___x_4059_ = v___x_4047_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_del_object(v___x_4042_);
lean_dec(v_val_4040_);
lean_dec_ref(v___x_4027_);
lean_dec_ref(v___x_4024_);
lean_dec_ref(v_sysroot_4019_);
lean_dec(v_val_4018_);
v_a_4063_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4044_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4044_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
}
else
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
lean_dec(v_a_4036_);
lean_dec_ref(v___x_4027_);
lean_dec_ref(v___x_4024_);
lean_dec_ref(v_sysroot_4019_);
lean_dec(v_val_4018_);
lean_dec_ref(v_projectDir_3984_);
v___x_4072_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4073_ = lean_string_append(v___x_4072_, v_cmd_3981_);
v___x_4074_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5));
v___x_4075_ = lean_string_append(v___x_4073_, v___x_4074_);
v___x_4076_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4075_);
lean_dec_ref(v___x_4075_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4087_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4079_ = v___x_4076_;
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4076_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4082_; 
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v_a_4077_);
v___x_4082_ = v___x_4038_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4077_);
v___x_4082_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
lean_object* v___x_4084_; 
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 0, v___x_4082_);
v___x_4084_ = v___x_4079_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4082_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
else
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4095_; 
lean_del_object(v___x_4038_);
v_a_4088_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4090_ = v___x_4076_;
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4076_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4093_; 
if (v_isShared_4091_ == 0)
{
v___x_4093_ = v___x_4090_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4088_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
return v___x_4093_;
}
}
}
}
}
}
else
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
lean_dec(v_a_4030_);
lean_dec_ref(v___x_4027_);
lean_dec_ref(v___x_4024_);
lean_dec_ref(v_sysroot_4019_);
lean_dec(v_val_4018_);
lean_dec_ref(v_projectDir_3984_);
v___x_4097_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4098_ = lean_string_append(v___x_4097_, v_cmd_3981_);
v___x_4099_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6));
v___x_4100_ = lean_string_append(v___x_4098_, v___x_4099_);
v___x_4101_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4100_);
lean_dec_ref(v___x_4100_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4112_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4104_ = v___x_4101_;
v_isShared_4105_ = v_isSharedCheck_4112_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_a_4102_);
lean_dec(v___x_4101_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4112_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4107_; 
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 0, v_a_4102_);
v___x_4107_ = v___x_4032_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4102_);
v___x_4107_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
lean_object* v___x_4109_; 
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 0, v___x_4107_);
v___x_4109_ = v___x_4104_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4107_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_del_object(v___x_4032_);
v_a_4113_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_4101_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4101_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
}
}
else
{
lean_object* v___x_4122_; lean_object* v___x_4123_; 
lean_dec(v_a_4014_);
lean_dec_ref(v_projectDir_3984_);
lean_dec_ref(v_lean_3982_);
v___x_4122_ = l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError(v_cmd_3981_, v___y_4012_);
lean_dec_ref(v___y_4012_);
v___x_4123_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4122_);
lean_dec_ref(v___x_4122_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4134_; 
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4126_ = v___x_4123_;
v_isShared_4127_ = v_isSharedCheck_4134_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4123_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4134_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v_a_4124_);
v___x_4129_ = v___x_4016_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
lean_object* v___x_4131_; 
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 0, v___x_4129_);
v___x_4131_ = v___x_4126_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_del_object(v___x_4016_);
v_a_4135_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4123_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4123_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___boxed(lean_object* v_cmd_4146_, lean_object* v_lean_4147_, lean_object* v_lake_4148_, lean_object* v_projectDir_4149_, lean_object* v_a_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v_cmd_4146_, v_lean_4147_, v_lake_4148_, v_projectDir_4149_);
lean_dec_ref(v_lake_4148_);
lean_dec_ref(v_cmd_4146_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(lean_object* v_init_4158_, lean_object* v_x_4159_){
_start:
{
lean_object* v_d_4162_; 
if (lean_obj_tag(v_x_4159_) == 0)
{
lean_object* v_k_4165_; lean_object* v_v_4166_; lean_object* v_l_4167_; lean_object* v_r_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v_k_4165_ = lean_ctor_get(v_x_4159_, 1);
v_v_4166_ = lean_ctor_get(v_x_4159_, 2);
v_l_4167_ = lean_ctor_get(v_x_4159_, 3);
v_r_4168_ = lean_ctor_get(v_x_4159_, 4);
v___x_4169_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
v___x_4170_ = lean_box(0);
v___x_4171_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_4172_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_4158_, v_l_4167_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4172_, 1);
if (lean_obj_tag(v_a_4173_) == 0)
{
lean_object* v_a_4174_; 
v_a_4174_ = lean_ctor_get(v_a_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref_known(v_a_4173_, 1);
v_d_4162_ = v_a_4174_;
goto v___jp_4161_;
}
else
{
lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4211_; 
v_isSharedCheck_4211_ = !lean_is_exclusive(v_a_4173_);
if (v_isSharedCheck_4211_ == 0)
{
lean_object* v_unused_4212_; 
v_unused_4212_ = lean_ctor_get(v_a_4173_, 0);
lean_dec(v_unused_4212_);
v___x_4176_ = v_a_4173_;
v_isShared_4177_ = v_isSharedCheck_4211_;
goto v_resetjp_4175_;
}
else
{
lean_dec(v_a_4173_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4211_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4210_; 
v___x_4178_ = lean_unsigned_to_nat(0u);
v___x_4179_ = lean_array_get_borrowed(v___x_4169_, v_v_4166_, v___x_4178_);
lean_inc(v___x_4179_);
v___x_4180_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4179_);
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4183_ = v___x_4180_;
v_isShared_4184_ = v_isSharedCheck_4210_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4180_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4210_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
if (lean_obj_tag(v_a_4181_) == 0)
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4185_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1));
v___x_4186_ = lean_string_append(v___x_4185_, v_k_4165_);
v___x_4187_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2));
v___x_4188_ = lean_string_append(v___x_4186_, v___x_4187_);
v___x_4189_ = lean_string_append(v___x_4188_, v___x_4179_);
v___x_4190_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v___x_4191_ = lean_string_append(v___x_4189_, v___x_4190_);
v___x_4192_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4191_);
lean_dec_ref(v___x_4191_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; lean_object* v___x_4195_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_a_4193_);
lean_dec_ref_known(v___x_4192_, 1);
if (v_isShared_4184_ == 0)
{
lean_ctor_set(v___x_4183_, 0, v_a_4193_);
v___x_4195_ = v___x_4183_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4193_);
v___x_4195_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
lean_object* v___x_4197_; 
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___x_4195_);
v___x_4197_ = v___x_4176_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4198_; 
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4197_);
lean_ctor_set(v___x_4198_, 1, v___x_4170_);
v_d_4162_ = v___x_4198_;
goto v___jp_4161_;
}
}
}
else
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4208_; 
lean_del_object(v___x_4183_);
lean_del_object(v___x_4176_);
v_a_4201_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4203_ = v___x_4192_;
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4192_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_4181_, 1);
lean_del_object(v___x_4183_);
lean_del_object(v___x_4176_);
v_init_4158_ = v___x_4171_;
v_x_4159_ = v_r_4168_;
goto _start;
}
}
}
}
}
else
{
return v___x_4172_;
}
}
else
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4213_, 0, v_init_4158_);
v___x_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
return v___x_4214_;
}
v___jp_4161_:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4163_, 0, v_d_4162_);
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
return v___x_4164_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___boxed(lean_object* v_init_4215_, lean_object* v_x_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_4215_, v_x_4216_);
lean_dec(v_x_4216_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(lean_object* v_k_4219_, lean_object* v_v_4220_, lean_object* v_t_4221_){
_start:
{
if (lean_obj_tag(v_t_4221_) == 0)
{
lean_object* v_size_4222_; lean_object* v_k_4223_; lean_object* v_v_4224_; lean_object* v_l_4225_; lean_object* v_r_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4506_; 
v_size_4222_ = lean_ctor_get(v_t_4221_, 0);
v_k_4223_ = lean_ctor_get(v_t_4221_, 1);
v_v_4224_ = lean_ctor_get(v_t_4221_, 2);
v_l_4225_ = lean_ctor_get(v_t_4221_, 3);
v_r_4226_ = lean_ctor_get(v_t_4221_, 4);
v_isSharedCheck_4506_ = !lean_is_exclusive(v_t_4221_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4228_ = v_t_4221_;
v_isShared_4229_ = v_isSharedCheck_4506_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_r_4226_);
lean_inc(v_l_4225_);
lean_inc(v_v_4224_);
lean_inc(v_k_4223_);
lean_inc(v_size_4222_);
lean_dec(v_t_4221_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4506_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
uint8_t v___x_4230_; 
v___x_4230_ = lean_string_compare(v_k_4219_, v_k_4223_);
switch(v___x_4230_)
{
case 0:
{
lean_object* v_impl_4231_; lean_object* v___x_4232_; 
lean_dec(v_size_4222_);
v_impl_4231_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_4219_, v_v_4220_, v_l_4225_);
v___x_4232_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4226_) == 0)
{
lean_object* v_size_4233_; lean_object* v_size_4234_; lean_object* v_k_4235_; lean_object* v_v_4236_; lean_object* v_l_4237_; lean_object* v_r_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; uint8_t v___x_4241_; 
v_size_4233_ = lean_ctor_get(v_r_4226_, 0);
v_size_4234_ = lean_ctor_get(v_impl_4231_, 0);
lean_inc(v_size_4234_);
v_k_4235_ = lean_ctor_get(v_impl_4231_, 1);
lean_inc(v_k_4235_);
v_v_4236_ = lean_ctor_get(v_impl_4231_, 2);
lean_inc(v_v_4236_);
v_l_4237_ = lean_ctor_get(v_impl_4231_, 3);
lean_inc(v_l_4237_);
v_r_4238_ = lean_ctor_get(v_impl_4231_, 4);
lean_inc(v_r_4238_);
v___x_4239_ = lean_unsigned_to_nat(3u);
v___x_4240_ = lean_nat_mul(v___x_4239_, v_size_4233_);
v___x_4241_ = lean_nat_dec_lt(v___x_4240_, v_size_4234_);
lean_dec(v___x_4240_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4245_; 
lean_dec(v_r_4238_);
lean_dec(v_l_4237_);
lean_dec(v_v_4236_);
lean_dec(v_k_4235_);
v___x_4242_ = lean_nat_add(v___x_4232_, v_size_4234_);
lean_dec(v_size_4234_);
v___x_4243_ = lean_nat_add(v___x_4242_, v_size_4233_);
lean_dec(v___x_4242_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 3, v_impl_4231_);
lean_ctor_set(v___x_4228_, 0, v___x_4243_);
v___x_4245_ = v___x_4228_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4243_);
lean_ctor_set(v_reuseFailAlloc_4246_, 1, v_k_4223_);
lean_ctor_set(v_reuseFailAlloc_4246_, 2, v_v_4224_);
lean_ctor_set(v_reuseFailAlloc_4246_, 3, v_impl_4231_);
lean_ctor_set(v_reuseFailAlloc_4246_, 4, v_r_4226_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
else
{
lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4312_; 
v_isSharedCheck_4312_ = !lean_is_exclusive(v_impl_4231_);
if (v_isSharedCheck_4312_ == 0)
{
lean_object* v_unused_4313_; lean_object* v_unused_4314_; lean_object* v_unused_4315_; lean_object* v_unused_4316_; lean_object* v_unused_4317_; 
v_unused_4313_ = lean_ctor_get(v_impl_4231_, 4);
lean_dec(v_unused_4313_);
v_unused_4314_ = lean_ctor_get(v_impl_4231_, 3);
lean_dec(v_unused_4314_);
v_unused_4315_ = lean_ctor_get(v_impl_4231_, 2);
lean_dec(v_unused_4315_);
v_unused_4316_ = lean_ctor_get(v_impl_4231_, 1);
lean_dec(v_unused_4316_);
v_unused_4317_ = lean_ctor_get(v_impl_4231_, 0);
lean_dec(v_unused_4317_);
v___x_4248_ = v_impl_4231_;
v_isShared_4249_ = v_isSharedCheck_4312_;
goto v_resetjp_4247_;
}
else
{
lean_dec(v_impl_4231_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4312_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v_size_4250_; lean_object* v_size_4251_; lean_object* v_k_4252_; lean_object* v_v_4253_; lean_object* v_l_4254_; lean_object* v_r_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; uint8_t v___x_4258_; 
v_size_4250_ = lean_ctor_get(v_l_4237_, 0);
v_size_4251_ = lean_ctor_get(v_r_4238_, 0);
v_k_4252_ = lean_ctor_get(v_r_4238_, 1);
v_v_4253_ = lean_ctor_get(v_r_4238_, 2);
v_l_4254_ = lean_ctor_get(v_r_4238_, 3);
v_r_4255_ = lean_ctor_get(v_r_4238_, 4);
v___x_4256_ = lean_unsigned_to_nat(2u);
v___x_4257_ = lean_nat_mul(v___x_4256_, v_size_4250_);
v___x_4258_ = lean_nat_dec_lt(v_size_4251_, v___x_4257_);
lean_dec(v___x_4257_);
if (v___x_4258_ == 0)
{
lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4287_; 
lean_inc(v_r_4255_);
lean_inc(v_l_4254_);
lean_inc(v_v_4253_);
lean_inc(v_k_4252_);
v_isSharedCheck_4287_ = !lean_is_exclusive(v_r_4238_);
if (v_isSharedCheck_4287_ == 0)
{
lean_object* v_unused_4288_; lean_object* v_unused_4289_; lean_object* v_unused_4290_; lean_object* v_unused_4291_; lean_object* v_unused_4292_; 
v_unused_4288_ = lean_ctor_get(v_r_4238_, 4);
lean_dec(v_unused_4288_);
v_unused_4289_ = lean_ctor_get(v_r_4238_, 3);
lean_dec(v_unused_4289_);
v_unused_4290_ = lean_ctor_get(v_r_4238_, 2);
lean_dec(v_unused_4290_);
v_unused_4291_ = lean_ctor_get(v_r_4238_, 1);
lean_dec(v_unused_4291_);
v_unused_4292_ = lean_ctor_get(v_r_4238_, 0);
lean_dec(v_unused_4292_);
v___x_4260_ = v_r_4238_;
v_isShared_4261_ = v_isSharedCheck_4287_;
goto v_resetjp_4259_;
}
else
{
lean_dec(v_r_4238_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4287_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___x_4275_; lean_object* v___y_4277_; 
v___x_4262_ = lean_nat_add(v___x_4232_, v_size_4234_);
lean_dec(v_size_4234_);
v___x_4263_ = lean_nat_add(v___x_4262_, v_size_4233_);
lean_dec(v___x_4262_);
v___x_4275_ = lean_nat_add(v___x_4232_, v_size_4250_);
if (lean_obj_tag(v_l_4254_) == 0)
{
lean_object* v_size_4285_; 
v_size_4285_ = lean_ctor_get(v_l_4254_, 0);
lean_inc(v_size_4285_);
v___y_4277_ = v_size_4285_;
goto v___jp_4276_;
}
else
{
lean_object* v___x_4286_; 
v___x_4286_ = lean_unsigned_to_nat(0u);
v___y_4277_ = v___x_4286_;
goto v___jp_4276_;
}
v___jp_4264_:
{
lean_object* v___x_4268_; lean_object* v___x_4270_; 
v___x_4268_ = lean_nat_add(v___y_4265_, v___y_4267_);
lean_dec(v___y_4267_);
lean_dec(v___y_4265_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 4, v_r_4226_);
lean_ctor_set(v___x_4260_, 3, v_r_4255_);
lean_ctor_set(v___x_4260_, 2, v_v_4224_);
lean_ctor_set(v___x_4260_, 1, v_k_4223_);
lean_ctor_set(v___x_4260_, 0, v___x_4268_);
v___x_4270_ = v___x_4260_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4268_);
lean_ctor_set(v_reuseFailAlloc_4274_, 1, v_k_4223_);
lean_ctor_set(v_reuseFailAlloc_4274_, 2, v_v_4224_);
lean_ctor_set(v_reuseFailAlloc_4274_, 3, v_r_4255_);
lean_ctor_set(v_reuseFailAlloc_4274_, 4, v_r_4226_);
v___x_4270_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
lean_object* v___x_4272_; 
if (v_isShared_4249_ == 0)
{
lean_ctor_set(v___x_4248_, 4, v___x_4270_);
lean_ctor_set(v___x_4248_, 3, v___y_4266_);
lean_ctor_set(v___x_4248_, 2, v_v_4253_);
lean_ctor_set(v___x_4248_, 1, v_k_4252_);
lean_ctor_set(v___x_4248_, 0, v___x_4263_);
v___x_4272_ = v___x_4248_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4263_);
lean_ctor_set(v_reuseFailAlloc_4273_, 1, v_k_4252_);
lean_ctor_set(v_reuseFailAlloc_4273_, 2, v_v_4253_);
lean_ctor_set(v_reuseFailAlloc_4273_, 3, v___y_4266_);
lean_ctor_set(v_reuseFailAlloc_4273_, 4, v___x_4270_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
v___jp_4276_:
{
lean_object* v___x_4278_; lean_object* v___x_4280_; 
v___x_4278_ = lean_nat_add(v___x_4275_, v___y_4277_);
lean_dec(v___y_4277_);
lean_dec(v___x_4275_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 4, v_l_4254_);
lean_ctor_set(v___x_4228_, 3, v_l_4237_);
lean_ctor_set(v___x_4228_, 2, v_v_4236_);
lean_ctor_set(v___x_4228_, 1, v_k_4235_);
lean_ctor_set(v___x_4228_, 0, v___x_4278_);
v___x_4280_ = v___x_4228_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4278_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v_k_4235_);
lean_ctor_set(v_reuseFailAlloc_4284_, 2, v_v_4236_);
lean_ctor_set(v_reuseFailAlloc_4284_, 3, v_l_4237_);
lean_ctor_set(v_reuseFailAlloc_4284_, 4, v_l_4254_);
v___x_4280_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
lean_object* v___x_4281_; 
v___x_4281_ = lean_nat_add(v___x_4232_, v_size_4233_);
if (lean_obj_tag(v_r_4255_) == 0)
{
lean_object* v_size_4282_; 
v_size_4282_ = lean_ctor_get(v_r_4255_, 0);
lean_inc(v_size_4282_);
v___y_4265_ = v___x_4281_;
v___y_4266_ = v___x_4280_;
v___y_4267_ = v_size_4282_;
goto v___jp_4264_;
}
else
{
lean_object* v___x_4283_; 
v___x_4283_ = lean_unsigned_to_nat(0u);
v___y_4265_ = v___x_4281_;
v___y_4266_ = v___x_4280_;
v___y_4267_ = v___x_4283_;
goto v___jp_4264_;
}
}
}
}
}
else
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4298_; 
lean_del_object(v___x_4228_);
v___x_4293_ = lean_nat_add(v___x_4232_, v_size_4234_);
lean_dec(v_size_4234_);
v___x_4294_ = lean_nat_add(v___x_4293_, v_size_4233_);
lean_dec(v___x_4293_);
v___x_4295_ = lean_nat_add(v___x_4232_, v_size_4233_);
v___x_4296_ = lean_nat_add(v___x_4295_, v_size_4251_);
lean_dec(v___x_4295_);
lean_inc_ref(v_r_4226_);
if (v_isShared_4249_ == 0)
{
lean_ctor_set(v___x_4248_, 4, v_r_4226_);
lean_ctor_set(v___x_4248_, 3, v_r_4238_);
lean_ctor_set(v___x_4248_, 2, v_v_4224_);
lean_ctor_set(v___x_4248_, 1, v_k_4223_);
lean_ctor_set(v___x_4248_, 0, v___x_4296_);
v___x_4298_ = v___x_4248_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4296_);
lean_ctor_set(v_reuseFailAlloc_4311_, 1, v_k_4223_);
lean_ctor_set(v_reuseFailAlloc_4311_, 2, v_v_4224_);
lean_ctor_set(v_reuseFailAlloc_4311_, 3, v_r_4238_);
lean_ctor_set(v_reuseFailAlloc_4311_, 4, v_r_4226_);
v___x_4298_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
v_isSharedCheck_4305_ = !lean_is_exclusive(v_r_4226_);
if (v_isSharedCheck_4305_ == 0)
{
lean_object* v_unused_4306_; lean_object* v_unused_4307_; lean_object* v_unused_4308_; lean_object* v_unused_4309_; lean_object* v_unused_4310_; 
v_unused_4306_ = lean_ctor_get(v_r_4226_, 4);
lean_dec(v_unused_4306_);
v_unused_4307_ = lean_ctor_get(v_r_4226_, 3);
lean_dec(v_unused_4307_);
v_unused_4308_ = lean_ctor_get(v_r_4226_, 2);
lean_dec(v_unused_4308_);
v_unused_4309_ = lean_ctor_get(v_r_4226_, 1);
lean_dec(v_unused_4309_);
v_unused_4310_ = lean_ctor_get(v_r_4226_, 0);
lean_dec(v_unused_4310_);
v___x_4300_ = v_r_4226_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_dec(v_r_4226_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 4, v___x_4298_);
lean_ctor_set(v___x_4300_, 3, v_l_4237_);
lean_ctor_set(v___x_4300_, 2, v_v_4236_);
lean_ctor_set(v___x_4300_, 1, v_k_4235_);
lean_ctor_set(v___x_4300_, 0, v___x_4294_);
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v___x_4294_);
lean_ctor_set(v_reuseFailAlloc_4304_, 1, v_k_4235_);
lean_ctor_set(v_reuseFailAlloc_4304_, 2, v_v_4236_);
lean_ctor_set(v_reuseFailAlloc_4304_, 3, v_l_4237_);
lean_ctor_set(v_reuseFailAlloc_4304_, 4, v___x_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4318_; 
v_l_4318_ = lean_ctor_get(v_impl_4231_, 3);
lean_inc(v_l_4318_);
if (lean_obj_tag(v_l_4318_) == 0)
{
lean_object* v_r_4319_; lean_object* v_k_4320_; lean_object* v_v_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4332_; 
v_r_4319_ = lean_ctor_get(v_impl_4231_, 4);
v_k_4320_ = lean_ctor_get(v_impl_4231_, 1);
v_v_4321_ = lean_ctor_get(v_impl_4231_, 2);
v_isSharedCheck_4332_ = !lean_is_exclusive(v_impl_4231_);
if (v_isSharedCheck_4332_ == 0)
{
lean_object* v_unused_4333_; lean_object* v_unused_4334_; 
v_unused_4333_ = lean_ctor_get(v_impl_4231_, 3);
lean_dec(v_unused_4333_);
v_unused_4334_ = lean_ctor_get(v_impl_4231_, 0);
lean_dec(v_unused_4334_);
v___x_4323_ = v_impl_4231_;
v_isShared_4324_ = v_isSharedCheck_4332_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_r_4319_);
lean_inc(v_v_4321_);
lean_inc(v_k_4320_);
lean_dec(v_impl_4231_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4332_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4325_; lean_object* v___x_4327_; 
v___x_4325_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4319_);
if (v_isShared_4324_ == 0)
{
lean_ctor_set(v___x_4323_, 3, v_r_4319_);
lean_ctor_set(v___x_4323_, 2, v_v_4224_);
lean_ctor_set(v___x_4323_, 1, v_k_4223_);
lean_ctor_set(v___x_4323_, 0, v___x_4232_);
v___x_4327_ = v___x_4323_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4232_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v_k_4223_);
lean_ctor_set(v_reuseFailAlloc_4331_, 2, v_v_4224_);
lean_ctor_set(v_reuseFailAlloc_4331_, 3, v_r_4319_);
lean_ctor_set(v_reuseFailAlloc_4331_, 4, v_r_4319_);
v___x_4327_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
lean_object* v___x_4329_; 
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 4, v___x_4327_);
lean_ctor_set(v___x_4228_, 3, v_l_4318_);
lean_ctor_set(v___x_4228_, 2, v_v_4321_);
lean_ctor_set(v___x_4228_, 1, v_k_4320_);
lean_ctor_set(v___x_4228_, 0, v___x_4325_);
v___x_4329_ = v___x_4228_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4325_);
lean_ctor_set(v_reuseFailAlloc_4330_, 1, v_k_4320_);
lean_ctor_set(v_reuseFailAlloc_4330_, 2, v_v_4321_);
lean_ctor_set(v_reuseFailAlloc_4330_, 3, v_l_4318_);
lean_ctor_set(v_reuseFailAlloc_4330_, 4, v___x_4327_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
}
else
{
lean_object* v_r_4335_; 
v_r_4335_ = lean_ctor_get(v_impl_4231_, 4);
lean_inc(v_r_4335_);
if (lean_obj_tag(v_r_4335_) == 0)
{
lean_object* v_k_4336_; lean_object* v_v_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4360_; 
v_k_4336_ = lean_ctor_get(v_impl_4231_, 1);
v_v_4337_ = lean_ctor_get(v_impl_4231_, 2);
v_isSharedCheck_4360_ = !lean_is_exclusive(v_impl_4231_);
if (v_isSharedCheck_4360_ == 0)
{
lean_object* v_unused_4361_; lean_object* v_unused_4362_; lean_object* v_unused_4363_; 
v_unused_4361_ = lean_ctor_get(v_impl_4231_, 4);
lean_dec(v_unused_4361_);
v_unused_4362_ = lean_ctor_get(v_impl_4231_, 3);
lean_dec(v_unused_4362_);
v_unused_4363_ = lean_ctor_get(v_impl_4231_, 0);
lean_dec(v_unused_4363_);
v___x_4339_ = v_impl_4231_;
v_isShared_4340_ = v_isSharedCheck_4360_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_v_4337_);
lean_inc(v_k_4336_);
lean_dec(v_impl_4231_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4360_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v_k_4341_; lean_object* v_v_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4356_; 
v_k_4341_ = lean_ctor_get(v_r_4335_, 1);
v_v_4342_ = lean_ctor_get(v_r_4335_, 2);
v_isSharedCheck_4356_ = !lean_is_exclusive(v_r_4335_);
if (v_isSharedCheck_4356_ == 0)
{
lean_object* v_unused_4357_; lean_object* v_unused_4358_; lean_object* v_unused_4359_; 
v_unused_4357_ = lean_ctor_get(v_r_4335_, 4);
lean_dec(v_unused_4357_);
v_unused_4358_ = lean_ctor_get(v_r_4335_, 3);
lean_dec(v_unused_4358_);
v_unused_4359_ = lean_ctor_get(v_r_4335_, 0);
lean_dec(v_unused_4359_);
v___x_4344_ = v_r_4335_;
v_isShared_4345_ = v_isSharedCheck_4356_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_v_4342_);
lean_inc(v_k_4341_);
lean_dec(v_r_4335_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4356_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4346_; lean_object* v___x_4348_; 
v___x_4346_ = lean_unsigned_to_nat(3u);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 4, v_l_4318_);
lean_ctor_set(v___x_4344_, 3, v_l_4318_);
lean_ctor_set(v___x_4344_, 2, v_v_4337_);
lean_ctor_set(v___x_4344_, 1, v_k_4336_);
lean_ctor_set(v___x_4344_, 0, v___x_4232_);
v___x_4348_ = v___x_4344_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v___x_4232_);
lean_ctor_set(v_reuseFailAlloc_4355_, 1, v_k_4336_);
lean_ctor_set(v_reuseFailAlloc_4355_, 2, v_v_4337_);
lean_ctor_set(v_reuseFailAlloc_4355_, 3, v_l_4318_);
lean_ctor_set(v_reuseFailAlloc_4355_, 4, v_l_4318_);
v___x_4348_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
lean_object* v___x_4350_; 
if (v_isShared_4340_ == 0)
{
lean_ctor_set(v___x_4339_, 4, v_l_4318_);
lean_ctor_set(v___x_4339_, 2, v_v_4224_);
lean_ctor_set(v___x_4339_, 1, v_k_4223_);
lean_ctor_set(v___x_4339_, 0, v___x_4232_);
v___x_4350_ = v___x_4339_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4232_);
lean_ctor_set(v_reuseFailAlloc_4354_, 1, v_k_4223_);
lean_ctor_set(v_reuseFailAlloc_4354_, 2, v_v_4224_);
lean_ctor_set(v_reuseFailAlloc_4354_, 3, v_l_4318_);
lean_ctor_set(v_reuseFailAlloc_4354_, 4, v_l_4318_);
v___x_4350_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
lean_object* v___x_4352_; 
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 4, v___x_4350_);
lean_ctor_set(v___x_4228_, 3, v___x_4348_);
lean_ctor_set(v___x_4228_, 2, v_v_4342_);
lean_ctor_set(v___x_4228_, 1, v_k_4341_);
lean_ctor_set(v___x_4228_, 0, v___x_4346_);
v___x_4352_ = v___x_4228_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4346_);
lean_ctor_set(v_reuseFailAlloc_4353_, 1, v_k_4341_);
lean_ctor_set(v_reuseFailAlloc_4353_, 2, v_v_4342_);
lean_ctor_set(v_reuseFailAlloc_4353_, 3, v___x_4348_);
lean_ctor_set(v_reuseFailAlloc_4353_, 4, v___x_4350_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
}
}
else
{
lean_object* v___x_4364_; lean_object* v___x_4366_; 
v___x_4364_ = lean_unsigned_to_nat(2u);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 4, v_r_4335_);
lean_ctor_set(v___x_4228_, 3, v_impl_4231_);
lean_ctor_set(v___x_4228_, 0, v___x_4364_);
v___x_4366_ = v___x_4228_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v___x_4364_);
lean_ctor_set(v_reuseFailAlloc_4367_, 1, v_k_4223_);
lean_ctor_set(v_reuseFailAlloc_4367_, 2, v_v_4224_);
lean_ctor_set(v_reuseFailAlloc_4367_, 3, v_impl_4231_);
lean_ctor_set(v_reuseFailAlloc_4367_, 4, v_r_4335_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4369_; 
lean_dec(v_v_4224_);
lean_dec(v_k_4223_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 2, v_v_4220_);
lean_ctor_set(v___x_4228_, 1, v_k_4219_);
v___x_4369_ = v___x_4228_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_size_4222_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_k_4219_);
lean_ctor_set(v_reuseFailAlloc_4370_, 2, v_v_4220_);
lean_ctor_set(v_reuseFailAlloc_4370_, 3, v_l_4225_);
lean_ctor_set(v_reuseFailAlloc_4370_, 4, v_r_4226_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
default: 
{
lean_object* v_impl_4371_; lean_object* v___x_4372_; 
lean_dec(v_size_4222_);
v_impl_4371_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_4219_, v_v_4220_, v_r_4226_);
v___x_4372_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4225_) == 0)
{
lean_object* v_size_4373_; lean_object* v_size_4374_; lean_object* v_k_4375_; lean_object* v_v_4376_; lean_object* v_l_4377_; lean_object* v_r_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; uint8_t v___x_4381_; 
v_size_4373_ = lean_ctor_get(v_l_4225_, 0);
v_size_4374_ = lean_ctor_get(v_impl_4371_, 0);
lean_inc(v_size_4374_);
v_k_4375_ = lean_ctor_get(v_impl_4371_, 1);
lean_inc(v_k_4375_);
v_v_4376_ = lean_ctor_get(v_impl_4371_, 2);
lean_inc(v_v_4376_);
v_l_4377_ = lean_ctor_get(v_impl_4371_, 3);
lean_inc(v_l_4377_);
v_r_4378_ = lean_ctor_get(v_impl_4371_, 4);
lean_inc(v_r_4378_);
v___x_4379_ = lean_unsigned_to_nat(3u);
v___x_4380_ = lean_nat_mul(v___x_4379_, v_size_4373_);
v___x_4381_ = lean_nat_dec_lt(v___x_4380_, v_size_4374_);
lean_dec(v___x_4380_);
if (v___x_4381_ == 0)
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4385_; 
lean_dec(v_r_4378_);
lean_dec(v_l_4377_);
lean_dec(v_v_4376_);
lean_dec(v_k_4375_);
v___x_4382_ = lean_nat_add(v___x_4372_, v_size_4373_);
v___x_4383_ = lean_nat_add(v___x_4382_, v_size_4374_);
lean_dec(v_size_4374_);
lean_dec(v___x_4382_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 4, v_impl_4371_);
lean_ctor_set(v___x_4228_, 0, v___x_4383_);
v___x_4385_ = v___x_4228_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4383_);
lean_ctor_set(v_reuseFailAlloc_4386_, 1, v_k_4223_);
lean_ctor_set(v_reuseFailAlloc_4386_, 2, v_v_4224_);
lean_ctor_set(v_reuseFailAlloc_4386_, 3, v_l_4225_);
lean_ctor_set(v_reuseFailAlloc_4386_, 4, v_impl_4371_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
else
{
lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4450_; 
v_isSharedCheck_4450_ = !lean_is_exclusive(v_impl_4371_);
if (v_isSharedCheck_4450_ == 0)
{
lean_object* v_unused_4451_; lean_object* v_unused_4452_; lean_object* v_unused_4453_; lean_object* v_unused_4454_; lean_object* v_unused_4455_; 
v_unused_4451_ = lean_ctor_get(v_impl_4371_, 4);
lean_dec(v_unused_4451_);
v_unused_4452_ = lean_ctor_get(v_impl_4371_, 3);
lean_dec(v_unused_4452_);
v_unused_4453_ = lean_ctor_get(v_impl_4371_, 2);
lean_dec(v_unused_4453_);
v_unused_4454_ = lean_ctor_get(v_impl_4371_, 1);
lean_dec(v_unused_4454_);
v_unused_4455_ = lean_ctor_get(v_impl_4371_, 0);
lean_dec(v_unused_4455_);
v___x_4388_ = v_impl_4371_;
v_isShared_4389_ = v_isSharedCheck_4450_;
goto v_resetjp_4387_;
}
else
{
lean_dec(v_impl_4371_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4450_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v_size_4390_; lean_object* v_k_4391_; lean_object* v_v_4392_; lean_object* v_l_4393_; lean_object* v_r_4394_; lean_object* v_size_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; uint8_t v___x_4398_; 
v_size_4390_ = lean_ctor_get(v_l_4377_, 0);
v_k_4391_ = lean_ctor_get(v_l_4377_, 1);
v_v_4392_ = lean_ctor_get(v_l_4377_, 2);
v_l_4393_ = lean_ctor_get(v_l_4377_, 3);
v_r_4394_ = lean_ctor_get(v_l_4377_, 4);
v_size_4395_ = lean_ctor_get(v_r_4378_, 0);
v___x_4396_ = lean_unsigned_to_nat(2u);
v___x_4397_ = lean_nat_mul(v___x_4396_, v_size_4395_);
v___x_4398_ = lean_nat_dec_lt(v_size_4390_, v___x_4397_);
lean_dec(v___x_4397_);
if (v___x_4398_ == 0)
{
lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4426_; 
lean_inc(v_r_4394_);
lean_inc(v_l_4393_);
lean_inc(v_v_4392_);
lean_inc(v_k_4391_);
v_isSharedCheck_4426_ = !lean_is_exclusive(v_l_4377_);
if (v_isSharedCheck_4426_ == 0)
{
lean_object* v_unused_4427_; lean_object* v_unused_4428_; lean_object* v_unused_4429_; lean_object* v_unused_4430_; lean_object* v_unused_4431_; 
v_unused_4427_ = lean_ctor_get(v_l_4377_, 4);
lean_dec(v_unused_4427_);
v_unused_4428_ = lean_ctor_get(v_l_4377_, 3);
lean_dec(v_unused_4428_);
v_unused_4429_ = lean_ctor_get(v_l_4377_, 2);
lean_dec(v_unused_4429_);
v_unused_4430_ = lean_ctor_get(v_l_4377_, 1);
lean_dec(v_unused_4430_);
v_unused_4431_ = lean_ctor_get(v_l_4377_, 0);
lean_dec(v_unused_4431_);
v___x_4400_ = v_l_4377_;
v_isShared_4401_ = v_isSharedCheck_4426_;
goto v_resetjp_4399_;
}
else
{
lean_dec(v_l_4377_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4426_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4416_; 
v___x_4402_ = lean_nat_add(v___x_4372_, v_size_4373_);
v___x_4403_ = lean_nat_add(v___x_4402_, v_size_4374_);
lean_dec(v_size_4374_);
if (lean_obj_tag(v_l_4393_) == 0)
{
lean_object* v_size_4424_; 
v_size_4424_ = lean_ctor_get(v_l_4393_, 0);
lean_inc(v_size_4424_);
v___y_4416_ = v_size_4424_;
goto v___jp_4415_;
}
else
{
lean_object* v___x_4425_; 
v___x_4425_ = lean_unsigned_to_nat(0u);
v___y_4416_ = v___x_4425_;
goto v___jp_4415_;
}
v___jp_4404_:
{
lean_object* v___x_4408_; lean_object* v___x_4410_; 
v___x_4408_ = lean_nat_add(v___y_4405_, v___y_4407_);
lean_dec(v___y_4407_);
lean_dec(v___y_4405_);
if (v_isShared_4401_ == 0)
{
lean_ctor_set(v___x_4400_, 4, v_r_4378_);
lean_ctor_set(v___x_4400_, 3, v_r_4394_);
lean_ctor_set(v___x_4400_, 2, v_v_4376_);
lean_ctor_set(v___x_4400_, 1, v_k_4375_);
lean_ctor_set(v___x_4400_, 0, v___x_4408_);
v___x_4410_ = v___x_4400_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4408_);
lean_ctor_set(v_reuseFailAlloc_4414_, 1, v_k_4375_);
lean_ctor_set(v_reuseFailAlloc_4414_, 2, v_v_4376_);
lean_ctor_set(v_reuseFailAlloc_4414_, 3, v_r_4394_);
lean_ctor_set(v_reuseFailAlloc_4414_, 4, v_r_4378_);
v___x_4410_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
lean_object* v___x_4412_; 
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 4, v___x_4410_);
lean_ctor_set(v___x_4388_, 3, v___y_4406_);
lean_ctor_set(v___x_4388_, 2, v_v_4392_);
lean_ctor_set(v___x_4388_, 1, v_k_4391_);
lean_ctor_set(v___x_4388_, 0, v___x_4403_);
v___x_4412_ = v___x_4388_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4403_);
lean_ctor_set(v_reuseFailAlloc_4413_, 1, v_k_4391_);
lean_ctor_set(v_reuseFailAlloc_4413_, 2, v_v_4392_);
lean_ctor_set(v_reuseFailAlloc_4413_, 3, v___y_4406_);
lean_ctor_set(v_reuseFailAlloc_4413_, 4, v___x_4410_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
v___jp_4415_:
{
lean_object* v___x_4417_; lean_object* v___x_4419_; 
v___x_4417_ = lean_nat_add(v___x_4402_, v___y_4416_);
lean_dec(v___y_4416_);
lean_dec(v___x_4402_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 4, v_l_4393_);
lean_ctor_set(v___x_4228_, 0, v___x_4417_);
v___x_4419_ = v___x_4228_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4417_);
lean_ctor_set(v_reuseFailAlloc_4423_, 1, v_k_4223_);
lean_ctor_set(v_reuseFailAlloc_4423_, 2, v_v_4224_);
lean_ctor_set(v_reuseFailAlloc_4423_, 3, v_l_4225_);
lean_ctor_set(v_reuseFailAlloc_4423_, 4, v_l_4393_);
v___x_4419_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
lean_object* v___x_4420_; 
v___x_4420_ = lean_nat_add(v___x_4372_, v_size_4395_);
if (lean_obj_tag(v_r_4394_) == 0)
{
lean_object* v_size_4421_; 
v_size_4421_ = lean_ctor_get(v_r_4394_, 0);
lean_inc(v_size_4421_);
v___y_4405_ = v___x_4420_;
v___y_4406_ = v___x_4419_;
v___y_4407_ = v_size_4421_;
goto v___jp_4404_;
}
else
{
lean_object* v___x_4422_; 
v___x_4422_ = lean_unsigned_to_nat(0u);
v___y_4405_ = v___x_4420_;
v___y_4406_ = v___x_4419_;
v___y_4407_ = v___x_4422_;
goto v___jp_4404_;
}
}
}
}
}
else
{
lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4436_; 
lean_del_object(v___x_4228_);
v___x_4432_ = lean_nat_add(v___x_4372_, v_size_4373_);
v___x_4433_ = lean_nat_add(v___x_4432_, v_size_4374_);
lean_dec(v_size_4374_);
v___x_4434_ = lean_nat_add(v___x_4432_, v_size_4390_);
lean_dec(v___x_4432_);
lean_inc_ref(v_l_4225_);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 4, v_l_4377_);
lean_ctor_set(v___x_4388_, 3, v_l_4225_);
lean_ctor_set(v___x_4388_, 2, v_v_4224_);
lean_ctor_set(v___x_4388_, 1, v_k_4223_);
lean_ctor_set(v___x_4388_, 0, v___x_4434_);
v___x_4436_ = v___x_4388_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4434_);
lean_ctor_set(v_reuseFailAlloc_4449_, 1, v_k_4223_);
lean_ctor_set(v_reuseFailAlloc_4449_, 2, v_v_4224_);
lean_ctor_set(v_reuseFailAlloc_4449_, 3, v_l_4225_);
lean_ctor_set(v_reuseFailAlloc_4449_, 4, v_l_4377_);
v___x_4436_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
v_isSharedCheck_4443_ = !lean_is_exclusive(v_l_4225_);
if (v_isSharedCheck_4443_ == 0)
{
lean_object* v_unused_4444_; lean_object* v_unused_4445_; lean_object* v_unused_4446_; lean_object* v_unused_4447_; lean_object* v_unused_4448_; 
v_unused_4444_ = lean_ctor_get(v_l_4225_, 4);
lean_dec(v_unused_4444_);
v_unused_4445_ = lean_ctor_get(v_l_4225_, 3);
lean_dec(v_unused_4445_);
v_unused_4446_ = lean_ctor_get(v_l_4225_, 2);
lean_dec(v_unused_4446_);
v_unused_4447_ = lean_ctor_get(v_l_4225_, 1);
lean_dec(v_unused_4447_);
v_unused_4448_ = lean_ctor_get(v_l_4225_, 0);
lean_dec(v_unused_4448_);
v___x_4438_ = v_l_4225_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_dec(v_l_4225_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 4, v_r_4378_);
lean_ctor_set(v___x_4438_, 3, v___x_4436_);
lean_ctor_set(v___x_4438_, 2, v_v_4376_);
lean_ctor_set(v___x_4438_, 1, v_k_4375_);
lean_ctor_set(v___x_4438_, 0, v___x_4433_);
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4433_);
lean_ctor_set(v_reuseFailAlloc_4442_, 1, v_k_4375_);
lean_ctor_set(v_reuseFailAlloc_4442_, 2, v_v_4376_);
lean_ctor_set(v_reuseFailAlloc_4442_, 3, v___x_4436_);
lean_ctor_set(v_reuseFailAlloc_4442_, 4, v_r_4378_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4456_; 
v_l_4456_ = lean_ctor_get(v_impl_4371_, 3);
lean_inc(v_l_4456_);
if (lean_obj_tag(v_l_4456_) == 0)
{
lean_object* v_r_4457_; lean_object* v_k_4458_; lean_object* v_v_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4482_; 
v_r_4457_ = lean_ctor_get(v_impl_4371_, 4);
v_k_4458_ = lean_ctor_get(v_impl_4371_, 1);
v_v_4459_ = lean_ctor_get(v_impl_4371_, 2);
v_isSharedCheck_4482_ = !lean_is_exclusive(v_impl_4371_);
if (v_isSharedCheck_4482_ == 0)
{
lean_object* v_unused_4483_; lean_object* v_unused_4484_; 
v_unused_4483_ = lean_ctor_get(v_impl_4371_, 3);
lean_dec(v_unused_4483_);
v_unused_4484_ = lean_ctor_get(v_impl_4371_, 0);
lean_dec(v_unused_4484_);
v___x_4461_ = v_impl_4371_;
v_isShared_4462_ = v_isSharedCheck_4482_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_r_4457_);
lean_inc(v_v_4459_);
lean_inc(v_k_4458_);
lean_dec(v_impl_4371_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4482_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v_k_4463_; lean_object* v_v_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4478_; 
v_k_4463_ = lean_ctor_get(v_l_4456_, 1);
v_v_4464_ = lean_ctor_get(v_l_4456_, 2);
v_isSharedCheck_4478_ = !lean_is_exclusive(v_l_4456_);
if (v_isSharedCheck_4478_ == 0)
{
lean_object* v_unused_4479_; lean_object* v_unused_4480_; lean_object* v_unused_4481_; 
v_unused_4479_ = lean_ctor_get(v_l_4456_, 4);
lean_dec(v_unused_4479_);
v_unused_4480_ = lean_ctor_get(v_l_4456_, 3);
lean_dec(v_unused_4480_);
v_unused_4481_ = lean_ctor_get(v_l_4456_, 0);
lean_dec(v_unused_4481_);
v___x_4466_ = v_l_4456_;
v_isShared_4467_ = v_isSharedCheck_4478_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_v_4464_);
lean_inc(v_k_4463_);
lean_dec(v_l_4456_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4478_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v___x_4468_; lean_object* v___x_4470_; 
v___x_4468_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4457_, 2);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 4, v_r_4457_);
lean_ctor_set(v___x_4466_, 3, v_r_4457_);
lean_ctor_set(v___x_4466_, 2, v_v_4224_);
lean_ctor_set(v___x_4466_, 1, v_k_4223_);
lean_ctor_set(v___x_4466_, 0, v___x_4372_);
v___x_4470_ = v___x_4466_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v_k_4223_);
lean_ctor_set(v_reuseFailAlloc_4477_, 2, v_v_4224_);
lean_ctor_set(v_reuseFailAlloc_4477_, 3, v_r_4457_);
lean_ctor_set(v_reuseFailAlloc_4477_, 4, v_r_4457_);
v___x_4470_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
lean_object* v___x_4472_; 
lean_inc(v_r_4457_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 3, v_r_4457_);
lean_ctor_set(v___x_4461_, 0, v___x_4372_);
v___x_4472_ = v___x_4461_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4476_, 1, v_k_4458_);
lean_ctor_set(v_reuseFailAlloc_4476_, 2, v_v_4459_);
lean_ctor_set(v_reuseFailAlloc_4476_, 3, v_r_4457_);
lean_ctor_set(v_reuseFailAlloc_4476_, 4, v_r_4457_);
v___x_4472_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
lean_object* v___x_4474_; 
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 4, v___x_4472_);
lean_ctor_set(v___x_4228_, 3, v___x_4470_);
lean_ctor_set(v___x_4228_, 2, v_v_4464_);
lean_ctor_set(v___x_4228_, 1, v_k_4463_);
lean_ctor_set(v___x_4228_, 0, v___x_4468_);
v___x_4474_ = v___x_4228_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4475_, 1, v_k_4463_);
lean_ctor_set(v_reuseFailAlloc_4475_, 2, v_v_4464_);
lean_ctor_set(v_reuseFailAlloc_4475_, 3, v___x_4470_);
lean_ctor_set(v_reuseFailAlloc_4475_, 4, v___x_4472_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
}
}
}
else
{
lean_object* v_r_4485_; 
v_r_4485_ = lean_ctor_get(v_impl_4371_, 4);
lean_inc(v_r_4485_);
if (lean_obj_tag(v_r_4485_) == 0)
{
lean_object* v_k_4486_; lean_object* v_v_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4498_; 
v_k_4486_ = lean_ctor_get(v_impl_4371_, 1);
v_v_4487_ = lean_ctor_get(v_impl_4371_, 2);
v_isSharedCheck_4498_ = !lean_is_exclusive(v_impl_4371_);
if (v_isSharedCheck_4498_ == 0)
{
lean_object* v_unused_4499_; lean_object* v_unused_4500_; lean_object* v_unused_4501_; 
v_unused_4499_ = lean_ctor_get(v_impl_4371_, 4);
lean_dec(v_unused_4499_);
v_unused_4500_ = lean_ctor_get(v_impl_4371_, 3);
lean_dec(v_unused_4500_);
v_unused_4501_ = lean_ctor_get(v_impl_4371_, 0);
lean_dec(v_unused_4501_);
v___x_4489_ = v_impl_4371_;
v_isShared_4490_ = v_isSharedCheck_4498_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_v_4487_);
lean_inc(v_k_4486_);
lean_dec(v_impl_4371_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4498_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4491_; lean_object* v___x_4493_; 
v___x_4491_ = lean_unsigned_to_nat(3u);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 4, v_l_4456_);
lean_ctor_set(v___x_4489_, 2, v_v_4224_);
lean_ctor_set(v___x_4489_, 1, v_k_4223_);
lean_ctor_set(v___x_4489_, 0, v___x_4372_);
v___x_4493_ = v___x_4489_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v_k_4223_);
lean_ctor_set(v_reuseFailAlloc_4497_, 2, v_v_4224_);
lean_ctor_set(v_reuseFailAlloc_4497_, 3, v_l_4456_);
lean_ctor_set(v_reuseFailAlloc_4497_, 4, v_l_4456_);
v___x_4493_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4495_; 
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 4, v_r_4485_);
lean_ctor_set(v___x_4228_, 3, v___x_4493_);
lean_ctor_set(v___x_4228_, 2, v_v_4487_);
lean_ctor_set(v___x_4228_, 1, v_k_4486_);
lean_ctor_set(v___x_4228_, 0, v___x_4491_);
v___x_4495_ = v___x_4228_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4491_);
lean_ctor_set(v_reuseFailAlloc_4496_, 1, v_k_4486_);
lean_ctor_set(v_reuseFailAlloc_4496_, 2, v_v_4487_);
lean_ctor_set(v_reuseFailAlloc_4496_, 3, v___x_4493_);
lean_ctor_set(v_reuseFailAlloc_4496_, 4, v_r_4485_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
else
{
lean_object* v___x_4502_; lean_object* v___x_4504_; 
v___x_4502_ = lean_unsigned_to_nat(2u);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 4, v_impl_4371_);
lean_ctor_set(v___x_4228_, 3, v_r_4485_);
lean_ctor_set(v___x_4228_, 0, v___x_4502_);
v___x_4504_ = v___x_4228_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
lean_ctor_set(v_reuseFailAlloc_4505_, 1, v_k_4223_);
lean_ctor_set(v_reuseFailAlloc_4505_, 2, v_v_4224_);
lean_ctor_set(v_reuseFailAlloc_4505_, 3, v_r_4485_);
lean_ctor_set(v_reuseFailAlloc_4505_, 4, v_impl_4371_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
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
lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4507_ = lean_unsigned_to_nat(1u);
v___x_4508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4507_);
lean_ctor_set(v___x_4508_, 1, v_k_4219_);
lean_ctor_set(v___x_4508_, 2, v_v_4220_);
lean_ctor_set(v___x_4508_, 3, v_t_4221_);
lean_ctor_set(v___x_4508_, 4, v_t_4221_);
return v___x_4508_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(lean_object* v_init_4510_, lean_object* v_x_4511_){
_start:
{
lean_object* v_d_4514_; 
if (lean_obj_tag(v_x_4511_) == 0)
{
lean_object* v_k_4517_; lean_object* v_v_4518_; lean_object* v_l_4519_; lean_object* v_r_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v_k_4517_ = lean_ctor_get(v_x_4511_, 1);
v_v_4518_ = lean_ctor_get(v_x_4511_, 2);
v_l_4519_ = lean_ctor_get(v_x_4511_, 3);
v_r_4520_ = lean_ctor_get(v_x_4511_, 4);
v___x_4521_ = lean_box(0);
v___x_4522_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_4523_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v_init_4510_, v_l_4519_);
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4559_; 
v_a_4524_ = lean_ctor_get(v___x_4523_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4526_ = v___x_4523_;
v_isShared_4527_ = v_isSharedCheck_4559_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4523_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4559_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
if (lean_obj_tag(v_a_4524_) == 0)
{
lean_object* v_a_4528_; 
lean_del_object(v___x_4526_);
v_a_4528_ = lean_ctor_get(v_a_4524_, 0);
lean_inc(v_a_4528_);
lean_dec_ref_known(v_a_4524_, 1);
v_d_4514_ = v_a_4528_;
goto v___jp_4513_;
}
else
{
lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4557_; 
v_isSharedCheck_4557_ = !lean_is_exclusive(v_a_4524_);
if (v_isSharedCheck_4557_ == 0)
{
lean_object* v_unused_4558_; 
v_unused_4558_ = lean_ctor_get(v_a_4524_, 0);
lean_dec(v_unused_4558_);
v___x_4530_ = v_a_4524_;
v_isShared_4531_ = v_isSharedCheck_4557_;
goto v_resetjp_4529_;
}
else
{
lean_dec(v_a_4524_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4557_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; uint8_t v___x_4534_; 
v___x_4532_ = lean_array_get_size(v_v_4518_);
v___x_4533_ = lean_unsigned_to_nat(0u);
v___x_4534_ = lean_nat_dec_eq(v___x_4532_, v___x_4533_);
if (v___x_4534_ == 0)
{
lean_del_object(v___x_4530_);
lean_del_object(v___x_4526_);
v_init_4510_ = v___x_4522_;
v_x_4511_ = v_r_4520_;
goto _start;
}
else
{
lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4536_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1));
v___x_4537_ = lean_string_append(v___x_4536_, v_k_4517_);
v___x_4538_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___closed__0));
v___x_4539_ = lean_string_append(v___x_4537_, v___x_4538_);
v___x_4540_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4539_);
lean_dec_ref(v___x_4539_);
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4543_; 
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
lean_inc(v_a_4541_);
lean_dec_ref_known(v___x_4540_, 1);
if (v_isShared_4531_ == 0)
{
lean_ctor_set_tag(v___x_4530_, 0);
lean_ctor_set(v___x_4530_, 0, v_a_4541_);
v___x_4543_ = v___x_4530_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4541_);
v___x_4543_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
lean_object* v___x_4545_; 
if (v_isShared_4527_ == 0)
{
lean_ctor_set_tag(v___x_4526_, 1);
lean_ctor_set(v___x_4526_, 0, v___x_4543_);
v___x_4545_ = v___x_4526_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v___x_4543_);
v___x_4545_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
lean_object* v___x_4546_; 
v___x_4546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4545_);
lean_ctor_set(v___x_4546_, 1, v___x_4521_);
v_d_4514_ = v___x_4546_;
goto v___jp_4513_;
}
}
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
lean_del_object(v___x_4530_);
lean_del_object(v___x_4526_);
v_a_4549_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4551_ = v___x_4540_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4540_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
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
return v___x_4523_;
}
}
else
{
lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4560_, 0, v_init_4510_);
v___x_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
return v___x_4561_;
}
v___jp_4513_:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4515_, 0, v_d_4514_);
v___x_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
return v___x_4516_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___boxed(lean_object* v_init_4562_, lean_object* v_x_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v_res_4565_; 
v_res_4565_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v_init_4562_, v_x_4563_);
lean_dec(v_x_4563_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(lean_object* v_cfg_4573_){
_start:
{
lean_object* v___y_4576_; lean_object* v_a_4577_; lean_object* v___y_4590_; lean_object* v_externalKernels_4591_; uint8_t v___y_4604_; lean_object* v___y_4605_; lean_object* v___y_4606_; lean_object* v_a_4607_; uint8_t v___y_4621_; lean_object* v___y_4622_; lean_object* v_enable__nanoda_x3f_4635_; lean_object* v_external__kernels_x3f_4636_; lean_object* v___y_4638_; 
v_enable__nanoda_x3f_4635_ = lean_ctor_get(v_cfg_4573_, 5);
lean_inc(v_enable__nanoda_x3f_4635_);
v_external__kernels_x3f_4636_ = lean_ctor_get(v_cfg_4573_, 6);
lean_inc(v_external__kernels_x3f_4636_);
lean_dec_ref(v_cfg_4573_);
if (lean_obj_tag(v_external__kernels_x3f_4636_) == 0)
{
lean_object* v___x_4669_; 
v___x_4669_ = lean_box(1);
v___y_4638_ = v___x_4669_;
goto v___jp_4637_;
}
else
{
lean_object* v_val_4670_; 
v_val_4670_ = lean_ctor_get(v_external__kernels_x3f_4636_, 0);
lean_inc(v_val_4670_);
lean_dec_ref_known(v_external__kernels_x3f_4636_, 1);
v___y_4638_ = v_val_4670_;
goto v___jp_4637_;
}
v___jp_4575_:
{
lean_object* v_fst_4578_; 
v_fst_4578_ = lean_ctor_get(v_a_4577_, 0);
lean_inc(v_fst_4578_);
lean_dec_ref(v_a_4577_);
if (lean_obj_tag(v_fst_4578_) == 0)
{
lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___y_4576_);
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
return v___x_4580_;
}
else
{
lean_object* v_val_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4588_; 
lean_dec(v___y_4576_);
v_val_4581_ = lean_ctor_get(v_fst_4578_, 0);
v_isSharedCheck_4588_ = !lean_is_exclusive(v_fst_4578_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4583_ = v_fst_4578_;
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_val_4581_);
lean_dec(v_fst_4578_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4586_; 
if (v_isShared_4584_ == 0)
{
lean_ctor_set_tag(v___x_4583_, 0);
v___x_4586_ = v___x_4583_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_val_4581_);
v___x_4586_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
return v___x_4586_;
}
}
}
}
v___jp_4589_:
{
lean_object* v___x_4592_; 
v___x_4592_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v___y_4590_, v_externalKernels_4591_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_object* v_a_4593_; lean_object* v_a_4594_; 
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_a_4593_);
lean_dec_ref_known(v___x_4592_, 1);
v_a_4594_ = lean_ctor_get(v_a_4593_, 0);
lean_inc(v_a_4594_);
lean_dec(v_a_4593_);
v___y_4576_ = v_externalKernels_4591_;
v_a_4577_ = v_a_4594_;
goto v___jp_4575_;
}
else
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4602_; 
lean_dec(v_externalKernels_4591_);
v_a_4595_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4597_ = v___x_4592_;
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v___x_4592_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4600_; 
if (v_isShared_4598_ == 0)
{
v___x_4600_ = v___x_4597_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4595_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
}
v___jp_4603_:
{
lean_object* v_fst_4608_; 
v_fst_4608_ = lean_ctor_get(v_a_4607_, 0);
lean_inc(v_fst_4608_);
lean_dec_ref(v_a_4607_);
if (lean_obj_tag(v_fst_4608_) == 0)
{
if (v___y_4604_ == 0)
{
v___y_4590_ = v___y_4605_;
v_externalKernels_4591_ = v___y_4606_;
goto v___jp_4589_;
}
else
{
lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4609_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0));
v___x_4610_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__2));
v___x_4611_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v___x_4609_, v___x_4610_, v___y_4606_);
v___y_4590_ = v___y_4605_;
v_externalKernels_4591_ = v___x_4611_;
goto v___jp_4589_;
}
}
else
{
lean_object* v_val_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4619_; 
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
v_val_4612_ = lean_ctor_get(v_fst_4608_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v_fst_4608_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4614_ = v_fst_4608_;
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_val_4612_);
lean_dec(v_fst_4608_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4617_; 
if (v_isShared_4615_ == 0)
{
lean_ctor_set_tag(v___x_4614_, 0);
v___x_4617_ = v___x_4614_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_val_4612_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
}
v___jp_4620_:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_4624_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v___x_4623_, v___y_4622_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v_a_4626_; 
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_a_4625_);
lean_dec_ref_known(v___x_4624_, 1);
v_a_4626_ = lean_ctor_get(v_a_4625_, 0);
lean_inc(v_a_4626_);
lean_dec(v_a_4625_);
v___y_4604_ = v___y_4621_;
v___y_4605_ = v___x_4623_;
v___y_4606_ = v___y_4622_;
v_a_4607_ = v_a_4626_;
goto v___jp_4603_;
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4634_; 
lean_dec(v___y_4622_);
v_a_4627_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4624_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4624_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4632_; 
if (v_isShared_4630_ == 0)
{
v___x_4632_ = v___x_4629_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4627_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
v___jp_4637_:
{
if (lean_obj_tag(v_enable__nanoda_x3f_4635_) == 0)
{
uint8_t v___x_4639_; 
v___x_4639_ = 0;
v___y_4621_ = v___x_4639_;
v___y_4622_ = v___y_4638_;
goto v___jp_4620_;
}
else
{
lean_object* v_val_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4668_; 
v_val_4640_ = lean_ctor_get(v_enable__nanoda_x3f_4635_, 0);
v_isSharedCheck_4668_ = !lean_is_exclusive(v_enable__nanoda_x3f_4635_);
if (v_isSharedCheck_4668_ == 0)
{
v___x_4642_ = v_enable__nanoda_x3f_4635_;
v_isShared_4643_ = v_isSharedCheck_4668_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_val_4640_);
lean_dec(v_enable__nanoda_x3f_4635_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4668_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
uint8_t v___x_4644_; 
v___x_4644_ = lean_unbox(v_val_4640_);
if (v___x_4644_ == 0)
{
uint8_t v___x_4645_; 
lean_del_object(v___x_4642_);
v___x_4645_ = lean_unbox(v_val_4640_);
lean_dec(v_val_4640_);
v___y_4621_ = v___x_4645_;
v___y_4622_ = v___y_4638_;
goto v___jp_4620_;
}
else
{
if (lean_obj_tag(v___y_4638_) == 0)
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
lean_dec_ref_known(v___y_4638_, 5);
lean_dec(v_val_4640_);
v___x_4646_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__3));
v___x_4647_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4646_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4658_; 
v_a_4648_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4650_ = v___x_4647_;
v_isShared_4651_ = v_isSharedCheck_4658_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4647_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4658_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4653_; 
if (v_isShared_4643_ == 0)
{
lean_ctor_set_tag(v___x_4642_, 0);
lean_ctor_set(v___x_4642_, 0, v_a_4648_);
v___x_4653_ = v___x_4642_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4648_);
v___x_4653_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
lean_object* v___x_4655_; 
if (v_isShared_4651_ == 0)
{
lean_ctor_set(v___x_4650_, 0, v___x_4653_);
v___x_4655_ = v___x_4650_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v___x_4653_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
else
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4666_; 
lean_del_object(v___x_4642_);
v_a_4659_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4661_ = v___x_4647_;
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4647_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4664_; 
if (v_isShared_4662_ == 0)
{
v___x_4664_ = v___x_4661_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_a_4659_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
}
else
{
uint8_t v___x_4667_; 
lean_del_object(v___x_4642_);
v___x_4667_ = lean_unbox(v_val_4640_);
lean_dec(v_val_4640_);
v___y_4621_ = v___x_4667_;
v___y_4622_ = v___y_4638_;
goto v___jp_4620_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___boxed(lean_object* v_cfg_4671_, lean_object* v_a_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v_cfg_4671_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(lean_object* v_00_u03b2_4674_, lean_object* v_k_4675_, lean_object* v_v_4676_, lean_object* v_t_4677_, lean_object* v_hl_4678_){
_start:
{
lean_object* v___x_4679_; 
v___x_4679_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_4675_, v_v_4676_, v_t_4677_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(lean_object* v_a_4697_, lean_object* v_a_4698_){
_start:
{
if (lean_obj_tag(v_a_4697_) == 0)
{
lean_object* v___x_4699_; 
v___x_4699_ = l_List_reverse___redArg(v_a_4698_);
return v___x_4699_;
}
else
{
lean_object* v_head_4700_; lean_object* v_tail_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4712_; 
v_head_4700_ = lean_ctor_get(v_a_4697_, 0);
v_tail_4701_ = lean_ctor_get(v_a_4697_, 1);
v_isSharedCheck_4712_ = !lean_is_exclusive(v_a_4697_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4703_ = v_a_4697_;
v_isShared_4704_ = v_isSharedCheck_4712_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_tail_4701_);
lean_inc(v_head_4700_);
lean_dec(v_a_4697_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4712_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v_fst_4705_; uint8_t v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4709_; 
v_fst_4705_ = lean_ctor_get(v_head_4700_, 0);
lean_inc(v_fst_4705_);
lean_dec(v_head_4700_);
v___x_4706_ = 1;
v___x_4707_ = l_Lean_Name_toString(v_fst_4705_, v___x_4706_);
if (v_isShared_4704_ == 0)
{
lean_ctor_set(v___x_4703_, 1, v_a_4698_);
lean_ctor_set(v___x_4703_, 0, v___x_4707_);
v___x_4709_ = v___x_4703_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v___x_4707_);
lean_ctor_set(v_reuseFailAlloc_4711_, 1, v_a_4698_);
v___x_4709_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
v_a_4697_ = v_tail_4701_;
v_a_4698_ = v___x_4709_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(lean_object* v_as_4713_, size_t v_i_4714_, size_t v_stop_4715_, lean_object* v_b_4716_){
_start:
{
lean_object* v___y_4718_; uint8_t v___x_4722_; 
v___x_4722_ = lean_usize_dec_eq(v_i_4714_, v_stop_4715_);
if (v___x_4722_ == 0)
{
lean_object* v___x_4723_; lean_object* v_fst_4724_; lean_object* v___x_4725_; uint8_t v___x_4726_; 
v___x_4723_ = lean_array_uget_borrowed(v_as_4713_, v_i_4714_);
v_fst_4724_ = lean_ctor_get(v___x_4723_, 0);
v___x_4725_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms));
v___x_4726_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v___x_4725_, v_fst_4724_);
if (v___x_4726_ == 0)
{
lean_object* v___x_4727_; 
lean_inc(v___x_4723_);
v___x_4727_ = lean_array_push(v_b_4716_, v___x_4723_);
v___y_4718_ = v___x_4727_;
goto v___jp_4717_;
}
else
{
v___y_4718_ = v_b_4716_;
goto v___jp_4717_;
}
}
else
{
return v_b_4716_;
}
v___jp_4717_:
{
size_t v___x_4719_; size_t v___x_4720_; 
v___x_4719_ = ((size_t)1ULL);
v___x_4720_ = lean_usize_add(v_i_4714_, v___x_4719_);
v_i_4714_ = v___x_4720_;
v_b_4716_ = v___y_4718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1___boxed(lean_object* v_as_4728_, lean_object* v_i_4729_, lean_object* v_stop_4730_, lean_object* v_b_4731_){
_start:
{
size_t v_i_boxed_4732_; size_t v_stop_boxed_4733_; lean_object* v_res_4734_; 
v_i_boxed_4732_ = lean_unbox_usize(v_i_4729_);
lean_dec(v_i_4729_);
v_stop_boxed_4733_ = lean_unbox_usize(v_stop_4730_);
lean_dec(v_stop_4730_);
v_res_4734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_as_4728_, v_i_boxed_4732_, v_stop_boxed_4733_, v_b_4731_);
lean_dec_ref(v_as_4728_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(lean_object* v_a_4737_, lean_object* v_a_4738_){
_start:
{
if (lean_obj_tag(v_a_4737_) == 0)
{
lean_object* v___x_4739_; 
v___x_4739_ = l_List_reverse___redArg(v_a_4738_);
return v___x_4739_;
}
else
{
lean_object* v_head_4740_; lean_object* v_tail_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4761_; 
v_head_4740_ = lean_ctor_get(v_a_4737_, 0);
v_tail_4741_ = lean_ctor_get(v_a_4737_, 1);
v_isSharedCheck_4761_ = !lean_is_exclusive(v_a_4737_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4743_ = v_a_4737_;
v_isShared_4744_ = v_isSharedCheck_4761_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_tail_4741_);
lean_inc(v_head_4740_);
lean_dec(v_a_4737_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4761_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v_fst_4745_; lean_object* v_snd_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4758_; 
v_fst_4745_ = lean_ctor_get(v_head_4740_, 0);
lean_inc(v_fst_4745_);
v_snd_4746_ = lean_ctor_get(v_head_4740_, 1);
lean_inc(v_snd_4746_);
lean_dec(v_head_4740_);
v___x_4747_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__0));
v___x_4748_ = 1;
v___x_4749_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_4745_, v___x_4748_);
v___x_4750_ = lean_string_append(v___x_4747_, v___x_4749_);
lean_dec_ref(v___x_4749_);
v___x_4751_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__1));
v___x_4752_ = lean_string_append(v___x_4750_, v___x_4751_);
v___x_4753_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_snd_4746_, v___x_4748_);
v___x_4754_ = lean_string_append(v___x_4752_, v___x_4753_);
lean_dec_ref(v___x_4753_);
v___x_4755_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_4756_ = lean_string_append(v___x_4754_, v___x_4755_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 1, v_a_4738_);
lean_ctor_set(v___x_4743_, 0, v___x_4756_);
v___x_4758_ = v___x_4743_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v___x_4756_);
lean_ctor_set(v_reuseFailAlloc_4760_, 1, v_a_4738_);
v___x_4758_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
v_a_4737_ = v_tail_4741_;
v_a_4738_ = v___x_4758_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(lean_object* v_exported_4767_){
_start:
{
lean_object* v___y_4770_; lean_object* v_used_4783_; lean_object* v___x_4796_; lean_object* v___x_4797_; uint8_t v___x_4798_; 
v_used_4783_ = l_Lake_Check_usedAxioms(v_exported_4767_);
v___x_4796_ = lean_array_get_size(v_used_4783_);
v___x_4797_ = lean_unsigned_to_nat(0u);
v___x_4798_ = lean_nat_dec_eq(v___x_4796_, v___x_4797_);
if (v___x_4798_ == 0)
{
lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4799_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__2));
v___x_4800_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0));
lean_inc_ref(v_used_4783_);
v___x_4801_ = lean_array_to_list(v_used_4783_);
v___x_4802_ = lean_box(0);
v___x_4803_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(v___x_4801_, v___x_4802_);
v___x_4804_ = l_String_intercalate(v___x_4800_, v___x_4803_);
v___x_4805_ = lean_string_append(v___x_4799_, v___x_4804_);
lean_dec_ref(v___x_4804_);
v___x_4806_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_4805_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_dec_ref_known(v___x_4806_, 1);
goto v___jp_4784_;
}
else
{
lean_dec_ref(v_used_4783_);
return v___x_4806_;
}
}
else
{
lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4807_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__3));
v___x_4808_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_4807_);
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_dec_ref_known(v___x_4808_, 1);
goto v___jp_4784_;
}
else
{
lean_dec_ref(v_used_4783_);
return v___x_4808_;
}
}
v___jp_4769_:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; uint8_t v___x_4773_; 
v___x_4771_ = lean_array_get_size(v___y_4770_);
v___x_4772_ = lean_unsigned_to_nat(0u);
v___x_4773_ = lean_nat_dec_eq(v___x_4771_, v___x_4772_);
if (v___x_4773_ == 0)
{
lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4774_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__0));
v___x_4775_ = lean_array_to_list(v___y_4770_);
v___x_4776_ = lean_box(0);
v___x_4777_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(v___x_4775_, v___x_4776_);
v___x_4778_ = l_String_intercalate(v___x_4774_, v___x_4777_);
v___x_4779_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_4779_, 0, v___x_4778_);
v___x_4780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
return v___x_4780_;
}
else
{
lean_object* v___x_4781_; lean_object* v___x_4782_; 
lean_dec_ref(v___y_4770_);
v___x_4781_ = lean_box(0);
v___x_4782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4781_);
return v___x_4782_;
}
}
v___jp_4784_:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; uint8_t v___x_4788_; 
v___x_4785_ = lean_unsigned_to_nat(0u);
v___x_4786_ = lean_array_get_size(v_used_4783_);
v___x_4787_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__1));
v___x_4788_ = lean_nat_dec_lt(v___x_4785_, v___x_4786_);
if (v___x_4788_ == 0)
{
lean_dec_ref(v_used_4783_);
v___y_4770_ = v___x_4787_;
goto v___jp_4769_;
}
else
{
uint8_t v___x_4789_; 
v___x_4789_ = lean_nat_dec_le(v___x_4786_, v___x_4786_);
if (v___x_4789_ == 0)
{
if (v___x_4788_ == 0)
{
lean_dec_ref(v_used_4783_);
v___y_4770_ = v___x_4787_;
goto v___jp_4769_;
}
else
{
size_t v___x_4790_; size_t v___x_4791_; lean_object* v___x_4792_; 
v___x_4790_ = ((size_t)0ULL);
v___x_4791_ = lean_usize_of_nat(v___x_4786_);
v___x_4792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_used_4783_, v___x_4790_, v___x_4791_, v___x_4787_);
lean_dec_ref(v_used_4783_);
v___y_4770_ = v___x_4792_;
goto v___jp_4769_;
}
}
else
{
size_t v___x_4793_; size_t v___x_4794_; lean_object* v___x_4795_; 
v___x_4793_ = ((size_t)0ULL);
v___x_4794_ = lean_usize_of_nat(v___x_4786_);
v___x_4795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_used_4783_, v___x_4793_, v___x_4794_, v___x_4787_);
lean_dec_ref(v_used_4783_);
v___y_4770_ = v___x_4795_;
goto v___jp_4769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___boxed(lean_object* v_exported_4809_, lean_object* v_a_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_4809_);
return v_res_4811_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(lean_object* v_exported_4812_, lean_object* v_a_4813_){
_start:
{
lean_object* v___x_4815_; 
v___x_4815_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_4812_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___boxed(lean_object* v_exported_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(v_exported_4816_, v_a_4817_);
lean_dec_ref(v_a_4817_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(lean_object* v_exportPath_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v___x_4823_; 
lean_inc_ref(v_exportPath_4820_);
v___x_4823_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_exportPath_4820_, v___y_4821_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4862_; 
v_a_4824_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4826_ = v___x_4823_;
v_isShared_4827_ = v_isSharedCheck_4862_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4823_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4862_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
if (lean_obj_tag(v_a_4824_) == 1)
{
lean_object* v_val_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4838_; 
lean_dec_ref(v_exportPath_4820_);
v_val_4828_ = lean_ctor_get(v_a_4824_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v_a_4824_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4830_ = v_a_4824_;
v_isShared_4831_ = v_isSharedCheck_4838_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_val_4828_);
lean_dec(v_a_4824_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4838_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
lean_ctor_set_tag(v___x_4830_, 18);
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_val_4828_);
v___x_4833_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
lean_object* v___x_4835_; 
if (v_isShared_4827_ == 0)
{
lean_ctor_set_tag(v___x_4826_, 1);
lean_ctor_set(v___x_4826_, 0, v___x_4833_);
v___x_4835_ = v___x_4826_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v___x_4833_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
}
else
{
uint8_t v___x_4839_; lean_object* v___x_4840_; 
lean_del_object(v___x_4826_);
lean_dec(v_a_4824_);
v___x_4839_ = 0;
v___x_4840_ = lean_io_prim_handle_mk(v_exportPath_4820_, v___x_4839_);
lean_dec_ref(v_exportPath_4820_);
if (lean_obj_tag(v___x_4840_) == 0)
{
lean_object* v_a_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v_a_4841_ = lean_ctor_get(v___x_4840_, 0);
lean_inc(v_a_4841_);
lean_dec_ref_known(v___x_4840_, 1);
v___x_4842_ = lean_stream_of_handle(v_a_4841_);
v___x_4843_ = l_LeanExport_parseStream(v___x_4842_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v_a_4844_; lean_object* v___x_4845_; 
v_a_4844_ = lean_ctor_get(v___x_4843_, 0);
lean_inc(v_a_4844_);
lean_dec_ref_known(v___x_4843_, 1);
v___x_4845_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_a_4844_);
return v___x_4845_;
}
else
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4853_; 
v_a_4846_ = lean_ctor_get(v___x_4843_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4848_ = v___x_4843_;
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4843_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4849_ == 0)
{
v___x_4851_ = v___x_4848_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4846_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
else
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4861_; 
v_a_4854_ = lean_ctor_get(v___x_4840_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4856_ = v___x_4840_;
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4840_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4859_; 
if (v_isShared_4857_ == 0)
{
v___x_4859_ = v___x_4856_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4854_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
}
}
}
}
}
}
else
{
lean_object* v_a_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4870_; 
lean_dec_ref(v_exportPath_4820_);
v_a_4863_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4865_ = v___x_4823_;
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_a_4863_);
lean_dec(v___x_4823_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4868_; 
if (v_isShared_4866_ == 0)
{
v___x_4868_ = v___x_4865_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0___boxed(lean_object* v_exportPath_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(v_exportPath_4871_, v___y_4872_);
lean_dec_ref(v___y_4872_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject(lean_object* v_a_4876_){
_start:
{
lean_object* v___f_4878_; lean_object* v___x_4879_; 
v___f_4878_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkProject___closed__0));
v___x_4879_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_4876_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v___x_4880_; 
lean_dec_ref_known(v___x_4879_, 1);
v___x_4880_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v___f_4878_, v_a_4876_);
return v___x_4880_;
}
else
{
return v___x_4879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___boxed(lean_object* v_a_4881_, lean_object* v_a_4882_){
_start:
{
lean_object* v_res_4883_; 
v_res_4883_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v_a_4881_);
lean_dec_ref(v_a_4881_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(size_t v_sz_4884_, size_t v_i_4885_, lean_object* v_bs_4886_){
_start:
{
uint8_t v___x_4887_; 
v___x_4887_ = lean_usize_dec_lt(v_i_4885_, v_sz_4884_);
if (v___x_4887_ == 0)
{
return v_bs_4886_;
}
else
{
lean_object* v_v_4888_; lean_object* v___x_4889_; lean_object* v_bs_x27_4890_; lean_object* v___x_4891_; size_t v___x_4892_; size_t v___x_4893_; lean_object* v___x_4894_; 
v_v_4888_ = lean_array_uget(v_bs_4886_, v_i_4885_);
v___x_4889_ = lean_unsigned_to_nat(0u);
v_bs_x27_4890_ = lean_array_uset(v_bs_4886_, v_i_4885_, v___x_4889_);
v___x_4891_ = l_String_toName(v_v_4888_);
v___x_4892_ = ((size_t)1ULL);
v___x_4893_ = lean_usize_add(v_i_4885_, v___x_4892_);
v___x_4894_ = lean_array_uset(v_bs_x27_4890_, v_i_4885_, v___x_4891_);
v_i_4885_ = v___x_4893_;
v_bs_4886_ = v___x_4894_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0___boxed(lean_object* v_sz_4896_, lean_object* v_i_4897_, lean_object* v_bs_4898_){
_start:
{
size_t v_sz_boxed_4899_; size_t v_i_boxed_4900_; lean_object* v_res_4901_; 
v_sz_boxed_4899_ = lean_unbox_usize(v_sz_4896_);
lean_dec(v_sz_4896_);
v_i_boxed_4900_ = lean_unbox_usize(v_i_4897_);
lean_dec(v_i_4897_);
v_res_4901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_boxed_4899_, v_i_boxed_4900_, v_bs_4898_);
return v_res_4901_;
}
}
static lean_object* _init_l_Lake_Check_runChallenge___boxed__const__1(void){
_start:
{
uint32_t v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = 1;
v___x_4909_ = lean_box_uint32(v___x_4908_);
return v___x_4909_;
}
}
static lean_object* _init_l_Lake_Check_runChallenge___boxed__const__2(void){
_start:
{
uint32_t v___x_4910_; lean_object* v___x_4911_; 
v___x_4910_ = 0;
v___x_4911_ = lean_box_uint32(v___x_4910_);
return v___x_4911_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runChallenge(lean_object* v_configFile_x3f_4912_, lean_object* v_lean_4913_, lean_object* v_lake_4914_, lean_object* v_projectDir_4915_){
_start:
{
lean_object* v_a_4918_; lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___x_4940_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__0));
v___x_4941_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_4940_, v_lean_4913_, v_lake_4914_, v_projectDir_4915_);
if (lean_obj_tag(v___x_4941_) == 0)
{
lean_object* v_a_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_5079_; 
v_a_4942_ = lean_ctor_get(v___x_4941_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_4941_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_4944_ = v___x_4941_;
v_isShared_4945_ = v_isSharedCheck_5079_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_a_4942_);
lean_dec(v___x_4941_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_5079_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
if (lean_obj_tag(v_a_4942_) == 0)
{
lean_object* v_a_4946_; lean_object* v___x_4948_; 
v_a_4946_ = lean_ctor_get(v_a_4942_, 0);
lean_inc(v_a_4946_);
lean_dec_ref_known(v_a_4942_, 1);
if (v_isShared_4945_ == 0)
{
lean_ctor_set(v___x_4944_, 0, v_a_4946_);
v___x_4948_ = v___x_4944_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_a_4946_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
}
}
else
{
lean_del_object(v___x_4944_);
if (lean_obj_tag(v_configFile_x3f_4912_) == 1)
{
lean_object* v_a_4950_; lean_object* v_val_4951_; lean_object* v___x_4952_; 
v_a_4950_ = lean_ctor_get(v_a_4942_, 0);
lean_inc(v_a_4950_);
lean_dec_ref_known(v_a_4942_, 1);
v_val_4951_ = lean_ctor_get(v_configFile_x3f_4912_, 0);
v___x_4952_ = l_IO_FS_readFile(v_val_4951_);
if (lean_obj_tag(v___x_4952_) == 0)
{
lean_object* v_a_4953_; lean_object* v_a_4955_; lean_object* v___x_4962_; 
v_a_4953_ = lean_ctor_get(v___x_4952_, 0);
lean_inc(v_a_4953_);
lean_dec_ref_known(v___x_4952_, 1);
v___x_4962_ = l_Lean_Json_parse(v_a_4953_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; 
lean_dec(v_a_4950_);
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_a_4963_);
lean_dec_ref_known(v___x_4962_, 1);
v_a_4955_ = v_a_4963_;
goto v___jp_4954_;
}
else
{
lean_object* v_a_4964_; lean_object* v___x_4965_; 
v_a_4964_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_a_4964_);
lean_dec_ref_known(v___x_4962_, 1);
v___x_4965_ = l_Lake_Check_instFromJsonConfig_fromJson(v_a_4964_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v_a_4966_; 
lean_dec(v_a_4950_);
v_a_4966_ = lean_ctor_get(v___x_4965_, 0);
lean_inc(v_a_4966_);
lean_dec_ref_known(v___x_4965_, 1);
v_a_4955_ = v_a_4966_;
goto v___jp_4954_;
}
else
{
lean_object* v_a_4967_; lean_object* v_challenge__module_4968_; lean_object* v_solution__module_4969_; lean_object* v_theorem__names_4970_; lean_object* v_definition__names_4971_; lean_object* v_permitted__axioms_4972_; size_t v_sz_4973_; size_t v___x_4974_; lean_object* v___x_4975_; lean_object* v___y_4977_; lean_object* v___y_5060_; 
v_a_4967_ = lean_ctor_get(v___x_4965_, 0);
lean_inc(v_a_4967_);
lean_dec_ref_known(v___x_4965_, 1);
v_challenge__module_4968_ = lean_ctor_get(v_a_4967_, 0);
lean_inc_ref(v_challenge__module_4968_);
v_solution__module_4969_ = lean_ctor_get(v_a_4967_, 1);
lean_inc_ref(v_solution__module_4969_);
v_theorem__names_4970_ = lean_ctor_get(v_a_4967_, 2);
v_definition__names_4971_ = lean_ctor_get(v_a_4967_, 3);
v_permitted__axioms_4972_ = lean_ctor_get(v_a_4967_, 4);
lean_inc_ref(v_permitted__axioms_4972_);
v_sz_4973_ = lean_array_size(v_theorem__names_4970_);
v___x_4974_ = ((size_t)0ULL);
lean_inc_ref(v_theorem__names_4970_);
v___x_4975_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_4973_, v___x_4974_, v_theorem__names_4970_);
if (lean_obj_tag(v_definition__names_4971_) == 0)
{
lean_object* v___x_5070_; 
v___x_5070_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___y_5060_ = v___x_5070_;
goto v___jp_5059_;
}
else
{
lean_object* v_val_5071_; 
v_val_5071_ = lean_ctor_get(v_definition__names_4971_, 0);
lean_inc(v_val_5071_);
v___y_5060_ = v_val_5071_;
goto v___jp_5059_;
}
v___jp_4976_:
{
lean_object* v___x_4978_; 
v___x_4978_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v_a_4967_);
if (lean_obj_tag(v___x_4978_) == 0)
{
lean_object* v_a_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_5050_; 
v_a_4979_ = lean_ctor_get(v___x_4978_, 0);
v_isSharedCheck_5050_ = !lean_is_exclusive(v___x_4978_);
if (v_isSharedCheck_5050_ == 0)
{
v___x_4981_ = v___x_4978_;
v_isShared_4982_ = v_isSharedCheck_5050_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_a_4979_);
lean_dec(v___x_4978_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_5050_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
if (lean_obj_tag(v_a_4979_) == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4985_; 
lean_dec_ref(v___y_4977_);
lean_dec_ref(v___x_4975_);
lean_dec_ref(v_permitted__axioms_4972_);
lean_dec_ref(v_solution__module_4969_);
lean_dec_ref(v_challenge__module_4968_);
lean_dec(v_a_4950_);
v_a_4983_ = lean_ctor_get(v_a_4979_, 0);
lean_inc(v_a_4983_);
lean_dec_ref_known(v_a_4979_, 1);
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 0, v_a_4983_);
v___x_4985_ = v___x_4981_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_a_4983_);
v___x_4985_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
return v___x_4985_;
}
}
else
{
lean_object* v_a_4987_; lean_object* v_projectDir_4988_; lean_object* v_leanPrefix_4989_; lean_object* v_leanPath_4990_; lean_object* v_binPath_4991_; lean_object* v_whichSandbox_4992_; lean_object* v_whichLake_4993_; lean_object* v_lakeHome_4994_; lean_object* v_whichLean4Export_4995_; lean_object* v_whichLeanChecker_4996_; lean_object* v_whichEnvBin_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5043_; 
lean_del_object(v___x_4981_);
v_a_4987_ = lean_ctor_get(v_a_4979_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v_a_4979_, 1);
v_projectDir_4988_ = lean_ctor_get(v_a_4950_, 0);
v_leanPrefix_4989_ = lean_ctor_get(v_a_4950_, 6);
v_leanPath_4990_ = lean_ctor_get(v_a_4950_, 7);
v_binPath_4991_ = lean_ctor_get(v_a_4950_, 8);
v_whichSandbox_4992_ = lean_ctor_get(v_a_4950_, 9);
v_whichLake_4993_ = lean_ctor_get(v_a_4950_, 10);
v_lakeHome_4994_ = lean_ctor_get(v_a_4950_, 11);
v_whichLean4Export_4995_ = lean_ctor_get(v_a_4950_, 12);
v_whichLeanChecker_4996_ = lean_ctor_get(v_a_4950_, 13);
v_whichEnvBin_4997_ = lean_ctor_get(v_a_4950_, 14);
v_isSharedCheck_5043_ = !lean_is_exclusive(v_a_4950_);
if (v_isSharedCheck_5043_ == 0)
{
lean_object* v_unused_5044_; lean_object* v_unused_5045_; lean_object* v_unused_5046_; lean_object* v_unused_5047_; lean_object* v_unused_5048_; lean_object* v_unused_5049_; 
v_unused_5044_ = lean_ctor_get(v_a_4950_, 15);
lean_dec(v_unused_5044_);
v_unused_5045_ = lean_ctor_get(v_a_4950_, 5);
lean_dec(v_unused_5045_);
v_unused_5046_ = lean_ctor_get(v_a_4950_, 4);
lean_dec(v_unused_5046_);
v_unused_5047_ = lean_ctor_get(v_a_4950_, 3);
lean_dec(v_unused_5047_);
v_unused_5048_ = lean_ctor_get(v_a_4950_, 2);
lean_dec(v_unused_5048_);
v_unused_5049_ = lean_ctor_get(v_a_4950_, 1);
lean_dec(v_unused_5049_);
v___x_4999_ = v_a_4950_;
v_isShared_5000_ = v_isSharedCheck_5043_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_whichEnvBin_4997_);
lean_inc(v_whichLeanChecker_4996_);
lean_inc(v_whichLean4Export_4995_);
lean_inc(v_lakeHome_4994_);
lean_inc(v_whichLake_4993_);
lean_inc(v_whichSandbox_4992_);
lean_inc(v_binPath_4991_);
lean_inc(v_leanPath_4990_);
lean_inc(v_leanPrefix_4989_);
lean_inc(v_projectDir_4988_);
lean_dec(v_a_4950_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5043_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v___x_5001_; 
lean_inc_ref(v_projectDir_4988_);
v___x_5001_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_4940_, v_projectDir_4988_);
if (lean_obj_tag(v___x_5001_) == 0)
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5034_; 
v_a_5002_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5034_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5034_ == 0)
{
v___x_5004_ = v___x_5001_;
v_isShared_5005_ = v_isSharedCheck_5034_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_5001_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5034_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
if (lean_obj_tag(v_a_5002_) == 1)
{
lean_object* v_val_5006_; lean_object* v___x_5008_; 
lean_del_object(v___x_4999_);
lean_dec_ref(v_whichEnvBin_4997_);
lean_dec_ref(v_whichLeanChecker_4996_);
lean_dec_ref(v_whichLean4Export_4995_);
lean_dec_ref(v_lakeHome_4994_);
lean_dec_ref(v_whichLake_4993_);
lean_dec_ref(v_whichSandbox_4992_);
lean_dec_ref(v_binPath_4991_);
lean_dec_ref(v_leanPath_4990_);
lean_dec_ref(v_leanPrefix_4989_);
lean_dec_ref(v_projectDir_4988_);
lean_dec(v_a_4987_);
lean_dec_ref(v___y_4977_);
lean_dec_ref(v___x_4975_);
lean_dec_ref(v_permitted__axioms_4972_);
lean_dec_ref(v_solution__module_4969_);
lean_dec_ref(v_challenge__module_4968_);
v_val_5006_ = lean_ctor_get(v_a_5002_, 0);
lean_inc(v_val_5006_);
lean_dec_ref_known(v_a_5002_, 1);
if (v_isShared_5005_ == 0)
{
lean_ctor_set(v___x_5004_, 0, v_val_5006_);
v___x_5008_ = v___x_5004_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_val_5006_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
return v___x_5008_;
}
}
else
{
lean_object* v___x_5010_; lean_object* v___x_5011_; size_t v_sz_5012_; lean_object* v___x_5013_; lean_object* v___x_5015_; 
lean_del_object(v___x_5004_);
lean_dec(v_a_5002_);
v___x_5010_ = l_String_toName(v_challenge__module_4968_);
v___x_5011_ = l_String_toName(v_solution__module_4969_);
v_sz_5012_ = lean_array_size(v_permitted__axioms_4972_);
v___x_5013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_5012_, v___x_4974_, v_permitted__axioms_4972_);
lean_inc(v_a_4987_);
lean_inc_ref(v_whichEnvBin_4997_);
lean_inc_ref(v_whichLeanChecker_4996_);
lean_inc_ref(v_whichLean4Export_4995_);
lean_inc_ref(v_lakeHome_4994_);
lean_inc_ref(v_whichLake_4993_);
lean_inc_ref(v_whichSandbox_4992_);
lean_inc_ref(v_leanPrefix_4989_);
lean_inc_ref(v___x_5013_);
lean_inc_ref(v___y_4977_);
lean_inc_ref(v___x_4975_);
lean_inc(v___x_5011_);
lean_inc(v___x_5010_);
lean_inc_ref(v_projectDir_4988_);
if (v_isShared_5000_ == 0)
{
lean_ctor_set(v___x_4999_, 15, v_a_4987_);
lean_ctor_set(v___x_4999_, 5, v___x_5013_);
lean_ctor_set(v___x_4999_, 4, v___y_4977_);
lean_ctor_set(v___x_4999_, 3, v___x_4975_);
lean_ctor_set(v___x_4999_, 2, v___x_5011_);
lean_ctor_set(v___x_4999_, 1, v___x_5010_);
v___x_5015_ = v___x_4999_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v_projectDir_4988_);
lean_ctor_set(v_reuseFailAlloc_5033_, 1, v___x_5010_);
lean_ctor_set(v_reuseFailAlloc_5033_, 2, v___x_5011_);
lean_ctor_set(v_reuseFailAlloc_5033_, 3, v___x_4975_);
lean_ctor_set(v_reuseFailAlloc_5033_, 4, v___y_4977_);
lean_ctor_set(v_reuseFailAlloc_5033_, 5, v___x_5013_);
lean_ctor_set(v_reuseFailAlloc_5033_, 6, v_leanPrefix_4989_);
lean_ctor_set(v_reuseFailAlloc_5033_, 7, v_leanPath_4990_);
lean_ctor_set(v_reuseFailAlloc_5033_, 8, v_binPath_4991_);
lean_ctor_set(v_reuseFailAlloc_5033_, 9, v_whichSandbox_4992_);
lean_ctor_set(v_reuseFailAlloc_5033_, 10, v_whichLake_4993_);
lean_ctor_set(v_reuseFailAlloc_5033_, 11, v_lakeHome_4994_);
lean_ctor_set(v_reuseFailAlloc_5033_, 12, v_whichLean4Export_4995_);
lean_ctor_set(v_reuseFailAlloc_5033_, 13, v_whichLeanChecker_4996_);
lean_ctor_set(v_reuseFailAlloc_5033_, 14, v_whichEnvBin_4997_);
lean_ctor_set(v_reuseFailAlloc_5033_, 15, v_a_4987_);
v___x_5015_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
lean_object* v___x_5016_; 
v___x_5016_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v___x_5015_);
lean_dec_ref(v___x_5015_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_object* v_a_5017_; lean_object* v_fst_5018_; lean_object* v_snd_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_a_5017_);
lean_dec_ref_known(v___x_5016_, 1);
v_fst_5018_ = lean_ctor_get(v_a_5017_, 0);
lean_inc(v_fst_5018_);
v_snd_5019_ = lean_ctor_get(v_a_5017_, 1);
lean_inc(v_snd_5019_);
lean_dec(v_a_5017_);
v___x_5020_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_5020_, 0, v_projectDir_4988_);
lean_ctor_set(v___x_5020_, 1, v___x_5010_);
lean_ctor_set(v___x_5020_, 2, v___x_5011_);
lean_ctor_set(v___x_5020_, 3, v___x_4975_);
lean_ctor_set(v___x_5020_, 4, v___y_4977_);
lean_ctor_set(v___x_5020_, 5, v___x_5013_);
lean_ctor_set(v___x_5020_, 6, v_leanPrefix_4989_);
lean_ctor_set(v___x_5020_, 7, v_fst_5018_);
lean_ctor_set(v___x_5020_, 8, v_snd_5019_);
lean_ctor_set(v___x_5020_, 9, v_whichSandbox_4992_);
lean_ctor_set(v___x_5020_, 10, v_whichLake_4993_);
lean_ctor_set(v___x_5020_, 11, v_lakeHome_4994_);
lean_ctor_set(v___x_5020_, 12, v_whichLean4Export_4995_);
lean_ctor_set(v___x_5020_, 13, v_whichLeanChecker_4996_);
lean_ctor_set(v___x_5020_, 14, v_whichEnvBin_4997_);
lean_ctor_set(v___x_5020_, 15, v_a_4987_);
v___x_5021_ = l_Lake_Check_compareIt(v___x_5020_);
lean_dec_ref_known(v___x_5020_, 16);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5029_; 
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_5021_);
if (v_isSharedCheck_5029_ == 0)
{
lean_object* v_unused_5030_; 
v_unused_5030_ = lean_ctor_get(v___x_5021_, 0);
lean_dec(v_unused_5030_);
v___x_5023_ = v___x_5021_;
v_isShared_5024_ = v_isSharedCheck_5029_;
goto v_resetjp_5022_;
}
else
{
lean_dec(v___x_5021_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5029_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5025_; lean_object* v___x_5027_; 
v___x_5025_ = l_Lake_Check_runChallenge___boxed__const__2;
if (v_isShared_5024_ == 0)
{
lean_ctor_set(v___x_5023_, 0, v___x_5025_);
v___x_5027_ = v___x_5023_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v___x_5025_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
}
else
{
lean_object* v_a_5031_; 
v_a_5031_ = lean_ctor_get(v___x_5021_, 0);
lean_inc(v_a_5031_);
lean_dec_ref_known(v___x_5021_, 1);
v_a_4918_ = v_a_5031_;
goto v___jp_4917_;
}
}
else
{
lean_object* v_a_5032_; 
lean_dec_ref(v___x_5013_);
lean_dec(v___x_5011_);
lean_dec(v___x_5010_);
lean_dec_ref(v_whichEnvBin_4997_);
lean_dec_ref(v_whichLeanChecker_4996_);
lean_dec_ref(v_whichLean4Export_4995_);
lean_dec_ref(v_lakeHome_4994_);
lean_dec_ref(v_whichLake_4993_);
lean_dec_ref(v_whichSandbox_4992_);
lean_dec_ref(v_leanPrefix_4989_);
lean_dec_ref(v_projectDir_4988_);
lean_dec(v_a_4987_);
lean_dec_ref(v___y_4977_);
lean_dec_ref(v___x_4975_);
v_a_5032_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_a_5032_);
lean_dec_ref_known(v___x_5016_, 1);
v_a_4918_ = v_a_5032_;
goto v___jp_4917_;
}
}
}
}
}
else
{
lean_object* v_a_5035_; lean_object* v___x_5037_; uint8_t v_isShared_5038_; uint8_t v_isSharedCheck_5042_; 
lean_del_object(v___x_4999_);
lean_dec_ref(v_whichEnvBin_4997_);
lean_dec_ref(v_whichLeanChecker_4996_);
lean_dec_ref(v_whichLean4Export_4995_);
lean_dec_ref(v_lakeHome_4994_);
lean_dec_ref(v_whichLake_4993_);
lean_dec_ref(v_whichSandbox_4992_);
lean_dec_ref(v_binPath_4991_);
lean_dec_ref(v_leanPath_4990_);
lean_dec_ref(v_leanPrefix_4989_);
lean_dec_ref(v_projectDir_4988_);
lean_dec(v_a_4987_);
lean_dec_ref(v___y_4977_);
lean_dec_ref(v___x_4975_);
lean_dec_ref(v_permitted__axioms_4972_);
lean_dec_ref(v_solution__module_4969_);
lean_dec_ref(v_challenge__module_4968_);
v_a_5035_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5037_ = v___x_5001_;
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
else
{
lean_inc(v_a_5035_);
lean_dec(v___x_5001_);
v___x_5037_ = lean_box(0);
v_isShared_5038_ = v_isSharedCheck_5042_;
goto v_resetjp_5036_;
}
v_resetjp_5036_:
{
lean_object* v___x_5040_; 
if (v_isShared_5038_ == 0)
{
v___x_5040_ = v___x_5037_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5035_);
v___x_5040_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
return v___x_5040_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5058_; 
lean_dec_ref(v___y_4977_);
lean_dec_ref(v___x_4975_);
lean_dec_ref(v_permitted__axioms_4972_);
lean_dec_ref(v_solution__module_4969_);
lean_dec_ref(v_challenge__module_4968_);
lean_dec(v_a_4950_);
v_a_5051_ = lean_ctor_get(v___x_4978_, 0);
v_isSharedCheck_5058_ = !lean_is_exclusive(v___x_4978_);
if (v_isSharedCheck_5058_ == 0)
{
v___x_5053_ = v___x_4978_;
v_isShared_5054_ = v_isSharedCheck_5058_;
goto v_resetjp_5052_;
}
else
{
lean_inc(v_a_5051_);
lean_dec(v___x_4978_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5058_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v___x_5056_; 
if (v_isShared_5054_ == 0)
{
v___x_5056_ = v___x_5053_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v_a_5051_);
v___x_5056_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
return v___x_5056_;
}
}
}
}
v___jp_5059_:
{
size_t v_sz_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; uint8_t v___x_5065_; 
v_sz_5061_ = lean_array_size(v___y_5060_);
v___x_5062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_5061_, v___x_4974_, v___y_5060_);
v___x_5063_ = lean_array_get_size(v___x_4975_);
v___x_5064_ = lean_unsigned_to_nat(0u);
v___x_5065_ = lean_nat_dec_eq(v___x_5063_, v___x_5064_);
if (v___x_5065_ == 0)
{
v___y_4977_ = v___x_5062_;
goto v___jp_4976_;
}
else
{
lean_object* v___x_5066_; uint8_t v___x_5067_; 
v___x_5066_ = lean_array_get_size(v___x_5062_);
v___x_5067_ = lean_nat_dec_eq(v___x_5066_, v___x_5064_);
if (v___x_5067_ == 0)
{
v___y_4977_ = v___x_5062_;
goto v___jp_4976_;
}
else
{
lean_object* v___x_5068_; lean_object* v___x_5069_; 
lean_dec_ref(v___x_5062_);
lean_dec_ref(v___x_4975_);
lean_dec_ref(v_permitted__axioms_4972_);
lean_dec_ref(v_solution__module_4969_);
lean_dec_ref(v_challenge__module_4968_);
lean_dec(v_a_4967_);
lean_dec(v_a_4950_);
v___x_5068_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__3));
v___x_5069_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5068_);
return v___x_5069_;
}
}
}
}
}
v___jp_4954_:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4956_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__1));
v___x_4957_ = lean_string_append(v___x_4956_, v_val_4951_);
v___x_4958_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__2));
v___x_4959_ = lean_string_append(v___x_4957_, v___x_4958_);
v___x_4960_ = lean_string_append(v___x_4959_, v_a_4955_);
lean_dec_ref(v_a_4955_);
v___x_4961_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4960_);
lean_dec_ref(v___x_4960_);
return v___x_4961_;
}
}
else
{
lean_object* v_a_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
lean_dec(v_a_4950_);
v_a_5072_ = lean_ctor_get(v___x_4952_, 0);
lean_inc(v_a_5072_);
lean_dec_ref_known(v___x_4952_, 1);
v___x_5073_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__4));
v___x_5074_ = lean_io_error_to_string(v_a_5072_);
v___x_5075_ = lean_string_append(v___x_5073_, v___x_5074_);
lean_dec_ref(v___x_5074_);
v___x_5076_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5075_);
lean_dec_ref(v___x_5075_);
return v___x_5076_;
}
}
else
{
lean_object* v___x_5077_; lean_object* v___x_5078_; 
lean_dec_ref_known(v_a_4942_, 1);
v___x_5077_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__5));
v___x_5078_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5077_);
return v___x_5078_;
}
}
}
}
else
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5087_; 
v_a_5080_ = lean_ctor_get(v___x_4941_, 0);
v_isSharedCheck_5087_ = !lean_is_exclusive(v___x_4941_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5082_ = v___x_4941_;
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_dec(v___x_4941_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5085_; 
if (v_isShared_5083_ == 0)
{
v___x_5085_ = v___x_5082_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
v___x_5085_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
return v___x_5085_;
}
}
}
v___jp_4917_:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
v___x_4919_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_4920_ = lean_io_error_to_string(v_a_4918_);
v___x_4921_ = lean_string_append(v___x_4919_, v___x_4920_);
lean_dec_ref(v___x_4920_);
v___x_4922_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_4921_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4930_; 
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4930_ == 0)
{
lean_object* v_unused_4931_; 
v_unused_4931_ = lean_ctor_get(v___x_4922_, 0);
lean_dec(v_unused_4931_);
v___x_4924_ = v___x_4922_;
v_isShared_4925_ = v_isSharedCheck_4930_;
goto v_resetjp_4923_;
}
else
{
lean_dec(v___x_4922_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4930_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4926_; lean_object* v___x_4928_; 
v___x_4926_ = l_Lake_Check_runChallenge___boxed__const__1;
if (v_isShared_4925_ == 0)
{
lean_ctor_set(v___x_4924_, 0, v___x_4926_);
v___x_4928_ = v___x_4924_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v___x_4926_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
else
{
lean_object* v_a_4932_; lean_object* v___x_4934_; uint8_t v_isShared_4935_; uint8_t v_isSharedCheck_4939_; 
v_a_4932_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4934_ = v___x_4922_;
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
else
{
lean_inc(v_a_4932_);
lean_dec(v___x_4922_);
v___x_4934_ = lean_box(0);
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
v_resetjp_4933_:
{
lean_object* v___x_4937_; 
if (v_isShared_4935_ == 0)
{
v___x_4937_ = v___x_4934_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4932_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runChallenge___boxed(lean_object* v_configFile_x3f_5088_, lean_object* v_lean_5089_, lean_object* v_lake_5090_, lean_object* v_projectDir_5091_, lean_object* v_a_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l_Lake_Check_runChallenge(v_configFile_x3f_5088_, v_lean_5089_, v_lake_5090_, v_projectDir_5091_);
lean_dec_ref(v_lake_5090_);
lean_dec(v_configFile_x3f_5088_);
return v_res_5093_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runCheck(lean_object* v_lean_5094_, lean_object* v_lake_5095_, lean_object* v_projectDir_5096_){
_start:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; 
v___x_5098_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__0));
v___x_5099_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_5098_, v_lean_5094_, v_lake_5095_, v_projectDir_5096_);
if (lean_obj_tag(v___x_5099_) == 0)
{
lean_object* v_a_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5160_; 
v_a_5100_ = lean_ctor_get(v___x_5099_, 0);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_5099_);
if (v_isSharedCheck_5160_ == 0)
{
v___x_5102_ = v___x_5099_;
v_isShared_5103_ = v_isSharedCheck_5160_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_a_5100_);
lean_dec(v___x_5099_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5160_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
if (lean_obj_tag(v_a_5100_) == 0)
{
lean_object* v_a_5104_; lean_object* v___x_5106_; 
v_a_5104_ = lean_ctor_get(v_a_5100_, 0);
lean_inc(v_a_5104_);
lean_dec_ref_known(v_a_5100_, 1);
if (v_isShared_5103_ == 0)
{
lean_ctor_set(v___x_5102_, 0, v_a_5104_);
v___x_5106_ = v___x_5102_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_a_5104_);
v___x_5106_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
return v___x_5106_;
}
}
else
{
lean_object* v_a_5108_; lean_object* v_projectDir_5109_; lean_object* v___x_5110_; 
lean_del_object(v___x_5102_);
v_a_5108_ = lean_ctor_get(v_a_5100_, 0);
lean_inc(v_a_5108_);
lean_dec_ref_known(v_a_5100_, 1);
v_projectDir_5109_ = lean_ctor_get(v_a_5108_, 0);
lean_inc_ref(v_projectDir_5109_);
v___x_5110_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_5098_, v_projectDir_5109_);
if (lean_obj_tag(v___x_5110_) == 0)
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5151_; 
v_a_5111_ = lean_ctor_get(v___x_5110_, 0);
v_isSharedCheck_5151_ = !lean_is_exclusive(v___x_5110_);
if (v_isSharedCheck_5151_ == 0)
{
v___x_5113_ = v___x_5110_;
v_isShared_5114_ = v_isSharedCheck_5151_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_5110_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5151_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
if (lean_obj_tag(v_a_5111_) == 1)
{
lean_object* v_val_5115_; lean_object* v___x_5117_; 
lean_dec(v_a_5108_);
v_val_5115_ = lean_ctor_get(v_a_5111_, 0);
lean_inc(v_val_5115_);
lean_dec_ref_known(v_a_5111_, 1);
if (v_isShared_5114_ == 0)
{
lean_ctor_set(v___x_5113_, 0, v_val_5115_);
v___x_5117_ = v___x_5113_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_val_5115_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
else
{
lean_object* v___x_5119_; 
lean_del_object(v___x_5113_);
lean_dec(v_a_5111_);
v___x_5119_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v_a_5108_);
lean_dec(v_a_5108_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5127_; 
v_isSharedCheck_5127_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5127_ == 0)
{
lean_object* v_unused_5128_; 
v_unused_5128_ = lean_ctor_get(v___x_5119_, 0);
lean_dec(v_unused_5128_);
v___x_5121_ = v___x_5119_;
v_isShared_5122_ = v_isSharedCheck_5127_;
goto v_resetjp_5120_;
}
else
{
lean_dec(v___x_5119_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5127_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5123_; lean_object* v___x_5125_; 
v___x_5123_ = l_Lake_Check_runChallenge___boxed__const__2;
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 0, v___x_5123_);
v___x_5125_ = v___x_5121_;
goto v_reusejp_5124_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v___x_5123_);
v___x_5125_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5124_;
}
v_reusejp_5124_:
{
return v___x_5125_;
}
}
}
else
{
lean_object* v_a_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; 
v_a_5129_ = lean_ctor_get(v___x_5119_, 0);
lean_inc(v_a_5129_);
lean_dec_ref_known(v___x_5119_, 1);
v___x_5130_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_5131_ = lean_io_error_to_string(v_a_5129_);
v___x_5132_ = lean_string_append(v___x_5130_, v___x_5131_);
lean_dec_ref(v___x_5131_);
v___x_5133_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_5132_);
if (lean_obj_tag(v___x_5133_) == 0)
{
lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5141_; 
v_isSharedCheck_5141_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5141_ == 0)
{
lean_object* v_unused_5142_; 
v_unused_5142_ = lean_ctor_get(v___x_5133_, 0);
lean_dec(v_unused_5142_);
v___x_5135_ = v___x_5133_;
v_isShared_5136_ = v_isSharedCheck_5141_;
goto v_resetjp_5134_;
}
else
{
lean_dec(v___x_5133_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5141_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v___x_5137_; lean_object* v___x_5139_; 
v___x_5137_ = l_Lake_Check_runChallenge___boxed__const__1;
if (v_isShared_5136_ == 0)
{
lean_ctor_set(v___x_5135_, 0, v___x_5137_);
v___x_5139_ = v___x_5135_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5140_; 
v_reuseFailAlloc_5140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5140_, 0, v___x_5137_);
v___x_5139_ = v_reuseFailAlloc_5140_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
return v___x_5139_;
}
}
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
v_a_5143_ = lean_ctor_get(v___x_5133_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_5133_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5133_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5152_; lean_object* v___x_5154_; uint8_t v_isShared_5155_; uint8_t v_isSharedCheck_5159_; 
lean_dec(v_a_5108_);
v_a_5152_ = lean_ctor_get(v___x_5110_, 0);
v_isSharedCheck_5159_ = !lean_is_exclusive(v___x_5110_);
if (v_isSharedCheck_5159_ == 0)
{
v___x_5154_ = v___x_5110_;
v_isShared_5155_ = v_isSharedCheck_5159_;
goto v_resetjp_5153_;
}
else
{
lean_inc(v_a_5152_);
lean_dec(v___x_5110_);
v___x_5154_ = lean_box(0);
v_isShared_5155_ = v_isSharedCheck_5159_;
goto v_resetjp_5153_;
}
v_resetjp_5153_:
{
lean_object* v___x_5157_; 
if (v_isShared_5155_ == 0)
{
v___x_5157_ = v___x_5154_;
goto v_reusejp_5156_;
}
else
{
lean_object* v_reuseFailAlloc_5158_; 
v_reuseFailAlloc_5158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5158_, 0, v_a_5152_);
v___x_5157_ = v_reuseFailAlloc_5158_;
goto v_reusejp_5156_;
}
v_reusejp_5156_:
{
return v___x_5157_;
}
}
}
}
}
}
else
{
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5168_; 
v_a_5161_ = lean_ctor_get(v___x_5099_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v___x_5099_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5163_ = v___x_5099_;
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v___x_5099_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5166_; 
if (v_isShared_5164_ == 0)
{
v___x_5166_ = v___x_5163_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_a_5161_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runCheck___boxed(lean_object* v_lean_5169_, lean_object* v_lake_5170_, lean_object* v_projectDir_5171_, lean_object* v_a_5172_){
_start:
{
lean_object* v_res_5173_; 
v_res_5173_ = l_Lake_Check_runCheck(v_lean_5169_, v_lake_5170_, v_projectDir_5171_);
lean_dec_ref(v_lake_5170_);
return v_res_5173_;
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
