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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
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
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
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
lean_object* lean_get_stderr();
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_io_create_dir(lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* l_LeanExport_parseStream(lean_object*);
lean_object* l_Lake_Check_compareAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Check_checkAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leanexport"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leanchecker"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` needs `env` on PATH to build inside the sandbox"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` needs `git` on PATH to build inside the sandbox"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "bwrap"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7_value;
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
uint8_t v___x_139_; 
v___x_139_ = lean_usize_dec_lt(v_i_136_, v_sz_135_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v_b_137_);
return v___x_140_;
}
else
{
lean_object* v_a_141_; lean_object* v___x_142_; lean_object* v_a_144_; 
v_a_141_ = lean_array_uget_borrowed(v_as_134_, v_i_136_);
v___x_142_ = lean_io_getenv(v_a_141_);
if (lean_obj_tag(v___x_142_) == 1)
{
lean_object* v_val_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_val_148_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_val_148_);
lean_dec_ref_known(v___x_142_, 1);
lean_inc(v_a_141_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v_a_141_);
lean_ctor_set(v___x_149_, 1, v_val_148_);
v___x_150_ = lean_array_push(v_b_137_, v___x_149_);
v_a_144_ = v___x_150_;
goto v___jp_143_;
}
else
{
lean_dec(v___x_142_);
v_a_144_ = v_b_137_;
goto v___jp_143_;
}
v___jp_143_:
{
size_t v___x_145_; size_t v___x_146_; 
v___x_145_ = ((size_t)1ULL);
v___x_146_ = lean_usize_add(v_i_136_, v___x_145_);
v_i_136_ = v___x_146_;
v_b_137_ = v_a_144_;
goto _start;
}
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(lean_object* v_s_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0));
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___boxed(lean_object* v_s_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(v_s_974_);
lean_dec_ref(v_s_974_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(lean_object* v_a_976_, lean_object* v___x_977_, lean_object* v___x_978_, lean_object* v_a_979_, lean_object* v_b_980_){
_start:
{
lean_object* v_it_982_; lean_object* v_startInclusive_983_; lean_object* v_endExclusive_984_; 
if (lean_obj_tag(v_a_979_) == 0)
{
lean_object* v_currPos_989_; lean_object* v_searcher_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1013_; 
v_currPos_989_ = lean_ctor_get(v_a_979_, 0);
v_searcher_990_ = lean_ctor_get(v_a_979_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_a_979_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_992_ = v_a_979_;
v_isShared_993_ = v_isSharedCheck_1013_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_searcher_990_);
lean_inc(v_currPos_989_);
lean_dec(v_a_979_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1013_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v_decide_994_; 
v_decide_994_ = lean_nat_dec_eq(v_searcher_990_, v___x_978_);
if (v_decide_994_ == 0)
{
uint32_t v___x_995_; uint32_t v___x_996_; uint8_t v___x_997_; 
v___x_995_ = 10;
v___x_996_ = lean_string_utf8_get_fast(v_a_976_, v_searcher_990_);
v___x_997_ = lean_uint32_dec_eq(v___x_996_, v___x_995_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_998_ = lean_string_utf8_next_fast(v_a_976_, v_searcher_990_);
lean_dec(v_searcher_990_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v___x_998_);
v___x_1000_ = v___x_992_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_currPos_989_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1002_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
v_a_979_ = v___x_1000_;
goto _start;
}
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_slice_1006_; lean_object* v_nextIt_1008_; 
v___x_1003_ = lean_string_utf8_next_fast(v_a_976_, v_searcher_990_);
v___x_1004_ = lean_nat_sub(v___x_1003_, v_searcher_990_);
v___x_1005_ = lean_nat_add(v_searcher_990_, v___x_1004_);
lean_dec(v___x_1004_);
v_slice_1006_ = l_String_Slice_subslice_x21(v___x_977_, v_currPos_989_, v_searcher_990_);
lean_inc(v___x_1005_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v___x_1005_);
lean_ctor_set(v___x_992_, 0, v___x_1005_);
v_nextIt_1008_ = v___x_992_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v___x_1005_);
v_nextIt_1008_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v_startInclusive_1009_; lean_object* v_endExclusive_1010_; 
v_startInclusive_1009_ = lean_ctor_get(v_slice_1006_, 0);
lean_inc(v_startInclusive_1009_);
v_endExclusive_1010_ = lean_ctor_get(v_slice_1006_, 1);
lean_inc(v_endExclusive_1010_);
lean_dec_ref(v_slice_1006_);
v_it_982_ = v_nextIt_1008_;
v_startInclusive_983_ = v_startInclusive_1009_;
v_endExclusive_984_ = v_endExclusive_1010_;
goto v___jp_981_;
}
}
}
else
{
lean_object* v___x_1012_; 
lean_del_object(v___x_992_);
lean_dec(v_searcher_990_);
v___x_1012_ = lean_box(1);
lean_inc(v___x_978_);
v_it_982_ = v___x_1012_;
v_startInclusive_983_ = v_currPos_989_;
v_endExclusive_984_ = v___x_978_;
goto v___jp_981_;
}
}
}
else
{
lean_dec(v___x_978_);
lean_dec_ref(v_a_976_);
return v_b_980_;
}
v___jp_981_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_inc_ref(v_a_976_);
v___x_985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_985_, 0, v_a_976_);
lean_ctor_set(v___x_985_, 1, v_startInclusive_983_);
lean_ctor_set(v___x_985_, 2, v_endExclusive_984_);
v___x_986_ = l_String_Slice_toString(v___x_985_);
lean_dec_ref_known(v___x_985_, 3);
v___x_987_ = lean_array_push(v_b_980_, v___x_986_);
v_a_979_ = v_it_982_;
v_b_980_ = v___x_987_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg___boxed(lean_object* v_a_1014_, lean_object* v___x_1015_, lean_object* v___x_1016_, lean_object* v_a_1017_, lean_object* v_b_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1014_, v___x_1015_, v___x_1016_, v_a_1017_, v_b_1018_);
lean_dec_ref(v___x_1015_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(lean_object* v_as_x27_1020_, lean_object* v_b_1021_){
_start:
{
if (lean_obj_tag(v_as_x27_1020_) == 0)
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1023_, 0, v_b_1021_);
return v___x_1023_;
}
else
{
lean_object* v_head_1024_; lean_object* v_tail_1025_; lean_object* v_fst_1026_; lean_object* v_snd_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1049_; 
v_head_1024_ = lean_ctor_get(v_as_x27_1020_, 0);
v_tail_1025_ = lean_ctor_get(v_as_x27_1020_, 1);
v_fst_1026_ = lean_ctor_get(v_b_1021_, 0);
v_snd_1027_ = lean_ctor_get(v_b_1021_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_b_1021_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1029_ = v_b_1021_;
v_isShared_1030_ = v_isSharedCheck_1049_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_snd_1027_);
lean_inc(v_fst_1026_);
lean_dec(v_b_1021_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1049_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; 
lean_inc(v_head_1024_);
v___x_1031_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_head_1024_);
if (lean_obj_tag(v___x_1031_) == 1)
{
lean_object* v_val_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
lean_dec(v_fst_1026_);
v_val_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_val_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = l_String_Slice_toString(v_val_1032_);
lean_dec(v_val_1032_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1033_);
v___x_1035_ = v___x_1029_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_snd_1027_);
v___x_1035_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
v_as_x27_1020_ = v_tail_1025_;
v_b_1021_ = v___x_1035_;
goto _start;
}
}
else
{
lean_object* v___x_1038_; 
lean_dec(v___x_1031_);
lean_inc(v_head_1024_);
v___x_1038_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_head_1024_);
if (lean_obj_tag(v___x_1038_) == 1)
{
lean_object* v_val_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
lean_dec(v_snd_1027_);
v_val_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_val_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = l_String_Slice_toString(v_val_1039_);
lean_dec(v_val_1039_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 1, v___x_1040_);
v___x_1042_ = v___x_1029_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_fst_1026_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
v_as_x27_1020_ = v_tail_1025_;
v_b_1021_ = v___x_1042_;
goto _start;
}
}
else
{
lean_object* v___x_1046_; 
lean_dec(v___x_1038_);
if (v_isShared_1030_ == 0)
{
v___x_1046_ = v___x_1029_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_fst_1026_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_snd_1027_);
v___x_1046_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
v_as_x27_1020_ = v_tail_1025_;
v_b_1021_ = v___x_1046_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg___boxed(lean_object* v_as_x27_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_1050_, v_b_1051_);
lean_dec(v_as_x27_1050_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(lean_object* v_s_1054_){
_start:
{
lean_object* v___x_1056_; lean_object* v_putStr_1057_; lean_object* v___x_1058_; 
v___x_1056_ = lean_get_stdout();
v_putStr_1057_ = lean_ctor_get(v___x_1056_, 4);
lean_inc_ref(v_putStr_1057_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = lean_apply_2(v_putStr_1057_, v_s_1054_, lean_box(0));
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2___boxed(lean_object* v_s_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v_s_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(lean_object* v_s_1062_){
_start:
{
uint32_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = 10;
v___x_1065_ = lean_string_push(v_s_1062_, v___x_1064_);
v___x_1066_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2___boxed(lean_object* v_s_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v_s_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(lean_object* v_a_1103_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_1109_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1108_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_projectDir_1110_; lean_object* v_leanPrefix_1111_; lean_object* v_whichLake_1112_; lean_object* v_lakeHome_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___y_1117_; lean_object* v_leanPrefix_1118_; lean_object* v_whichLake_1119_; lean_object* v_lakeHome_1120_; uint8_t v___x_1175_; 
lean_dec_ref_known(v___x_1109_, 1);
v_projectDir_1110_ = lean_ctor_get(v_a_1103_, 0);
v_leanPrefix_1111_ = lean_ctor_get(v_a_1103_, 6);
v_whichLake_1112_ = lean_ctor_get(v_a_1103_, 10);
v_lakeHome_1113_ = lean_ctor_get(v_a_1103_, 11);
v___x_1114_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1110_);
v___x_1115_ = l_System_FilePath_join(v_projectDir_1110_, v___x_1114_);
v___x_1175_ = l_System_FilePath_pathExists(v___x_1115_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_io_create_dir(v___x_1115_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_dec_ref_known(v___x_1176_, 1);
v___y_1117_ = v_a_1103_;
v_leanPrefix_1118_ = v_leanPrefix_1111_;
v_whichLake_1119_ = v_whichLake_1112_;
v_lakeHome_1120_ = v_lakeHome_1113_;
goto v___jp_1116_;
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec_ref(v___x_1115_);
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
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
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
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
else
{
v___y_1117_ = v_a_1103_;
v_leanPrefix_1118_ = v_leanPrefix_1111_;
v_whichLake_1119_ = v_whichLake_1112_;
v_lakeHome_1120_ = v_lakeHome_1113_;
goto v___jp_1116_;
}
v___jp_1116_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_mk_empty_array_with_capacity(v___x_1121_);
v___x_1123_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__5));
v___x_1124_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8));
v___x_1125_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1126_ = lean_unsigned_to_nat(3u);
v___x_1127_ = lean_mk_empty_array_with_capacity(v___x_1126_);
lean_inc_ref(v_projectDir_1110_);
v___x_1128_ = lean_array_push(v___x_1127_, v_projectDir_1110_);
lean_inc_ref(v_leanPrefix_1118_);
v___x_1129_ = lean_array_push(v___x_1128_, v_leanPrefix_1118_);
lean_inc_ref(v_lakeHome_1120_);
v___x_1130_ = lean_array_push(v___x_1129_, v_lakeHome_1120_);
v___x_1131_ = lean_array_push(v___x_1122_, v___x_1115_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1134_ = 1;
v___x_1135_ = lean_box(0);
lean_inc_ref(v_whichLake_1119_);
v___x_1136_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1136_, 0, v_whichLake_1119_);
lean_ctor_set(v___x_1136_, 1, v___x_1123_);
lean_ctor_set(v___x_1136_, 2, v___x_1124_);
lean_ctor_set(v___x_1136_, 3, v___x_1125_);
lean_ctor_set(v___x_1136_, 4, v___x_1130_);
lean_ctor_set(v___x_1136_, 5, v___x_1131_);
lean_ctor_set(v___x_1136_, 6, v___x_1133_);
lean_ctor_set(v___x_1136_, 7, v___x_1135_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*8, v___x_1134_);
v___x_1137_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v___x_1136_, v___y_1117_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1166_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc_n(v_a_1138_, 2);
lean_dec_ref_known(v___x_1137_, 1);
v___x_1139_ = lean_string_utf8_byte_size(v_a_1138_);
v___x_1140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1140_, 0, v_a_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1132_);
lean_ctor_set(v___x_1140_, 2, v___x_1139_);
v___x_1141_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(v___x_1140_);
v___x_1142_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1138_, v___x_1140_, v___x_1139_, v___x_1141_, v___x_1133_);
lean_dec_ref_known(v___x_1140_, 3);
v___x_1143_ = lean_array_to_list(v___x_1142_);
v___x_1144_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__15));
v___x_1145_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v___x_1143_, v___x_1144_);
lean_dec(v___x_1143_);
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1166_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1166_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_fst_1150_; lean_object* v_snd_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1165_; 
v_fst_1150_ = lean_ctor_get(v_a_1146_, 0);
v_snd_1151_ = lean_ctor_get(v_a_1146_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_a_1146_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1153_ = v_a_1146_;
v_isShared_1154_ = v_isSharedCheck_1165_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_snd_1151_);
lean_inc(v_fst_1150_);
lean_dec(v_a_1146_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1165_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_string_utf8_byte_size(v_fst_1150_);
v___x_1156_ = lean_nat_dec_eq(v___x_1155_, v___x_1132_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = lean_string_utf8_byte_size(v_snd_1151_);
v___x_1158_ = lean_nat_dec_eq(v___x_1157_, v___x_1132_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1160_; 
if (v_isShared_1154_ == 0)
{
v___x_1160_ = v___x_1153_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_fst_1150_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_snd_1151_);
v___x_1160_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1162_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1160_);
v___x_1162_ = v___x_1148_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
else
{
lean_del_object(v___x_1153_);
lean_dec(v_snd_1151_);
lean_dec(v_fst_1150_);
lean_del_object(v___x_1148_);
goto v___jp_1105_;
}
}
else
{
lean_del_object(v___x_1153_);
lean_dec(v_snd_1151_);
lean_dec(v_fst_1150_);
lean_del_object(v___x_1148_);
goto v___jp_1105_;
}
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_a_1167_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1137_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1137_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
v_a_1185_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1109_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1109_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
v___jp_1105_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__1));
v___x_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___boxed(lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v_a_1193_);
lean_dec_ref(v_a_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(lean_object* v_a_1196_, lean_object* v___x_1197_, lean_object* v___x_1198_, lean_object* v_inst_1199_, lean_object* v_R_1200_, lean_object* v_a_1201_, lean_object* v_b_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1196_, v___x_1197_, v___x_1198_, v_a_1201_, v_b_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___boxed(lean_object* v_a_1204_, lean_object* v___x_1205_, lean_object* v___x_1206_, lean_object* v_inst_1207_, lean_object* v_R_1208_, lean_object* v_a_1209_, lean_object* v_b_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(v_a_1204_, v___x_1205_, v___x_1206_, v_inst_1207_, v_R_1208_, v_a_1209_, v_b_1210_);
lean_dec_ref(v___x_1205_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(lean_object* v_as_1212_, lean_object* v_as_x27_1213_, lean_object* v_b_1214_, lean_object* v_a_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_1213_, v_b_1214_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___boxed(lean_object* v_as_1219_, lean_object* v_as_x27_1220_, lean_object* v_b_1221_, lean_object* v_a_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(v_as_1219_, v_as_x27_1220_, v_b_1221_, v_a_1222_, v___y_1223_);
lean_dec_ref(v___y_1223_);
lean_dec(v_as_x27_1220_);
lean_dec(v_as_1219_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(lean_object* v_a_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_1242_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1241_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_projectDir_1243_; lean_object* v_leanPrefix_1244_; lean_object* v_whichLake_1245_; lean_object* v_lakeHome_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___y_1250_; lean_object* v_leanPrefix_1251_; lean_object* v_whichLake_1252_; lean_object* v_lakeHome_1253_; uint8_t v___x_1270_; 
lean_dec_ref_known(v___x_1242_, 1);
v_projectDir_1243_ = lean_ctor_get(v_a_1239_, 0);
v_leanPrefix_1244_ = lean_ctor_get(v_a_1239_, 6);
v_whichLake_1245_ = lean_ctor_get(v_a_1239_, 10);
v_lakeHome_1246_ = lean_ctor_get(v_a_1239_, 11);
v___x_1247_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1243_);
v___x_1248_ = l_System_FilePath_join(v_projectDir_1243_, v___x_1247_);
v___x_1270_ = l_System_FilePath_pathExists(v___x_1248_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_io_create_dir(v___x_1248_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_dec_ref_known(v___x_1271_, 1);
v___y_1250_ = v_a_1239_;
v_leanPrefix_1251_ = v_leanPrefix_1244_;
v_whichLake_1252_ = v_whichLake_1245_;
v_lakeHome_1253_ = v_lakeHome_1246_;
goto v___jp_1249_;
}
else
{
lean_dec_ref(v___x_1248_);
return v___x_1271_;
}
}
else
{
v___y_1250_ = v_a_1239_;
v_leanPrefix_1251_ = v_leanPrefix_1244_;
v_whichLake_1252_ = v_whichLake_1245_;
v_lakeHome_1253_ = v_lakeHome_1246_;
goto v___jp_1249_;
}
v___jp_1249_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1254_ = lean_unsigned_to_nat(1u);
v___x_1255_ = lean_mk_empty_array_with_capacity(v___x_1254_);
v___x_1256_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__1));
v___x_1257_ = lean_unsigned_to_nat(3u);
v___x_1258_ = lean_mk_empty_array_with_capacity(v___x_1257_);
v___x_1259_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2));
v___x_1260_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
lean_inc_ref(v_projectDir_1243_);
v___x_1261_ = lean_array_push(v___x_1258_, v_projectDir_1243_);
lean_inc_ref(v_leanPrefix_1251_);
v___x_1262_ = lean_array_push(v___x_1261_, v_leanPrefix_1251_);
lean_inc_ref(v_lakeHome_1253_);
v___x_1263_ = lean_array_push(v___x_1262_, v_lakeHome_1253_);
v___x_1264_ = lean_array_push(v___x_1255_, v___x_1248_);
v___x_1265_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1266_ = 1;
v___x_1267_ = lean_box(0);
lean_inc_ref(v_whichLake_1252_);
v___x_1268_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1268_, 0, v_whichLake_1252_);
lean_ctor_set(v___x_1268_, 1, v___x_1256_);
lean_ctor_set(v___x_1268_, 2, v___x_1259_);
lean_ctor_set(v___x_1268_, 3, v___x_1260_);
lean_ctor_set(v___x_1268_, 4, v___x_1263_);
lean_ctor_set(v___x_1268_, 5, v___x_1264_);
lean_ctor_set(v___x_1268_, 6, v___x_1265_);
lean_ctor_set(v___x_1268_, 7, v___x_1267_);
lean_ctor_set_uint8(v___x_1268_, sizeof(void*)*8, v___x_1266_);
v___x_1269_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_1268_, v___y_1250_);
return v___x_1269_;
}
}
else
{
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___boxed(lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_1272_);
lean_dec_ref(v_a_1272_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg(lean_object* v_f_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v_fst_1289_; lean_object* v_snd_1290_; lean_object* v_r_1291_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v_fst_1289_ = lean_ctor_get(v_a_1288_, 0);
lean_inc(v_fst_1289_);
v_snd_1290_ = lean_ctor_get(v_a_1288_, 1);
lean_inc_n(v_snd_1290_, 2);
lean_dec(v_a_1288_);
lean_inc_ref(v___y_1285_);
v_r_1291_ = lean_apply_4(v_f_1284_, v_fst_1289_, v_snd_1290_, v___y_1285_, lean_box(0));
if (lean_obj_tag(v_r_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1293_; 
v_a_1292_ = lean_ctor_get(v_r_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v_r_1291_, 1);
v___x_1293_ = lean_io_remove_file(v_snd_1290_);
lean_dec(v_snd_1290_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v___x_1293_, 0);
lean_dec(v_unused_1301_);
v___x_1295_ = v___x_1293_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_dec(v___x_1293_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v_a_1292_);
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1292_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v_a_1292_);
v_a_1302_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1293_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1293_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1311_; 
v_a_1310_ = lean_ctor_get(v_r_1291_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v_r_1291_, 1);
v___x_1311_ = lean_io_remove_file(v_snd_1290_);
lean_dec(v_snd_1290_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v___x_1311_, 0);
lean_dec(v_unused_1319_);
v___x_1313_ = v___x_1311_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_dec(v___x_1311_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set_tag(v___x_1313_, 1);
lean_ctor_set(v___x_1313_, 0, v_a_1310_);
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1310_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v_a_1310_);
v_a_1320_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1311_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1311_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_f_1284_);
v_a_1328_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1287_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1287_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg___boxed(lean_object* v_f_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg(v_f_1336_, v___y_1337_);
lean_dec_ref(v___y_1337_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0(lean_object* v_00_u03b1_1340_, lean_object* v_f_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg(v_f_1341_, v___y_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_f_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0(v_00_u03b1_1345_, v_f_1346_, v___y_1347_);
lean_dec_ref(v___y_1347_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0(lean_object* v_projectDir_1365_, lean_object* v_f_1366_, lean_object* v_handle_1367_, lean_object* v_path_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_leanPrefix_1371_; lean_object* v_whichLake_1372_; lean_object* v_lakeHome_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_leanPrefix_1371_ = lean_ctor_get(v___y_1369_, 6);
v_whichLake_1372_ = lean_ctor_get(v___y_1369_, 10);
v_lakeHome_1373_ = lean_ctor_get(v___y_1369_, 11);
v___x_1374_ = lean_unsigned_to_nat(1u);
v___x_1375_ = lean_mk_empty_array_with_capacity(v___x_1374_);
v___x_1376_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__1));
v___x_1377_ = lean_unsigned_to_nat(3u);
v___x_1378_ = lean_mk_empty_array_with_capacity(v___x_1377_);
v___x_1379_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2));
v___x_1380_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__4));
lean_inc_ref(v_projectDir_1365_);
v___x_1381_ = lean_array_push(v___x_1378_, v_projectDir_1365_);
lean_inc_ref(v_leanPrefix_1371_);
v___x_1382_ = lean_array_push(v___x_1381_, v_leanPrefix_1371_);
lean_inc_ref(v_lakeHome_1373_);
v___x_1383_ = lean_array_push(v___x_1382_, v_lakeHome_1373_);
v___x_1384_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
v___x_1385_ = l_System_FilePath_join(v_projectDir_1365_, v___x_1384_);
v___x_1386_ = lean_array_push(v___x_1375_, v___x_1385_);
v___x_1387_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1388_ = 0;
v___x_1389_ = lean_box(0);
lean_inc_ref(v_whichLake_1372_);
v___x_1390_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1390_, 0, v_whichLake_1372_);
lean_ctor_set(v___x_1390_, 1, v___x_1376_);
lean_ctor_set(v___x_1390_, 2, v___x_1379_);
lean_ctor_set(v___x_1390_, 3, v___x_1380_);
lean_ctor_set(v___x_1390_, 4, v___x_1383_);
lean_ctor_set(v___x_1390_, 5, v___x_1386_);
lean_ctor_set(v___x_1390_, 6, v___x_1387_);
lean_ctor_set(v___x_1390_, 7, v___x_1389_);
lean_ctor_set_uint8(v___x_1390_, sizeof(void*)*8, v___x_1388_);
v___x_1391_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_handle_1367_, v___x_1390_, v___y_1369_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v___x_1392_; 
lean_dec_ref_known(v___x_1391_, 1);
lean_inc_ref(v___y_1369_);
v___x_1392_ = lean_apply_3(v_f_1366_, v_path_1368_, v___y_1369_, lean_box(0));
return v___x_1392_;
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref(v_path_1368_);
lean_dec_ref(v_f_1366_);
v_a_1393_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1391_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1391_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___boxed(lean_object* v_projectDir_1401_, lean_object* v_f_1402_, lean_object* v_handle_1403_, lean_object* v_path_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0(v_projectDir_1401_, v_f_1402_, v_handle_1403_, v_path_1404_, v___y_1405_);
lean_dec_ref(v___y_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(lean_object* v_f_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___closed__0));
v___x_1413_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1412_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_projectDir_1414_; lean_object* v___f_1415_; lean_object* v___x_1416_; 
lean_dec_ref_known(v___x_1413_, 1);
v_projectDir_1414_ = lean_ctor_get(v_a_1410_, 0);
lean_inc_ref(v_projectDir_1414_);
v___f_1415_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_1415_, 0, v_projectDir_1414_);
lean_closure_set(v___f_1415_, 1, v_f_1409_);
v___x_1416_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg(v___f_1415_, v_a_1410_);
return v___x_1416_;
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v_f_1409_);
v_a_1417_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1413_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1413_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___boxed(lean_object* v_f_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v_f_1425_, v_a_1426_);
lean_dec_ref(v_a_1426_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(lean_object* v_00_u03b1_1429_, lean_object* v_f_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v_f_1430_, v_a_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___boxed(lean_object* v_00_u03b1_1434_, lean_object* v_f_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(v_00_u03b1_1434_, v_f_1435_, v_a_1436_);
lean_dec_ref(v_a_1436_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(size_t v_sz_1439_, size_t v_i_1440_, lean_object* v_bs_1441_){
_start:
{
uint8_t v___x_1442_; 
v___x_1442_ = lean_usize_dec_lt(v_i_1440_, v_sz_1439_);
if (v___x_1442_ == 0)
{
return v_bs_1441_;
}
else
{
lean_object* v_v_1443_; lean_object* v___x_1444_; lean_object* v_bs_x27_1445_; lean_object* v___x_1446_; size_t v___x_1447_; size_t v___x_1448_; lean_object* v___x_1449_; 
v_v_1443_ = lean_array_uget(v_bs_1441_, v_i_1440_);
v___x_1444_ = lean_unsigned_to_nat(0u);
v_bs_x27_1445_ = lean_array_uset(v_bs_1441_, v_i_1440_, v___x_1444_);
v___x_1446_ = l_Lean_Name_toString(v_v_1443_, v___x_1442_);
v___x_1447_ = ((size_t)1ULL);
v___x_1448_ = lean_usize_add(v_i_1440_, v___x_1447_);
v___x_1449_ = lean_array_uset(v_bs_x27_1445_, v_i_1440_, v___x_1446_);
v_i_1440_ = v___x_1448_;
v_bs_1441_ = v___x_1449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0___boxed(lean_object* v_sz_1451_, lean_object* v_i_1452_, lean_object* v_bs_1453_){
_start:
{
size_t v_sz_boxed_1454_; size_t v_i_boxed_1455_; lean_object* v_res_1456_; 
v_sz_boxed_1454_ = lean_unbox_usize(v_sz_1451_);
lean_dec(v_sz_1451_);
v_i_boxed_1455_ = lean_unbox_usize(v_i_1452_);
lean_dec(v_i_1452_);
v_res_1456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_boxed_1454_, v_i_boxed_1455_, v_bs_1453_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(lean_object* v_targets_1464_, lean_object* v_a_1465_){
_start:
{
size_t v_sz_1467_; size_t v___x_1468_; lean_object* v_targetArgs_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v_targetList_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_sz_1467_ = lean_array_size(v_targets_1464_);
v___x_1468_ = ((size_t)0ULL);
v_targetArgs_1469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_1467_, v___x_1468_, v_targets_1464_);
v___x_1470_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
lean_inc_ref(v_targetArgs_1469_);
v___x_1471_ = lean_array_to_list(v_targetArgs_1469_);
v_targetList_1472_ = l_String_intercalate(v___x_1470_, v___x_1471_);
v___x_1473_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1));
v___x_1474_ = lean_string_append(v___x_1473_, v_targetList_1472_);
lean_dec_ref(v_targetList_1472_);
v___x_1475_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1474_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_projectDir_1476_; lean_object* v_leanPrefix_1477_; lean_object* v_whichLake_1478_; lean_object* v_lakeHome_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___y_1483_; lean_object* v_leanPrefix_1484_; lean_object* v_whichLake_1485_; lean_object* v_lakeHome_1486_; uint8_t v___x_1504_; 
lean_dec_ref_known(v___x_1475_, 1);
v_projectDir_1476_ = lean_ctor_get(v_a_1465_, 0);
v_leanPrefix_1477_ = lean_ctor_get(v_a_1465_, 6);
v_whichLake_1478_ = lean_ctor_get(v_a_1465_, 10);
v_lakeHome_1479_ = lean_ctor_get(v_a_1465_, 11);
v___x_1480_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1476_);
v___x_1481_ = l_System_FilePath_join(v_projectDir_1476_, v___x_1480_);
v___x_1504_ = l_System_FilePath_pathExists(v___x_1481_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_io_create_dir(v___x_1481_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_dec_ref_known(v___x_1505_, 1);
v___y_1483_ = v_a_1465_;
v_leanPrefix_1484_ = v_leanPrefix_1477_;
v_whichLake_1485_ = v_whichLake_1478_;
v_lakeHome_1486_ = v_lakeHome_1479_;
goto v___jp_1482_;
}
else
{
lean_dec_ref(v___x_1481_);
lean_dec_ref(v_targetArgs_1469_);
return v___x_1505_;
}
}
else
{
v___y_1483_ = v_a_1465_;
v_leanPrefix_1484_ = v_leanPrefix_1477_;
v_whichLake_1485_ = v_whichLake_1478_;
v_lakeHome_1486_ = v_lakeHome_1479_;
goto v___jp_1482_;
}
v___jp_1482_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1487_ = lean_unsigned_to_nat(1u);
v___x_1488_ = lean_mk_empty_array_with_capacity(v___x_1487_);
v___x_1489_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3));
v___x_1490_ = l_Array_append___redArg(v___x_1489_, v_targetArgs_1469_);
lean_dec_ref(v_targetArgs_1469_);
v___x_1491_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8));
v___x_1492_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1493_ = lean_unsigned_to_nat(3u);
v___x_1494_ = lean_mk_empty_array_with_capacity(v___x_1493_);
lean_inc_ref(v_projectDir_1476_);
v___x_1495_ = lean_array_push(v___x_1494_, v_projectDir_1476_);
lean_inc_ref(v_leanPrefix_1484_);
v___x_1496_ = lean_array_push(v___x_1495_, v_leanPrefix_1484_);
lean_inc_ref(v_lakeHome_1486_);
v___x_1497_ = lean_array_push(v___x_1496_, v_lakeHome_1486_);
v___x_1498_ = lean_array_push(v___x_1488_, v___x_1481_);
v___x_1499_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1500_ = 0;
v___x_1501_ = lean_box(0);
lean_inc_ref(v_whichLake_1485_);
v___x_1502_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1502_, 0, v_whichLake_1485_);
lean_ctor_set(v___x_1502_, 1, v___x_1490_);
lean_ctor_set(v___x_1502_, 2, v___x_1491_);
lean_ctor_set(v___x_1502_, 3, v___x_1492_);
lean_ctor_set(v___x_1502_, 4, v___x_1497_);
lean_ctor_set(v___x_1502_, 5, v___x_1498_);
lean_ctor_set(v___x_1502_, 6, v___x_1499_);
lean_ctor_set(v___x_1502_, 7, v___x_1501_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*8, v___x_1500_);
v___x_1503_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_1502_, v___y_1483_);
return v___x_1503_;
}
}
else
{
lean_dec_ref(v_targetArgs_1469_);
return v___x_1475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___boxed(lean_object* v_targets_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v_targets_1506_, v_a_1507_);
lean_dec_ref(v_a_1507_);
return v_res_1509_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1519_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11));
v___x_1520_ = lean_unsigned_to_nat(3u);
v___x_1521_ = lean_mk_empty_array_with_capacity(v___x_1520_);
v___x_1522_ = lean_array_push(v___x_1521_, v___x_1519_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(lean_object* v_projectDir_1523_, lean_object* v_whichLean4Export_1524_, lean_object* v_args_1525_, lean_object* v_f_1526_, lean_object* v_exportHandle_1527_, lean_object* v_exportPath_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_leanPrefix_1531_; lean_object* v_leanPath_1532_; lean_object* v_binPath_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_leanPrefix_1531_ = lean_ctor_get(v___y_1529_, 6);
v_leanPath_1532_ = lean_ctor_get(v___y_1529_, 7);
v_binPath_1533_ = lean_ctor_get(v___y_1529_, 8);
v___x_1534_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6));
v___x_1535_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__0));
v___x_1536_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__1));
lean_inc_ref(v_leanPath_1532_);
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_leanPath_1532_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1535_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
lean_inc_ref(v_binPath_1533_);
v___x_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1539_, 0, v_binPath_1533_);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1534_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2);
v___x_1542_ = lean_array_push(v___x_1541_, v___x_1538_);
v___x_1543_ = lean_array_push(v___x_1542_, v___x_1540_);
v___x_1544_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1523_);
v___x_1545_ = l_System_FilePath_join(v_projectDir_1523_, v___x_1544_);
v___x_1546_ = lean_unsigned_to_nat(4u);
v___x_1547_ = lean_mk_empty_array_with_capacity(v___x_1546_);
v___x_1548_ = lean_array_push(v___x_1547_, v_projectDir_1523_);
v___x_1549_ = lean_array_push(v___x_1548_, v___x_1545_);
lean_inc_ref(v_leanPrefix_1531_);
v___x_1550_ = lean_array_push(v___x_1549_, v_leanPrefix_1531_);
lean_inc_ref(v_whichLean4Export_1524_);
v___x_1551_ = lean_array_push(v___x_1550_, v_whichLean4Export_1524_);
v___x_1552_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1553_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1554_ = 0;
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1556_, 0, v_whichLean4Export_1524_);
lean_ctor_set(v___x_1556_, 1, v_args_1525_);
lean_ctor_set(v___x_1556_, 2, v___x_1536_);
lean_ctor_set(v___x_1556_, 3, v___x_1543_);
lean_ctor_set(v___x_1556_, 4, v___x_1551_);
lean_ctor_set(v___x_1556_, 5, v___x_1552_);
lean_ctor_set(v___x_1556_, 6, v___x_1553_);
lean_ctor_set(v___x_1556_, 7, v___x_1555_);
lean_ctor_set_uint8(v___x_1556_, sizeof(void*)*8, v___x_1554_);
v___x_1557_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_exportHandle_1527_, v___x_1556_, v___y_1529_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; 
lean_dec_ref_known(v___x_1557_, 1);
lean_inc_ref(v___y_1529_);
v___x_1558_ = lean_apply_3(v_f_1526_, v_exportPath_1528_, v___y_1529_, lean_box(0));
return v___x_1558_;
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec_ref(v_exportPath_1528_);
lean_dec_ref(v_f_1526_);
v_a_1559_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1557_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1557_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___boxed(lean_object* v_projectDir_1567_, lean_object* v_whichLean4Export_1568_, lean_object* v_args_1569_, lean_object* v_f_1570_, lean_object* v_exportHandle_1571_, lean_object* v_exportPath_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(v_projectDir_1567_, v_whichLean4Export_1568_, v_args_1569_, v_f_1570_, v_exportHandle_1571_, v_exportPath_1572_, v___y_1573_);
lean_dec_ref(v___y_1573_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(lean_object* v_args_1576_, lean_object* v_f_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_projectDir_1580_; lean_object* v_whichLean4Export_1581_; lean_object* v___f_1582_; lean_object* v___x_1583_; 
v_projectDir_1580_ = lean_ctor_get(v_a_1578_, 0);
v_whichLean4Export_1581_ = lean_ctor_get(v_a_1578_, 12);
lean_inc_ref(v_whichLean4Export_1581_);
lean_inc_ref(v_projectDir_1580_);
v___f_1582_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_1582_, 0, v_projectDir_1580_);
lean_closure_set(v___f_1582_, 1, v_whichLean4Export_1581_);
lean_closure_set(v___f_1582_, 2, v_args_1576_);
lean_closure_set(v___f_1582_, 3, v_f_1577_);
v___x_1583_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg(v___f_1582_, v_a_1578_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___boxed(lean_object* v_args_1584_, lean_object* v_f_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v_args_1584_, v_f_1585_, v_a_1586_);
lean_dec_ref(v_a_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(lean_object* v_00_u03b1_1589_, lean_object* v_args_1590_, lean_object* v_f_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v_args_1590_, v_f_1591_, v_a_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___boxed(lean_object* v_00_u03b1_1595_, lean_object* v_args_1596_, lean_object* v_f_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(v_00_u03b1_1595_, v_args_1596_, v_f_1597_, v_a_1598_);
lean_dec_ref(v_a_1598_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0(lean_object* v_x_1602_, lean_object* v_x_1603_){
_start:
{
if (lean_obj_tag(v_x_1603_) == 0)
{
return v_x_1602_;
}
else
{
lean_object* v_head_1604_; lean_object* v_tail_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_head_1604_ = lean_ctor_get(v_x_1603_, 0);
lean_inc(v_head_1604_);
v_tail_1605_ = lean_ctor_get(v_x_1603_, 1);
lean_inc(v_tail_1605_);
lean_dec_ref_known(v_x_1603_, 2);
v___x_1606_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0));
v___x_1607_ = lean_string_append(v_x_1602_, v___x_1606_);
v___x_1608_ = 1;
v___x_1609_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1604_, v___x_1608_);
v___x_1610_ = lean_string_append(v___x_1607_, v___x_1609_);
lean_dec_ref(v___x_1609_);
v_x_1602_ = v___x_1610_;
v_x_1603_ = v_tail_1605_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0(lean_object* v_x_1615_){
_start:
{
if (lean_obj_tag(v_x_1615_) == 0)
{
lean_object* v___x_1616_; 
v___x_1616_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__0));
return v___x_1616_;
}
else
{
lean_object* v_tail_1617_; 
v_tail_1617_ = lean_ctor_get(v_x_1615_, 1);
if (lean_obj_tag(v_tail_1617_) == 0)
{
lean_object* v_head_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v_head_1618_ = lean_ctor_get(v_x_1615_, 0);
lean_inc(v_head_1618_);
lean_dec_ref_known(v_x_1615_, 2);
v___x_1619_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_1620_ = 1;
v___x_1621_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1618_, v___x_1620_);
v___x_1622_ = lean_string_append(v___x_1619_, v___x_1621_);
lean_dec_ref(v___x_1621_);
v___x_1623_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__2));
v___x_1624_ = lean_string_append(v___x_1622_, v___x_1623_);
return v___x_1624_;
}
else
{
lean_object* v_head_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint32_t v___x_1631_; lean_object* v___x_1632_; 
lean_inc(v_tail_1617_);
v_head_1625_ = lean_ctor_get(v_x_1615_, 0);
lean_inc(v_head_1625_);
lean_dec_ref_known(v_x_1615_, 2);
v___x_1626_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_1627_ = 1;
v___x_1628_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1625_, v___x_1627_);
v___x_1629_ = lean_string_append(v___x_1626_, v___x_1628_);
lean_dec_ref(v___x_1628_);
v___x_1630_ = l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0(v___x_1629_, v_tail_1617_);
v___x_1631_ = 93;
v___x_1632_ = lean_string_push(v___x_1630_, v___x_1631_);
return v___x_1632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(size_t v_sz_1633_, size_t v_i_1634_, lean_object* v_bs_1635_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_usize_dec_lt(v_i_1634_, v_sz_1633_);
if (v___x_1636_ == 0)
{
return v_bs_1635_;
}
else
{
lean_object* v_v_1637_; lean_object* v___x_1638_; lean_object* v_bs_x27_1639_; lean_object* v___x_1640_; size_t v___x_1641_; size_t v___x_1642_; lean_object* v___x_1643_; 
v_v_1637_ = lean_array_uget(v_bs_1635_, v_i_1634_);
v___x_1638_ = lean_unsigned_to_nat(0u);
v_bs_x27_1639_ = lean_array_uset(v_bs_1635_, v_i_1634_, v___x_1638_);
v___x_1640_ = l_Lean_Name_toString(v_v_1637_, v___x_1636_);
v___x_1641_ = ((size_t)1ULL);
v___x_1642_ = lean_usize_add(v_i_1634_, v___x_1641_);
v___x_1643_ = lean_array_uset(v_bs_x27_1639_, v_i_1634_, v___x_1640_);
v_i_1634_ = v___x_1642_;
v_bs_1635_ = v___x_1643_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1___boxed(lean_object* v_sz_1645_, lean_object* v_i_1646_, lean_object* v_bs_1647_){
_start:
{
size_t v_sz_boxed_1648_; size_t v_i_boxed_1649_; lean_object* v_res_1650_; 
v_sz_boxed_1648_ = lean_unbox_usize(v_sz_1645_);
lean_dec(v_sz_1645_);
v_i_boxed_1649_ = lean_unbox_usize(v_i_1646_);
lean_dec(v_i_1646_);
v_res_1650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(v_sz_boxed_1648_, v_i_boxed_1649_, v_bs_1647_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(lean_object* v_module_1654_, lean_object* v_decls_1655_, lean_object* v_f_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1659_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__0));
v___x_1660_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__1));
lean_inc_ref(v_decls_1655_);
v___x_1661_ = lean_array_to_list(v_decls_1655_);
v___x_1662_ = l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0(v___x_1661_);
v___x_1663_ = lean_string_append(v___x_1660_, v___x_1662_);
lean_dec_ref(v___x_1662_);
v___x_1664_ = lean_string_append(v___x_1659_, v___x_1663_);
lean_dec_ref(v___x_1663_);
v___x_1665_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__2));
v___x_1666_ = lean_string_append(v___x_1664_, v___x_1665_);
v___x_1667_ = 1;
lean_inc(v_module_1654_);
v___x_1668_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_1654_, v___x_1667_);
v___x_1669_ = lean_string_append(v___x_1666_, v___x_1668_);
lean_dec_ref(v___x_1668_);
v___x_1670_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1669_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; size_t v_sz_1677_; size_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec_ref_known(v___x_1670_, 1);
v___x_1671_ = l_Lean_Name_toString(v_module_1654_, v___x_1667_);
v___x_1672_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__8));
v___x_1673_ = lean_unsigned_to_nat(2u);
v___x_1674_ = lean_mk_empty_array_with_capacity(v___x_1673_);
v___x_1675_ = lean_array_push(v___x_1674_, v___x_1671_);
v___x_1676_ = lean_array_push(v___x_1675_, v___x_1672_);
v_sz_1677_ = lean_array_size(v_decls_1655_);
v___x_1678_ = ((size_t)0ULL);
v___x_1679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(v_sz_1677_, v___x_1678_, v_decls_1655_);
v___x_1680_ = l_Array_append___redArg(v___x_1676_, v___x_1679_);
lean_dec_ref(v___x_1679_);
v___x_1681_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v___x_1680_, v_f_1656_, v_a_1657_);
return v___x_1681_;
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec_ref(v_f_1656_);
lean_dec_ref(v_decls_1655_);
lean_dec(v_module_1654_);
v_a_1682_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1670_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1670_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___boxed(lean_object* v_module_1690_, lean_object* v_decls_1691_, lean_object* v_f_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1690_, v_decls_1691_, v_f_1692_, v_a_1693_);
lean_dec_ref(v_a_1693_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(lean_object* v_00_u03b1_1696_, lean_object* v_module_1697_, lean_object* v_decls_1698_, lean_object* v_f_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1697_, v_decls_1698_, v_f_1699_, v_a_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_module_1704_, lean_object* v_decls_1705_, lean_object* v_f_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(v_00_u03b1_1703_, v_module_1704_, v_decls_1705_, v_f_1706_, v_a_1707_);
lean_dec_ref(v_a_1707_);
return v_res_1709_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(lean_object* v_s_1710_, lean_object* v_a_1711_, uint8_t v_b_1712_){
_start:
{
uint8_t v___x_1713_; 
v___x_1713_ = 0;
switch(lean_obj_tag(v_a_1711_))
{
case 0:
{
lean_object* v_pos_1714_; lean_object* v_startInclusive_1715_; lean_object* v_endExclusive_1716_; lean_object* v___x_1717_; uint8_t v_decide_1718_; 
v_pos_1714_ = lean_ctor_get(v_a_1711_, 0);
lean_inc(v_pos_1714_);
lean_dec_ref_known(v_a_1711_, 1);
v_startInclusive_1715_ = lean_ctor_get(v_s_1710_, 1);
v_endExclusive_1716_ = lean_ctor_get(v_s_1710_, 2);
v___x_1717_ = lean_nat_sub(v_endExclusive_1716_, v_startInclusive_1715_);
v_decide_1718_ = lean_nat_dec_eq(v_pos_1714_, v___x_1717_);
lean_dec(v___x_1717_);
lean_dec(v_pos_1714_);
if (v_decide_1718_ == 0)
{
uint8_t v___x_1719_; 
v___x_1719_ = 1;
return v___x_1719_;
}
else
{
return v_decide_1718_;
}
}
case 1:
{
lean_object* v_pos_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1733_; 
v_pos_1720_ = lean_ctor_get(v_a_1711_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_a_1711_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1722_ = v_a_1711_;
v_isShared_1723_ = v_isSharedCheck_1733_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_pos_1720_);
lean_dec(v_a_1711_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1733_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v_str_1724_; lean_object* v_startInclusive_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v_str_1724_ = lean_ctor_get(v_s_1710_, 0);
v_startInclusive_1725_ = lean_ctor_get(v_s_1710_, 1);
v___x_1726_ = lean_nat_add(v_startInclusive_1725_, v_pos_1720_);
lean_dec(v_pos_1720_);
v___x_1727_ = lean_string_utf8_next_fast(v_str_1724_, v___x_1726_);
lean_dec(v___x_1726_);
v___x_1728_ = lean_nat_sub(v___x_1727_, v_startInclusive_1725_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set_tag(v___x_1722_, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1728_);
v___x_1730_ = v___x_1722_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
v_a_1711_ = v___x_1730_;
v_b_1712_ = v___x_1713_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_1734_; lean_object* v_table_1735_; lean_object* v_stackPos_1736_; lean_object* v_needlePos_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1792_; 
v_needle_1734_ = lean_ctor_get(v_a_1711_, 0);
v_table_1735_ = lean_ctor_get(v_a_1711_, 1);
v_stackPos_1736_ = lean_ctor_get(v_a_1711_, 2);
v_needlePos_1737_ = lean_ctor_get(v_a_1711_, 3);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_a_1711_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1739_ = v_a_1711_;
v_isShared_1740_ = v_isSharedCheck_1792_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_needlePos_1737_);
lean_inc(v_stackPos_1736_);
lean_inc(v_table_1735_);
lean_inc(v_needle_1734_);
lean_dec(v_a_1711_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1792_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v_str_1741_; lean_object* v_startInclusive_1742_; lean_object* v_endExclusive_1743_; lean_object* v_str_1744_; lean_object* v_startInclusive_1745_; lean_object* v_endExclusive_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v_str_1741_ = lean_ctor_get(v_needle_1734_, 0);
v_startInclusive_1742_ = lean_ctor_get(v_needle_1734_, 1);
v_endExclusive_1743_ = lean_ctor_get(v_needle_1734_, 2);
v_str_1744_ = lean_ctor_get(v_s_1710_, 0);
v_startInclusive_1745_ = lean_ctor_get(v_s_1710_, 1);
v_endExclusive_1746_ = lean_ctor_get(v_s_1710_, 2);
v___x_1747_ = lean_nat_sub(v_stackPos_1736_, v_needlePos_1737_);
v___x_1748_ = lean_nat_sub(v_endExclusive_1743_, v_startInclusive_1742_);
v___x_1749_ = lean_nat_add(v___x_1747_, v___x_1748_);
v___x_1750_ = lean_nat_sub(v_endExclusive_1746_, v_startInclusive_1745_);
v___x_1751_ = lean_nat_dec_le(v___x_1749_, v___x_1750_);
lean_dec(v___x_1749_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
lean_dec(v___x_1748_);
lean_del_object(v___x_1739_);
lean_dec(v_needlePos_1737_);
lean_dec(v_stackPos_1736_);
lean_dec_ref(v_table_1735_);
lean_dec_ref(v_needle_1734_);
v___x_1752_ = lean_unsigned_to_nat(1u);
v___x_1753_ = lean_nat_add(v___x_1747_, v___x_1752_);
lean_dec(v___x_1747_);
v___x_1754_ = lean_nat_dec_le(v___x_1753_, v___x_1750_);
lean_dec(v___x_1750_);
lean_dec(v___x_1753_);
if (v___x_1754_ == 0)
{
return v_b_1712_;
}
else
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_box(3);
v_a_1711_ = v___x_1755_;
v_b_1712_ = v___x_1713_;
goto _start;
}
}
else
{
lean_object* v___x_1757_; uint8_t v_stackByte_1758_; lean_object* v___x_1759_; uint8_t v_patByte_1760_; uint8_t v___x_1761_; 
lean_dec(v___x_1750_);
lean_dec(v___x_1747_);
v___x_1757_ = lean_nat_add(v_startInclusive_1745_, v_stackPos_1736_);
v_stackByte_1758_ = lean_string_get_byte_fast(v_str_1744_, v___x_1757_);
v___x_1759_ = lean_nat_add(v_startInclusive_1742_, v_needlePos_1737_);
v_patByte_1760_ = lean_string_get_byte_fast(v_str_1741_, v___x_1759_);
v___x_1761_ = lean_uint8_dec_eq(v_stackByte_1758_, v_patByte_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; uint8_t v_decide_1763_; 
lean_dec(v___x_1748_);
v___x_1762_ = lean_unsigned_to_nat(0u);
v_decide_1763_ = lean_nat_dec_eq(v_needlePos_1737_, v___x_1762_);
if (v_decide_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v_newNeedlePos_1766_; uint8_t v___x_1767_; 
v___x_1764_ = lean_unsigned_to_nat(1u);
v___x_1765_ = lean_nat_sub(v_needlePos_1737_, v___x_1764_);
lean_dec(v_needlePos_1737_);
v_newNeedlePos_1766_ = lean_array_fget_borrowed(v_table_1735_, v___x_1765_);
lean_dec(v___x_1765_);
v___x_1767_ = lean_nat_dec_eq(v_newNeedlePos_1766_, v___x_1762_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1769_; 
lean_inc(v_newNeedlePos_1766_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 3, v_newNeedlePos_1766_);
v___x_1769_ = v___x_1739_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_needle_1734_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_table_1735_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v_stackPos_1736_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v_newNeedlePos_1766_);
v___x_1769_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
v_a_1711_ = v___x_1769_;
v_b_1712_ = v___x_1713_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_1772_; lean_object* v___x_1774_; 
v_nextStackPos_1772_ = l_String_Slice_posGE___redArg(v_s_1710_, v_stackPos_1736_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 3, v___x_1762_);
lean_ctor_set(v___x_1739_, 2, v_nextStackPos_1772_);
v___x_1774_ = v___x_1739_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_needle_1734_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_table_1735_);
lean_ctor_set(v_reuseFailAlloc_1776_, 2, v_nextStackPos_1772_);
lean_ctor_set(v_reuseFailAlloc_1776_, 3, v___x_1762_);
v___x_1774_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
v_a_1711_ = v___x_1774_;
v_b_1712_ = v___x_1713_;
goto _start;
}
}
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v_nextStackPos_1779_; lean_object* v___x_1781_; 
lean_dec(v_needlePos_1737_);
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_nat_add(v_stackPos_1736_, v___x_1777_);
lean_dec(v_stackPos_1736_);
v_nextStackPos_1779_ = l_String_Slice_posGE___redArg(v_s_1710_, v___x_1778_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 3, v___x_1762_);
lean_ctor_set(v___x_1739_, 2, v_nextStackPos_1779_);
v___x_1781_ = v___x_1739_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_needle_1734_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_table_1735_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_nextStackPos_1779_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v___x_1762_);
v___x_1781_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
v_a_1711_ = v___x_1781_;
v_b_1712_ = v___x_1713_;
goto _start;
}
}
}
else
{
lean_object* v___x_1784_; lean_object* v_nextNeedlePos_1785_; uint8_t v_decide_1786_; 
v___x_1784_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_1785_ = lean_nat_add(v_needlePos_1737_, v___x_1784_);
lean_dec(v_needlePos_1737_);
v_decide_1786_ = lean_nat_dec_eq(v_nextNeedlePos_1785_, v___x_1748_);
lean_dec(v___x_1748_);
if (v_decide_1786_ == 0)
{
lean_object* v_nextStackPos_1787_; lean_object* v___x_1789_; 
v_nextStackPos_1787_ = lean_nat_add(v_stackPos_1736_, v___x_1784_);
lean_dec(v_stackPos_1736_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 3, v_nextNeedlePos_1785_);
lean_ctor_set(v___x_1739_, 2, v_nextStackPos_1787_);
v___x_1789_ = v___x_1739_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_needle_1734_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_table_1735_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_nextStackPos_1787_);
lean_ctor_set(v_reuseFailAlloc_1791_, 3, v_nextNeedlePos_1785_);
v___x_1789_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
v_a_1711_ = v___x_1789_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_1785_);
lean_del_object(v___x_1739_);
lean_dec(v_stackPos_1736_);
lean_dec_ref(v_table_1735_);
lean_dec_ref(v_needle_1734_);
return v_decide_1786_;
}
}
}
}
}
default: 
{
return v_b_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg___boxed(lean_object* v_s_1793_, lean_object* v_a_1794_, lean_object* v_b_1795_){
_start:
{
uint8_t v_b_boxed_1796_; uint8_t v_res_1797_; lean_object* v_r_1798_; 
v_b_boxed_1796_ = lean_unbox(v_b_1795_);
v_res_1797_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_1793_, v_a_1794_, v_b_boxed_1796_);
lean_dec_ref(v_s_1793_);
v_r_1798_ = lean_box(v_res_1797_);
return v_r_1798_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0));
v___x_1801_ = lean_string_utf8_byte_size(v___x_1800_);
return v___x_1801_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1);
v___x_1804_ = lean_nat_dec_eq(v___x_1803_, v___x_1802_);
return v___x_1804_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0));
v___x_1808_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v___x_1806_);
lean_ctor_set(v___x_1808_, 2, v___x_1805_);
return v___x_1808_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3);
v___x_1810_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1809_);
return v___x_1810_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4);
v___x_1813_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3);
v___x_1814_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
lean_ctor_set(v___x_1814_, 1, v___x_1812_);
lean_ctor_set(v___x_1814_, 2, v___x_1811_);
lean_ctor_set(v___x_1814_, 3, v___x_1811_);
return v___x_1814_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(lean_object* v_s_1817_){
_start:
{
lean_object* v___y_1819_; uint8_t v___x_1822_; 
v___x_1822_ = lean_uint8_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5);
v___y_1819_ = v___x_1823_;
goto v___jp_1818_;
}
else
{
lean_object* v___x_1824_; 
v___x_1824_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__6));
v___y_1819_ = v___x_1824_;
goto v___jp_1818_;
}
v___jp_1818_:
{
uint8_t v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = 0;
lean_inc(v___y_1819_);
v___x_1821_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_1817_, v___y_1819_, v___x_1820_);
return v___x_1821_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___boxed(lean_object* v_s_1825_){
_start:
{
uint8_t v_res_1826_; lean_object* v_r_1827_; 
v_res_1826_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v_s_1825_);
lean_dec_ref(v_s_1825_);
v_r_1827_ = lean_box(v_res_1826_);
return v_r_1827_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(lean_object* v_kernelName_1828_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1830_ = lean_string_utf8_byte_size(v_kernelName_1828_);
v___x_1831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1831_, 0, v_kernelName_1828_);
lean_ctor_set(v___x_1831_, 1, v___x_1829_);
lean_ctor_set(v___x_1831_, 2, v___x_1830_);
v___x_1832_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v___x_1831_);
lean_dec_ref_known(v___x_1831_, 3);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel___boxed(lean_object* v_kernelName_1833_){
_start:
{
uint8_t v_res_1834_; lean_object* v_r_1835_; 
v_res_1834_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_1833_);
v_r_1835_ = lean_box(v_res_1834_);
return v_r_1835_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(lean_object* v_s_1836_, lean_object* v_inst_1837_, lean_object* v_R_1838_, lean_object* v_a_1839_, uint8_t v_b_1840_, lean_object* v_c_1841_){
_start:
{
uint8_t v___x_1842_; 
v___x_1842_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_1836_, v_a_1839_, v_b_1840_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___boxed(lean_object* v_s_1843_, lean_object* v_inst_1844_, lean_object* v_R_1845_, lean_object* v_a_1846_, lean_object* v_b_1847_, lean_object* v_c_1848_){
_start:
{
uint8_t v_b_boxed_1849_; uint8_t v_res_1850_; lean_object* v_r_1851_; 
v_b_boxed_1849_ = lean_unbox(v_b_1847_);
v_res_1850_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(v_s_1843_, v_inst_1844_, v_R_1845_, v_a_1846_, v_b_boxed_1849_, v_c_1848_);
lean_dec_ref(v_s_1843_);
v_r_1851_ = lean_box(v_res_1850_);
return v_r_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(lean_object* v_a_1852_, lean_object* v_b_1853_){
_start:
{
lean_object* v_array_1854_; lean_object* v_start_1855_; lean_object* v_stop_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1869_; 
v_array_1854_ = lean_ctor_get(v_a_1852_, 0);
v_start_1855_ = lean_ctor_get(v_a_1852_, 1);
v_stop_1856_ = lean_ctor_get(v_a_1852_, 2);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_a_1852_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1858_ = v_a_1852_;
v_isShared_1859_ = v_isSharedCheck_1869_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_stop_1856_);
lean_inc(v_start_1855_);
lean_inc(v_array_1854_);
lean_dec(v_a_1852_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1869_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_nat_dec_lt(v_start_1855_, v_stop_1856_);
if (v___x_1860_ == 0)
{
lean_del_object(v___x_1858_);
lean_dec(v_stop_1856_);
lean_dec(v_start_1855_);
lean_dec_ref(v_array_1854_);
return v_b_1853_;
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1861_ = lean_unsigned_to_nat(1u);
v___x_1862_ = lean_nat_add(v_start_1855_, v___x_1861_);
lean_inc_ref(v_array_1854_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v___x_1862_);
v___x_1864_ = v___x_1858_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_array_1854_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v___x_1862_);
lean_ctor_set(v_reuseFailAlloc_1868_, 2, v_stop_1856_);
v___x_1864_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_array_fget(v_array_1854_, v_start_1855_);
lean_dec(v_start_1855_);
lean_dec_ref(v_array_1854_);
v___x_1866_ = lean_array_push(v_b_1853_, v___x_1865_);
v_a_1852_ = v___x_1864_;
v_b_1853_ = v___x_1866_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(size_t v_sz_1870_, size_t v_i_1871_, lean_object* v_bs_1872_){
_start:
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_usize_dec_lt(v_i_1871_, v_sz_1870_);
if (v___x_1873_ == 0)
{
return v_bs_1872_;
}
else
{
lean_object* v_v_1874_; lean_object* v___x_1875_; lean_object* v_bs_x27_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; size_t v___x_1879_; size_t v___x_1880_; lean_object* v___x_1881_; 
v_v_1874_ = lean_array_uget(v_bs_1872_, v_i_1871_);
v___x_1875_ = lean_unsigned_to_nat(0u);
v_bs_x27_1876_ = lean_array_uset(v_bs_1872_, v_i_1871_, v___x_1875_);
v___x_1877_ = l_Lean_Name_toString(v_v_1874_, v___x_1873_);
v___x_1878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
v___x_1879_ = ((size_t)1ULL);
v___x_1880_ = lean_usize_add(v_i_1871_, v___x_1879_);
v___x_1881_ = lean_array_uset(v_bs_x27_1876_, v_i_1871_, v___x_1878_);
v_i_1871_ = v___x_1880_;
v_bs_1872_ = v___x_1881_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0___boxed(lean_object* v_sz_1883_, lean_object* v_i_1884_, lean_object* v_bs_1885_){
_start:
{
size_t v_sz_boxed_1886_; size_t v_i_boxed_1887_; lean_object* v_res_1888_; 
v_sz_boxed_1886_ = lean_unbox_usize(v_sz_1883_);
lean_dec(v_sz_1883_);
v_i_boxed_1887_ = lean_unbox_usize(v_i_1884_);
lean_dec(v_i_1884_);
v_res_1888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_boxed_1886_, v_i_boxed_1887_, v_bs_1885_);
return v_res_1888_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_unsigned_to_nat(4u);
v___x_1917_ = l_Lean_JsonNumber_fromNat(v___x_1916_);
return v___x_1917_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17);
v___x_1919_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
return v___x_1919_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18);
v___x_1921_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16));
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v___x_1920_);
return v___x_1922_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1937_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25));
v___x_1938_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19);
v___x_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v___x_1937_);
return v___x_1939_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__27(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26);
v___x_1941_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15));
v___x_1942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v___x_1940_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(lean_object* v_solutionPath_1943_, lean_object* v_kernelName_1944_, lean_object* v___x_1945_, lean_object* v_kernelCommand_1946_, lean_object* v_configHandle_1947_, lean_object* v_configPath_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_a_1952_; lean_object* v_legalAxioms_1979_; uint8_t v___x_1980_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; size_t v_sz_2048_; size_t v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v_legalAxioms_1979_ = lean_ctor_get(v___y_1949_, 5);
v___x_1980_ = 0;
v___x_2043_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10));
v___x_2044_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
lean_inc_ref(v_solutionPath_1943_);
v___x_2045_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_solutionPath_1943_);
v___x_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12));
v_sz_2048_ = lean_array_size(v_legalAxioms_1979_);
v___x_2049_ = ((size_t)0ULL);
lean_inc_ref(v_legalAxioms_1979_);
v___x_2050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_2048_, v___x_2049_, v_legalAxioms_1979_);
v___x_2051_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2047_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v___x_2053_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__27, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__27_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__27);
v___x_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2052_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v___x_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2046_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2043_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = l_Lean_Json_mkObj(v___x_2056_);
lean_dec_ref_known(v___x_2056_, 2);
v___x_2058_ = l_Lean_Json_compress(v___x_2057_);
v___x_2059_ = lean_io_prim_handle_put_str(v_configHandle_1947_, v___x_2058_);
lean_dec_ref(v___x_2058_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v___x_2060_; 
lean_dec_ref_known(v___x_2059_, 1);
v___x_2060_ = lean_io_prim_handle_flush(v_configHandle_1947_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_kernelArgs_2062_; lean_object* v___y_2063_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
lean_dec_ref_known(v___x_2060_, 1);
v___x_2069_ = lean_unsigned_to_nat(1u);
v___x_2070_ = lean_array_get_size(v_kernelCommand_1946_);
lean_inc_ref(v_kernelCommand_1946_);
v___x_2071_ = l_Array_toSubarray___redArg(v_kernelCommand_1946_, v___x_2069_, v___x_2070_);
v___x_2072_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_2073_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v___x_2071_, v___x_2072_);
lean_inc_ref(v_kernelName_1944_);
v___x_2074_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_1944_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; 
lean_inc_ref(v_solutionPath_1943_);
v___x_2075_ = lean_array_push(v___x_2073_, v_solutionPath_1943_);
v_kernelArgs_2062_ = v___x_2075_;
v___y_2063_ = v___y_1949_;
goto v___jp_2061_;
}
else
{
lean_object* v___x_2076_; 
lean_inc_ref(v_configPath_1948_);
v___x_2076_ = lean_array_push(v___x_2073_, v_configPath_1948_);
v_kernelArgs_2062_ = v___x_2076_;
v___y_2063_ = v___y_1949_;
goto v___jp_2061_;
}
v___jp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v_a_2067_; 
v___x_2064_ = lean_unsigned_to_nat(0u);
v___x_2065_ = lean_array_get(v___x_1945_, v_kernelCommand_1946_, v___x_2064_);
lean_dec_ref(v_kernelCommand_1946_);
lean_inc(v___x_2065_);
v___x_2066_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_2065_);
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref(v___x_2066_);
if (lean_obj_tag(v_a_2067_) == 0)
{
v___y_1982_ = v___x_2064_;
v___y_1983_ = v_kernelArgs_2062_;
v___y_1984_ = v___y_2063_;
v___y_1985_ = v___x_2065_;
goto v___jp_1981_;
}
else
{
lean_object* v_val_2068_; 
lean_dec(v___x_2065_);
v_val_2068_ = lean_ctor_get(v_a_2067_, 0);
lean_inc(v_val_2068_);
lean_dec_ref_known(v_a_2067_, 1);
v___y_1982_ = v___x_2064_;
v___y_1983_ = v_kernelArgs_2062_;
v___y_1984_ = v___y_2063_;
v___y_1985_ = v_val_2068_;
goto v___jp_1981_;
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec_ref(v_configPath_1948_);
lean_dec_ref(v_kernelCommand_1946_);
lean_dec_ref(v_kernelName_1944_);
lean_dec_ref(v_solutionPath_1943_);
v_a_2077_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2060_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2060_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v_configPath_1948_);
lean_dec_ref(v_kernelCommand_1946_);
lean_dec_ref(v_kernelName_1944_);
lean_dec_ref(v_solutionPath_1943_);
v_a_2085_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2059_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2059_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
v___jp_1951_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1953_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__0));
v___x_1954_ = lean_string_append(v___x_1953_, v_kernelName_1944_);
lean_dec_ref(v_kernelName_1944_);
v___x_1955_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__1));
lean_inc_ref(v___x_1954_);
v___x_1956_ = lean_string_append(v___x_1954_, v___x_1955_);
v___x_1957_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1956_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1969_; 
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v___x_1957_, 0);
lean_dec(v_unused_1970_);
v___x_1959_ = v___x_1957_;
v_isShared_1960_ = v_isSharedCheck_1969_;
goto v_resetjp_1958_;
}
else
{
lean_dec(v___x_1957_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1969_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1961_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__2));
v___x_1962_ = lean_string_append(v___x_1954_, v___x_1961_);
v___x_1963_ = lean_io_error_to_string(v_a_1952_);
v___x_1964_ = lean_string_append(v___x_1962_, v___x_1963_);
lean_dec_ref(v___x_1963_);
v___x_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1965_);
v___x_1967_ = v___x_1959_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec_ref(v___x_1954_);
lean_dec(v_a_1952_);
v_a_1971_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1957_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1957_);
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
v___jp_1981_:
{
lean_object* v_leanPrefix_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v_leanPrefix_1986_ = lean_ctor_get(v___y_1984_, 6);
v___x_1987_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__4));
v___x_1988_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1989_ = lean_unsigned_to_nat(4u);
v___x_1990_ = lean_mk_empty_array_with_capacity(v___x_1989_);
v___x_1991_ = lean_array_push(v___x_1990_, v_configPath_1948_);
v___x_1992_ = lean_array_push(v___x_1991_, v_solutionPath_1943_);
lean_inc_ref(v___y_1985_);
v___x_1993_ = lean_array_push(v___x_1992_, v___y_1985_);
lean_inc_ref(v_leanPrefix_1986_);
v___x_1994_ = lean_array_push(v___x_1993_, v_leanPrefix_1986_);
v___x_1995_ = lean_mk_empty_array_with_capacity(v___y_1982_);
v___x_1996_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1997_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5));
v___x_1998_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1998_, 0, v___y_1985_);
lean_ctor_set(v___x_1998_, 1, v___y_1983_);
lean_ctor_set(v___x_1998_, 2, v___x_1987_);
lean_ctor_set(v___x_1998_, 3, v___x_1988_);
lean_ctor_set(v___x_1998_, 4, v___x_1994_);
lean_ctor_set(v___x_1998_, 5, v___x_1995_);
lean_ctor_set(v___x_1998_, 6, v___x_1996_);
lean_ctor_set(v___x_1998_, 7, v___x_1997_);
lean_ctor_set_uint8(v___x_1998_, sizeof(void*)*8, v___x_1980_);
v___x_1999_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v___x_1998_, v___y_1984_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2041_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2041_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2041_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
uint32_t v___x_2004_; uint32_t v___x_2005_; uint8_t v___x_2006_; 
v___x_2004_ = 0;
v___x_2005_ = lean_unbox_uint32(v_a_2000_);
v___x_2006_ = lean_uint32_dec_eq(v___x_2005_, v___x_2004_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6));
lean_inc_ref(v_kernelName_1944_);
v___x_2008_ = lean_string_append(v_kernelName_1944_, v___x_2007_);
v___x_2009_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2008_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2025_; 
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v___x_2009_, 0);
lean_dec(v_unused_2026_);
v___x_2011_ = v___x_2009_;
v_isShared_2012_ = v_isSharedCheck_2025_;
goto v_resetjp_2010_;
}
else
{
lean_dec(v___x_2009_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2025_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; uint32_t v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2013_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7));
v___x_2014_ = lean_string_append(v_kernelName_1944_, v___x_2013_);
v___x_2015_ = lean_unbox_uint32(v_a_2000_);
lean_dec(v_a_2000_);
v___x_2016_ = lean_uint32_to_nat(v___x_2015_);
v___x_2017_ = l_Nat_reprFast(v___x_2016_);
v___x_2018_ = lean_string_append(v___x_2014_, v___x_2017_);
lean_dec_ref(v___x_2017_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 1);
lean_ctor_set(v___x_2002_, 0, v___x_2018_);
v___x_2020_ = v___x_2002_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2022_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2020_);
v___x_2022_ = v___x_2011_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
else
{
lean_object* v_a_2027_; 
lean_del_object(v___x_2002_);
lean_dec(v_a_2000_);
v_a_2027_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2009_, 1);
v_a_1952_ = v_a_2027_;
goto v___jp_1951_;
}
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
lean_del_object(v___x_2002_);
lean_dec(v_a_2000_);
v___x_2028_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8));
lean_inc_ref(v_kernelName_1944_);
v___x_2029_ = lean_string_append(v_kernelName_1944_, v___x_2028_);
v___x_2030_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2029_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v_kernelName_1944_);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; 
v_unused_2039_ = lean_ctor_get(v___x_2030_, 0);
lean_dec(v_unused_2039_);
v___x_2032_ = v___x_2030_;
v_isShared_2033_ = v_isSharedCheck_2038_;
goto v_resetjp_2031_;
}
else
{
lean_dec(v___x_2030_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2038_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2034_ = lean_box(0);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2034_);
v___x_2036_ = v___x_2032_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
else
{
lean_object* v_a_2040_; 
v_a_2040_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2030_, 1);
v_a_1952_ = v_a_2040_;
goto v___jp_1951_;
}
}
}
}
else
{
lean_object* v_a_2042_; 
v_a_2042_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_1999_, 1);
v_a_1952_ = v_a_2042_;
goto v___jp_1951_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed(lean_object* v_solutionPath_2093_, lean_object* v_kernelName_2094_, lean_object* v___x_2095_, lean_object* v_kernelCommand_2096_, lean_object* v_configHandle_2097_, lean_object* v_configPath_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(v_solutionPath_2093_, v_kernelName_2094_, v___x_2095_, v_kernelCommand_2096_, v_configHandle_2097_, v_configPath_2098_, v___y_2099_);
lean_dec_ref(v___y_2099_);
lean_dec(v_configHandle_2097_);
lean_dec_ref(v___x_2095_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(lean_object* v_kernelName_2104_, lean_object* v_kernelCommand_2105_, lean_object* v_solutionPath_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2109_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0));
v___x_2110_ = lean_string_append(v___x_2109_, v_kernelName_2104_);
v___x_2111_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1));
v___x_2112_ = lean_string_append(v___x_2110_, v___x_2111_);
v___x_2113_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2112_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v___x_2114_; lean_object* v___f_2115_; lean_object* v___x_2116_; 
lean_dec_ref_known(v___x_2113_, 1);
v___x_2114_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
v___f_2115_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed), 8, 4);
lean_closure_set(v___f_2115_, 0, v_solutionPath_2106_);
lean_closure_set(v___f_2115_, 1, v_kernelName_2104_);
lean_closure_set(v___f_2115_, 2, v___x_2114_);
lean_closure_set(v___f_2115_, 3, v_kernelCommand_2105_);
v___x_2116_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_spec__0___redArg(v___f_2115_, v_a_2107_);
return v___x_2116_;
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref(v_solutionPath_2106_);
lean_dec_ref(v_kernelCommand_2105_);
lean_dec_ref(v_kernelName_2104_);
v_a_2117_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2113_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2113_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___boxed(lean_object* v_kernelName_2125_, lean_object* v_kernelCommand_2126_, lean_object* v_solutionPath_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_kernelName_2125_, v_kernelCommand_2126_, v_solutionPath_2127_, v_a_2128_);
lean_dec_ref(v_a_2128_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1(lean_object* v_inst_2131_, lean_object* v_R_2132_, lean_object* v_a_2133_, lean_object* v_b_2134_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v_a_2133_, v_b_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(lean_object* v_solutionPath_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v_whichLeanChecker_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_whichLeanChecker_2142_ = lean_ctor_get(v_a_2140_, 13);
v___x_2143_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0));
v___x_2144_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_2145_ = lean_unsigned_to_nat(3u);
v___x_2146_ = lean_mk_empty_array_with_capacity(v___x_2145_);
lean_inc_ref(v_whichLeanChecker_2142_);
v___x_2147_ = lean_array_push(v___x_2146_, v_whichLeanChecker_2142_);
v___x_2148_ = lean_array_push(v___x_2147_, v___x_2143_);
v___x_2149_ = lean_array_push(v___x_2148_, v___x_2144_);
v___x_2150_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2));
v___x_2151_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v___x_2150_, v___x_2149_, v_solutionPath_2139_, v_a_2140_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___boxed(lean_object* v_solutionPath_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_solutionPath_2152_, v_a_2153_);
lean_dec_ref(v_a_2153_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg(){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__52));
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___boxed(lean_object* v_a_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___boxed(lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(v_a_2313_);
lean_dec_ref(v_a_2313_);
return v_res_2315_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(lean_object* v_a_2316_, lean_object* v_as_2317_, size_t v_i_2318_, size_t v_stop_2319_){
_start:
{
uint8_t v___x_2320_; 
v___x_2320_ = lean_usize_dec_eq(v_i_2318_, v_stop_2319_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2321_ = lean_array_uget_borrowed(v_as_2317_, v_i_2318_);
v___x_2322_ = lean_name_eq(v_a_2316_, v___x_2321_);
if (v___x_2322_ == 0)
{
size_t v___x_2323_; size_t v___x_2324_; 
v___x_2323_ = ((size_t)1ULL);
v___x_2324_ = lean_usize_add(v_i_2318_, v___x_2323_);
v_i_2318_ = v___x_2324_;
goto _start;
}
else
{
return v___x_2322_;
}
}
else
{
uint8_t v___x_2326_; 
v___x_2326_ = 0;
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0___boxed(lean_object* v_a_2327_, lean_object* v_as_2328_, lean_object* v_i_2329_, lean_object* v_stop_2330_){
_start:
{
size_t v_i_boxed_2331_; size_t v_stop_boxed_2332_; uint8_t v_res_2333_; lean_object* v_r_2334_; 
v_i_boxed_2331_ = lean_unbox_usize(v_i_2329_);
lean_dec(v_i_2329_);
v_stop_boxed_2332_ = lean_unbox_usize(v_stop_2330_);
lean_dec(v_stop_2330_);
v_res_2333_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_2327_, v_as_2328_, v_i_boxed_2331_, v_stop_boxed_2332_);
lean_dec_ref(v_as_2328_);
lean_dec(v_a_2327_);
v_r_2334_ = lean_box(v_res_2333_);
return v_r_2334_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(lean_object* v_as_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2337_ = lean_unsigned_to_nat(0u);
v___x_2338_ = lean_array_get_size(v_as_2335_);
v___x_2339_ = lean_nat_dec_lt(v___x_2337_, v___x_2338_);
if (v___x_2339_ == 0)
{
return v___x_2339_;
}
else
{
if (v___x_2339_ == 0)
{
return v___x_2339_;
}
else
{
size_t v___x_2340_; size_t v___x_2341_; uint8_t v___x_2342_; 
v___x_2340_ = ((size_t)0ULL);
v___x_2341_ = lean_usize_of_nat(v___x_2338_);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_2336_, v_as_2335_, v___x_2340_, v___x_2341_);
return v___x_2342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0___boxed(lean_object* v_as_2343_, lean_object* v_a_2344_){
_start:
{
uint8_t v_res_2345_; lean_object* v_r_2346_; 
v_res_2345_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_as_2343_, v_a_2344_);
lean_dec(v_a_2344_);
lean_dec_ref(v_as_2343_);
v_r_2346_ = lean_box(v_res_2345_);
return v_r_2346_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11(void){
_start:
{
lean_object* v___x_2377_; lean_object* v_additional_2378_; lean_object* v___x_2379_; 
v___x_2377_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__10));
v_additional_2378_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_2379_ = l_Array_append___redArg(v_additional_2378_, v___x_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(lean_object* v_a_2380_){
_start:
{
lean_object* v_legalAxioms_2382_; lean_object* v_additional_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v_legalAxioms_2382_ = lean_ctor_get(v_a_2380_, 5);
v_additional_2383_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_2384_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3));
v___x_2385_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_legalAxioms_2382_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v_additional_2383_);
return v___x_2386_;
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
return v___x_2388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___boxed(lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_2389_);
lean_dec_ref(v_a_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(lean_object* v_e_2392_){
_start:
{
if (lean_obj_tag(v_e_2392_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2402_; 
v_a_2394_ = lean_ctor_get(v_e_2392_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_e_2392_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2396_ = v_e_2392_;
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v_e_2392_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2402_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2398_ = lean_mk_io_user_error(v_a_2394_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2398_);
v___x_2400_ = v___x_2396_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
v_a_2403_ = lean_ctor_get(v_e_2392_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_e_2392_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v_e_2392_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v_e_2392_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
lean_ctor_set_tag(v___x_2405_, 0);
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg___boxed(lean_object* v_e_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v_e_2411_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(lean_object* v_00_u03b1_2414_, lean_object* v_e_2415_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v_e_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___boxed(lean_object* v_00_u03b1_2418_, lean_object* v_e_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(v_00_u03b1_2418_, v_e_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(lean_object* v_challengeExportPath_2422_, lean_object* v_solutionExportPath_2423_, lean_object* v_a_2424_){
_start:
{
uint8_t v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = 0;
v___x_2427_ = lean_io_prim_handle_mk(v_challengeExportPath_2422_, v___x_2426_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref_known(v___x_2427_, 1);
v___x_2429_ = lean_stream_of_handle(v_a_2428_);
v___x_2430_ = l_LeanExport_parseStream(v___x_2429_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2432_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2430_, 1);
v___x_2432_ = lean_io_prim_handle_mk(v_solutionExportPath_2423_, v___x_2426_);
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
lean_object* v_a_2436_; lean_object* v___x_2437_; lean_object* v_a_2438_; lean_object* v_theoremNames_2439_; lean_object* v_definitionNames_2440_; lean_object* v_legalAxioms_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc_n(v_a_2436_, 2);
lean_dec_ref_known(v___x_2435_, 1);
v___x_2437_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref(v___x_2437_);
v_theoremNames_2439_ = lean_ctor_get(v_a_2424_, 3);
v_definitionNames_2440_ = lean_ctor_get(v_a_2424_, 4);
v_legalAxioms_2441_ = lean_ctor_get(v_a_2424_, 5);
lean_inc_ref(v_theoremNames_2439_);
v___x_2442_ = l_Array_append___redArg(v_theoremNames_2439_, v_legalAxioms_2441_);
v___x_2443_ = l_Lake_Check_compareAt(v_a_2431_, v_a_2436_, v___x_2442_, v_definitionNames_2440_, v_a_2438_);
lean_dec_ref(v___x_2442_);
v___x_2444_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v___x_2443_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
lean_dec_ref_known(v___x_2444_, 1);
v___x_2445_ = l_Lake_Check_checkAxioms(v_a_2436_, v_theoremNames_2439_, v_definitionNames_2440_, v_legalAxioms_2441_);
v___x_2446_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v___x_2445_);
return v___x_2446_;
}
else
{
lean_dec(v_a_2436_);
return v___x_2444_;
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_dec(v_a_2431_);
v_a_2447_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2435_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2435_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec(v_a_2431_);
v_a_2455_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2432_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2432_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
v_a_2463_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2430_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2430_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
v_a_2471_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2427_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2427_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare___boxed(lean_object* v_challengeExportPath_2479_, lean_object* v_solutionExportPath_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(v_challengeExportPath_2479_, v_solutionExportPath_2480_, v_a_2481_);
lean_dec_ref(v_a_2481_);
lean_dec_ref(v_solutionExportPath_2480_);
lean_dec_ref(v_challengeExportPath_2479_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels_spec__0(lean_object* v_solutionExportPath_2484_, lean_object* v_init_2485_, lean_object* v_x_2486_, lean_object* v___y_2487_){
_start:
{
if (lean_obj_tag(v_x_2486_) == 0)
{
lean_object* v_k_2489_; lean_object* v_v_2490_; lean_object* v_l_2491_; lean_object* v_r_2492_; lean_object* v___x_2493_; 
v_k_2489_ = lean_ctor_get(v_x_2486_, 1);
lean_inc(v_k_2489_);
v_v_2490_ = lean_ctor_get(v_x_2486_, 2);
lean_inc(v_v_2490_);
v_l_2491_ = lean_ctor_get(v_x_2486_, 3);
lean_inc(v_l_2491_);
v_r_2492_ = lean_ctor_get(v_x_2486_, 4);
lean_inc(v_r_2492_);
lean_dec_ref_known(v_x_2486_, 5);
lean_inc_ref(v_solutionExportPath_2484_);
v___x_2493_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels_spec__0(v_solutionExportPath_2484_, v_init_2485_, v_l_2491_, v___y_2487_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v_a_2495_; lean_object* v___x_2496_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
v_a_2495_ = lean_ctor_get(v_a_2494_, 0);
lean_inc(v_a_2495_);
lean_dec(v_a_2494_);
lean_inc_ref(v_solutionExportPath_2484_);
v___x_2496_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_k_2489_, v_v_2490_, v_solutionExportPath_2484_, v___y_2487_);
if (lean_obj_tag(v___x_2496_) == 0)
{
if (lean_obj_tag(v_a_2495_) == 0)
{
lean_object* v_a_2497_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2496_, 1);
v_init_2485_ = v_a_2497_;
v_x_2486_ = v_r_2492_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_2496_, 1);
v_init_2485_ = v_a_2495_;
v_x_2486_ = v_r_2492_;
goto _start;
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_a_2495_);
lean_dec(v_r_2492_);
lean_dec_ref(v_solutionExportPath_2484_);
v_a_2500_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2496_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2496_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_dec(v_r_2492_);
lean_dec(v_v_2490_);
lean_dec(v_k_2489_);
lean_dec_ref(v_solutionExportPath_2484_);
return v___x_2493_;
}
}
else
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_dec_ref(v_solutionExportPath_2484_);
v___x_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2508_, 0, v_init_2485_);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels_spec__0___boxed(lean_object* v_solutionExportPath_2510_, lean_object* v_init_2511_, lean_object* v_x_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels_spec__0(v_solutionExportPath_2510_, v_init_2511_, v_x_2512_, v___y_2513_);
lean_dec_ref(v___y_2513_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels(lean_object* v_solutionExportPath_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v_val_2520_; lean_object* v_externalKernels_2523_; lean_object* v_result_2524_; lean_object* v___x_2525_; 
v_externalKernels_2523_ = lean_ctor_get(v_a_2517_, 15);
v_result_2524_ = lean_box(0);
lean_inc(v_externalKernels_2523_);
lean_inc_ref(v_solutionExportPath_2516_);
v___x_2525_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels_spec__0(v_solutionExportPath_2516_, v_result_2524_, v_externalKernels_2523_, v_a_2517_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v_a_2528_; lean_object* v_a_2549_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v_a_2549_ = lean_ctor_get(v_a_2526_, 0);
lean_inc(v_a_2549_);
lean_dec(v_a_2526_);
v_a_2528_ = v_a_2549_;
goto v___jp_2527_;
v___jp_2527_:
{
lean_object* v___x_2529_; 
v___x_2529_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_solutionExportPath_2516_, v_a_2517_);
if (lean_obj_tag(v___x_2529_) == 0)
{
if (lean_obj_tag(v_a_2528_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2539_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2539_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2539_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
if (lean_obj_tag(v_a_2530_) == 1)
{
lean_object* v_val_2534_; 
lean_del_object(v___x_2532_);
v_val_2534_ = lean_ctor_get(v_a_2530_, 0);
lean_inc(v_val_2534_);
lean_dec_ref_known(v_a_2530_, 1);
v_val_2520_ = v_val_2534_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
lean_dec(v_a_2530_);
v___x_2535_ = lean_box(0);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2535_);
v___x_2537_ = v___x_2532_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
else
{
lean_object* v_val_2540_; 
lean_dec_ref_known(v___x_2529_, 1);
v_val_2540_ = lean_ctor_get(v_a_2528_, 0);
lean_inc(v_val_2540_);
lean_dec_ref_known(v_a_2528_, 1);
v_val_2520_ = v_val_2540_;
goto v___jp_2519_;
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_a_2528_);
v_a_2541_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2529_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2529_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_dec_ref(v_solutionExportPath_2516_);
v_a_2550_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2525_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2525_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
v___jp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_mk_io_user_error(v_val_2520_);
v___x_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
return v___x_2522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels___boxed(lean_object* v_solutionExportPath_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels(v_solutionExportPath_2558_, v_a_2559_);
lean_dec_ref(v_a_2559_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(lean_object* v_challengeExportPath_2562_, lean_object* v_solutionExportPath_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(v_challengeExportPath_2562_, v_solutionExportPath_2563_, v_a_2564_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2567_; 
lean_dec_ref_known(v___x_2566_, 1);
v___x_2567_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyKernels(v_solutionExportPath_2563_, v_a_2564_);
return v___x_2567_;
}
else
{
lean_dec_ref(v_solutionExportPath_2563_);
return v___x_2566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch___boxed(lean_object* v_challengeExportPath_2568_, lean_object* v_solutionExportPath_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExportPath_2568_, v_solutionExportPath_2569_, v_a_2570_);
lean_dec_ref(v_a_2570_);
lean_dec_ref(v_challengeExportPath_2568_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__0(lean_object* v_challengeExportPath_2574_, lean_object* v_solutionExportPath_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExportPath_2574_, v_solutionExportPath_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_dec_ref_known(v___x_2578_, 1);
v___x_2579_ = ((lean_object*)(l_Lake_Check_compareIt___lam__0___closed__0));
v___x_2580_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2579_);
return v___x_2580_;
}
else
{
return v___x_2578_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__0___boxed(lean_object* v_challengeExportPath_2581_, lean_object* v_solutionExportPath_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lake_Check_compareIt___lam__0(v_challengeExportPath_2581_, v_solutionExportPath_2582_, v___y_2583_);
lean_dec_ref(v___y_2583_);
lean_dec_ref(v_challengeExportPath_2581_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__1(lean_object* v___x_2586_, lean_object* v___x_2587_, lean_object* v_challengeExportPath_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_solutionModule_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v_solutionModule_2591_ = lean_ctor_get(v___y_2589_, 2);
lean_inc(v_solutionModule_2591_);
v___x_2592_ = lean_array_push(v___x_2586_, v_solutionModule_2591_);
v___x_2593_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v___x_2592_, v___y_2589_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v___f_2594_; lean_object* v___x_2595_; 
lean_dec_ref_known(v___x_2593_, 1);
v___f_2594_ = lean_alloc_closure((void*)(l_Lake_Check_compareIt___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2594_, 0, v_challengeExportPath_2588_);
lean_inc(v_solutionModule_2591_);
v___x_2595_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_solutionModule_2591_, v___x_2587_, v___f_2594_, v___y_2589_);
return v___x_2595_;
}
else
{
lean_dec_ref(v_challengeExportPath_2588_);
lean_dec_ref(v___x_2587_);
return v___x_2593_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___lam__1___boxed(lean_object* v___x_2596_, lean_object* v___x_2597_, lean_object* v_challengeExportPath_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lake_Check_compareIt___lam__1(v___x_2596_, v___x_2597_, v_challengeExportPath_2598_, v___y_2599_);
lean_dec_ref(v___y_2599_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt(lean_object* v_a_2602_){
_start:
{
lean_object* v___x_2604_; lean_object* v_a_2605_; lean_object* v___x_2606_; lean_object* v_a_2607_; lean_object* v_challengeModule_2608_; lean_object* v_theoremNames_2609_; lean_object* v_definitionNames_2610_; lean_object* v_legalAxioms_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2604_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_2602_);
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref(v___x_2604_);
v___x_2606_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref(v___x_2606_);
v_challengeModule_2608_ = lean_ctor_get(v_a_2602_, 1);
v_theoremNames_2609_ = lean_ctor_get(v_a_2602_, 3);
v_definitionNames_2610_ = lean_ctor_get(v_a_2602_, 4);
v_legalAxioms_2611_ = lean_ctor_get(v_a_2602_, 5);
v___x_2612_ = lean_unsigned_to_nat(1u);
v___x_2613_ = lean_mk_empty_array_with_capacity(v___x_2612_);
lean_inc(v_challengeModule_2608_);
lean_inc_ref(v___x_2613_);
v___x_2614_ = lean_array_push(v___x_2613_, v_challengeModule_2608_);
v___x_2615_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v___x_2614_, v_a_2602_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___f_2620_; lean_object* v___x_2621_; 
lean_dec_ref_known(v___x_2615_, 1);
v___x_2616_ = l_Array_append___redArg(v_a_2605_, v_theoremNames_2609_);
v___x_2617_ = l_Array_append___redArg(v___x_2616_, v_legalAxioms_2611_);
v___x_2618_ = l_Array_append___redArg(v___x_2617_, v_a_2607_);
lean_dec(v_a_2607_);
v___x_2619_ = l_Array_append___redArg(v___x_2618_, v_definitionNames_2610_);
lean_inc_ref(v___x_2619_);
v___f_2620_ = lean_alloc_closure((void*)(l_Lake_Check_compareIt___lam__1___boxed), 5, 2);
lean_closure_set(v___f_2620_, 0, v___x_2613_);
lean_closure_set(v___f_2620_, 1, v___x_2619_);
lean_inc(v_challengeModule_2608_);
v___x_2621_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_challengeModule_2608_, v___x_2619_, v___f_2620_, v_a_2602_);
return v___x_2621_;
}
else
{
lean_dec_ref(v___x_2613_);
lean_dec(v_a_2607_);
lean_dec(v_a_2605_);
return v___x_2615_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareIt___boxed(lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lake_Check_compareIt(v_a_2622_);
lean_dec_ref(v_a_2622_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(lean_object* v_j_2625_, lean_object* v_k_2626_){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = l_Lean_Json_getObjValD(v_j_2625_, v_k_2626_);
v___x_2628_ = l_Lean_Json_getStr_x3f(v___x_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0___boxed(lean_object* v_j_2629_, lean_object* v_k_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_j_2629_, v_k_2630_);
lean_dec_ref(v_k_2630_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(size_t v_sz_2632_, size_t v_i_2633_, lean_object* v_bs_2634_){
_start:
{
uint8_t v___x_2635_; 
v___x_2635_ = lean_usize_dec_lt(v_i_2633_, v_sz_2632_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2636_, 0, v_bs_2634_);
return v___x_2636_;
}
else
{
lean_object* v_v_2637_; lean_object* v___x_2638_; 
v_v_2637_ = lean_array_uget_borrowed(v_bs_2634_, v_i_2633_);
lean_inc(v_v_2637_);
v___x_2638_ = l_Lean_Json_getStr_x3f(v_v_2637_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec_ref(v_bs_2634_);
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2648_; lean_object* v_bs_x27_2649_; size_t v___x_2650_; size_t v___x_2651_; lean_object* v___x_2652_; 
v_a_2647_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2638_, 1);
v___x_2648_ = lean_unsigned_to_nat(0u);
v_bs_x27_2649_ = lean_array_uset(v_bs_2634_, v_i_2633_, v___x_2648_);
v___x_2650_ = ((size_t)1ULL);
v___x_2651_ = lean_usize_add(v_i_2633_, v___x_2650_);
v___x_2652_ = lean_array_uset(v_bs_x27_2649_, v_i_2633_, v_a_2647_);
v_i_2633_ = v___x_2651_;
v_bs_2634_ = v___x_2652_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2654_, lean_object* v_i_2655_, lean_object* v_bs_2656_){
_start:
{
size_t v_sz_boxed_2657_; size_t v_i_boxed_2658_; lean_object* v_res_2659_; 
v_sz_boxed_2657_ = lean_unbox_usize(v_sz_2654_);
lean_dec(v_sz_2654_);
v_i_boxed_2658_ = lean_unbox_usize(v_i_2655_);
lean_dec(v_i_2655_);
v_res_2659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_2657_, v_i_boxed_2658_, v_bs_2656_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(lean_object* v_x_2662_){
_start:
{
if (lean_obj_tag(v_x_2662_) == 4)
{
lean_object* v_elems_2663_; size_t v_sz_2664_; size_t v___x_2665_; lean_object* v___x_2666_; 
v_elems_2663_ = lean_ctor_get(v_x_2662_, 0);
lean_inc_ref(v_elems_2663_);
lean_dec_ref_known(v_x_2662_, 1);
v_sz_2664_ = lean_array_size(v_elems_2663_);
v___x_2665_ = ((size_t)0ULL);
v___x_2666_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_2664_, v___x_2665_, v_elems_2663_);
return v___x_2666_;
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2667_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__0));
v___x_2668_ = lean_unsigned_to_nat(80u);
v___x_2669_ = l_Lean_Json_pretty(v_x_2662_, v___x_2668_);
v___x_2670_ = lean_string_append(v___x_2667_, v___x_2669_);
lean_dec_ref(v___x_2669_);
v___x_2671_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_2672_ = lean_string_append(v___x_2670_, v___x_2671_);
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
return v___x_2673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(lean_object* v_x_2676_){
_start:
{
if (lean_obj_tag(v_x_2676_) == 0)
{
lean_object* v___x_2677_; 
v___x_2677_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3___closed__0));
return v___x_2677_;
}
else
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_x_2676_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2678_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2678_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2695_; 
v_a_2687_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2689_ = v___x_2678_;
v_isShared_2690_ = v_isSharedCheck_2695_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2678_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2695_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; lean_object* v___x_2693_; 
v___x_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2691_, 0, v_a_2687_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v___x_2691_);
v___x_2693_ = v___x_2689_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(lean_object* v_j_2696_, lean_object* v_k_2697_){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = l_Lean_Json_getObjValD(v_j_2696_, v_k_2697_);
v___x_2699_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(v___x_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2___boxed(lean_object* v_j_2700_, lean_object* v_k_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_j_2700_, v_k_2701_);
lean_dec_ref(v_k_2701_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(lean_object* v_x_2705_){
_start:
{
if (lean_obj_tag(v_x_2705_) == 0)
{
lean_object* v___x_2706_; 
v___x_2706_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___closed__0));
return v___x_2706_;
}
else
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_Json_getBool_x3f(v_x_2705_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2724_; 
v_a_2716_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2718_ = v___x_2707_;
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2707_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_a_2716_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2720_);
v___x_2722_ = v___x_2718_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___boxed(lean_object* v_x_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v_x_2725_);
lean_dec(v_x_2725_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(lean_object* v_j_2727_, lean_object* v_k_2728_){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2729_ = l_Lean_Json_getObjValD(v_j_2727_, v_k_2728_);
v___x_2730_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v___x_2729_);
lean_dec(v___x_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3___boxed(lean_object* v_j_2731_, lean_object* v_k_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_j_2731_, v_k_2732_);
lean_dec_ref(v_k_2732_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_cmp_2734_, lean_object* v_k_2735_, lean_object* v_v_2736_, lean_object* v_t_2737_){
_start:
{
if (lean_obj_tag(v_t_2737_) == 0)
{
lean_object* v_size_2738_; lean_object* v_k_2739_; lean_object* v_v_2740_; lean_object* v_l_2741_; lean_object* v_r_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_3023_; 
v_size_2738_ = lean_ctor_get(v_t_2737_, 0);
v_k_2739_ = lean_ctor_get(v_t_2737_, 1);
v_v_2740_ = lean_ctor_get(v_t_2737_, 2);
v_l_2741_ = lean_ctor_get(v_t_2737_, 3);
v_r_2742_ = lean_ctor_get(v_t_2737_, 4);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_t_2737_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_2744_ = v_t_2737_;
v_isShared_2745_ = v_isSharedCheck_3023_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_r_2742_);
lean_inc(v_l_2741_);
lean_inc(v_v_2740_);
lean_inc(v_k_2739_);
lean_inc(v_size_2738_);
lean_dec(v_t_2737_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_3023_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; uint8_t v___x_2747_; 
lean_inc_ref(v_cmp_2734_);
lean_inc(v_k_2739_);
lean_inc_ref(v_k_2735_);
v___x_2746_ = lean_apply_2(v_cmp_2734_, v_k_2735_, v_k_2739_);
v___x_2747_ = lean_unbox(v___x_2746_);
switch(v___x_2747_)
{
case 0:
{
lean_object* v_impl_2748_; lean_object* v___x_2749_; 
lean_dec(v_size_2738_);
v_impl_2748_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_2734_, v_k_2735_, v_v_2736_, v_l_2741_);
v___x_2749_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2742_) == 0)
{
lean_object* v_size_2750_; lean_object* v_size_2751_; lean_object* v_k_2752_; lean_object* v_v_2753_; lean_object* v_l_2754_; lean_object* v_r_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v_size_2750_ = lean_ctor_get(v_r_2742_, 0);
v_size_2751_ = lean_ctor_get(v_impl_2748_, 0);
lean_inc(v_size_2751_);
v_k_2752_ = lean_ctor_get(v_impl_2748_, 1);
lean_inc(v_k_2752_);
v_v_2753_ = lean_ctor_get(v_impl_2748_, 2);
lean_inc(v_v_2753_);
v_l_2754_ = lean_ctor_get(v_impl_2748_, 3);
lean_inc(v_l_2754_);
v_r_2755_ = lean_ctor_get(v_impl_2748_, 4);
lean_inc(v_r_2755_);
v___x_2756_ = lean_unsigned_to_nat(3u);
v___x_2757_ = lean_nat_mul(v___x_2756_, v_size_2750_);
v___x_2758_ = lean_nat_dec_lt(v___x_2757_, v_size_2751_);
lean_dec(v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2762_; 
lean_dec(v_r_2755_);
lean_dec(v_l_2754_);
lean_dec(v_v_2753_);
lean_dec(v_k_2752_);
v___x_2759_ = lean_nat_add(v___x_2749_, v_size_2751_);
lean_dec(v_size_2751_);
v___x_2760_ = lean_nat_add(v___x_2759_, v_size_2750_);
lean_dec(v___x_2759_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 3, v_impl_2748_);
lean_ctor_set(v___x_2744_, 0, v___x_2760_);
v___x_2762_ = v___x_2744_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v_k_2739_);
lean_ctor_set(v_reuseFailAlloc_2763_, 2, v_v_2740_);
lean_ctor_set(v_reuseFailAlloc_2763_, 3, v_impl_2748_);
lean_ctor_set(v_reuseFailAlloc_2763_, 4, v_r_2742_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
else
{
lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2829_; 
v_isSharedCheck_2829_ = !lean_is_exclusive(v_impl_2748_);
if (v_isSharedCheck_2829_ == 0)
{
lean_object* v_unused_2830_; lean_object* v_unused_2831_; lean_object* v_unused_2832_; lean_object* v_unused_2833_; lean_object* v_unused_2834_; 
v_unused_2830_ = lean_ctor_get(v_impl_2748_, 4);
lean_dec(v_unused_2830_);
v_unused_2831_ = lean_ctor_get(v_impl_2748_, 3);
lean_dec(v_unused_2831_);
v_unused_2832_ = lean_ctor_get(v_impl_2748_, 2);
lean_dec(v_unused_2832_);
v_unused_2833_ = lean_ctor_get(v_impl_2748_, 1);
lean_dec(v_unused_2833_);
v_unused_2834_ = lean_ctor_get(v_impl_2748_, 0);
lean_dec(v_unused_2834_);
v___x_2765_ = v_impl_2748_;
v_isShared_2766_ = v_isSharedCheck_2829_;
goto v_resetjp_2764_;
}
else
{
lean_dec(v_impl_2748_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2829_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v_size_2767_; lean_object* v_size_2768_; lean_object* v_k_2769_; lean_object* v_v_2770_; lean_object* v_l_2771_; lean_object* v_r_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
v_size_2767_ = lean_ctor_get(v_l_2754_, 0);
v_size_2768_ = lean_ctor_get(v_r_2755_, 0);
v_k_2769_ = lean_ctor_get(v_r_2755_, 1);
v_v_2770_ = lean_ctor_get(v_r_2755_, 2);
v_l_2771_ = lean_ctor_get(v_r_2755_, 3);
v_r_2772_ = lean_ctor_get(v_r_2755_, 4);
v___x_2773_ = lean_unsigned_to_nat(2u);
v___x_2774_ = lean_nat_mul(v___x_2773_, v_size_2767_);
v___x_2775_ = lean_nat_dec_lt(v_size_2768_, v___x_2774_);
lean_dec(v___x_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2804_; 
lean_inc(v_r_2772_);
lean_inc(v_l_2771_);
lean_inc(v_v_2770_);
lean_inc(v_k_2769_);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_r_2755_);
if (v_isSharedCheck_2804_ == 0)
{
lean_object* v_unused_2805_; lean_object* v_unused_2806_; lean_object* v_unused_2807_; lean_object* v_unused_2808_; lean_object* v_unused_2809_; 
v_unused_2805_ = lean_ctor_get(v_r_2755_, 4);
lean_dec(v_unused_2805_);
v_unused_2806_ = lean_ctor_get(v_r_2755_, 3);
lean_dec(v_unused_2806_);
v_unused_2807_ = lean_ctor_get(v_r_2755_, 2);
lean_dec(v_unused_2807_);
v_unused_2808_ = lean_ctor_get(v_r_2755_, 1);
lean_dec(v_unused_2808_);
v_unused_2809_ = lean_ctor_get(v_r_2755_, 0);
lean_dec(v_unused_2809_);
v___x_2777_ = v_r_2755_;
v_isShared_2778_ = v_isSharedCheck_2804_;
goto v_resetjp_2776_;
}
else
{
lean_dec(v_r_2755_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2804_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___x_2792_; lean_object* v___y_2794_; 
v___x_2779_ = lean_nat_add(v___x_2749_, v_size_2751_);
lean_dec(v_size_2751_);
v___x_2780_ = lean_nat_add(v___x_2779_, v_size_2750_);
lean_dec(v___x_2779_);
v___x_2792_ = lean_nat_add(v___x_2749_, v_size_2767_);
if (lean_obj_tag(v_l_2771_) == 0)
{
lean_object* v_size_2802_; 
v_size_2802_ = lean_ctor_get(v_l_2771_, 0);
lean_inc(v_size_2802_);
v___y_2794_ = v_size_2802_;
goto v___jp_2793_;
}
else
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_unsigned_to_nat(0u);
v___y_2794_ = v___x_2803_;
goto v___jp_2793_;
}
v___jp_2781_:
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2785_ = lean_nat_add(v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec(v___y_2783_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 4, v_r_2742_);
lean_ctor_set(v___x_2777_, 3, v_r_2772_);
lean_ctor_set(v___x_2777_, 2, v_v_2740_);
lean_ctor_set(v___x_2777_, 1, v_k_2739_);
lean_ctor_set(v___x_2777_, 0, v___x_2785_);
v___x_2787_ = v___x_2777_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_k_2739_);
lean_ctor_set(v_reuseFailAlloc_2791_, 2, v_v_2740_);
lean_ctor_set(v_reuseFailAlloc_2791_, 3, v_r_2772_);
lean_ctor_set(v_reuseFailAlloc_2791_, 4, v_r_2742_);
v___x_2787_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2789_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 4, v___x_2787_);
lean_ctor_set(v___x_2765_, 3, v___y_2782_);
lean_ctor_set(v___x_2765_, 2, v_v_2770_);
lean_ctor_set(v___x_2765_, 1, v_k_2769_);
lean_ctor_set(v___x_2765_, 0, v___x_2780_);
v___x_2789_ = v___x_2765_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_k_2769_);
lean_ctor_set(v_reuseFailAlloc_2790_, 2, v_v_2770_);
lean_ctor_set(v_reuseFailAlloc_2790_, 3, v___y_2782_);
lean_ctor_set(v_reuseFailAlloc_2790_, 4, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
v___jp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2795_ = lean_nat_add(v___x_2792_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec(v___x_2792_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 4, v_l_2771_);
lean_ctor_set(v___x_2744_, 3, v_l_2754_);
lean_ctor_set(v___x_2744_, 2, v_v_2753_);
lean_ctor_set(v___x_2744_, 1, v_k_2752_);
lean_ctor_set(v___x_2744_, 0, v___x_2795_);
v___x_2797_ = v___x_2744_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2795_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_k_2752_);
lean_ctor_set(v_reuseFailAlloc_2801_, 2, v_v_2753_);
lean_ctor_set(v_reuseFailAlloc_2801_, 3, v_l_2754_);
lean_ctor_set(v_reuseFailAlloc_2801_, 4, v_l_2771_);
v___x_2797_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_nat_add(v___x_2749_, v_size_2750_);
if (lean_obj_tag(v_r_2772_) == 0)
{
lean_object* v_size_2799_; 
v_size_2799_ = lean_ctor_get(v_r_2772_, 0);
lean_inc(v_size_2799_);
v___y_2782_ = v___x_2797_;
v___y_2783_ = v___x_2798_;
v___y_2784_ = v_size_2799_;
goto v___jp_2781_;
}
else
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_unsigned_to_nat(0u);
v___y_2782_ = v___x_2797_;
v___y_2783_ = v___x_2798_;
v___y_2784_ = v___x_2800_;
goto v___jp_2781_;
}
}
}
}
}
else
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2815_; 
lean_del_object(v___x_2744_);
v___x_2810_ = lean_nat_add(v___x_2749_, v_size_2751_);
lean_dec(v_size_2751_);
v___x_2811_ = lean_nat_add(v___x_2810_, v_size_2750_);
lean_dec(v___x_2810_);
v___x_2812_ = lean_nat_add(v___x_2749_, v_size_2750_);
v___x_2813_ = lean_nat_add(v___x_2812_, v_size_2768_);
lean_dec(v___x_2812_);
lean_inc_ref(v_r_2742_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 4, v_r_2742_);
lean_ctor_set(v___x_2765_, 3, v_r_2755_);
lean_ctor_set(v___x_2765_, 2, v_v_2740_);
lean_ctor_set(v___x_2765_, 1, v_k_2739_);
lean_ctor_set(v___x_2765_, 0, v___x_2813_);
v___x_2815_ = v___x_2765_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_k_2739_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_v_2740_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_r_2755_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v_r_2742_);
v___x_2815_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
v_isSharedCheck_2822_ = !lean_is_exclusive(v_r_2742_);
if (v_isSharedCheck_2822_ == 0)
{
lean_object* v_unused_2823_; lean_object* v_unused_2824_; lean_object* v_unused_2825_; lean_object* v_unused_2826_; lean_object* v_unused_2827_; 
v_unused_2823_ = lean_ctor_get(v_r_2742_, 4);
lean_dec(v_unused_2823_);
v_unused_2824_ = lean_ctor_get(v_r_2742_, 3);
lean_dec(v_unused_2824_);
v_unused_2825_ = lean_ctor_get(v_r_2742_, 2);
lean_dec(v_unused_2825_);
v_unused_2826_ = lean_ctor_get(v_r_2742_, 1);
lean_dec(v_unused_2826_);
v_unused_2827_ = lean_ctor_get(v_r_2742_, 0);
lean_dec(v_unused_2827_);
v___x_2817_ = v_r_2742_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_dec(v_r_2742_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 4, v___x_2815_);
lean_ctor_set(v___x_2817_, 3, v_l_2754_);
lean_ctor_set(v___x_2817_, 2, v_v_2753_);
lean_ctor_set(v___x_2817_, 1, v_k_2752_);
lean_ctor_set(v___x_2817_, 0, v___x_2811_);
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v_k_2752_);
lean_ctor_set(v_reuseFailAlloc_2821_, 2, v_v_2753_);
lean_ctor_set(v_reuseFailAlloc_2821_, 3, v_l_2754_);
lean_ctor_set(v_reuseFailAlloc_2821_, 4, v___x_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2835_; 
v_l_2835_ = lean_ctor_get(v_impl_2748_, 3);
lean_inc(v_l_2835_);
if (lean_obj_tag(v_l_2835_) == 0)
{
lean_object* v_r_2836_; lean_object* v_k_2837_; lean_object* v_v_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2849_; 
v_r_2836_ = lean_ctor_get(v_impl_2748_, 4);
v_k_2837_ = lean_ctor_get(v_impl_2748_, 1);
v_v_2838_ = lean_ctor_get(v_impl_2748_, 2);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_impl_2748_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; lean_object* v_unused_2851_; 
v_unused_2850_ = lean_ctor_get(v_impl_2748_, 3);
lean_dec(v_unused_2850_);
v_unused_2851_ = lean_ctor_get(v_impl_2748_, 0);
lean_dec(v_unused_2851_);
v___x_2840_ = v_impl_2748_;
v_isShared_2841_ = v_isSharedCheck_2849_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_r_2836_);
lean_inc(v_v_2838_);
lean_inc(v_k_2837_);
lean_dec(v_impl_2748_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2849_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2842_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2836_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 3, v_r_2836_);
lean_ctor_set(v___x_2840_, 2, v_v_2740_);
lean_ctor_set(v___x_2840_, 1, v_k_2739_);
lean_ctor_set(v___x_2840_, 0, v___x_2749_);
v___x_2844_ = v___x_2840_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_k_2739_);
lean_ctor_set(v_reuseFailAlloc_2848_, 2, v_v_2740_);
lean_ctor_set(v_reuseFailAlloc_2848_, 3, v_r_2836_);
lean_ctor_set(v_reuseFailAlloc_2848_, 4, v_r_2836_);
v___x_2844_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
lean_object* v___x_2846_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 4, v___x_2844_);
lean_ctor_set(v___x_2744_, 3, v_l_2835_);
lean_ctor_set(v___x_2744_, 2, v_v_2838_);
lean_ctor_set(v___x_2744_, 1, v_k_2837_);
lean_ctor_set(v___x_2744_, 0, v___x_2842_);
v___x_2846_ = v___x_2744_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_k_2837_);
lean_ctor_set(v_reuseFailAlloc_2847_, 2, v_v_2838_);
lean_ctor_set(v_reuseFailAlloc_2847_, 3, v_l_2835_);
lean_ctor_set(v_reuseFailAlloc_2847_, 4, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
else
{
lean_object* v_r_2852_; 
v_r_2852_ = lean_ctor_get(v_impl_2748_, 4);
lean_inc(v_r_2852_);
if (lean_obj_tag(v_r_2852_) == 0)
{
lean_object* v_k_2853_; lean_object* v_v_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2877_; 
v_k_2853_ = lean_ctor_get(v_impl_2748_, 1);
v_v_2854_ = lean_ctor_get(v_impl_2748_, 2);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_impl_2748_);
if (v_isSharedCheck_2877_ == 0)
{
lean_object* v_unused_2878_; lean_object* v_unused_2879_; lean_object* v_unused_2880_; 
v_unused_2878_ = lean_ctor_get(v_impl_2748_, 4);
lean_dec(v_unused_2878_);
v_unused_2879_ = lean_ctor_get(v_impl_2748_, 3);
lean_dec(v_unused_2879_);
v_unused_2880_ = lean_ctor_get(v_impl_2748_, 0);
lean_dec(v_unused_2880_);
v___x_2856_ = v_impl_2748_;
v_isShared_2857_ = v_isSharedCheck_2877_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_v_2854_);
lean_inc(v_k_2853_);
lean_dec(v_impl_2748_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2877_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v_k_2858_; lean_object* v_v_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2873_; 
v_k_2858_ = lean_ctor_get(v_r_2852_, 1);
v_v_2859_ = lean_ctor_get(v_r_2852_, 2);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_r_2852_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; lean_object* v_unused_2875_; lean_object* v_unused_2876_; 
v_unused_2874_ = lean_ctor_get(v_r_2852_, 4);
lean_dec(v_unused_2874_);
v_unused_2875_ = lean_ctor_get(v_r_2852_, 3);
lean_dec(v_unused_2875_);
v_unused_2876_ = lean_ctor_get(v_r_2852_, 0);
lean_dec(v_unused_2876_);
v___x_2861_ = v_r_2852_;
v_isShared_2862_ = v_isSharedCheck_2873_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_v_2859_);
lean_inc(v_k_2858_);
lean_dec(v_r_2852_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2873_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; lean_object* v___x_2865_; 
v___x_2863_ = lean_unsigned_to_nat(3u);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 4, v_l_2835_);
lean_ctor_set(v___x_2861_, 3, v_l_2835_);
lean_ctor_set(v___x_2861_, 2, v_v_2854_);
lean_ctor_set(v___x_2861_, 1, v_k_2853_);
lean_ctor_set(v___x_2861_, 0, v___x_2749_);
v___x_2865_ = v___x_2861_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_k_2853_);
lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_v_2854_);
lean_ctor_set(v_reuseFailAlloc_2872_, 3, v_l_2835_);
lean_ctor_set(v_reuseFailAlloc_2872_, 4, v_l_2835_);
v___x_2865_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2867_; 
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 4, v_l_2835_);
lean_ctor_set(v___x_2856_, 2, v_v_2740_);
lean_ctor_set(v___x_2856_, 1, v_k_2739_);
lean_ctor_set(v___x_2856_, 0, v___x_2749_);
v___x_2867_ = v___x_2856_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_k_2739_);
lean_ctor_set(v_reuseFailAlloc_2871_, 2, v_v_2740_);
lean_ctor_set(v_reuseFailAlloc_2871_, 3, v_l_2835_);
lean_ctor_set(v_reuseFailAlloc_2871_, 4, v_l_2835_);
v___x_2867_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2869_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 4, v___x_2867_);
lean_ctor_set(v___x_2744_, 3, v___x_2865_);
lean_ctor_set(v___x_2744_, 2, v_v_2859_);
lean_ctor_set(v___x_2744_, 1, v_k_2858_);
lean_ctor_set(v___x_2744_, 0, v___x_2863_);
v___x_2869_ = v___x_2744_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2863_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_k_2858_);
lean_ctor_set(v_reuseFailAlloc_2870_, 2, v_v_2859_);
lean_ctor_set(v_reuseFailAlloc_2870_, 3, v___x_2865_);
lean_ctor_set(v_reuseFailAlloc_2870_, 4, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = lean_unsigned_to_nat(2u);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 4, v_r_2852_);
lean_ctor_set(v___x_2744_, 3, v_impl_2748_);
lean_ctor_set(v___x_2744_, 0, v___x_2881_);
v___x_2883_ = v___x_2744_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_k_2739_);
lean_ctor_set(v_reuseFailAlloc_2884_, 2, v_v_2740_);
lean_ctor_set(v_reuseFailAlloc_2884_, 3, v_impl_2748_);
lean_ctor_set(v_reuseFailAlloc_2884_, 4, v_r_2852_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2886_; 
lean_dec(v_v_2740_);
lean_dec(v_k_2739_);
lean_dec_ref(v_cmp_2734_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 2, v_v_2736_);
lean_ctor_set(v___x_2744_, 1, v_k_2735_);
v___x_2886_ = v___x_2744_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_size_2738_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_k_2735_);
lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_v_2736_);
lean_ctor_set(v_reuseFailAlloc_2887_, 3, v_l_2741_);
lean_ctor_set(v_reuseFailAlloc_2887_, 4, v_r_2742_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
default: 
{
lean_object* v_impl_2888_; lean_object* v___x_2889_; 
lean_dec(v_size_2738_);
v_impl_2888_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_2734_, v_k_2735_, v_v_2736_, v_r_2742_);
v___x_2889_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2741_) == 0)
{
lean_object* v_size_2890_; lean_object* v_size_2891_; lean_object* v_k_2892_; lean_object* v_v_2893_; lean_object* v_l_2894_; lean_object* v_r_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; uint8_t v___x_2898_; 
v_size_2890_ = lean_ctor_get(v_l_2741_, 0);
v_size_2891_ = lean_ctor_get(v_impl_2888_, 0);
lean_inc(v_size_2891_);
v_k_2892_ = lean_ctor_get(v_impl_2888_, 1);
lean_inc(v_k_2892_);
v_v_2893_ = lean_ctor_get(v_impl_2888_, 2);
lean_inc(v_v_2893_);
v_l_2894_ = lean_ctor_get(v_impl_2888_, 3);
lean_inc(v_l_2894_);
v_r_2895_ = lean_ctor_get(v_impl_2888_, 4);
lean_inc(v_r_2895_);
v___x_2896_ = lean_unsigned_to_nat(3u);
v___x_2897_ = lean_nat_mul(v___x_2896_, v_size_2890_);
v___x_2898_ = lean_nat_dec_lt(v___x_2897_, v_size_2891_);
lean_dec(v___x_2897_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2902_; 
lean_dec(v_r_2895_);
lean_dec(v_l_2894_);
lean_dec(v_v_2893_);
lean_dec(v_k_2892_);
v___x_2899_ = lean_nat_add(v___x_2889_, v_size_2890_);
v___x_2900_ = lean_nat_add(v___x_2899_, v_size_2891_);
lean_dec(v_size_2891_);
lean_dec(v___x_2899_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 4, v_impl_2888_);
lean_ctor_set(v___x_2744_, 0, v___x_2900_);
v___x_2902_ = v___x_2744_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_k_2739_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_v_2740_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_l_2741_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v_impl_2888_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
else
{
lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2967_; 
v_isSharedCheck_2967_ = !lean_is_exclusive(v_impl_2888_);
if (v_isSharedCheck_2967_ == 0)
{
lean_object* v_unused_2968_; lean_object* v_unused_2969_; lean_object* v_unused_2970_; lean_object* v_unused_2971_; lean_object* v_unused_2972_; 
v_unused_2968_ = lean_ctor_get(v_impl_2888_, 4);
lean_dec(v_unused_2968_);
v_unused_2969_ = lean_ctor_get(v_impl_2888_, 3);
lean_dec(v_unused_2969_);
v_unused_2970_ = lean_ctor_get(v_impl_2888_, 2);
lean_dec(v_unused_2970_);
v_unused_2971_ = lean_ctor_get(v_impl_2888_, 1);
lean_dec(v_unused_2971_);
v_unused_2972_ = lean_ctor_get(v_impl_2888_, 0);
lean_dec(v_unused_2972_);
v___x_2905_ = v_impl_2888_;
v_isShared_2906_ = v_isSharedCheck_2967_;
goto v_resetjp_2904_;
}
else
{
lean_dec(v_impl_2888_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2967_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v_size_2907_; lean_object* v_k_2908_; lean_object* v_v_2909_; lean_object* v_l_2910_; lean_object* v_r_2911_; lean_object* v_size_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v_size_2907_ = lean_ctor_get(v_l_2894_, 0);
v_k_2908_ = lean_ctor_get(v_l_2894_, 1);
v_v_2909_ = lean_ctor_get(v_l_2894_, 2);
v_l_2910_ = lean_ctor_get(v_l_2894_, 3);
v_r_2911_ = lean_ctor_get(v_l_2894_, 4);
v_size_2912_ = lean_ctor_get(v_r_2895_, 0);
v___x_2913_ = lean_unsigned_to_nat(2u);
v___x_2914_ = lean_nat_mul(v___x_2913_, v_size_2912_);
v___x_2915_ = lean_nat_dec_lt(v_size_2907_, v___x_2914_);
lean_dec(v___x_2914_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2943_; 
lean_inc(v_r_2911_);
lean_inc(v_l_2910_);
lean_inc(v_v_2909_);
lean_inc(v_k_2908_);
v_isSharedCheck_2943_ = !lean_is_exclusive(v_l_2894_);
if (v_isSharedCheck_2943_ == 0)
{
lean_object* v_unused_2944_; lean_object* v_unused_2945_; lean_object* v_unused_2946_; lean_object* v_unused_2947_; lean_object* v_unused_2948_; 
v_unused_2944_ = lean_ctor_get(v_l_2894_, 4);
lean_dec(v_unused_2944_);
v_unused_2945_ = lean_ctor_get(v_l_2894_, 3);
lean_dec(v_unused_2945_);
v_unused_2946_ = lean_ctor_get(v_l_2894_, 2);
lean_dec(v_unused_2946_);
v_unused_2947_ = lean_ctor_get(v_l_2894_, 1);
lean_dec(v_unused_2947_);
v_unused_2948_ = lean_ctor_get(v_l_2894_, 0);
lean_dec(v_unused_2948_);
v___x_2917_ = v_l_2894_;
v_isShared_2918_ = v_isSharedCheck_2943_;
goto v_resetjp_2916_;
}
else
{
lean_dec(v_l_2894_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2943_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2933_; 
v___x_2919_ = lean_nat_add(v___x_2889_, v_size_2890_);
v___x_2920_ = lean_nat_add(v___x_2919_, v_size_2891_);
lean_dec(v_size_2891_);
if (lean_obj_tag(v_l_2910_) == 0)
{
lean_object* v_size_2941_; 
v_size_2941_ = lean_ctor_get(v_l_2910_, 0);
lean_inc(v_size_2941_);
v___y_2933_ = v_size_2941_;
goto v___jp_2932_;
}
else
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_unsigned_to_nat(0u);
v___y_2933_ = v___x_2942_;
goto v___jp_2932_;
}
v___jp_2921_:
{
lean_object* v___x_2925_; lean_object* v___x_2927_; 
v___x_2925_ = lean_nat_add(v___y_2923_, v___y_2924_);
lean_dec(v___y_2924_);
lean_dec(v___y_2923_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 4, v_r_2895_);
lean_ctor_set(v___x_2917_, 3, v_r_2911_);
lean_ctor_set(v___x_2917_, 2, v_v_2893_);
lean_ctor_set(v___x_2917_, 1, v_k_2892_);
lean_ctor_set(v___x_2917_, 0, v___x_2925_);
v___x_2927_ = v___x_2917_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2925_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_k_2892_);
lean_ctor_set(v_reuseFailAlloc_2931_, 2, v_v_2893_);
lean_ctor_set(v_reuseFailAlloc_2931_, 3, v_r_2911_);
lean_ctor_set(v_reuseFailAlloc_2931_, 4, v_r_2895_);
v___x_2927_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
lean_object* v___x_2929_; 
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 4, v___x_2927_);
lean_ctor_set(v___x_2905_, 3, v___y_2922_);
lean_ctor_set(v___x_2905_, 2, v_v_2909_);
lean_ctor_set(v___x_2905_, 1, v_k_2908_);
lean_ctor_set(v___x_2905_, 0, v___x_2920_);
v___x_2929_ = v___x_2905_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_k_2908_);
lean_ctor_set(v_reuseFailAlloc_2930_, 2, v_v_2909_);
lean_ctor_set(v_reuseFailAlloc_2930_, 3, v___y_2922_);
lean_ctor_set(v_reuseFailAlloc_2930_, 4, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
v___jp_2932_:
{
lean_object* v___x_2934_; lean_object* v___x_2936_; 
v___x_2934_ = lean_nat_add(v___x_2919_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec(v___x_2919_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 4, v_l_2910_);
lean_ctor_set(v___x_2744_, 0, v___x_2934_);
v___x_2936_ = v___x_2744_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2934_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_k_2739_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_v_2740_);
lean_ctor_set(v_reuseFailAlloc_2940_, 3, v_l_2741_);
lean_ctor_set(v_reuseFailAlloc_2940_, 4, v_l_2910_);
v___x_2936_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_nat_add(v___x_2889_, v_size_2912_);
if (lean_obj_tag(v_r_2911_) == 0)
{
lean_object* v_size_2938_; 
v_size_2938_ = lean_ctor_get(v_r_2911_, 0);
lean_inc(v_size_2938_);
v___y_2922_ = v___x_2936_;
v___y_2923_ = v___x_2937_;
v___y_2924_ = v_size_2938_;
goto v___jp_2921_;
}
else
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_unsigned_to_nat(0u);
v___y_2922_ = v___x_2936_;
v___y_2923_ = v___x_2937_;
v___y_2924_ = v___x_2939_;
goto v___jp_2921_;
}
}
}
}
}
else
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2953_; 
lean_del_object(v___x_2744_);
v___x_2949_ = lean_nat_add(v___x_2889_, v_size_2890_);
v___x_2950_ = lean_nat_add(v___x_2949_, v_size_2891_);
lean_dec(v_size_2891_);
v___x_2951_ = lean_nat_add(v___x_2949_, v_size_2907_);
lean_dec(v___x_2949_);
lean_inc_ref(v_l_2741_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 4, v_l_2894_);
lean_ctor_set(v___x_2905_, 3, v_l_2741_);
lean_ctor_set(v___x_2905_, 2, v_v_2740_);
lean_ctor_set(v___x_2905_, 1, v_k_2739_);
lean_ctor_set(v___x_2905_, 0, v___x_2951_);
v___x_2953_ = v___x_2905_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2951_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_k_2739_);
lean_ctor_set(v_reuseFailAlloc_2966_, 2, v_v_2740_);
lean_ctor_set(v_reuseFailAlloc_2966_, 3, v_l_2741_);
lean_ctor_set(v_reuseFailAlloc_2966_, 4, v_l_2894_);
v___x_2953_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
v_isSharedCheck_2960_ = !lean_is_exclusive(v_l_2741_);
if (v_isSharedCheck_2960_ == 0)
{
lean_object* v_unused_2961_; lean_object* v_unused_2962_; lean_object* v_unused_2963_; lean_object* v_unused_2964_; lean_object* v_unused_2965_; 
v_unused_2961_ = lean_ctor_get(v_l_2741_, 4);
lean_dec(v_unused_2961_);
v_unused_2962_ = lean_ctor_get(v_l_2741_, 3);
lean_dec(v_unused_2962_);
v_unused_2963_ = lean_ctor_get(v_l_2741_, 2);
lean_dec(v_unused_2963_);
v_unused_2964_ = lean_ctor_get(v_l_2741_, 1);
lean_dec(v_unused_2964_);
v_unused_2965_ = lean_ctor_get(v_l_2741_, 0);
lean_dec(v_unused_2965_);
v___x_2955_ = v_l_2741_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_dec(v_l_2741_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 4, v_r_2895_);
lean_ctor_set(v___x_2955_, 3, v___x_2953_);
lean_ctor_set(v___x_2955_, 2, v_v_2893_);
lean_ctor_set(v___x_2955_, 1, v_k_2892_);
lean_ctor_set(v___x_2955_, 0, v___x_2950_);
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_k_2892_);
lean_ctor_set(v_reuseFailAlloc_2959_, 2, v_v_2893_);
lean_ctor_set(v_reuseFailAlloc_2959_, 3, v___x_2953_);
lean_ctor_set(v_reuseFailAlloc_2959_, 4, v_r_2895_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2973_; 
v_l_2973_ = lean_ctor_get(v_impl_2888_, 3);
lean_inc(v_l_2973_);
if (lean_obj_tag(v_l_2973_) == 0)
{
lean_object* v_r_2974_; lean_object* v_k_2975_; lean_object* v_v_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2999_; 
v_r_2974_ = lean_ctor_get(v_impl_2888_, 4);
v_k_2975_ = lean_ctor_get(v_impl_2888_, 1);
v_v_2976_ = lean_ctor_get(v_impl_2888_, 2);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_impl_2888_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; lean_object* v_unused_3001_; 
v_unused_3000_ = lean_ctor_get(v_impl_2888_, 3);
lean_dec(v_unused_3000_);
v_unused_3001_ = lean_ctor_get(v_impl_2888_, 0);
lean_dec(v_unused_3001_);
v___x_2978_ = v_impl_2888_;
v_isShared_2979_ = v_isSharedCheck_2999_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_r_2974_);
lean_inc(v_v_2976_);
lean_inc(v_k_2975_);
lean_dec(v_impl_2888_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2999_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v_k_2980_; lean_object* v_v_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2995_; 
v_k_2980_ = lean_ctor_get(v_l_2973_, 1);
v_v_2981_ = lean_ctor_get(v_l_2973_, 2);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_l_2973_);
if (v_isSharedCheck_2995_ == 0)
{
lean_object* v_unused_2996_; lean_object* v_unused_2997_; lean_object* v_unused_2998_; 
v_unused_2996_ = lean_ctor_get(v_l_2973_, 4);
lean_dec(v_unused_2996_);
v_unused_2997_ = lean_ctor_get(v_l_2973_, 3);
lean_dec(v_unused_2997_);
v_unused_2998_ = lean_ctor_get(v_l_2973_, 0);
lean_dec(v_unused_2998_);
v___x_2983_ = v_l_2973_;
v_isShared_2984_ = v_isSharedCheck_2995_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_v_2981_);
lean_inc(v_k_2980_);
lean_dec(v_l_2973_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2995_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2985_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2974_, 2);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 4, v_r_2974_);
lean_ctor_set(v___x_2983_, 3, v_r_2974_);
lean_ctor_set(v___x_2983_, 2, v_v_2740_);
lean_ctor_set(v___x_2983_, 1, v_k_2739_);
lean_ctor_set(v___x_2983_, 0, v___x_2889_);
v___x_2987_ = v___x_2983_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_k_2739_);
lean_ctor_set(v_reuseFailAlloc_2994_, 2, v_v_2740_);
lean_ctor_set(v_reuseFailAlloc_2994_, 3, v_r_2974_);
lean_ctor_set(v_reuseFailAlloc_2994_, 4, v_r_2974_);
v___x_2987_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2989_; 
lean_inc(v_r_2974_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 3, v_r_2974_);
lean_ctor_set(v___x_2978_, 0, v___x_2889_);
v___x_2989_ = v___x_2978_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_k_2975_);
lean_ctor_set(v_reuseFailAlloc_2993_, 2, v_v_2976_);
lean_ctor_set(v_reuseFailAlloc_2993_, 3, v_r_2974_);
lean_ctor_set(v_reuseFailAlloc_2993_, 4, v_r_2974_);
v___x_2989_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2991_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 4, v___x_2989_);
lean_ctor_set(v___x_2744_, 3, v___x_2987_);
lean_ctor_set(v___x_2744_, 2, v_v_2981_);
lean_ctor_set(v___x_2744_, 1, v_k_2980_);
lean_ctor_set(v___x_2744_, 0, v___x_2985_);
v___x_2991_ = v___x_2744_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_k_2980_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v_v_2981_);
lean_ctor_set(v_reuseFailAlloc_2992_, 3, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_2992_, 4, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
}
}
else
{
lean_object* v_r_3002_; 
v_r_3002_ = lean_ctor_get(v_impl_2888_, 4);
lean_inc(v_r_3002_);
if (lean_obj_tag(v_r_3002_) == 0)
{
lean_object* v_k_3003_; lean_object* v_v_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3015_; 
v_k_3003_ = lean_ctor_get(v_impl_2888_, 1);
v_v_3004_ = lean_ctor_get(v_impl_2888_, 2);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_impl_2888_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; lean_object* v_unused_3017_; lean_object* v_unused_3018_; 
v_unused_3016_ = lean_ctor_get(v_impl_2888_, 4);
lean_dec(v_unused_3016_);
v_unused_3017_ = lean_ctor_get(v_impl_2888_, 3);
lean_dec(v_unused_3017_);
v_unused_3018_ = lean_ctor_get(v_impl_2888_, 0);
lean_dec(v_unused_3018_);
v___x_3006_ = v_impl_2888_;
v_isShared_3007_ = v_isSharedCheck_3015_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_v_3004_);
lean_inc(v_k_3003_);
lean_dec(v_impl_2888_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3015_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3010_; 
v___x_3008_ = lean_unsigned_to_nat(3u);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 4, v_l_2973_);
lean_ctor_set(v___x_3006_, 2, v_v_2740_);
lean_ctor_set(v___x_3006_, 1, v_k_2739_);
lean_ctor_set(v___x_3006_, 0, v___x_2889_);
v___x_3010_ = v___x_3006_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v_k_2739_);
lean_ctor_set(v_reuseFailAlloc_3014_, 2, v_v_2740_);
lean_ctor_set(v_reuseFailAlloc_3014_, 3, v_l_2973_);
lean_ctor_set(v_reuseFailAlloc_3014_, 4, v_l_2973_);
v___x_3010_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3012_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 4, v_r_3002_);
lean_ctor_set(v___x_2744_, 3, v___x_3010_);
lean_ctor_set(v___x_2744_, 2, v_v_3004_);
lean_ctor_set(v___x_2744_, 1, v_k_3003_);
lean_ctor_set(v___x_2744_, 0, v___x_3008_);
v___x_3012_ = v___x_2744_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3008_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_k_3003_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_v_3004_);
lean_ctor_set(v_reuseFailAlloc_3013_, 3, v___x_3010_);
lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_r_3002_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3019_ = lean_unsigned_to_nat(2u);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 4, v_impl_2888_);
lean_ctor_set(v___x_2744_, 3, v_r_3002_);
lean_ctor_set(v___x_2744_, 0, v___x_3019_);
v___x_3021_ = v___x_2744_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_k_2739_);
lean_ctor_set(v_reuseFailAlloc_3022_, 2, v_v_2740_);
lean_ctor_set(v_reuseFailAlloc_3022_, 3, v_r_3002_);
lean_ctor_set(v_reuseFailAlloc_3022_, 4, v_impl_2888_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
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
lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_dec_ref(v_cmp_2734_);
v___x_3024_ = lean_unsigned_to_nat(1u);
v___x_3025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
lean_ctor_set(v___x_3025_, 1, v_k_2735_);
lean_ctor_set(v___x_3025_, 2, v_v_2736_);
lean_ctor_set(v___x_3025_, 3, v_t_2737_);
lean_ctor_set(v___x_3025_, 4, v_t_2737_);
return v___x_3025_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(lean_object* v_cmp_3026_, lean_object* v_init_3027_, lean_object* v_x_3028_){
_start:
{
if (lean_obj_tag(v_x_3028_) == 0)
{
lean_object* v_k_3029_; lean_object* v_v_3030_; lean_object* v_l_3031_; lean_object* v_r_3032_; lean_object* v___x_3033_; 
v_k_3029_ = lean_ctor_get(v_x_3028_, 1);
lean_inc(v_k_3029_);
v_v_3030_ = lean_ctor_get(v_x_3028_, 2);
lean_inc(v_v_3030_);
v_l_3031_ = lean_ctor_get(v_x_3028_, 3);
lean_inc(v_l_3031_);
v_r_3032_ = lean_ctor_get(v_x_3028_, 4);
lean_inc(v_r_3032_);
lean_dec_ref_known(v_x_3028_, 5);
lean_inc_ref(v_cmp_3026_);
v___x_3033_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_3026_, v_init_3027_, v_l_3031_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_dec(v_r_3032_);
lean_dec(v_v_3030_);
lean_dec(v_k_3029_);
lean_dec_ref(v_cmp_3026_);
return v___x_3033_;
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3035_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3033_, 1);
v___x_3035_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_v_3030_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec(v_a_3034_);
lean_dec(v_r_3032_);
lean_dec(v_k_3029_);
lean_dec_ref(v_cmp_3026_);
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3045_; 
v_a_3044_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3035_, 1);
lean_inc_ref(v_cmp_3026_);
v___x_3045_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3026_, v_k_3029_, v_a_3044_, v_a_3034_);
v_init_3027_ = v___x_3045_;
v_x_3028_ = v_r_3032_;
goto _start;
}
}
}
else
{
lean_object* v___x_3047_; 
lean_dec_ref(v_cmp_3026_);
v___x_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_init_3027_);
return v___x_3047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(lean_object* v_cmp_3048_, lean_object* v_j_3049_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lean_Json_getObj_x3f(v_j_3049_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec_ref(v_cmp_3048_);
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3050_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3050_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v_a_3059_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3050_, 1);
v___x_3060_ = lean_box(1);
v___x_3061_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_3048_, v___x_3060_, v_a_3059_);
return v___x_3061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(lean_object* v_x_3065_){
_start:
{
if (lean_obj_tag(v_x_3065_) == 0)
{
lean_object* v___x_3066_; 
v___x_3066_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__0));
return v___x_3066_;
}
else
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__1));
v___x_3068_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(v___x_3067_, v_x_3065_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3085_; 
v_a_3077_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3079_ = v___x_3068_;
v_isShared_3080_ = v_isSharedCheck_3085_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3068_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3085_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3081_; lean_object* v___x_3083_; 
v___x_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3081_, 0, v_a_3077_);
if (v_isShared_3080_ == 0)
{
lean_ctor_set(v___x_3079_, 0, v___x_3081_);
v___x_3083_ = v___x_3079_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3081_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(lean_object* v_j_3086_, lean_object* v_k_3087_){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = l_Lean_Json_getObjValD(v_j_3086_, v_k_3087_);
v___x_3089_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(v___x_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4___boxed(lean_object* v_j_3090_, lean_object* v_k_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_j_3090_, v_k_3091_);
lean_dec_ref(v_k_3091_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(lean_object* v_j_3093_, lean_object* v_k_3094_){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = l_Lean_Json_getObjValD(v_j_3093_, v_k_3094_);
v___x_3096_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v___x_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1___boxed(lean_object* v_j_3097_, lean_object* v_k_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_j_3097_, v_k_3098_);
lean_dec_ref(v_k_3098_);
return v_res_3099_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = 1;
v___x_3109_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__4));
v___x_3110_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3109_, v___x_3108_);
return v___x_3110_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__6));
v___x_3113_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__5, &l_Lake_Check_instFromJsonConfig_fromJson___closed__5_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5);
v___x_3114_ = lean_string_append(v___x_3113_, v___x_3112_);
return v___x_3114_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3117_ = 1;
v___x_3118_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__8));
v___x_3119_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3118_, v___x_3117_);
return v___x_3119_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__9, &l_Lake_Check_instFromJsonConfig_fromJson___closed__9_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9);
v___x_3121_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3122_ = lean_string_append(v___x_3121_, v___x_3120_);
return v___x_3122_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3124_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3125_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__10, &l_Lake_Check_instFromJsonConfig_fromJson___closed__10_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10);
v___x_3126_ = lean_string_append(v___x_3125_, v___x_3124_);
return v___x_3126_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15(void){
_start:
{
uint8_t v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3130_ = 1;
v___x_3131_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__14));
v___x_3132_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3131_, v___x_3130_);
return v___x_3132_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16(void){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__15, &l_Lake_Check_instFromJsonConfig_fromJson___closed__15_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15);
v___x_3134_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3135_ = lean_string_append(v___x_3134_, v___x_3133_);
return v___x_3135_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3137_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__16, &l_Lake_Check_instFromJsonConfig_fromJson___closed__16_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16);
v___x_3138_ = lean_string_append(v___x_3137_, v___x_3136_);
return v___x_3138_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20(void){
_start:
{
uint8_t v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = 1;
v___x_3143_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__19));
v___x_3144_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3143_, v___x_3142_);
return v___x_3144_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3145_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__20, &l_Lake_Check_instFromJsonConfig_fromJson___closed__20_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20);
v___x_3146_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3147_ = lean_string_append(v___x_3146_, v___x_3145_);
return v___x_3147_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22(void){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3148_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3149_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__21, &l_Lake_Check_instFromJsonConfig_fromJson___closed__21_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21);
v___x_3150_ = lean_string_append(v___x_3149_, v___x_3148_);
return v___x_3150_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25(void){
_start:
{
uint8_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3154_ = 1;
v___x_3155_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__24));
v___x_3156_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3155_, v___x_3154_);
return v___x_3156_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26(void){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3157_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__25, &l_Lake_Check_instFromJsonConfig_fromJson___closed__25_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25);
v___x_3158_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3159_ = lean_string_append(v___x_3158_, v___x_3157_);
return v___x_3159_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27(void){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3160_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3161_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__26, &l_Lake_Check_instFromJsonConfig_fromJson___closed__26_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26);
v___x_3162_ = lean_string_append(v___x_3161_, v___x_3160_);
return v___x_3162_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29(void){
_start:
{
uint8_t v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = 1;
v___x_3166_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__28));
v___x_3167_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3166_, v___x_3165_);
return v___x_3167_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__29, &l_Lake_Check_instFromJsonConfig_fromJson___closed__29_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29);
v___x_3169_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3170_ = lean_string_append(v___x_3169_, v___x_3168_);
return v___x_3170_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3172_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__30, &l_Lake_Check_instFromJsonConfig_fromJson___closed__30_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30);
v___x_3173_ = lean_string_append(v___x_3172_, v___x_3171_);
return v___x_3173_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35(void){
_start:
{
uint8_t v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = 1;
v___x_3179_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__34));
v___x_3180_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3179_, v___x_3178_);
return v___x_3180_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3181_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__35, &l_Lake_Check_instFromJsonConfig_fromJson___closed__35_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35);
v___x_3182_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3183_ = lean_string_append(v___x_3182_, v___x_3181_);
return v___x_3183_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3184_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3185_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__36, &l_Lake_Check_instFromJsonConfig_fromJson___closed__36_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36);
v___x_3186_ = lean_string_append(v___x_3185_, v___x_3184_);
return v___x_3186_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41(void){
_start:
{
uint8_t v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = 1;
v___x_3192_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__40));
v___x_3193_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3192_, v___x_3191_);
return v___x_3193_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3194_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__41, &l_Lake_Check_instFromJsonConfig_fromJson___closed__41_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41);
v___x_3195_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3196_ = lean_string_append(v___x_3195_, v___x_3194_);
return v___x_3196_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43(void){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3198_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__42, &l_Lake_Check_instFromJsonConfig_fromJson___closed__42_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42);
v___x_3199_ = lean_string_append(v___x_3198_, v___x_3197_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instFromJsonConfig_fromJson(lean_object* v_json_3200_){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
lean_inc(v_json_3200_);
v___x_3202_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_3200_, v___x_3201_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3212_; 
lean_dec(v_json_3200_);
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3205_ = v___x_3202_;
v_isShared_3206_ = v_isSharedCheck_3212_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3212_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3210_; 
v___x_3207_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__12, &l_Lake_Check_instFromJsonConfig_fromJson___closed__12_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12);
v___x_3208_ = lean_string_append(v___x_3207_, v_a_3203_);
lean_dec(v_a_3203_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___x_3208_);
v___x_3210_ = v___x_3205_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
else
{
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec(v_json_3200_);
v_a_3213_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3202_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3202_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
lean_ctor_set_tag(v___x_3215_, 0);
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v_a_3221_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3221_);
lean_dec_ref_known(v___x_3202_, 1);
v___x_3222_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
lean_inc(v_json_3200_);
v___x_3223_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_3200_, v___x_3222_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3233_; 
lean_dec(v_a_3221_);
lean_dec(v_json_3200_);
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3226_ = v___x_3223_;
v_isShared_3227_ = v_isSharedCheck_3233_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3233_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3228_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__17, &l_Lake_Check_instFromJsonConfig_fromJson___closed__17_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17);
v___x_3229_ = lean_string_append(v___x_3228_, v_a_3224_);
lean_dec(v_a_3224_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3229_);
v___x_3231_ = v___x_3226_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3229_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
else
{
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v_a_3221_);
lean_dec(v_json_3200_);
v_a_3234_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3223_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3223_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
lean_ctor_set_tag(v___x_3236_, 0);
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v_a_3242_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3223_, 1);
v___x_3243_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
lean_inc(v_json_3200_);
v___x_3244_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_3200_, v___x_3243_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3254_; 
lean_dec(v_a_3242_);
lean_dec(v_a_3221_);
lean_dec(v_json_3200_);
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3247_ = v___x_3244_;
v_isShared_3248_ = v_isSharedCheck_3254_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3244_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3254_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3252_; 
v___x_3249_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__22, &l_Lake_Check_instFromJsonConfig_fromJson___closed__22_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22);
v___x_3250_ = lean_string_append(v___x_3249_, v_a_3245_);
lean_dec(v_a_3245_);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 0, v___x_3250_);
v___x_3252_ = v___x_3247_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3250_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
else
{
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec(v_a_3242_);
lean_dec(v_a_3221_);
lean_dec(v_json_3200_);
v_a_3255_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3244_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3244_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
lean_ctor_set_tag(v___x_3257_, 0);
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v_a_3263_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3244_, 1);
v___x_3264_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
lean_inc(v_json_3200_);
v___x_3265_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_json_3200_, v___x_3264_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3275_; 
lean_dec(v_a_3263_);
lean_dec(v_a_3242_);
lean_dec(v_a_3221_);
lean_dec(v_json_3200_);
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3275_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3275_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3270_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__27, &l_Lake_Check_instFromJsonConfig_fromJson___closed__27_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27);
v___x_3271_ = lean_string_append(v___x_3270_, v_a_3266_);
lean_dec(v_a_3266_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3271_);
v___x_3273_ = v___x_3268_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
else
{
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec(v_a_3263_);
lean_dec(v_a_3242_);
lean_dec(v_a_3221_);
lean_dec(v_json_3200_);
v_a_3276_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3265_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3265_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
lean_ctor_set_tag(v___x_3278_, 0);
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_a_3284_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3284_);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3285_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12));
lean_inc(v_json_3200_);
v___x_3286_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_3200_, v___x_3285_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3296_; 
lean_dec(v_a_3284_);
lean_dec(v_a_3263_);
lean_dec(v_a_3242_);
lean_dec(v_a_3221_);
lean_dec(v_json_3200_);
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3296_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3296_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3294_; 
v___x_3291_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__31, &l_Lake_Check_instFromJsonConfig_fromJson___closed__31_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31);
v___x_3292_ = lean_string_append(v___x_3291_, v_a_3287_);
lean_dec(v_a_3287_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 0, v___x_3292_);
v___x_3294_ = v___x_3289_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3292_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
else
{
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec(v_a_3284_);
lean_dec(v_a_3263_);
lean_dec(v_a_3242_);
lean_dec(v_a_3221_);
lean_dec(v_json_3200_);
v_a_3297_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3286_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3286_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
lean_ctor_set_tag(v___x_3299_, 0);
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_a_3305_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3286_, 1);
v___x_3306_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
lean_inc(v_json_3200_);
v___x_3307_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_json_3200_, v___x_3306_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3317_; 
lean_dec(v_a_3305_);
lean_dec(v_a_3284_);
lean_dec(v_a_3263_);
lean_dec(v_a_3242_);
lean_dec(v_a_3221_);
lean_dec(v_json_3200_);
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3310_ = v___x_3307_;
v_isShared_3311_ = v_isSharedCheck_3317_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3307_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3317_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3312_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__37, &l_Lake_Check_instFromJsonConfig_fromJson___closed__37_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37);
v___x_3313_ = lean_string_append(v___x_3312_, v_a_3308_);
lean_dec(v_a_3308_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v___x_3313_);
v___x_3315_ = v___x_3310_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
else
{
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec(v_a_3305_);
lean_dec(v_a_3284_);
lean_dec(v_a_3263_);
lean_dec(v_a_3242_);
lean_dec(v_a_3221_);
lean_dec(v_json_3200_);
v_a_3318_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3307_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3307_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
lean_ctor_set_tag(v___x_3320_, 0);
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v_a_3326_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3307_, 1);
v___x_3327_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_3328_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_json_3200_, v___x_3327_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3338_; 
lean_dec(v_a_3326_);
lean_dec(v_a_3305_);
lean_dec(v_a_3284_);
lean_dec(v_a_3263_);
lean_dec(v_a_3242_);
lean_dec(v_a_3221_);
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3338_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3338_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3333_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__43, &l_Lake_Check_instFromJsonConfig_fromJson___closed__43_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43);
v___x_3334_ = lean_string_append(v___x_3333_, v_a_3329_);
lean_dec(v_a_3329_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3334_);
v___x_3336_ = v___x_3331_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
else
{
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_dec(v_a_3326_);
lean_dec(v_a_3305_);
lean_dec(v_a_3284_);
lean_dec(v_a_3263_);
lean_dec(v_a_3242_);
lean_dec(v_a_3221_);
v_a_3339_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3328_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3328_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
lean_ctor_set_tag(v___x_3341_, 0);
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3355_; 
v_a_3347_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3349_ = v___x_3328_;
v_isShared_3350_ = v_isSharedCheck_3355_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3328_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3355_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3351_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3351_, 0, v_a_3221_);
lean_ctor_set(v___x_3351_, 1, v_a_3242_);
lean_ctor_set(v___x_3351_, 2, v_a_3263_);
lean_ctor_set(v___x_3351_, 3, v_a_3284_);
lean_ctor_set(v___x_3351_, 4, v_a_3305_);
lean_ctor_set(v___x_3351_, 5, v_a_3326_);
lean_ctor_set(v___x_3351_, 6, v_a_3347_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 0, v___x_3351_);
v___x_3353_ = v___x_3349_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10(lean_object* v_cmp_3356_, lean_object* v_00_u03b2_3357_, lean_object* v_k_3358_, lean_object* v_v_3359_, lean_object* v_t_3360_, lean_object* v_hl_3361_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3356_, v_k_3358_, v_v_3359_, v_t_3360_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(lean_object* v_k_3365_, lean_object* v_x_3366_){
_start:
{
if (lean_obj_tag(v_x_3366_) == 0)
{
lean_object* v___x_3367_; 
lean_dec_ref(v_k_3365_);
v___x_3367_ = lean_box(0);
return v___x_3367_;
}
else
{
lean_object* v_val_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_val_3368_ = lean_ctor_get(v_x_3366_, 0);
v___x_3369_ = lean_alloc_ctor(1, 0, 1);
v___x_3370_ = lean_unbox(v_val_3368_);
lean_ctor_set_uint8(v___x_3369_, 0, v___x_3370_);
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v_k_3365_);
lean_ctor_set(v___x_3371_, 1, v___x_3369_);
v___x_3372_ = lean_box(0);
v___x_3373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3371_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
return v___x_3373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2___boxed(lean_object* v_k_3374_, lean_object* v_x_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v_k_3374_, v_x_3375_);
lean_dec(v_x_3375_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(size_t v_sz_3377_, size_t v_i_3378_, lean_object* v_bs_3379_){
_start:
{
uint8_t v___x_3380_; 
v___x_3380_ = lean_usize_dec_lt(v_i_3378_, v_sz_3377_);
if (v___x_3380_ == 0)
{
return v_bs_3379_;
}
else
{
lean_object* v_v_3381_; lean_object* v___x_3382_; lean_object* v_bs_x27_3383_; lean_object* v___x_3384_; size_t v___x_3385_; size_t v___x_3386_; lean_object* v___x_3387_; 
v_v_3381_ = lean_array_uget(v_bs_3379_, v_i_3378_);
v___x_3382_ = lean_unsigned_to_nat(0u);
v_bs_x27_3383_ = lean_array_uset(v_bs_3379_, v_i_3378_, v___x_3382_);
v___x_3384_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_v_3381_);
v___x_3385_ = ((size_t)1ULL);
v___x_3386_ = lean_usize_add(v_i_3378_, v___x_3385_);
v___x_3387_ = lean_array_uset(v_bs_x27_3383_, v_i_3378_, v___x_3384_);
v_i_3378_ = v___x_3386_;
v_bs_3379_ = v___x_3387_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3389_, lean_object* v_i_3390_, lean_object* v_bs_3391_){
_start:
{
size_t v_sz_boxed_3392_; size_t v_i_boxed_3393_; lean_object* v_res_3394_; 
v_sz_boxed_3392_ = lean_unbox_usize(v_sz_3389_);
lean_dec(v_sz_3389_);
v_i_boxed_3393_ = lean_unbox_usize(v_i_3390_);
lean_dec(v_i_3390_);
v_res_3394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_boxed_3392_, v_i_boxed_3393_, v_bs_3391_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(lean_object* v_a_3395_){
_start:
{
size_t v_sz_3396_; size_t v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v_sz_3396_ = lean_array_size(v_a_3395_);
v___x_3397_ = ((size_t)0ULL);
v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_3396_, v___x_3397_, v_a_3395_);
v___x_3399_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(lean_object* v_x_3400_){
_start:
{
if (lean_obj_tag(v_x_3400_) == 0)
{
lean_object* v___x_3401_; 
v___x_3401_ = lean_box(0);
return v___x_3401_;
}
else
{
lean_object* v_val_3402_; lean_object* v___x_3403_; 
v_val_3402_ = lean_ctor_get(v_x_3400_, 0);
lean_inc(v_val_3402_);
lean_dec_ref_known(v_x_3400_, 1);
v___x_3403_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_val_3402_);
return v___x_3403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
if (lean_obj_tag(v_a_3404_) == 0)
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_array_to_list(v_a_3405_);
return v___x_3406_;
}
else
{
lean_object* v_head_3407_; lean_object* v_tail_3408_; lean_object* v___x_3409_; 
v_head_3407_ = lean_ctor_get(v_a_3404_, 0);
lean_inc(v_head_3407_);
v_tail_3408_ = lean_ctor_get(v_a_3404_, 1);
lean_inc(v_tail_3408_);
lean_dec_ref_known(v_a_3404_, 2);
v___x_3409_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_3405_, v_head_3407_);
v_a_3404_ = v_tail_3408_;
v_a_3405_ = v___x_3409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(lean_object* v_t_3411_){
_start:
{
if (lean_obj_tag(v_t_3411_) == 0)
{
lean_object* v_size_3412_; lean_object* v_k_3413_; lean_object* v_v_3414_; lean_object* v_l_3415_; lean_object* v_r_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3426_; 
v_size_3412_ = lean_ctor_get(v_t_3411_, 0);
v_k_3413_ = lean_ctor_get(v_t_3411_, 1);
v_v_3414_ = lean_ctor_get(v_t_3411_, 2);
v_l_3415_ = lean_ctor_get(v_t_3411_, 3);
v_r_3416_ = lean_ctor_get(v_t_3411_, 4);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_t_3411_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3418_ = v_t_3411_;
v_isShared_3419_ = v_isSharedCheck_3426_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_r_3416_);
lean_inc(v_l_3415_);
lean_inc(v_v_3414_);
lean_inc(v_k_3413_);
lean_inc(v_size_3412_);
lean_dec(v_t_3411_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3426_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
v___x_3420_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_v_3414_);
v___x_3421_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_l_3415_);
v___x_3422_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_r_3416_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 4, v___x_3422_);
lean_ctor_set(v___x_3418_, 3, v___x_3421_);
lean_ctor_set(v___x_3418_, 2, v___x_3420_);
v___x_3424_ = v___x_3418_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_size_3412_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_k_3413_);
lean_ctor_set(v_reuseFailAlloc_3425_, 2, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3425_, 3, v___x_3421_);
lean_ctor_set(v_reuseFailAlloc_3425_, 4, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
else
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_box(1);
return v___x_3427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(lean_object* v_map_3428_){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_map_3428_);
v___x_3430_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(lean_object* v_k_3431_, lean_object* v_x_3432_){
_start:
{
if (lean_obj_tag(v_x_3432_) == 0)
{
lean_object* v___x_3433_; 
lean_dec_ref(v_k_3431_);
v___x_3433_ = lean_box(0);
return v___x_3433_;
}
else
{
lean_object* v_val_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v_val_3434_ = lean_ctor_get(v_x_3432_, 0);
lean_inc(v_val_3434_);
lean_dec_ref_known(v_x_3432_, 1);
v___x_3435_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(v_val_3434_);
v___x_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3436_, 0, v_k_3431_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = lean_box(0);
v___x_3438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3436_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
return v___x_3438_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instToJsonConfig_toJson(lean_object* v_x_3441_){
_start:
{
lean_object* v_challenge__module_3442_; lean_object* v_solution__module_3443_; lean_object* v_theorem__names_3444_; lean_object* v_definition__names_3445_; lean_object* v_permitted__axioms_3446_; lean_object* v_enable__nanoda_x3f_3447_; lean_object* v_external__kernels_x3f_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v_challenge__module_3442_ = lean_ctor_get(v_x_3441_, 0);
lean_inc_ref(v_challenge__module_3442_);
v_solution__module_3443_ = lean_ctor_get(v_x_3441_, 1);
lean_inc_ref(v_solution__module_3443_);
v_theorem__names_3444_ = lean_ctor_get(v_x_3441_, 2);
lean_inc_ref(v_theorem__names_3444_);
v_definition__names_3445_ = lean_ctor_get(v_x_3441_, 3);
lean_inc(v_definition__names_3445_);
v_permitted__axioms_3446_ = lean_ctor_get(v_x_3441_, 4);
lean_inc_ref(v_permitted__axioms_3446_);
v_enable__nanoda_x3f_3447_ = lean_ctor_get(v_x_3441_, 5);
lean_inc(v_enable__nanoda_x3f_3447_);
v_external__kernels_x3f_3448_ = lean_ctor_get(v_x_3441_, 6);
lean_inc(v_external__kernels_x3f_3448_);
lean_dec_ref(v_x_3441_);
v___x_3449_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
v___x_3450_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3450_, 0, v_challenge__module_3442_);
v___x_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3449_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
v___x_3452_ = lean_box(0);
v___x_3453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3451_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
v___x_3454_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
v___x_3455_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3455_, 0, v_solution__module_3443_);
v___x_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
lean_ctor_set(v___x_3457_, 1, v___x_3452_);
v___x_3458_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
v___x_3459_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_theorem__names_3444_);
v___x_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3458_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___x_3461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
lean_ctor_set(v___x_3461_, 1, v___x_3452_);
v___x_3462_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
v___x_3463_ = l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(v_definition__names_3445_);
v___x_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3462_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
lean_ctor_set(v___x_3465_, 1, v___x_3452_);
v___x_3466_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12));
v___x_3467_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_permitted__axioms_3446_);
v___x_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3466_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
lean_ctor_set(v___x_3469_, 1, v___x_3452_);
v___x_3470_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
v___x_3471_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v___x_3470_, v_enable__nanoda_x3f_3447_);
lean_dec(v_enable__nanoda_x3f_3447_);
v___x_3472_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_3473_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(v___x_3472_, v_external__kernels_x3f_3448_);
v___x_3474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___x_3452_);
v___x_3475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3471_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3469_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3465_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v___x_3478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3461_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3457_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
v___x_3480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3453_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = ((lean_object*)(l_Lake_Check_instToJsonConfig_toJson___closed__0));
v___x_3482_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(v___x_3480_, v___x_3481_);
v___x_3483_ = l_Lean_Json_mkObj(v___x_3482_);
lean_dec(v___x_3482_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(lean_object* v_x_3492_, lean_object* v_x_3493_){
_start:
{
if (lean_obj_tag(v_x_3492_) == 0)
{
lean_object* v___x_3494_; 
v___x_3494_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3494_;
}
else
{
lean_object* v_val_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v_val_3495_ = lean_ctor_get(v_x_3492_, 0);
v___x_3496_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3497_ = lean_unbox(v_val_3495_);
v___x_3498_ = l_Bool_repr___redArg(v___x_3497_);
v___x_3499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3496_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = l_Repr_addAppParen(v___x_3499_, v_x_3493_);
return v___x_3500_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___boxed(lean_object* v_x_3501_, lean_object* v_x_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_x_3501_, v_x_3502_);
lean_dec(v_x_3502_);
lean_dec(v_x_3501_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_Check_instReprConfig_repr_spec__4(lean_object* v_a_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = lean_nat_to_int(v_a_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(lean_object* v_x_3506_, lean_object* v_x_3507_, lean_object* v_x_3508_){
_start:
{
if (lean_obj_tag(v_x_3508_) == 0)
{
lean_dec(v_x_3506_);
return v_x_3507_;
}
else
{
lean_object* v_head_3509_; lean_object* v_tail_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3521_; 
v_head_3509_ = lean_ctor_get(v_x_3508_, 0);
v_tail_3510_ = lean_ctor_get(v_x_3508_, 1);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_x_3508_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3512_ = v_x_3508_;
v_isShared_3513_ = v_isSharedCheck_3521_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_tail_3510_);
lean_inc(v_head_3509_);
lean_dec(v_x_3508_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3521_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
lean_inc(v_x_3506_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set_tag(v___x_3512_, 5);
lean_ctor_set(v___x_3512_, 1, v_x_3506_);
lean_ctor_set(v___x_3512_, 0, v_x_3507_);
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_x_3507_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_x_3506_);
v___x_3515_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = l_String_quote(v_head_3509_);
v___x_3517_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
v___x_3518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3515_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
v_x_3507_ = v___x_3518_;
v_x_3508_ = v_tail_3510_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_3522_, lean_object* v_x_3523_, lean_object* v_x_3524_){
_start:
{
if (lean_obj_tag(v_x_3524_) == 0)
{
lean_dec(v_x_3522_);
return v_x_3523_;
}
else
{
lean_object* v_head_3525_; lean_object* v_tail_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3537_; 
v_head_3525_ = lean_ctor_get(v_x_3524_, 0);
v_tail_3526_ = lean_ctor_get(v_x_3524_, 1);
v_isSharedCheck_3537_ = !lean_is_exclusive(v_x_3524_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3528_ = v_x_3524_;
v_isShared_3529_ = v_isSharedCheck_3537_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_tail_3526_);
lean_inc(v_head_3525_);
lean_dec(v_x_3524_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3537_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
lean_inc(v_x_3522_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set_tag(v___x_3528_, 5);
lean_ctor_set(v___x_3528_, 1, v_x_3522_);
lean_ctor_set(v___x_3528_, 0, v_x_3523_);
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_x_3523_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_x_3522_);
v___x_3531_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3532_ = l_String_quote(v_head_3525_);
v___x_3533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
v___x_3534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3531_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
v___x_3535_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(v_x_3522_, v___x_3534_, v_tail_3526_);
return v___x_3535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(lean_object* v___y_3538_){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = l_String_quote(v___y_3538_);
v___x_3540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(lean_object* v_x_3541_, lean_object* v_x_3542_){
_start:
{
if (lean_obj_tag(v_x_3541_) == 0)
{
lean_object* v___x_3543_; 
lean_dec(v_x_3542_);
v___x_3543_ = lean_box(0);
return v___x_3543_;
}
else
{
lean_object* v_tail_3544_; 
v_tail_3544_ = lean_ctor_get(v_x_3541_, 1);
if (lean_obj_tag(v_tail_3544_) == 0)
{
lean_object* v_head_3545_; lean_object* v___x_3546_; 
lean_dec(v_x_3542_);
v_head_3545_ = lean_ctor_get(v_x_3541_, 0);
lean_inc(v_head_3545_);
lean_dec_ref_known(v_x_3541_, 2);
v___x_3546_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3545_);
return v___x_3546_;
}
else
{
lean_object* v_head_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
lean_inc(v_tail_3544_);
v_head_3547_ = lean_ctor_get(v_x_3541_, 0);
lean_inc(v_head_3547_);
lean_dec_ref_known(v_x_3541_, 2);
v___x_3548_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3547_);
v___x_3549_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(v_x_3542_, v___x_3548_, v_tail_3544_);
return v___x_3549_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__0));
v___x_3558_ = lean_string_length(v___x_3557_);
return v___x_3558_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4);
v___x_3560_ = lean_nat_to_int(v___x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(lean_object* v_xs_3568_){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v___x_3569_ = lean_array_get_size(v_xs_3568_);
v___x_3570_ = lean_unsigned_to_nat(0u);
v___x_3571_ = lean_nat_dec_eq(v___x_3569_, v___x_3570_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3572_ = lean_array_to_list(v_xs_3568_);
v___x_3573_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3574_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(v___x_3572_, v___x_3573_);
v___x_3575_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5);
v___x_3576_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__6));
v___x_3577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
lean_ctor_set(v___x_3577_, 1, v___x_3574_);
v___x_3578_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_3579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3577_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
v___x_3580_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3575_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
v___x_3581_ = l_Std_Format_fill(v___x_3580_);
return v___x_3581_;
}
else
{
lean_object* v___x_3582_; 
lean_dec_ref(v_xs_3568_);
v___x_3582_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__9));
return v___x_3582_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(lean_object* v_x_3583_, lean_object* v_x_3584_){
_start:
{
if (lean_obj_tag(v_x_3583_) == 0)
{
lean_object* v___x_3585_; 
v___x_3585_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3585_;
}
else
{
lean_object* v_val_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v_val_3586_ = lean_ctor_get(v_x_3583_, 0);
lean_inc(v_val_3586_);
lean_dec_ref_known(v_x_3583_, 1);
v___x_3587_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3588_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_val_3586_);
v___x_3589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3587_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = l_Repr_addAppParen(v___x_3589_, v_x_3584_);
return v___x_3590_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1___boxed(lean_object* v_x_3591_, lean_object* v_x_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_x_3591_, v_x_3592_);
lean_dec(v_x_3592_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(lean_object* v_init_3594_, lean_object* v_x_3595_){
_start:
{
if (lean_obj_tag(v_x_3595_) == 0)
{
lean_object* v_k_3596_; lean_object* v_v_3597_; lean_object* v_l_3598_; lean_object* v_r_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_k_3596_ = lean_ctor_get(v_x_3595_, 1);
v_v_3597_ = lean_ctor_get(v_x_3595_, 2);
v_l_3598_ = lean_ctor_get(v_x_3595_, 3);
v_r_3599_ = lean_ctor_get(v_x_3595_, 4);
v___x_3600_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_3594_, v_r_3599_);
lean_inc(v_v_3597_);
lean_inc(v_k_3596_);
v___x_3601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3601_, 0, v_k_3596_);
lean_ctor_set(v___x_3601_, 1, v_v_3597_);
v___x_3602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
lean_ctor_set(v___x_3602_, 1, v___x_3600_);
v_init_3594_ = v___x_3602_;
v_x_3595_ = v_l_3598_;
goto _start;
}
else
{
return v_init_3594_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4___boxed(lean_object* v_init_3604_, lean_object* v_x_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_3604_, v_x_3605_);
lean_dec(v_x_3605_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(lean_object* v_x_3607_, lean_object* v_x_3608_, lean_object* v_x_3609_){
_start:
{
if (lean_obj_tag(v_x_3609_) == 0)
{
lean_dec(v_x_3607_);
return v_x_3608_;
}
else
{
lean_object* v_head_3610_; lean_object* v_tail_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3620_; 
v_head_3610_ = lean_ctor_get(v_x_3609_, 0);
v_tail_3611_ = lean_ctor_get(v_x_3609_, 1);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_x_3609_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3613_ = v_x_3609_;
v_isShared_3614_ = v_isSharedCheck_3620_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_tail_3611_);
lean_inc(v_head_3610_);
lean_dec(v_x_3609_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3620_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
lean_inc(v_x_3607_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set_tag(v___x_3613_, 5);
lean_ctor_set(v___x_3613_, 1, v_x_3607_);
lean_ctor_set(v___x_3613_, 0, v_x_3608_);
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_x_3608_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_x_3607_);
v___x_3616_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
lean_object* v___x_3617_; 
v___x_3617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
lean_ctor_set(v___x_3617_, 1, v_head_3610_);
v_x_3608_ = v___x_3617_;
v_x_3609_ = v_tail_3611_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(lean_object* v_x_3621_, lean_object* v_x_3622_){
_start:
{
if (lean_obj_tag(v_x_3621_) == 0)
{
lean_object* v___x_3623_; 
lean_dec(v_x_3622_);
v___x_3623_ = lean_box(0);
return v___x_3623_;
}
else
{
lean_object* v_tail_3624_; 
v_tail_3624_ = lean_ctor_get(v_x_3621_, 1);
if (lean_obj_tag(v_tail_3624_) == 0)
{
lean_object* v_head_3625_; 
lean_dec(v_x_3622_);
v_head_3625_ = lean_ctor_get(v_x_3621_, 0);
lean_inc(v_head_3625_);
lean_dec_ref_known(v_x_3621_, 2);
return v_head_3625_;
}
else
{
lean_object* v_head_3626_; lean_object* v___x_3627_; 
lean_inc(v_tail_3624_);
v_head_3626_ = lean_ctor_get(v_x_3621_, 0);
lean_inc(v_head_3626_);
lean_dec_ref_known(v_x_3621_, 2);
v___x_3627_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(v_x_3622_, v_head_3626_, v_tail_3624_);
return v___x_3627_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__0));
v___x_3631_ = lean_string_length(v___x_3630_);
return v___x_3631_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2);
v___x_3633_ = lean_nat_to_int(v___x_3632_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(lean_object* v_x_3638_){
_start:
{
lean_object* v_fst_3639_; lean_object* v_snd_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3663_; 
v_fst_3639_ = lean_ctor_get(v_x_3638_, 0);
v_snd_3640_ = lean_ctor_get(v_x_3638_, 1);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_x_3638_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3642_ = v_x_3638_;
v_isShared_3643_ = v_isSharedCheck_3663_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_snd_3640_);
lean_inc(v_fst_3639_);
lean_dec(v_x_3638_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3663_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3644_ = l_String_quote(v_fst_3639_);
v___x_3645_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
v___x_3646_ = lean_box(0);
if (v_isShared_3643_ == 0)
{
lean_ctor_set_tag(v___x_3642_, 1);
lean_ctor_set(v___x_3642_, 1, v___x_3646_);
lean_ctor_set(v___x_3642_, 0, v___x_3645_);
v___x_3648_ = v___x_3642_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v___x_3646_);
v___x_3648_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; lean_object* v___x_3661_; 
v___x_3649_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_snd_3640_);
v___x_3650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
lean_ctor_set(v___x_3650_, 1, v___x_3648_);
v___x_3651_ = l_List_reverse___redArg(v___x_3650_);
v___x_3652_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3653_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(v___x_3651_, v___x_3652_);
v___x_3654_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3);
v___x_3655_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__4));
v___x_3656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
lean_ctor_set(v___x_3656_, 1, v___x_3653_);
v___x_3657_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__5));
v___x_3658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3656_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
v___x_3659_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3654_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = 0;
v___x_3661_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3661_, 0, v___x_3659_);
lean_ctor_set_uint8(v___x_3661_, sizeof(void*)*1, v___x_3660_);
return v___x_3661_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(lean_object* v_x_3664_, lean_object* v_x_3665_, lean_object* v_x_3666_){
_start:
{
if (lean_obj_tag(v_x_3666_) == 0)
{
lean_dec(v_x_3664_);
return v_x_3665_;
}
else
{
lean_object* v_head_3667_; lean_object* v_tail_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3678_; 
v_head_3667_ = lean_ctor_get(v_x_3666_, 0);
v_tail_3668_ = lean_ctor_get(v_x_3666_, 1);
v_isSharedCheck_3678_ = !lean_is_exclusive(v_x_3666_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3670_ = v_x_3666_;
v_isShared_3671_ = v_isSharedCheck_3678_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_tail_3668_);
lean_inc(v_head_3667_);
lean_dec(v_x_3666_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3678_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
lean_inc(v_x_3664_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set_tag(v___x_3670_, 5);
lean_ctor_set(v___x_3670_, 1, v_x_3664_);
lean_ctor_set(v___x_3670_, 0, v_x_3665_);
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_x_3665_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v_x_3664_);
v___x_3673_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3667_);
v___x_3675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3673_);
lean_ctor_set(v___x_3675_, 1, v___x_3674_);
v_x_3665_ = v___x_3675_;
v_x_3666_ = v_tail_3668_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(lean_object* v_x_3679_, lean_object* v_x_3680_, lean_object* v_x_3681_){
_start:
{
if (lean_obj_tag(v_x_3681_) == 0)
{
lean_dec(v_x_3679_);
return v_x_3680_;
}
else
{
lean_object* v_head_3682_; lean_object* v_tail_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3693_; 
v_head_3682_ = lean_ctor_get(v_x_3681_, 0);
v_tail_3683_ = lean_ctor_get(v_x_3681_, 1);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_x_3681_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3685_ = v_x_3681_;
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_tail_3683_);
lean_inc(v_head_3682_);
lean_dec(v_x_3681_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
lean_inc(v_x_3679_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set_tag(v___x_3685_, 5);
lean_ctor_set(v___x_3685_, 1, v_x_3679_);
lean_ctor_set(v___x_3685_, 0, v_x_3680_);
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_x_3680_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_x_3679_);
v___x_3688_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3689_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3682_);
v___x_3690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(v_x_3679_, v___x_3690_, v_tail_3683_);
return v___x_3691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(lean_object* v_x_3694_, lean_object* v_x_3695_){
_start:
{
if (lean_obj_tag(v_x_3694_) == 0)
{
lean_object* v___x_3696_; 
lean_dec(v_x_3695_);
v___x_3696_ = lean_box(0);
return v___x_3696_;
}
else
{
lean_object* v_tail_3697_; 
v_tail_3697_ = lean_ctor_get(v_x_3694_, 1);
if (lean_obj_tag(v_tail_3697_) == 0)
{
lean_object* v_head_3698_; lean_object* v___x_3699_; 
lean_dec(v_x_3695_);
v_head_3698_ = lean_ctor_get(v_x_3694_, 0);
lean_inc(v_head_3698_);
lean_dec_ref_known(v_x_3694_, 2);
v___x_3699_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3698_);
return v___x_3699_;
}
else
{
lean_object* v_head_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
lean_inc(v_tail_3697_);
v_head_3700_ = lean_ctor_get(v_x_3694_, 0);
lean_inc(v_head_3700_);
lean_dec_ref_known(v_x_3694_, 2);
v___x_3701_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3700_);
v___x_3702_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(v_x_3695_, v___x_3701_, v_tail_3697_);
return v___x_3702_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_3706_ = lean_string_length(v___x_3705_);
return v___x_3706_;
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1);
v___x_3708_ = lean_nat_to_int(v___x_3707_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(lean_object* v_a_3711_){
_start:
{
if (lean_obj_tag(v_a_3711_) == 0)
{
lean_object* v___x_3712_; 
v___x_3712_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0));
return v___x_3712_;
}
else
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; lean_object* v___x_3722_; 
v___x_3713_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3714_ = l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(v_a_3711_, v___x_3713_);
v___x_3715_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2);
v___x_3716_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__3));
v___x_3717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
lean_ctor_set(v___x_3717_, 1, v___x_3714_);
v___x_3718_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_3719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3717_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3715_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = 0;
v___x_3722_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3722_, 0, v___x_3720_);
lean_ctor_set_uint8(v___x_3722_, sizeof(void*)*1, v___x_3721_);
return v___x_3722_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(lean_object* v_x_3726_, lean_object* v_x_3727_){
_start:
{
if (lean_obj_tag(v_x_3726_) == 0)
{
lean_object* v___x_3728_; 
v___x_3728_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3728_;
}
else
{
lean_object* v_val_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v_val_3729_ = lean_ctor_get(v_x_3726_, 0);
v___x_3730_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3731_ = lean_unsigned_to_nat(1024u);
v___x_3732_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__1));
v___x_3733_ = lean_box(0);
v___x_3734_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v___x_3733_, v_val_3729_);
v___x_3735_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v___x_3734_);
v___x_3736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3732_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = l_Repr_addAppParen(v___x_3736_, v___x_3731_);
v___x_3738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3730_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = l_Repr_addAppParen(v___x_3738_, v_x_3727_);
return v___x_3739_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___boxed(lean_object* v_x_3740_, lean_object* v_x_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_x_3740_, v_x_3741_);
lean_dec(v_x_3741_);
lean_dec(v_x_3740_);
return v_res_3742_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3755_ = lean_unsigned_to_nat(20u);
v___x_3756_ = lean_nat_to_int(v___x_3755_);
return v___x_3756_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3759_ = lean_unsigned_to_nat(19u);
v___x_3760_ = lean_nat_to_int(v___x_3759_);
return v___x_3760_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = lean_unsigned_to_nat(17u);
v___x_3764_ = lean_nat_to_int(v___x_3763_);
return v___x_3764_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = lean_unsigned_to_nat(18u);
v___x_3772_ = lean_nat_to_int(v___x_3771_);
return v___x_3772_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3775_ = lean_unsigned_to_nat(21u);
v___x_3776_ = lean_nat_to_int(v___x_3775_);
return v___x_3776_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__0));
v___x_3779_ = lean_string_length(v___x_3778_);
return v___x_3779_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3780_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__18, &l_Lake_Check_instReprConfig_repr___redArg___closed__18_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18);
v___x_3781_ = lean_nat_to_int(v___x_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___redArg(lean_object* v_x_3786_){
_start:
{
lean_object* v_challenge__module_3787_; lean_object* v_solution__module_3788_; lean_object* v_theorem__names_3789_; lean_object* v_definition__names_3790_; lean_object* v_permitted__axioms_3791_; lean_object* v_enable__nanoda_x3f_3792_; lean_object* v_external__kernels_x3f_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v_challenge__module_3787_ = lean_ctor_get(v_x_3786_, 0);
lean_inc_ref(v_challenge__module_3787_);
v_solution__module_3788_ = lean_ctor_get(v_x_3786_, 1);
lean_inc_ref(v_solution__module_3788_);
v_theorem__names_3789_ = lean_ctor_get(v_x_3786_, 2);
lean_inc_ref(v_theorem__names_3789_);
v_definition__names_3790_ = lean_ctor_get(v_x_3786_, 3);
lean_inc(v_definition__names_3790_);
v_permitted__axioms_3791_ = lean_ctor_get(v_x_3786_, 4);
lean_inc_ref(v_permitted__axioms_3791_);
v_enable__nanoda_x3f_3792_ = lean_ctor_get(v_x_3786_, 5);
lean_inc(v_enable__nanoda_x3f_3792_);
v_external__kernels_x3f_3793_ = lean_ctor_get(v_x_3786_, 6);
lean_inc(v_external__kernels_x3f_3793_);
lean_dec_ref(v_x_3786_);
v___x_3794_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__4));
v___x_3795_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__5));
v___x_3796_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__6, &l_Lake_Check_instReprConfig_repr___redArg___closed__6_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6);
v___x_3797_ = l_String_quote(v_challenge__module_3787_);
v___x_3798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
v___x_3799_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3796_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
v___x_3800_ = 0;
v___x_3801_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3801_, 0, v___x_3799_);
lean_ctor_set_uint8(v___x_3801_, sizeof(void*)*1, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3795_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
v___x_3803_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__2));
v___x_3804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3802_);
lean_ctor_set(v___x_3804_, 1, v___x_3803_);
v___x_3805_ = lean_box(1);
v___x_3806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3804_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__7));
v___x_3808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3806_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
lean_ctor_set(v___x_3809_, 1, v___x_3794_);
v___x_3810_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__8, &l_Lake_Check_instReprConfig_repr___redArg___closed__8_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8);
v___x_3811_ = l_String_quote(v_solution__module_3788_);
v___x_3812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
v___x_3813_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3810_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set_uint8(v___x_3814_, sizeof(void*)*1, v___x_3800_);
v___x_3815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3809_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
lean_ctor_set(v___x_3816_, 1, v___x_3803_);
v___x_3817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
lean_ctor_set(v___x_3817_, 1, v___x_3805_);
v___x_3818_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__9));
v___x_3819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3817_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
v___x_3820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
lean_ctor_set(v___x_3820_, 1, v___x_3794_);
v___x_3821_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__10, &l_Lake_Check_instReprConfig_repr___redArg___closed__10_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10);
v___x_3822_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_theorem__names_3789_);
v___x_3823_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3821_);
lean_ctor_set(v___x_3823_, 1, v___x_3822_);
v___x_3824_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
lean_ctor_set_uint8(v___x_3824_, sizeof(void*)*1, v___x_3800_);
v___x_3825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3820_);
lean_ctor_set(v___x_3825_, 1, v___x_3824_);
v___x_3826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
lean_ctor_set(v___x_3826_, 1, v___x_3803_);
v___x_3827_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
lean_ctor_set(v___x_3827_, 1, v___x_3805_);
v___x_3828_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__11));
v___x_3829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3827_);
lean_ctor_set(v___x_3829_, 1, v___x_3828_);
v___x_3830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
lean_ctor_set(v___x_3830_, 1, v___x_3794_);
v___x_3831_ = lean_unsigned_to_nat(0u);
v___x_3832_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_definition__names_3790_, v___x_3831_);
v___x_3833_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3796_);
lean_ctor_set(v___x_3833_, 1, v___x_3832_);
v___x_3834_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
lean_ctor_set_uint8(v___x_3834_, sizeof(void*)*1, v___x_3800_);
v___x_3835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3830_);
lean_ctor_set(v___x_3835_, 1, v___x_3834_);
v___x_3836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3835_);
lean_ctor_set(v___x_3836_, 1, v___x_3803_);
v___x_3837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3836_);
lean_ctor_set(v___x_3837_, 1, v___x_3805_);
v___x_3838_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__12));
v___x_3839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3837_);
lean_ctor_set(v___x_3839_, 1, v___x_3838_);
v___x_3840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3839_);
lean_ctor_set(v___x_3840_, 1, v___x_3794_);
v___x_3841_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_permitted__axioms_3791_);
v___x_3842_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3796_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v___x_3843_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
lean_ctor_set_uint8(v___x_3843_, sizeof(void*)*1, v___x_3800_);
v___x_3844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3840_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
v___x_3845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
lean_ctor_set(v___x_3845_, 1, v___x_3803_);
v___x_3846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
lean_ctor_set(v___x_3846_, 1, v___x_3805_);
v___x_3847_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__13));
v___x_3848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3846_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3848_);
lean_ctor_set(v___x_3849_, 1, v___x_3794_);
v___x_3850_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__14, &l_Lake_Check_instReprConfig_repr___redArg___closed__14_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14);
v___x_3851_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_enable__nanoda_x3f_3792_, v___x_3831_);
lean_dec(v_enable__nanoda_x3f_3792_);
v___x_3852_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3850_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
v___x_3853_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
lean_ctor_set_uint8(v___x_3853_, sizeof(void*)*1, v___x_3800_);
v___x_3854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3849_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
v___x_3855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
lean_ctor_set(v___x_3855_, 1, v___x_3803_);
v___x_3856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3855_);
lean_ctor_set(v___x_3856_, 1, v___x_3805_);
v___x_3857_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__15));
v___x_3858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3858_);
lean_ctor_set(v___x_3859_, 1, v___x_3794_);
v___x_3860_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__16, &l_Lake_Check_instReprConfig_repr___redArg___closed__16_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16);
v___x_3861_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_external__kernels_x3f_3793_, v___x_3831_);
lean_dec(v_external__kernels_x3f_3793_);
v___x_3862_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3860_);
lean_ctor_set(v___x_3862_, 1, v___x_3861_);
v___x_3863_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
lean_ctor_set_uint8(v___x_3863_, sizeof(void*)*1, v___x_3800_);
v___x_3864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3859_);
lean_ctor_set(v___x_3864_, 1, v___x_3863_);
v___x_3865_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__19, &l_Lake_Check_instReprConfig_repr___redArg___closed__19_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19);
v___x_3866_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__20));
v___x_3867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
lean_ctor_set(v___x_3867_, 1, v___x_3864_);
v___x_3868_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__21));
v___x_3869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3867_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___x_3870_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3865_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
v___x_3871_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3871_, 0, v___x_3870_);
lean_ctor_set_uint8(v___x_3871_, sizeof(void*)*1, v___x_3800_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr(lean_object* v_x_3872_, lean_object* v_prec_3873_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_Lake_Check_instReprConfig_repr___redArg(v_x_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___boxed(lean_object* v_x_3875_, lean_object* v_prec_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lake_Check_instReprConfig_repr(v_x_3875_, v_prec_3876_);
lean_dec(v_prec_3876_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(lean_object* v_a_3878_, lean_object* v_n_3879_){
_start:
{
lean_object* v___x_3880_; 
v___x_3880_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v_a_3878_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___boxed(lean_object* v_a_3881_, lean_object* v_n_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(v_a_3881_, v_n_3882_);
lean_dec(v_n_3882_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(lean_object* v_x_3884_, lean_object* v_x_3885_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_x_3884_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___boxed(lean_object* v_x_3887_, lean_object* v_x_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(v_x_3887_, v_x_3888_);
lean_dec(v_x_3888_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(lean_object* v_s_3892_){
_start:
{
uint32_t v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3894_ = 10;
v___x_3895_ = lean_string_push(v_s_3892_, v___x_3894_);
v___x_3896_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v___x_3895_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0___boxed(lean_object* v_s_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v_s_3897_);
return v_res_3899_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1(void){
_start:
{
uint32_t v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = 2;
v___x_3902_ = lean_box_uint32(v___x_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(lean_object* v_msg_3903_){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3905_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_3906_ = lean_string_append(v___x_3905_, v_msg_3903_);
v___x_3907_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_3906_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3915_; 
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3915_ == 0)
{
lean_object* v_unused_3916_; 
v_unused_3916_ = lean_ctor_get(v___x_3907_, 0);
lean_dec(v_unused_3916_);
v___x_3909_ = v___x_3907_;
v_isShared_3910_ = v_isSharedCheck_3915_;
goto v_resetjp_3908_;
}
else
{
lean_dec(v___x_3907_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3915_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3911_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1;
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3911_);
v___x_3913_ = v___x_3909_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
else
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
v_a_3917_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3907_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3907_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed(lean_object* v_msg_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v_msg_3925_);
lean_dec_ref(v_msg_3925_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(lean_object* v_cmd_3931_, lean_object* v_projectDir_3932_){
_start:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; uint8_t v___x_3936_; 
v___x_3934_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__0));
lean_inc_ref(v_projectDir_3932_);
v___x_3935_ = l_System_FilePath_join(v_projectDir_3932_, v___x_3934_);
v___x_3936_ = l_System_FilePath_pathExists(v___x_3935_);
lean_dec_ref(v___x_3935_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3937_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_3938_ = lean_string_append(v___x_3937_, v_projectDir_3932_);
lean_dec_ref(v_projectDir_3932_);
v___x_3939_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__1));
v___x_3940_ = lean_string_append(v___x_3938_, v___x_3939_);
v___x_3941_ = lean_string_append(v___x_3940_, v_cmd_3931_);
v___x_3942_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__2));
v___x_3943_ = lean_string_append(v___x_3941_, v___x_3942_);
v___x_3944_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3943_);
lean_dec_ref(v___x_3943_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3953_; 
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3947_ = v___x_3944_;
v_isShared_3948_ = v_isSharedCheck_3953_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3944_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3953_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3949_; lean_object* v___x_3951_; 
v___x_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3949_, 0, v_a_3945_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 0, v___x_3949_);
v___x_3951_ = v___x_3947_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3949_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
v_a_3954_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3944_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3944_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
lean_dec_ref(v_projectDir_3932_);
v___x_3962_ = lean_box(0);
v___x_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
return v___x_3963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___boxed(lean_object* v_cmd_3964_, lean_object* v_projectDir_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v_cmd_3964_, v_projectDir_3965_);
lean_dec_ref(v_cmd_3964_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext(lean_object* v_cmd_3976_, lean_object* v_lean_3977_, lean_object* v_lake_3978_, lean_object* v_projectDir_3979_){
_start:
{
uint8_t v___x_3981_; 
v___x_3981_ = l_System_Platform_isLinux;
if (v___x_3981_ == 0)
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
lean_dec_ref(v_projectDir_3979_);
lean_dec_ref(v_lean_3977_);
v___x_3982_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_3983_ = lean_string_append(v___x_3982_, v_cmd_3976_);
v___x_3984_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0));
v___x_3985_ = lean_string_append(v___x_3983_, v___x_3984_);
v___x_3986_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_3985_);
lean_dec_ref(v___x_3985_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3995_; 
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3989_ = v___x_3986_;
v_isShared_3990_ = v_isSharedCheck_3995_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3986_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3995_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3991_; lean_object* v___x_3993_; 
v___x_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3991_, 0, v_a_3987_);
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 0, v___x_3991_);
v___x_3993_ = v___x_3989_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
v_a_3996_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3986_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3986_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
else
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___y_4007_; 
v___x_4004_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1));
v___x_4005_ = lean_io_getenv(v___x_4004_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v___x_4139_; 
v___x_4139_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7));
v___y_4007_ = v___x_4139_;
goto v___jp_4006_;
}
else
{
lean_object* v_val_4140_; 
v_val_4140_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_val_4140_);
lean_dec_ref_known(v___x_4005_, 1);
v___y_4007_ = v_val_4140_;
goto v___jp_4006_;
}
v___jp_4006_:
{
lean_object* v___x_4008_; lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4138_; 
lean_inc_ref(v___y_4007_);
v___x_4008_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___y_4007_);
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4011_ = v___x_4008_;
v_isShared_4012_ = v_isSharedCheck_4138_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_4008_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4138_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
if (lean_obj_tag(v_a_4009_) == 1)
{
lean_object* v_val_4013_; lean_object* v_sysroot_4014_; lean_object* v_binDir_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4116_; 
lean_del_object(v___x_4011_);
lean_dec_ref(v___y_4007_);
v_val_4013_ = lean_ctor_get(v_a_4009_, 0);
lean_inc(v_val_4013_);
lean_dec_ref_known(v_a_4009_, 1);
v_sysroot_4014_ = lean_ctor_get(v_lean_3977_, 0);
lean_inc_ref(v_sysroot_4014_);
v_binDir_4015_ = lean_ctor_get(v_lean_3977_, 6);
lean_inc_ref(v_binDir_4015_);
lean_dec_ref(v_lean_3977_);
v___x_4016_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2));
v___x_4017_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4016_);
v_a_4018_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4020_ = v___x_4017_;
v_isShared_4021_ = v_isSharedCheck_4116_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4017_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4116_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
if (lean_obj_tag(v_a_4018_) == 1)
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4091_; 
lean_dec_ref_known(v_a_4018_, 1);
lean_del_object(v___x_4020_);
v___x_4022_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__4));
v___x_4023_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4022_);
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4026_ = v___x_4023_;
v_isShared_4027_ = v_isSharedCheck_4091_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4023_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4091_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
if (lean_obj_tag(v_a_4024_) == 1)
{
lean_object* v_val_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4066_; 
lean_del_object(v___x_4026_);
v_val_4028_ = lean_ctor_get(v_a_4024_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v_a_4024_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4030_ = v_a_4024_;
v_isShared_4031_ = v_isSharedCheck_4066_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_val_4028_);
lean_dec(v_a_4024_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4066_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4032_; 
v___x_4032_ = lean_io_realpath(v_projectDir_3979_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4057_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4035_ = v___x_4032_;
v_isShared_4036_ = v_isSharedCheck_4057_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4057_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v_home_4037_; lean_object* v_lake_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4052_; 
v_home_4037_ = lean_ctor_get(v_lake_3978_, 0);
v_lake_4038_ = lean_ctor_get(v_lake_3978_, 5);
v___x_4039_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3));
lean_inc_ref(v_binDir_4015_);
v___x_4040_ = l_System_FilePath_join(v_binDir_4015_, v___x_4039_);
v___x_4041_ = l_System_FilePath_exeExtension;
v___x_4042_ = l_System_FilePath_addExtension(v___x_4040_, v___x_4041_);
v___x_4043_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4));
v___x_4044_ = l_System_FilePath_join(v_binDir_4015_, v___x_4043_);
v___x_4045_ = l_System_FilePath_addExtension(v___x_4044_, v___x_4041_);
v___x_4046_ = lean_box(0);
v___x_4047_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_4048_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
v___x_4049_ = lean_box(1);
lean_inc_ref(v_home_4037_);
lean_inc_ref(v_lake_4038_);
v___x_4050_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_4050_, 0, v_a_4033_);
lean_ctor_set(v___x_4050_, 1, v___x_4046_);
lean_ctor_set(v___x_4050_, 2, v___x_4046_);
lean_ctor_set(v___x_4050_, 3, v___x_4047_);
lean_ctor_set(v___x_4050_, 4, v___x_4047_);
lean_ctor_set(v___x_4050_, 5, v___x_4047_);
lean_ctor_set(v___x_4050_, 6, v_sysroot_4014_);
lean_ctor_set(v___x_4050_, 7, v___x_4048_);
lean_ctor_set(v___x_4050_, 8, v___x_4048_);
lean_ctor_set(v___x_4050_, 9, v_val_4013_);
lean_ctor_set(v___x_4050_, 10, v_lake_4038_);
lean_ctor_set(v___x_4050_, 11, v_home_4037_);
lean_ctor_set(v___x_4050_, 12, v___x_4042_);
lean_ctor_set(v___x_4050_, 13, v___x_4045_);
lean_ctor_set(v___x_4050_, 14, v_val_4028_);
lean_ctor_set(v___x_4050_, 15, v___x_4049_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 0, v___x_4050_);
v___x_4052_ = v___x_4030_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4050_);
v___x_4052_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4054_; 
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v___x_4052_);
v___x_4054_ = v___x_4035_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4052_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
lean_del_object(v___x_4030_);
lean_dec(v_val_4028_);
lean_dec_ref(v_binDir_4015_);
lean_dec_ref(v_sysroot_4014_);
lean_dec(v_val_4013_);
v_a_4058_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4032_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4032_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
}
else
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
lean_dec(v_a_4024_);
lean_dec_ref(v_binDir_4015_);
lean_dec_ref(v_sysroot_4014_);
lean_dec(v_val_4013_);
lean_dec_ref(v_projectDir_3979_);
v___x_4067_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4068_ = lean_string_append(v___x_4067_, v_cmd_3976_);
v___x_4069_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5));
v___x_4070_ = lean_string_append(v___x_4068_, v___x_4069_);
v___x_4071_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4070_);
lean_dec_ref(v___x_4070_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4082_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4074_ = v___x_4071_;
v_isShared_4075_ = v_isSharedCheck_4082_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v___x_4071_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4082_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4077_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 0, v_a_4072_);
v___x_4077_ = v___x_4026_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4072_);
v___x_4077_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
lean_object* v___x_4079_; 
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 0, v___x_4077_);
v___x_4079_ = v___x_4074_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_del_object(v___x_4026_);
v_a_4083_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4071_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4071_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
}
}
else
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
lean_dec(v_a_4018_);
lean_dec_ref(v_binDir_4015_);
lean_dec_ref(v_sysroot_4014_);
lean_dec(v_val_4013_);
lean_dec_ref(v_projectDir_3979_);
v___x_4092_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4093_ = lean_string_append(v___x_4092_, v_cmd_3976_);
v___x_4094_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6));
v___x_4095_ = lean_string_append(v___x_4093_, v___x_4094_);
v___x_4096_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4095_);
lean_dec_ref(v___x_4095_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4107_; 
v_a_4097_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4099_ = v___x_4096_;
v_isShared_4100_ = v_isSharedCheck_4107_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4096_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4107_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 0, v_a_4097_);
v___x_4102_ = v___x_4020_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
lean_object* v___x_4104_; 
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 0, v___x_4102_);
v___x_4104_ = v___x_4099_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4102_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_del_object(v___x_4020_);
v_a_4108_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4096_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4096_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
}
}
else
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
lean_dec(v_a_4009_);
lean_dec_ref(v_projectDir_3979_);
lean_dec_ref(v_lean_3977_);
v___x_4117_ = l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError(v_cmd_3976_, v___y_4007_);
lean_dec_ref(v___y_4007_);
v___x_4118_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4117_);
lean_dec_ref(v___x_4117_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4129_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4121_ = v___x_4118_;
v_isShared_4122_ = v_isSharedCheck_4129_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4118_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4129_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v_a_4119_);
v___x_4124_ = v___x_4011_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
lean_object* v___x_4126_; 
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 0, v___x_4124_);
v___x_4126_ = v___x_4121_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4124_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
}
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_del_object(v___x_4011_);
v_a_4130_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4118_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4118_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___boxed(lean_object* v_cmd_4141_, lean_object* v_lean_4142_, lean_object* v_lake_4143_, lean_object* v_projectDir_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v_cmd_4141_, v_lean_4142_, v_lake_4143_, v_projectDir_4144_);
lean_dec_ref(v_lake_4143_);
lean_dec_ref(v_cmd_4141_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(lean_object* v_init_4153_, lean_object* v_x_4154_){
_start:
{
lean_object* v_d_4157_; 
if (lean_obj_tag(v_x_4154_) == 0)
{
lean_object* v_k_4160_; lean_object* v_v_4161_; lean_object* v_l_4162_; lean_object* v_r_4163_; lean_object* v___x_4164_; 
v_k_4160_ = lean_ctor_get(v_x_4154_, 1);
v_v_4161_ = lean_ctor_get(v_x_4154_, 2);
v_l_4162_ = lean_ctor_get(v_x_4154_, 3);
v_r_4163_ = lean_ctor_get(v_x_4154_, 4);
v___x_4164_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_4153_, v_l_4162_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4164_, 1);
if (lean_obj_tag(v_a_4165_) == 0)
{
lean_object* v_a_4166_; 
v_a_4166_ = lean_ctor_get(v_a_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v_a_4165_, 1);
v_d_4157_ = v_a_4166_;
goto v___jp_4156_;
}
else
{
lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4206_; 
v_isSharedCheck_4206_ = !lean_is_exclusive(v_a_4165_);
if (v_isSharedCheck_4206_ == 0)
{
lean_object* v_unused_4207_; 
v_unused_4207_ = lean_ctor_get(v_a_4165_, 0);
lean_dec(v_unused_4207_);
v___x_4168_ = v_a_4165_;
v_isShared_4169_ = v_isSharedCheck_4206_;
goto v_resetjp_4167_;
}
else
{
lean_dec(v_a_4165_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4206_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4205_; 
v___x_4170_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
v___x_4171_ = lean_unsigned_to_nat(0u);
v___x_4172_ = lean_array_get_borrowed(v___x_4170_, v_v_4161_, v___x_4171_);
lean_inc(v___x_4172_);
v___x_4173_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4172_);
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4176_ = v___x_4173_;
v_isShared_4177_ = v_isSharedCheck_4205_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4173_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4205_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4178_; 
v___x_4178_ = lean_box(0);
if (lean_obj_tag(v_a_4174_) == 0)
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4179_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_4180_ = lean_string_append(v___x_4179_, v_k_4160_);
v___x_4181_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1));
v___x_4182_ = lean_string_append(v___x_4180_, v___x_4181_);
v___x_4183_ = lean_string_append(v___x_4182_, v___x_4172_);
v___x_4184_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2));
v___x_4185_ = lean_string_append(v___x_4183_, v___x_4184_);
v___x_4186_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4185_);
lean_dec_ref(v___x_4185_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v___x_4189_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4187_);
lean_dec_ref_known(v___x_4186_, 1);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v_a_4187_);
v___x_4189_ = v___x_4176_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4187_);
v___x_4189_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
lean_object* v___x_4191_; 
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v___x_4189_);
v___x_4191_ = v___x_4168_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4189_);
v___x_4191_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4192_; 
v___x_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
lean_ctor_set(v___x_4192_, 1, v___x_4178_);
v_d_4157_ = v___x_4192_;
goto v___jp_4156_;
}
}
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
lean_del_object(v___x_4176_);
lean_del_object(v___x_4168_);
v_a_4195_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4186_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4186_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
else
{
lean_object* v___x_4203_; 
lean_dec_ref_known(v_a_4174_, 1);
lean_del_object(v___x_4176_);
lean_del_object(v___x_4168_);
v___x_4203_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v_init_4153_ = v___x_4203_;
v_x_4154_ = v_r_4163_;
goto _start;
}
}
}
}
}
else
{
return v___x_4164_;
}
}
else
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4208_, 0, v_init_4153_);
v___x_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
return v___x_4209_;
}
v___jp_4156_:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4158_, 0, v_d_4157_);
v___x_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
return v___x_4159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___boxed(lean_object* v_init_4210_, lean_object* v_x_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_4210_, v_x_4211_);
lean_dec(v_x_4211_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(lean_object* v_init_4215_, lean_object* v_x_4216_){
_start:
{
lean_object* v_d_4219_; 
if (lean_obj_tag(v_x_4216_) == 0)
{
lean_object* v_k_4222_; lean_object* v_v_4223_; lean_object* v_l_4224_; lean_object* v_r_4225_; lean_object* v___x_4226_; 
v_k_4222_ = lean_ctor_get(v_x_4216_, 1);
v_v_4223_ = lean_ctor_get(v_x_4216_, 2);
v_l_4224_ = lean_ctor_get(v_x_4216_, 3);
v_r_4225_ = lean_ctor_get(v_x_4216_, 4);
v___x_4226_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(v_init_4215_, v_l_4224_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4264_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4229_ = v___x_4226_;
v_isShared_4230_ = v_isSharedCheck_4264_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4226_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4264_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
if (lean_obj_tag(v_a_4227_) == 0)
{
lean_object* v_a_4231_; 
lean_del_object(v___x_4229_);
v_a_4231_ = lean_ctor_get(v_a_4227_, 0);
lean_inc(v_a_4231_);
lean_dec_ref_known(v_a_4227_, 1);
v_d_4219_ = v_a_4231_;
goto v___jp_4218_;
}
else
{
lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4262_; 
v_isSharedCheck_4262_ = !lean_is_exclusive(v_a_4227_);
if (v_isSharedCheck_4262_ == 0)
{
lean_object* v_unused_4263_; 
v_unused_4263_ = lean_ctor_get(v_a_4227_, 0);
lean_dec(v_unused_4263_);
v___x_4233_ = v_a_4227_;
v_isShared_4234_ = v_isSharedCheck_4262_;
goto v_resetjp_4232_;
}
else
{
lean_dec(v_a_4227_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4262_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; uint8_t v___x_4238_; 
v___x_4235_ = lean_box(0);
v___x_4236_ = lean_array_get_size(v_v_4223_);
v___x_4237_ = lean_unsigned_to_nat(0u);
v___x_4238_ = lean_nat_dec_eq(v___x_4236_, v___x_4237_);
if (v___x_4238_ == 0)
{
lean_object* v___x_4239_; 
lean_del_object(v___x_4233_);
lean_del_object(v___x_4229_);
v___x_4239_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v_init_4215_ = v___x_4239_;
v_x_4216_ = v_r_4225_;
goto _start;
}
else
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4241_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_4242_ = lean_string_append(v___x_4241_, v_k_4222_);
v___x_4243_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___closed__0));
v___x_4244_ = lean_string_append(v___x_4242_, v___x_4243_);
v___x_4245_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4244_);
lean_dec_ref(v___x_4244_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v_a_4246_; lean_object* v___x_4248_; 
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4246_);
lean_dec_ref_known(v___x_4245_, 1);
if (v_isShared_4234_ == 0)
{
lean_ctor_set_tag(v___x_4233_, 0);
lean_ctor_set(v___x_4233_, 0, v_a_4246_);
v___x_4248_ = v___x_4233_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4246_);
v___x_4248_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
lean_object* v___x_4250_; 
if (v_isShared_4230_ == 0)
{
lean_ctor_set_tag(v___x_4229_, 1);
lean_ctor_set(v___x_4229_, 0, v___x_4248_);
v___x_4250_ = v___x_4229_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
lean_object* v___x_4251_; 
v___x_4251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4250_);
lean_ctor_set(v___x_4251_, 1, v___x_4235_);
v_d_4219_ = v___x_4251_;
goto v___jp_4218_;
}
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_del_object(v___x_4233_);
lean_del_object(v___x_4229_);
v_a_4254_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4245_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4245_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
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
return v___x_4226_;
}
}
else
{
lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4265_, 0, v_init_4215_);
v___x_4266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4265_);
return v___x_4266_;
}
v___jp_4218_:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4220_, 0, v_d_4219_);
v___x_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4220_);
return v___x_4221_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___boxed(lean_object* v_init_4267_, lean_object* v_x_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(v_init_4267_, v_x_4268_);
lean_dec(v_x_4268_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(lean_object* v_k_4271_, lean_object* v_v_4272_, lean_object* v_t_4273_){
_start:
{
if (lean_obj_tag(v_t_4273_) == 0)
{
lean_object* v_size_4274_; lean_object* v_k_4275_; lean_object* v_v_4276_; lean_object* v_l_4277_; lean_object* v_r_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4558_; 
v_size_4274_ = lean_ctor_get(v_t_4273_, 0);
v_k_4275_ = lean_ctor_get(v_t_4273_, 1);
v_v_4276_ = lean_ctor_get(v_t_4273_, 2);
v_l_4277_ = lean_ctor_get(v_t_4273_, 3);
v_r_4278_ = lean_ctor_get(v_t_4273_, 4);
v_isSharedCheck_4558_ = !lean_is_exclusive(v_t_4273_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4280_ = v_t_4273_;
v_isShared_4281_ = v_isSharedCheck_4558_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_r_4278_);
lean_inc(v_l_4277_);
lean_inc(v_v_4276_);
lean_inc(v_k_4275_);
lean_inc(v_size_4274_);
lean_dec(v_t_4273_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4558_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
uint8_t v___x_4282_; 
v___x_4282_ = lean_string_compare(v_k_4271_, v_k_4275_);
switch(v___x_4282_)
{
case 0:
{
lean_object* v_impl_4283_; lean_object* v___x_4284_; 
lean_dec(v_size_4274_);
v_impl_4283_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(v_k_4271_, v_v_4272_, v_l_4277_);
v___x_4284_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4278_) == 0)
{
lean_object* v_size_4285_; lean_object* v_size_4286_; lean_object* v_k_4287_; lean_object* v_v_4288_; lean_object* v_l_4289_; lean_object* v_r_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; uint8_t v___x_4293_; 
v_size_4285_ = lean_ctor_get(v_r_4278_, 0);
v_size_4286_ = lean_ctor_get(v_impl_4283_, 0);
lean_inc(v_size_4286_);
v_k_4287_ = lean_ctor_get(v_impl_4283_, 1);
lean_inc(v_k_4287_);
v_v_4288_ = lean_ctor_get(v_impl_4283_, 2);
lean_inc(v_v_4288_);
v_l_4289_ = lean_ctor_get(v_impl_4283_, 3);
lean_inc(v_l_4289_);
v_r_4290_ = lean_ctor_get(v_impl_4283_, 4);
lean_inc(v_r_4290_);
v___x_4291_ = lean_unsigned_to_nat(3u);
v___x_4292_ = lean_nat_mul(v___x_4291_, v_size_4285_);
v___x_4293_ = lean_nat_dec_lt(v___x_4292_, v_size_4286_);
lean_dec(v___x_4292_);
if (v___x_4293_ == 0)
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4297_; 
lean_dec(v_r_4290_);
lean_dec(v_l_4289_);
lean_dec(v_v_4288_);
lean_dec(v_k_4287_);
v___x_4294_ = lean_nat_add(v___x_4284_, v_size_4286_);
lean_dec(v_size_4286_);
v___x_4295_ = lean_nat_add(v___x_4294_, v_size_4285_);
lean_dec(v___x_4294_);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 3, v_impl_4283_);
lean_ctor_set(v___x_4280_, 0, v___x_4295_);
v___x_4297_ = v___x_4280_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4295_);
lean_ctor_set(v_reuseFailAlloc_4298_, 1, v_k_4275_);
lean_ctor_set(v_reuseFailAlloc_4298_, 2, v_v_4276_);
lean_ctor_set(v_reuseFailAlloc_4298_, 3, v_impl_4283_);
lean_ctor_set(v_reuseFailAlloc_4298_, 4, v_r_4278_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
else
{
lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4364_; 
v_isSharedCheck_4364_ = !lean_is_exclusive(v_impl_4283_);
if (v_isSharedCheck_4364_ == 0)
{
lean_object* v_unused_4365_; lean_object* v_unused_4366_; lean_object* v_unused_4367_; lean_object* v_unused_4368_; lean_object* v_unused_4369_; 
v_unused_4365_ = lean_ctor_get(v_impl_4283_, 4);
lean_dec(v_unused_4365_);
v_unused_4366_ = lean_ctor_get(v_impl_4283_, 3);
lean_dec(v_unused_4366_);
v_unused_4367_ = lean_ctor_get(v_impl_4283_, 2);
lean_dec(v_unused_4367_);
v_unused_4368_ = lean_ctor_get(v_impl_4283_, 1);
lean_dec(v_unused_4368_);
v_unused_4369_ = lean_ctor_get(v_impl_4283_, 0);
lean_dec(v_unused_4369_);
v___x_4300_ = v_impl_4283_;
v_isShared_4301_ = v_isSharedCheck_4364_;
goto v_resetjp_4299_;
}
else
{
lean_dec(v_impl_4283_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4364_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v_size_4302_; lean_object* v_size_4303_; lean_object* v_k_4304_; lean_object* v_v_4305_; lean_object* v_l_4306_; lean_object* v_r_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; uint8_t v___x_4310_; 
v_size_4302_ = lean_ctor_get(v_l_4289_, 0);
v_size_4303_ = lean_ctor_get(v_r_4290_, 0);
v_k_4304_ = lean_ctor_get(v_r_4290_, 1);
v_v_4305_ = lean_ctor_get(v_r_4290_, 2);
v_l_4306_ = lean_ctor_get(v_r_4290_, 3);
v_r_4307_ = lean_ctor_get(v_r_4290_, 4);
v___x_4308_ = lean_unsigned_to_nat(2u);
v___x_4309_ = lean_nat_mul(v___x_4308_, v_size_4302_);
v___x_4310_ = lean_nat_dec_lt(v_size_4303_, v___x_4309_);
lean_dec(v___x_4309_);
if (v___x_4310_ == 0)
{
lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4339_; 
lean_inc(v_r_4307_);
lean_inc(v_l_4306_);
lean_inc(v_v_4305_);
lean_inc(v_k_4304_);
v_isSharedCheck_4339_ = !lean_is_exclusive(v_r_4290_);
if (v_isSharedCheck_4339_ == 0)
{
lean_object* v_unused_4340_; lean_object* v_unused_4341_; lean_object* v_unused_4342_; lean_object* v_unused_4343_; lean_object* v_unused_4344_; 
v_unused_4340_ = lean_ctor_get(v_r_4290_, 4);
lean_dec(v_unused_4340_);
v_unused_4341_ = lean_ctor_get(v_r_4290_, 3);
lean_dec(v_unused_4341_);
v_unused_4342_ = lean_ctor_get(v_r_4290_, 2);
lean_dec(v_unused_4342_);
v_unused_4343_ = lean_ctor_get(v_r_4290_, 1);
lean_dec(v_unused_4343_);
v_unused_4344_ = lean_ctor_get(v_r_4290_, 0);
lean_dec(v_unused_4344_);
v___x_4312_ = v_r_4290_;
v_isShared_4313_ = v_isSharedCheck_4339_;
goto v_resetjp_4311_;
}
else
{
lean_dec(v_r_4290_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4339_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___x_4327_; lean_object* v___y_4329_; 
v___x_4314_ = lean_nat_add(v___x_4284_, v_size_4286_);
lean_dec(v_size_4286_);
v___x_4315_ = lean_nat_add(v___x_4314_, v_size_4285_);
lean_dec(v___x_4314_);
v___x_4327_ = lean_nat_add(v___x_4284_, v_size_4302_);
if (lean_obj_tag(v_l_4306_) == 0)
{
lean_object* v_size_4337_; 
v_size_4337_ = lean_ctor_get(v_l_4306_, 0);
lean_inc(v_size_4337_);
v___y_4329_ = v_size_4337_;
goto v___jp_4328_;
}
else
{
lean_object* v___x_4338_; 
v___x_4338_ = lean_unsigned_to_nat(0u);
v___y_4329_ = v___x_4338_;
goto v___jp_4328_;
}
v___jp_4316_:
{
lean_object* v___x_4320_; lean_object* v___x_4322_; 
v___x_4320_ = lean_nat_add(v___y_4318_, v___y_4319_);
lean_dec(v___y_4319_);
lean_dec(v___y_4318_);
if (v_isShared_4313_ == 0)
{
lean_ctor_set(v___x_4312_, 4, v_r_4278_);
lean_ctor_set(v___x_4312_, 3, v_r_4307_);
lean_ctor_set(v___x_4312_, 2, v_v_4276_);
lean_ctor_set(v___x_4312_, 1, v_k_4275_);
lean_ctor_set(v___x_4312_, 0, v___x_4320_);
v___x_4322_ = v___x_4312_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v___x_4320_);
lean_ctor_set(v_reuseFailAlloc_4326_, 1, v_k_4275_);
lean_ctor_set(v_reuseFailAlloc_4326_, 2, v_v_4276_);
lean_ctor_set(v_reuseFailAlloc_4326_, 3, v_r_4307_);
lean_ctor_set(v_reuseFailAlloc_4326_, 4, v_r_4278_);
v___x_4322_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
lean_object* v___x_4324_; 
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 4, v___x_4322_);
lean_ctor_set(v___x_4300_, 3, v___y_4317_);
lean_ctor_set(v___x_4300_, 2, v_v_4305_);
lean_ctor_set(v___x_4300_, 1, v_k_4304_);
lean_ctor_set(v___x_4300_, 0, v___x_4315_);
v___x_4324_ = v___x_4300_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4315_);
lean_ctor_set(v_reuseFailAlloc_4325_, 1, v_k_4304_);
lean_ctor_set(v_reuseFailAlloc_4325_, 2, v_v_4305_);
lean_ctor_set(v_reuseFailAlloc_4325_, 3, v___y_4317_);
lean_ctor_set(v_reuseFailAlloc_4325_, 4, v___x_4322_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
v___jp_4328_:
{
lean_object* v___x_4330_; lean_object* v___x_4332_; 
v___x_4330_ = lean_nat_add(v___x_4327_, v___y_4329_);
lean_dec(v___y_4329_);
lean_dec(v___x_4327_);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 4, v_l_4306_);
lean_ctor_set(v___x_4280_, 3, v_l_4289_);
lean_ctor_set(v___x_4280_, 2, v_v_4288_);
lean_ctor_set(v___x_4280_, 1, v_k_4287_);
lean_ctor_set(v___x_4280_, 0, v___x_4330_);
v___x_4332_ = v___x_4280_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4330_);
lean_ctor_set(v_reuseFailAlloc_4336_, 1, v_k_4287_);
lean_ctor_set(v_reuseFailAlloc_4336_, 2, v_v_4288_);
lean_ctor_set(v_reuseFailAlloc_4336_, 3, v_l_4289_);
lean_ctor_set(v_reuseFailAlloc_4336_, 4, v_l_4306_);
v___x_4332_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
lean_object* v___x_4333_; 
v___x_4333_ = lean_nat_add(v___x_4284_, v_size_4285_);
if (lean_obj_tag(v_r_4307_) == 0)
{
lean_object* v_size_4334_; 
v_size_4334_ = lean_ctor_get(v_r_4307_, 0);
lean_inc(v_size_4334_);
v___y_4317_ = v___x_4332_;
v___y_4318_ = v___x_4333_;
v___y_4319_ = v_size_4334_;
goto v___jp_4316_;
}
else
{
lean_object* v___x_4335_; 
v___x_4335_ = lean_unsigned_to_nat(0u);
v___y_4317_ = v___x_4332_;
v___y_4318_ = v___x_4333_;
v___y_4319_ = v___x_4335_;
goto v___jp_4316_;
}
}
}
}
}
else
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4350_; 
lean_del_object(v___x_4280_);
v___x_4345_ = lean_nat_add(v___x_4284_, v_size_4286_);
lean_dec(v_size_4286_);
v___x_4346_ = lean_nat_add(v___x_4345_, v_size_4285_);
lean_dec(v___x_4345_);
v___x_4347_ = lean_nat_add(v___x_4284_, v_size_4285_);
v___x_4348_ = lean_nat_add(v___x_4347_, v_size_4303_);
lean_dec(v___x_4347_);
lean_inc_ref(v_r_4278_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 4, v_r_4278_);
lean_ctor_set(v___x_4300_, 3, v_r_4290_);
lean_ctor_set(v___x_4300_, 2, v_v_4276_);
lean_ctor_set(v___x_4300_, 1, v_k_4275_);
lean_ctor_set(v___x_4300_, 0, v___x_4348_);
v___x_4350_ = v___x_4300_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4348_);
lean_ctor_set(v_reuseFailAlloc_4363_, 1, v_k_4275_);
lean_ctor_set(v_reuseFailAlloc_4363_, 2, v_v_4276_);
lean_ctor_set(v_reuseFailAlloc_4363_, 3, v_r_4290_);
lean_ctor_set(v_reuseFailAlloc_4363_, 4, v_r_4278_);
v___x_4350_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
v_isSharedCheck_4357_ = !lean_is_exclusive(v_r_4278_);
if (v_isSharedCheck_4357_ == 0)
{
lean_object* v_unused_4358_; lean_object* v_unused_4359_; lean_object* v_unused_4360_; lean_object* v_unused_4361_; lean_object* v_unused_4362_; 
v_unused_4358_ = lean_ctor_get(v_r_4278_, 4);
lean_dec(v_unused_4358_);
v_unused_4359_ = lean_ctor_get(v_r_4278_, 3);
lean_dec(v_unused_4359_);
v_unused_4360_ = lean_ctor_get(v_r_4278_, 2);
lean_dec(v_unused_4360_);
v_unused_4361_ = lean_ctor_get(v_r_4278_, 1);
lean_dec(v_unused_4361_);
v_unused_4362_ = lean_ctor_get(v_r_4278_, 0);
lean_dec(v_unused_4362_);
v___x_4352_ = v_r_4278_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_dec(v_r_4278_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 4, v___x_4350_);
lean_ctor_set(v___x_4352_, 3, v_l_4289_);
lean_ctor_set(v___x_4352_, 2, v_v_4288_);
lean_ctor_set(v___x_4352_, 1, v_k_4287_);
lean_ctor_set(v___x_4352_, 0, v___x_4346_);
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v___x_4346_);
lean_ctor_set(v_reuseFailAlloc_4356_, 1, v_k_4287_);
lean_ctor_set(v_reuseFailAlloc_4356_, 2, v_v_4288_);
lean_ctor_set(v_reuseFailAlloc_4356_, 3, v_l_4289_);
lean_ctor_set(v_reuseFailAlloc_4356_, 4, v___x_4350_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4370_; 
v_l_4370_ = lean_ctor_get(v_impl_4283_, 3);
lean_inc(v_l_4370_);
if (lean_obj_tag(v_l_4370_) == 0)
{
lean_object* v_r_4371_; lean_object* v_k_4372_; lean_object* v_v_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4384_; 
v_r_4371_ = lean_ctor_get(v_impl_4283_, 4);
v_k_4372_ = lean_ctor_get(v_impl_4283_, 1);
v_v_4373_ = lean_ctor_get(v_impl_4283_, 2);
v_isSharedCheck_4384_ = !lean_is_exclusive(v_impl_4283_);
if (v_isSharedCheck_4384_ == 0)
{
lean_object* v_unused_4385_; lean_object* v_unused_4386_; 
v_unused_4385_ = lean_ctor_get(v_impl_4283_, 3);
lean_dec(v_unused_4385_);
v_unused_4386_ = lean_ctor_get(v_impl_4283_, 0);
lean_dec(v_unused_4386_);
v___x_4375_ = v_impl_4283_;
v_isShared_4376_ = v_isSharedCheck_4384_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_r_4371_);
lean_inc(v_v_4373_);
lean_inc(v_k_4372_);
lean_dec(v_impl_4283_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4384_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4377_; lean_object* v___x_4379_; 
v___x_4377_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4371_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 3, v_r_4371_);
lean_ctor_set(v___x_4375_, 2, v_v_4276_);
lean_ctor_set(v___x_4375_, 1, v_k_4275_);
lean_ctor_set(v___x_4375_, 0, v___x_4284_);
v___x_4379_ = v___x_4375_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4284_);
lean_ctor_set(v_reuseFailAlloc_4383_, 1, v_k_4275_);
lean_ctor_set(v_reuseFailAlloc_4383_, 2, v_v_4276_);
lean_ctor_set(v_reuseFailAlloc_4383_, 3, v_r_4371_);
lean_ctor_set(v_reuseFailAlloc_4383_, 4, v_r_4371_);
v___x_4379_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
lean_object* v___x_4381_; 
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 4, v___x_4379_);
lean_ctor_set(v___x_4280_, 3, v_l_4370_);
lean_ctor_set(v___x_4280_, 2, v_v_4373_);
lean_ctor_set(v___x_4280_, 1, v_k_4372_);
lean_ctor_set(v___x_4280_, 0, v___x_4377_);
v___x_4381_ = v___x_4280_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4377_);
lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_k_4372_);
lean_ctor_set(v_reuseFailAlloc_4382_, 2, v_v_4373_);
lean_ctor_set(v_reuseFailAlloc_4382_, 3, v_l_4370_);
lean_ctor_set(v_reuseFailAlloc_4382_, 4, v___x_4379_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
else
{
lean_object* v_r_4387_; 
v_r_4387_ = lean_ctor_get(v_impl_4283_, 4);
lean_inc(v_r_4387_);
if (lean_obj_tag(v_r_4387_) == 0)
{
lean_object* v_k_4388_; lean_object* v_v_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4412_; 
v_k_4388_ = lean_ctor_get(v_impl_4283_, 1);
v_v_4389_ = lean_ctor_get(v_impl_4283_, 2);
v_isSharedCheck_4412_ = !lean_is_exclusive(v_impl_4283_);
if (v_isSharedCheck_4412_ == 0)
{
lean_object* v_unused_4413_; lean_object* v_unused_4414_; lean_object* v_unused_4415_; 
v_unused_4413_ = lean_ctor_get(v_impl_4283_, 4);
lean_dec(v_unused_4413_);
v_unused_4414_ = lean_ctor_get(v_impl_4283_, 3);
lean_dec(v_unused_4414_);
v_unused_4415_ = lean_ctor_get(v_impl_4283_, 0);
lean_dec(v_unused_4415_);
v___x_4391_ = v_impl_4283_;
v_isShared_4392_ = v_isSharedCheck_4412_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_v_4389_);
lean_inc(v_k_4388_);
lean_dec(v_impl_4283_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4412_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v_k_4393_; lean_object* v_v_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4408_; 
v_k_4393_ = lean_ctor_get(v_r_4387_, 1);
v_v_4394_ = lean_ctor_get(v_r_4387_, 2);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_r_4387_);
if (v_isSharedCheck_4408_ == 0)
{
lean_object* v_unused_4409_; lean_object* v_unused_4410_; lean_object* v_unused_4411_; 
v_unused_4409_ = lean_ctor_get(v_r_4387_, 4);
lean_dec(v_unused_4409_);
v_unused_4410_ = lean_ctor_get(v_r_4387_, 3);
lean_dec(v_unused_4410_);
v_unused_4411_ = lean_ctor_get(v_r_4387_, 0);
lean_dec(v_unused_4411_);
v___x_4396_ = v_r_4387_;
v_isShared_4397_ = v_isSharedCheck_4408_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_v_4394_);
lean_inc(v_k_4393_);
lean_dec(v_r_4387_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4408_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4398_; lean_object* v___x_4400_; 
v___x_4398_ = lean_unsigned_to_nat(3u);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 4, v_l_4370_);
lean_ctor_set(v___x_4396_, 3, v_l_4370_);
lean_ctor_set(v___x_4396_, 2, v_v_4389_);
lean_ctor_set(v___x_4396_, 1, v_k_4388_);
lean_ctor_set(v___x_4396_, 0, v___x_4284_);
v___x_4400_ = v___x_4396_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4284_);
lean_ctor_set(v_reuseFailAlloc_4407_, 1, v_k_4388_);
lean_ctor_set(v_reuseFailAlloc_4407_, 2, v_v_4389_);
lean_ctor_set(v_reuseFailAlloc_4407_, 3, v_l_4370_);
lean_ctor_set(v_reuseFailAlloc_4407_, 4, v_l_4370_);
v___x_4400_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
lean_object* v___x_4402_; 
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 4, v_l_4370_);
lean_ctor_set(v___x_4391_, 2, v_v_4276_);
lean_ctor_set(v___x_4391_, 1, v_k_4275_);
lean_ctor_set(v___x_4391_, 0, v___x_4284_);
v___x_4402_ = v___x_4391_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4284_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v_k_4275_);
lean_ctor_set(v_reuseFailAlloc_4406_, 2, v_v_4276_);
lean_ctor_set(v_reuseFailAlloc_4406_, 3, v_l_4370_);
lean_ctor_set(v_reuseFailAlloc_4406_, 4, v_l_4370_);
v___x_4402_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
lean_object* v___x_4404_; 
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 4, v___x_4402_);
lean_ctor_set(v___x_4280_, 3, v___x_4400_);
lean_ctor_set(v___x_4280_, 2, v_v_4394_);
lean_ctor_set(v___x_4280_, 1, v_k_4393_);
lean_ctor_set(v___x_4280_, 0, v___x_4398_);
v___x_4404_ = v___x_4280_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4398_);
lean_ctor_set(v_reuseFailAlloc_4405_, 1, v_k_4393_);
lean_ctor_set(v_reuseFailAlloc_4405_, 2, v_v_4394_);
lean_ctor_set(v_reuseFailAlloc_4405_, 3, v___x_4400_);
lean_ctor_set(v_reuseFailAlloc_4405_, 4, v___x_4402_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
}
}
else
{
lean_object* v___x_4416_; lean_object* v___x_4418_; 
v___x_4416_ = lean_unsigned_to_nat(2u);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 4, v_r_4387_);
lean_ctor_set(v___x_4280_, 3, v_impl_4283_);
lean_ctor_set(v___x_4280_, 0, v___x_4416_);
v___x_4418_ = v___x_4280_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4416_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v_k_4275_);
lean_ctor_set(v_reuseFailAlloc_4419_, 2, v_v_4276_);
lean_ctor_set(v_reuseFailAlloc_4419_, 3, v_impl_4283_);
lean_ctor_set(v_reuseFailAlloc_4419_, 4, v_r_4387_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4421_; 
lean_dec(v_v_4276_);
lean_dec(v_k_4275_);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 2, v_v_4272_);
lean_ctor_set(v___x_4280_, 1, v_k_4271_);
v___x_4421_ = v___x_4280_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_size_4274_);
lean_ctor_set(v_reuseFailAlloc_4422_, 1, v_k_4271_);
lean_ctor_set(v_reuseFailAlloc_4422_, 2, v_v_4272_);
lean_ctor_set(v_reuseFailAlloc_4422_, 3, v_l_4277_);
lean_ctor_set(v_reuseFailAlloc_4422_, 4, v_r_4278_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
default: 
{
lean_object* v_impl_4423_; lean_object* v___x_4424_; 
lean_dec(v_size_4274_);
v_impl_4423_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(v_k_4271_, v_v_4272_, v_r_4278_);
v___x_4424_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4277_) == 0)
{
lean_object* v_size_4425_; lean_object* v_size_4426_; lean_object* v_k_4427_; lean_object* v_v_4428_; lean_object* v_l_4429_; lean_object* v_r_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; uint8_t v___x_4433_; 
v_size_4425_ = lean_ctor_get(v_l_4277_, 0);
v_size_4426_ = lean_ctor_get(v_impl_4423_, 0);
lean_inc(v_size_4426_);
v_k_4427_ = lean_ctor_get(v_impl_4423_, 1);
lean_inc(v_k_4427_);
v_v_4428_ = lean_ctor_get(v_impl_4423_, 2);
lean_inc(v_v_4428_);
v_l_4429_ = lean_ctor_get(v_impl_4423_, 3);
lean_inc(v_l_4429_);
v_r_4430_ = lean_ctor_get(v_impl_4423_, 4);
lean_inc(v_r_4430_);
v___x_4431_ = lean_unsigned_to_nat(3u);
v___x_4432_ = lean_nat_mul(v___x_4431_, v_size_4425_);
v___x_4433_ = lean_nat_dec_lt(v___x_4432_, v_size_4426_);
lean_dec(v___x_4432_);
if (v___x_4433_ == 0)
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4437_; 
lean_dec(v_r_4430_);
lean_dec(v_l_4429_);
lean_dec(v_v_4428_);
lean_dec(v_k_4427_);
v___x_4434_ = lean_nat_add(v___x_4424_, v_size_4425_);
v___x_4435_ = lean_nat_add(v___x_4434_, v_size_4426_);
lean_dec(v_size_4426_);
lean_dec(v___x_4434_);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 4, v_impl_4423_);
lean_ctor_set(v___x_4280_, 0, v___x_4435_);
v___x_4437_ = v___x_4280_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v___x_4435_);
lean_ctor_set(v_reuseFailAlloc_4438_, 1, v_k_4275_);
lean_ctor_set(v_reuseFailAlloc_4438_, 2, v_v_4276_);
lean_ctor_set(v_reuseFailAlloc_4438_, 3, v_l_4277_);
lean_ctor_set(v_reuseFailAlloc_4438_, 4, v_impl_4423_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
else
{
lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4502_; 
v_isSharedCheck_4502_ = !lean_is_exclusive(v_impl_4423_);
if (v_isSharedCheck_4502_ == 0)
{
lean_object* v_unused_4503_; lean_object* v_unused_4504_; lean_object* v_unused_4505_; lean_object* v_unused_4506_; lean_object* v_unused_4507_; 
v_unused_4503_ = lean_ctor_get(v_impl_4423_, 4);
lean_dec(v_unused_4503_);
v_unused_4504_ = lean_ctor_get(v_impl_4423_, 3);
lean_dec(v_unused_4504_);
v_unused_4505_ = lean_ctor_get(v_impl_4423_, 2);
lean_dec(v_unused_4505_);
v_unused_4506_ = lean_ctor_get(v_impl_4423_, 1);
lean_dec(v_unused_4506_);
v_unused_4507_ = lean_ctor_get(v_impl_4423_, 0);
lean_dec(v_unused_4507_);
v___x_4440_ = v_impl_4423_;
v_isShared_4441_ = v_isSharedCheck_4502_;
goto v_resetjp_4439_;
}
else
{
lean_dec(v_impl_4423_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4502_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v_size_4442_; lean_object* v_k_4443_; lean_object* v_v_4444_; lean_object* v_l_4445_; lean_object* v_r_4446_; lean_object* v_size_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; uint8_t v___x_4450_; 
v_size_4442_ = lean_ctor_get(v_l_4429_, 0);
v_k_4443_ = lean_ctor_get(v_l_4429_, 1);
v_v_4444_ = lean_ctor_get(v_l_4429_, 2);
v_l_4445_ = lean_ctor_get(v_l_4429_, 3);
v_r_4446_ = lean_ctor_get(v_l_4429_, 4);
v_size_4447_ = lean_ctor_get(v_r_4430_, 0);
v___x_4448_ = lean_unsigned_to_nat(2u);
v___x_4449_ = lean_nat_mul(v___x_4448_, v_size_4447_);
v___x_4450_ = lean_nat_dec_lt(v_size_4442_, v___x_4449_);
lean_dec(v___x_4449_);
if (v___x_4450_ == 0)
{
lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4478_; 
lean_inc(v_r_4446_);
lean_inc(v_l_4445_);
lean_inc(v_v_4444_);
lean_inc(v_k_4443_);
v_isSharedCheck_4478_ = !lean_is_exclusive(v_l_4429_);
if (v_isSharedCheck_4478_ == 0)
{
lean_object* v_unused_4479_; lean_object* v_unused_4480_; lean_object* v_unused_4481_; lean_object* v_unused_4482_; lean_object* v_unused_4483_; 
v_unused_4479_ = lean_ctor_get(v_l_4429_, 4);
lean_dec(v_unused_4479_);
v_unused_4480_ = lean_ctor_get(v_l_4429_, 3);
lean_dec(v_unused_4480_);
v_unused_4481_ = lean_ctor_get(v_l_4429_, 2);
lean_dec(v_unused_4481_);
v_unused_4482_ = lean_ctor_get(v_l_4429_, 1);
lean_dec(v_unused_4482_);
v_unused_4483_ = lean_ctor_get(v_l_4429_, 0);
lean_dec(v_unused_4483_);
v___x_4452_ = v_l_4429_;
v_isShared_4453_ = v_isSharedCheck_4478_;
goto v_resetjp_4451_;
}
else
{
lean_dec(v_l_4429_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4478_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4468_; 
v___x_4454_ = lean_nat_add(v___x_4424_, v_size_4425_);
v___x_4455_ = lean_nat_add(v___x_4454_, v_size_4426_);
lean_dec(v_size_4426_);
if (lean_obj_tag(v_l_4445_) == 0)
{
lean_object* v_size_4476_; 
v_size_4476_ = lean_ctor_get(v_l_4445_, 0);
lean_inc(v_size_4476_);
v___y_4468_ = v_size_4476_;
goto v___jp_4467_;
}
else
{
lean_object* v___x_4477_; 
v___x_4477_ = lean_unsigned_to_nat(0u);
v___y_4468_ = v___x_4477_;
goto v___jp_4467_;
}
v___jp_4456_:
{
lean_object* v___x_4460_; lean_object* v___x_4462_; 
v___x_4460_ = lean_nat_add(v___y_4457_, v___y_4459_);
lean_dec(v___y_4459_);
lean_dec(v___y_4457_);
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 4, v_r_4430_);
lean_ctor_set(v___x_4452_, 3, v_r_4446_);
lean_ctor_set(v___x_4452_, 2, v_v_4428_);
lean_ctor_set(v___x_4452_, 1, v_k_4427_);
lean_ctor_set(v___x_4452_, 0, v___x_4460_);
v___x_4462_ = v___x_4452_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4460_);
lean_ctor_set(v_reuseFailAlloc_4466_, 1, v_k_4427_);
lean_ctor_set(v_reuseFailAlloc_4466_, 2, v_v_4428_);
lean_ctor_set(v_reuseFailAlloc_4466_, 3, v_r_4446_);
lean_ctor_set(v_reuseFailAlloc_4466_, 4, v_r_4430_);
v___x_4462_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
lean_object* v___x_4464_; 
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 4, v___x_4462_);
lean_ctor_set(v___x_4440_, 3, v___y_4458_);
lean_ctor_set(v___x_4440_, 2, v_v_4444_);
lean_ctor_set(v___x_4440_, 1, v_k_4443_);
lean_ctor_set(v___x_4440_, 0, v___x_4455_);
v___x_4464_ = v___x_4440_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4455_);
lean_ctor_set(v_reuseFailAlloc_4465_, 1, v_k_4443_);
lean_ctor_set(v_reuseFailAlloc_4465_, 2, v_v_4444_);
lean_ctor_set(v_reuseFailAlloc_4465_, 3, v___y_4458_);
lean_ctor_set(v_reuseFailAlloc_4465_, 4, v___x_4462_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
v___jp_4467_:
{
lean_object* v___x_4469_; lean_object* v___x_4471_; 
v___x_4469_ = lean_nat_add(v___x_4454_, v___y_4468_);
lean_dec(v___y_4468_);
lean_dec(v___x_4454_);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 4, v_l_4445_);
lean_ctor_set(v___x_4280_, 0, v___x_4469_);
v___x_4471_ = v___x_4280_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v___x_4469_);
lean_ctor_set(v_reuseFailAlloc_4475_, 1, v_k_4275_);
lean_ctor_set(v_reuseFailAlloc_4475_, 2, v_v_4276_);
lean_ctor_set(v_reuseFailAlloc_4475_, 3, v_l_4277_);
lean_ctor_set(v_reuseFailAlloc_4475_, 4, v_l_4445_);
v___x_4471_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
lean_object* v___x_4472_; 
v___x_4472_ = lean_nat_add(v___x_4424_, v_size_4447_);
if (lean_obj_tag(v_r_4446_) == 0)
{
lean_object* v_size_4473_; 
v_size_4473_ = lean_ctor_get(v_r_4446_, 0);
lean_inc(v_size_4473_);
v___y_4457_ = v___x_4472_;
v___y_4458_ = v___x_4471_;
v___y_4459_ = v_size_4473_;
goto v___jp_4456_;
}
else
{
lean_object* v___x_4474_; 
v___x_4474_ = lean_unsigned_to_nat(0u);
v___y_4457_ = v___x_4472_;
v___y_4458_ = v___x_4471_;
v___y_4459_ = v___x_4474_;
goto v___jp_4456_;
}
}
}
}
}
else
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4488_; 
lean_del_object(v___x_4280_);
v___x_4484_ = lean_nat_add(v___x_4424_, v_size_4425_);
v___x_4485_ = lean_nat_add(v___x_4484_, v_size_4426_);
lean_dec(v_size_4426_);
v___x_4486_ = lean_nat_add(v___x_4484_, v_size_4442_);
lean_dec(v___x_4484_);
lean_inc_ref(v_l_4277_);
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 4, v_l_4429_);
lean_ctor_set(v___x_4440_, 3, v_l_4277_);
lean_ctor_set(v___x_4440_, 2, v_v_4276_);
lean_ctor_set(v___x_4440_, 1, v_k_4275_);
lean_ctor_set(v___x_4440_, 0, v___x_4486_);
v___x_4488_ = v___x_4440_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4486_);
lean_ctor_set(v_reuseFailAlloc_4501_, 1, v_k_4275_);
lean_ctor_set(v_reuseFailAlloc_4501_, 2, v_v_4276_);
lean_ctor_set(v_reuseFailAlloc_4501_, 3, v_l_4277_);
lean_ctor_set(v_reuseFailAlloc_4501_, 4, v_l_4429_);
v___x_4488_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
v_isSharedCheck_4495_ = !lean_is_exclusive(v_l_4277_);
if (v_isSharedCheck_4495_ == 0)
{
lean_object* v_unused_4496_; lean_object* v_unused_4497_; lean_object* v_unused_4498_; lean_object* v_unused_4499_; lean_object* v_unused_4500_; 
v_unused_4496_ = lean_ctor_get(v_l_4277_, 4);
lean_dec(v_unused_4496_);
v_unused_4497_ = lean_ctor_get(v_l_4277_, 3);
lean_dec(v_unused_4497_);
v_unused_4498_ = lean_ctor_get(v_l_4277_, 2);
lean_dec(v_unused_4498_);
v_unused_4499_ = lean_ctor_get(v_l_4277_, 1);
lean_dec(v_unused_4499_);
v_unused_4500_ = lean_ctor_get(v_l_4277_, 0);
lean_dec(v_unused_4500_);
v___x_4490_ = v_l_4277_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_dec(v_l_4277_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 4, v_r_4430_);
lean_ctor_set(v___x_4490_, 3, v___x_4488_);
lean_ctor_set(v___x_4490_, 2, v_v_4428_);
lean_ctor_set(v___x_4490_, 1, v_k_4427_);
lean_ctor_set(v___x_4490_, 0, v___x_4485_);
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4485_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v_k_4427_);
lean_ctor_set(v_reuseFailAlloc_4494_, 2, v_v_4428_);
lean_ctor_set(v_reuseFailAlloc_4494_, 3, v___x_4488_);
lean_ctor_set(v_reuseFailAlloc_4494_, 4, v_r_4430_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4508_; 
v_l_4508_ = lean_ctor_get(v_impl_4423_, 3);
lean_inc(v_l_4508_);
if (lean_obj_tag(v_l_4508_) == 0)
{
lean_object* v_r_4509_; lean_object* v_k_4510_; lean_object* v_v_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4534_; 
v_r_4509_ = lean_ctor_get(v_impl_4423_, 4);
v_k_4510_ = lean_ctor_get(v_impl_4423_, 1);
v_v_4511_ = lean_ctor_get(v_impl_4423_, 2);
v_isSharedCheck_4534_ = !lean_is_exclusive(v_impl_4423_);
if (v_isSharedCheck_4534_ == 0)
{
lean_object* v_unused_4535_; lean_object* v_unused_4536_; 
v_unused_4535_ = lean_ctor_get(v_impl_4423_, 3);
lean_dec(v_unused_4535_);
v_unused_4536_ = lean_ctor_get(v_impl_4423_, 0);
lean_dec(v_unused_4536_);
v___x_4513_ = v_impl_4423_;
v_isShared_4514_ = v_isSharedCheck_4534_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_r_4509_);
lean_inc(v_v_4511_);
lean_inc(v_k_4510_);
lean_dec(v_impl_4423_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4534_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v_k_4515_; lean_object* v_v_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4530_; 
v_k_4515_ = lean_ctor_get(v_l_4508_, 1);
v_v_4516_ = lean_ctor_get(v_l_4508_, 2);
v_isSharedCheck_4530_ = !lean_is_exclusive(v_l_4508_);
if (v_isSharedCheck_4530_ == 0)
{
lean_object* v_unused_4531_; lean_object* v_unused_4532_; lean_object* v_unused_4533_; 
v_unused_4531_ = lean_ctor_get(v_l_4508_, 4);
lean_dec(v_unused_4531_);
v_unused_4532_ = lean_ctor_get(v_l_4508_, 3);
lean_dec(v_unused_4532_);
v_unused_4533_ = lean_ctor_get(v_l_4508_, 0);
lean_dec(v_unused_4533_);
v___x_4518_ = v_l_4508_;
v_isShared_4519_ = v_isSharedCheck_4530_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_v_4516_);
lean_inc(v_k_4515_);
lean_dec(v_l_4508_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4530_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4520_; lean_object* v___x_4522_; 
v___x_4520_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4509_, 2);
if (v_isShared_4519_ == 0)
{
lean_ctor_set(v___x_4518_, 4, v_r_4509_);
lean_ctor_set(v___x_4518_, 3, v_r_4509_);
lean_ctor_set(v___x_4518_, 2, v_v_4276_);
lean_ctor_set(v___x_4518_, 1, v_k_4275_);
lean_ctor_set(v___x_4518_, 0, v___x_4424_);
v___x_4522_ = v___x_4518_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4424_);
lean_ctor_set(v_reuseFailAlloc_4529_, 1, v_k_4275_);
lean_ctor_set(v_reuseFailAlloc_4529_, 2, v_v_4276_);
lean_ctor_set(v_reuseFailAlloc_4529_, 3, v_r_4509_);
lean_ctor_set(v_reuseFailAlloc_4529_, 4, v_r_4509_);
v___x_4522_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
lean_object* v___x_4524_; 
lean_inc(v_r_4509_);
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 3, v_r_4509_);
lean_ctor_set(v___x_4513_, 0, v___x_4424_);
v___x_4524_ = v___x_4513_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v___x_4424_);
lean_ctor_set(v_reuseFailAlloc_4528_, 1, v_k_4510_);
lean_ctor_set(v_reuseFailAlloc_4528_, 2, v_v_4511_);
lean_ctor_set(v_reuseFailAlloc_4528_, 3, v_r_4509_);
lean_ctor_set(v_reuseFailAlloc_4528_, 4, v_r_4509_);
v___x_4524_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
lean_object* v___x_4526_; 
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 4, v___x_4524_);
lean_ctor_set(v___x_4280_, 3, v___x_4522_);
lean_ctor_set(v___x_4280_, 2, v_v_4516_);
lean_ctor_set(v___x_4280_, 1, v_k_4515_);
lean_ctor_set(v___x_4280_, 0, v___x_4520_);
v___x_4526_ = v___x_4280_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4520_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v_k_4515_);
lean_ctor_set(v_reuseFailAlloc_4527_, 2, v_v_4516_);
lean_ctor_set(v_reuseFailAlloc_4527_, 3, v___x_4522_);
lean_ctor_set(v_reuseFailAlloc_4527_, 4, v___x_4524_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
}
}
else
{
lean_object* v_r_4537_; 
v_r_4537_ = lean_ctor_get(v_impl_4423_, 4);
lean_inc(v_r_4537_);
if (lean_obj_tag(v_r_4537_) == 0)
{
lean_object* v_k_4538_; lean_object* v_v_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4550_; 
v_k_4538_ = lean_ctor_get(v_impl_4423_, 1);
v_v_4539_ = lean_ctor_get(v_impl_4423_, 2);
v_isSharedCheck_4550_ = !lean_is_exclusive(v_impl_4423_);
if (v_isSharedCheck_4550_ == 0)
{
lean_object* v_unused_4551_; lean_object* v_unused_4552_; lean_object* v_unused_4553_; 
v_unused_4551_ = lean_ctor_get(v_impl_4423_, 4);
lean_dec(v_unused_4551_);
v_unused_4552_ = lean_ctor_get(v_impl_4423_, 3);
lean_dec(v_unused_4552_);
v_unused_4553_ = lean_ctor_get(v_impl_4423_, 0);
lean_dec(v_unused_4553_);
v___x_4541_ = v_impl_4423_;
v_isShared_4542_ = v_isSharedCheck_4550_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_v_4539_);
lean_inc(v_k_4538_);
lean_dec(v_impl_4423_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4550_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4543_; lean_object* v___x_4545_; 
v___x_4543_ = lean_unsigned_to_nat(3u);
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 4, v_l_4508_);
lean_ctor_set(v___x_4541_, 2, v_v_4276_);
lean_ctor_set(v___x_4541_, 1, v_k_4275_);
lean_ctor_set(v___x_4541_, 0, v___x_4424_);
v___x_4545_ = v___x_4541_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4424_);
lean_ctor_set(v_reuseFailAlloc_4549_, 1, v_k_4275_);
lean_ctor_set(v_reuseFailAlloc_4549_, 2, v_v_4276_);
lean_ctor_set(v_reuseFailAlloc_4549_, 3, v_l_4508_);
lean_ctor_set(v_reuseFailAlloc_4549_, 4, v_l_4508_);
v___x_4545_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
lean_object* v___x_4547_; 
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 4, v_r_4537_);
lean_ctor_set(v___x_4280_, 3, v___x_4545_);
lean_ctor_set(v___x_4280_, 2, v_v_4539_);
lean_ctor_set(v___x_4280_, 1, v_k_4538_);
lean_ctor_set(v___x_4280_, 0, v___x_4543_);
v___x_4547_ = v___x_4280_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4543_);
lean_ctor_set(v_reuseFailAlloc_4548_, 1, v_k_4538_);
lean_ctor_set(v_reuseFailAlloc_4548_, 2, v_v_4539_);
lean_ctor_set(v_reuseFailAlloc_4548_, 3, v___x_4545_);
lean_ctor_set(v_reuseFailAlloc_4548_, 4, v_r_4537_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
}
else
{
lean_object* v___x_4554_; lean_object* v___x_4556_; 
v___x_4554_ = lean_unsigned_to_nat(2u);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 4, v_impl_4423_);
lean_ctor_set(v___x_4280_, 3, v_r_4537_);
lean_ctor_set(v___x_4280_, 0, v___x_4554_);
v___x_4556_ = v___x_4280_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4554_);
lean_ctor_set(v_reuseFailAlloc_4557_, 1, v_k_4275_);
lean_ctor_set(v_reuseFailAlloc_4557_, 2, v_v_4276_);
lean_ctor_set(v_reuseFailAlloc_4557_, 3, v_r_4537_);
lean_ctor_set(v_reuseFailAlloc_4557_, 4, v_impl_4423_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
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
lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4559_ = lean_unsigned_to_nat(1u);
v___x_4560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4559_);
lean_ctor_set(v___x_4560_, 1, v_k_4271_);
lean_ctor_set(v___x_4560_, 2, v_v_4272_);
lean_ctor_set(v___x_4560_, 3, v_t_4273_);
lean_ctor_set(v___x_4560_, 4, v_t_4273_);
return v___x_4560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(lean_object* v_cfg_4568_){
_start:
{
lean_object* v___y_4571_; lean_object* v_a_4572_; lean_object* v___y_4585_; lean_object* v_externalKernels_4586_; uint8_t v___y_4599_; lean_object* v___y_4600_; lean_object* v___y_4601_; lean_object* v_a_4602_; uint8_t v___y_4616_; lean_object* v___y_4617_; lean_object* v_enable__nanoda_x3f_4630_; lean_object* v_external__kernels_x3f_4631_; lean_object* v___y_4633_; 
v_enable__nanoda_x3f_4630_ = lean_ctor_get(v_cfg_4568_, 5);
lean_inc(v_enable__nanoda_x3f_4630_);
v_external__kernels_x3f_4631_ = lean_ctor_get(v_cfg_4568_, 6);
lean_inc(v_external__kernels_x3f_4631_);
lean_dec_ref(v_cfg_4568_);
if (lean_obj_tag(v_external__kernels_x3f_4631_) == 0)
{
lean_object* v___x_4664_; 
v___x_4664_ = lean_box(1);
v___y_4633_ = v___x_4664_;
goto v___jp_4632_;
}
else
{
lean_object* v_val_4665_; 
v_val_4665_ = lean_ctor_get(v_external__kernels_x3f_4631_, 0);
lean_inc(v_val_4665_);
lean_dec_ref_known(v_external__kernels_x3f_4631_, 1);
v___y_4633_ = v_val_4665_;
goto v___jp_4632_;
}
v___jp_4570_:
{
lean_object* v_fst_4573_; 
v_fst_4573_ = lean_ctor_get(v_a_4572_, 0);
lean_inc(v_fst_4573_);
lean_dec_ref(v_a_4572_);
if (lean_obj_tag(v_fst_4573_) == 0)
{
lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4574_, 0, v___y_4571_);
v___x_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4574_);
return v___x_4575_;
}
else
{
lean_object* v_val_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4583_; 
lean_dec(v___y_4571_);
v_val_4576_ = lean_ctor_get(v_fst_4573_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v_fst_4573_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4578_ = v_fst_4573_;
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_val_4576_);
lean_dec(v_fst_4573_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4581_; 
if (v_isShared_4579_ == 0)
{
lean_ctor_set_tag(v___x_4578_, 0);
v___x_4581_ = v___x_4578_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_val_4576_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
}
v___jp_4584_:
{
lean_object* v___x_4587_; 
v___x_4587_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v___y_4585_, v_externalKernels_4586_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; lean_object* v_a_4589_; 
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
lean_inc(v_a_4588_);
lean_dec_ref_known(v___x_4587_, 1);
v_a_4589_ = lean_ctor_get(v_a_4588_, 0);
lean_inc(v_a_4589_);
lean_dec(v_a_4588_);
v___y_4571_ = v_externalKernels_4586_;
v_a_4572_ = v_a_4589_;
goto v___jp_4570_;
}
else
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4597_; 
lean_dec(v_externalKernels_4586_);
v_a_4590_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4592_ = v___x_4587_;
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4587_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4595_; 
if (v_isShared_4593_ == 0)
{
v___x_4595_ = v___x_4592_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_a_4590_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
v___jp_4598_:
{
lean_object* v_fst_4603_; 
v_fst_4603_ = lean_ctor_get(v_a_4602_, 0);
lean_inc(v_fst_4603_);
lean_dec_ref(v_a_4602_);
if (lean_obj_tag(v_fst_4603_) == 0)
{
if (v___y_4599_ == 0)
{
v___y_4585_ = v___y_4600_;
v_externalKernels_4586_ = v___y_4601_;
goto v___jp_4584_;
}
else
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4604_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0));
v___x_4605_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__2));
v___x_4606_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(v___x_4604_, v___x_4605_, v___y_4601_);
v___y_4585_ = v___y_4600_;
v_externalKernels_4586_ = v___x_4606_;
goto v___jp_4584_;
}
}
else
{
lean_object* v_val_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
v_val_4607_ = lean_ctor_get(v_fst_4603_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v_fst_4603_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v_fst_4603_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_val_4607_);
lean_dec(v_fst_4603_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
lean_ctor_set_tag(v___x_4609_, 0);
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_val_4607_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
}
v___jp_4615_:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4618_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v___x_4619_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(v___x_4618_, v___y_4617_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v_a_4620_; lean_object* v_a_4621_; 
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
lean_inc(v_a_4620_);
lean_dec_ref_known(v___x_4619_, 1);
v_a_4621_ = lean_ctor_get(v_a_4620_, 0);
lean_inc(v_a_4621_);
lean_dec(v_a_4620_);
v___y_4599_ = v___y_4616_;
v___y_4600_ = v___x_4618_;
v___y_4601_ = v___y_4617_;
v_a_4602_ = v_a_4621_;
goto v___jp_4598_;
}
else
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4629_; 
lean_dec(v___y_4617_);
v_a_4622_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4624_ = v___x_4619_;
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4619_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4627_; 
if (v_isShared_4625_ == 0)
{
v___x_4627_ = v___x_4624_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_a_4622_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
}
v___jp_4632_:
{
if (lean_obj_tag(v_enable__nanoda_x3f_4630_) == 0)
{
uint8_t v___x_4634_; 
v___x_4634_ = 0;
v___y_4616_ = v___x_4634_;
v___y_4617_ = v___y_4633_;
goto v___jp_4615_;
}
else
{
lean_object* v_val_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4663_; 
v_val_4635_ = lean_ctor_get(v_enable__nanoda_x3f_4630_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v_enable__nanoda_x3f_4630_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4637_ = v_enable__nanoda_x3f_4630_;
v_isShared_4638_ = v_isSharedCheck_4663_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_val_4635_);
lean_dec(v_enable__nanoda_x3f_4630_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4663_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
uint8_t v___x_4639_; 
v___x_4639_ = lean_unbox(v_val_4635_);
if (v___x_4639_ == 0)
{
uint8_t v___x_4640_; 
lean_del_object(v___x_4637_);
v___x_4640_ = lean_unbox(v_val_4635_);
lean_dec(v_val_4635_);
v___y_4616_ = v___x_4640_;
v___y_4617_ = v___y_4633_;
goto v___jp_4615_;
}
else
{
if (lean_obj_tag(v___y_4633_) == 0)
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
lean_dec_ref_known(v___y_4633_, 5);
lean_dec(v_val_4635_);
v___x_4641_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__3));
v___x_4642_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4641_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v_a_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4653_; 
v_a_4643_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4645_ = v___x_4642_;
v_isShared_4646_ = v_isSharedCheck_4653_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_a_4643_);
lean_dec(v___x_4642_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4653_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v___x_4648_; 
if (v_isShared_4638_ == 0)
{
lean_ctor_set_tag(v___x_4637_, 0);
lean_ctor_set(v___x_4637_, 0, v_a_4643_);
v___x_4648_ = v___x_4637_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4643_);
v___x_4648_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
lean_object* v___x_4650_; 
if (v_isShared_4646_ == 0)
{
lean_ctor_set(v___x_4645_, 0, v___x_4648_);
v___x_4650_ = v___x_4645_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v___x_4648_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
lean_del_object(v___x_4637_);
v_a_4654_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4642_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4642_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
else
{
uint8_t v___x_4662_; 
lean_del_object(v___x_4637_);
v___x_4662_ = lean_unbox(v_val_4635_);
lean_dec(v_val_4635_);
v___y_4616_ = v___x_4662_;
v___y_4617_ = v___y_4633_;
goto v___jp_4615_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___boxed(lean_object* v_cfg_4666_, lean_object* v_a_4667_){
_start:
{
lean_object* v_res_4668_; 
v_res_4668_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v_cfg_4666_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(lean_object* v_00_u03b2_4669_, lean_object* v_k_4670_, lean_object* v_v_4671_, lean_object* v_t_4672_, lean_object* v_hl_4673_){
_start:
{
lean_object* v___x_4674_; 
v___x_4674_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___redArg(v_k_4670_, v_v_4671_, v_t_4672_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(lean_object* v_a_4692_, lean_object* v_a_4693_){
_start:
{
if (lean_obj_tag(v_a_4692_) == 0)
{
lean_object* v___x_4694_; 
v___x_4694_ = l_List_reverse___redArg(v_a_4693_);
return v___x_4694_;
}
else
{
lean_object* v_head_4695_; lean_object* v_tail_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4707_; 
v_head_4695_ = lean_ctor_get(v_a_4692_, 0);
v_tail_4696_ = lean_ctor_get(v_a_4692_, 1);
v_isSharedCheck_4707_ = !lean_is_exclusive(v_a_4692_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4698_ = v_a_4692_;
v_isShared_4699_ = v_isSharedCheck_4707_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_tail_4696_);
lean_inc(v_head_4695_);
lean_dec(v_a_4692_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4707_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v_fst_4700_; uint8_t v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4704_; 
v_fst_4700_ = lean_ctor_get(v_head_4695_, 0);
lean_inc(v_fst_4700_);
lean_dec(v_head_4695_);
v___x_4701_ = 1;
v___x_4702_ = l_Lean_Name_toString(v_fst_4700_, v___x_4701_);
if (v_isShared_4699_ == 0)
{
lean_ctor_set(v___x_4698_, 1, v_a_4693_);
lean_ctor_set(v___x_4698_, 0, v___x_4702_);
v___x_4704_ = v___x_4698_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v___x_4702_);
lean_ctor_set(v_reuseFailAlloc_4706_, 1, v_a_4693_);
v___x_4704_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
v_a_4692_ = v_tail_4696_;
v_a_4693_ = v___x_4704_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(lean_object* v_as_4708_, size_t v_i_4709_, size_t v_stop_4710_, lean_object* v_b_4711_){
_start:
{
lean_object* v___y_4713_; uint8_t v___x_4717_; 
v___x_4717_ = lean_usize_dec_eq(v_i_4709_, v_stop_4710_);
if (v___x_4717_ == 0)
{
lean_object* v___x_4718_; lean_object* v_fst_4719_; lean_object* v___x_4720_; uint8_t v___x_4721_; 
v___x_4718_ = lean_array_uget_borrowed(v_as_4708_, v_i_4709_);
v_fst_4719_ = lean_ctor_get(v___x_4718_, 0);
v___x_4720_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms));
v___x_4721_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v___x_4720_, v_fst_4719_);
if (v___x_4721_ == 0)
{
lean_object* v___x_4722_; 
lean_inc(v___x_4718_);
v___x_4722_ = lean_array_push(v_b_4711_, v___x_4718_);
v___y_4713_ = v___x_4722_;
goto v___jp_4712_;
}
else
{
v___y_4713_ = v_b_4711_;
goto v___jp_4712_;
}
}
else
{
return v_b_4711_;
}
v___jp_4712_:
{
size_t v___x_4714_; size_t v___x_4715_; 
v___x_4714_ = ((size_t)1ULL);
v___x_4715_ = lean_usize_add(v_i_4709_, v___x_4714_);
v_i_4709_ = v___x_4715_;
v_b_4711_ = v___y_4713_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1___boxed(lean_object* v_as_4723_, lean_object* v_i_4724_, lean_object* v_stop_4725_, lean_object* v_b_4726_){
_start:
{
size_t v_i_boxed_4727_; size_t v_stop_boxed_4728_; lean_object* v_res_4729_; 
v_i_boxed_4727_ = lean_unbox_usize(v_i_4724_);
lean_dec(v_i_4724_);
v_stop_boxed_4728_ = lean_unbox_usize(v_stop_4725_);
lean_dec(v_stop_4725_);
v_res_4729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_as_4723_, v_i_boxed_4727_, v_stop_boxed_4728_, v_b_4726_);
lean_dec_ref(v_as_4723_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(lean_object* v_a_4732_, lean_object* v_a_4733_){
_start:
{
if (lean_obj_tag(v_a_4732_) == 0)
{
lean_object* v___x_4734_; 
v___x_4734_ = l_List_reverse___redArg(v_a_4733_);
return v___x_4734_;
}
else
{
lean_object* v_head_4735_; lean_object* v_tail_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4756_; 
v_head_4735_ = lean_ctor_get(v_a_4732_, 0);
v_tail_4736_ = lean_ctor_get(v_a_4732_, 1);
v_isSharedCheck_4756_ = !lean_is_exclusive(v_a_4732_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4738_ = v_a_4732_;
v_isShared_4739_ = v_isSharedCheck_4756_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_tail_4736_);
lean_inc(v_head_4735_);
lean_dec(v_a_4732_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4756_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v_fst_4740_; lean_object* v_snd_4741_; lean_object* v___x_4742_; uint8_t v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4753_; 
v_fst_4740_ = lean_ctor_get(v_head_4735_, 0);
lean_inc(v_fst_4740_);
v_snd_4741_ = lean_ctor_get(v_head_4735_, 1);
lean_inc(v_snd_4741_);
lean_dec(v_head_4735_);
v___x_4742_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__0));
v___x_4743_ = 1;
v___x_4744_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_4740_, v___x_4743_);
v___x_4745_ = lean_string_append(v___x_4742_, v___x_4744_);
lean_dec_ref(v___x_4744_);
v___x_4746_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__1));
v___x_4747_ = lean_string_append(v___x_4745_, v___x_4746_);
v___x_4748_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_snd_4741_, v___x_4743_);
v___x_4749_ = lean_string_append(v___x_4747_, v___x_4748_);
lean_dec_ref(v___x_4748_);
v___x_4750_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_4751_ = lean_string_append(v___x_4749_, v___x_4750_);
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 1, v_a_4733_);
lean_ctor_set(v___x_4738_, 0, v___x_4751_);
v___x_4753_ = v___x_4738_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___x_4751_);
lean_ctor_set(v_reuseFailAlloc_4755_, 1, v_a_4733_);
v___x_4753_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
v_a_4732_ = v_tail_4736_;
v_a_4733_ = v___x_4753_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(lean_object* v_exported_4762_){
_start:
{
lean_object* v___y_4765_; lean_object* v_used_4778_; lean_object* v___x_4791_; lean_object* v___x_4792_; uint8_t v___x_4793_; 
v_used_4778_ = l_Lake_Check_usedAxioms(v_exported_4762_);
v___x_4791_ = lean_array_get_size(v_used_4778_);
v___x_4792_ = lean_unsigned_to_nat(0u);
v___x_4793_ = lean_nat_dec_eq(v___x_4791_, v___x_4792_);
if (v___x_4793_ == 0)
{
lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4794_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__2));
v___x_4795_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0));
lean_inc_ref(v_used_4778_);
v___x_4796_ = lean_array_to_list(v_used_4778_);
v___x_4797_ = lean_box(0);
v___x_4798_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(v___x_4796_, v___x_4797_);
v___x_4799_ = l_String_intercalate(v___x_4795_, v___x_4798_);
v___x_4800_ = lean_string_append(v___x_4794_, v___x_4799_);
lean_dec_ref(v___x_4799_);
v___x_4801_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_4800_);
if (lean_obj_tag(v___x_4801_) == 0)
{
lean_dec_ref_known(v___x_4801_, 1);
goto v___jp_4779_;
}
else
{
lean_dec_ref(v_used_4778_);
return v___x_4801_;
}
}
else
{
lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4802_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__3));
v___x_4803_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_4802_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_dec_ref_known(v___x_4803_, 1);
goto v___jp_4779_;
}
else
{
lean_dec_ref(v_used_4778_);
return v___x_4803_;
}
}
v___jp_4764_:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; uint8_t v___x_4768_; 
v___x_4766_ = lean_array_get_size(v___y_4765_);
v___x_4767_ = lean_unsigned_to_nat(0u);
v___x_4768_ = lean_nat_dec_eq(v___x_4766_, v___x_4767_);
if (v___x_4768_ == 0)
{
lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4769_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__0));
v___x_4770_ = lean_array_to_list(v___y_4765_);
v___x_4771_ = lean_box(0);
v___x_4772_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(v___x_4770_, v___x_4771_);
v___x_4773_ = l_String_intercalate(v___x_4769_, v___x_4772_);
v___x_4774_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4773_);
v___x_4775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4775_, 0, v___x_4774_);
return v___x_4775_;
}
else
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
lean_dec_ref(v___y_4765_);
v___x_4776_ = lean_box(0);
v___x_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4776_);
return v___x_4777_;
}
}
v___jp_4779_:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; uint8_t v___x_4783_; 
v___x_4780_ = lean_unsigned_to_nat(0u);
v___x_4781_ = lean_array_get_size(v_used_4778_);
v___x_4782_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__1));
v___x_4783_ = lean_nat_dec_lt(v___x_4780_, v___x_4781_);
if (v___x_4783_ == 0)
{
lean_dec_ref(v_used_4778_);
v___y_4765_ = v___x_4782_;
goto v___jp_4764_;
}
else
{
uint8_t v___x_4784_; 
v___x_4784_ = lean_nat_dec_le(v___x_4781_, v___x_4781_);
if (v___x_4784_ == 0)
{
if (v___x_4783_ == 0)
{
lean_dec_ref(v_used_4778_);
v___y_4765_ = v___x_4782_;
goto v___jp_4764_;
}
else
{
size_t v___x_4785_; size_t v___x_4786_; lean_object* v___x_4787_; 
v___x_4785_ = ((size_t)0ULL);
v___x_4786_ = lean_usize_of_nat(v___x_4781_);
v___x_4787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_used_4778_, v___x_4785_, v___x_4786_, v___x_4782_);
lean_dec_ref(v_used_4778_);
v___y_4765_ = v___x_4787_;
goto v___jp_4764_;
}
}
else
{
size_t v___x_4788_; size_t v___x_4789_; lean_object* v___x_4790_; 
v___x_4788_ = ((size_t)0ULL);
v___x_4789_ = lean_usize_of_nat(v___x_4781_);
v___x_4790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_used_4778_, v___x_4788_, v___x_4789_, v___x_4782_);
lean_dec_ref(v_used_4778_);
v___y_4765_ = v___x_4790_;
goto v___jp_4764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___boxed(lean_object* v_exported_4804_, lean_object* v_a_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_4804_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(lean_object* v_exported_4807_, lean_object* v_a_4808_){
_start:
{
lean_object* v___x_4810_; 
v___x_4810_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_4807_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___boxed(lean_object* v_exported_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(v_exported_4811_, v_a_4812_);
lean_dec_ref(v_a_4812_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(lean_object* v_exportPath_4815_, lean_object* v___y_4816_){
_start:
{
lean_object* v___x_4818_; 
lean_inc_ref(v_exportPath_4815_);
v___x_4818_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_exportPath_4815_, v___y_4816_);
if (lean_obj_tag(v___x_4818_) == 0)
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4857_; 
v_a_4819_ = lean_ctor_get(v___x_4818_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4818_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4821_ = v___x_4818_;
v_isShared_4822_ = v_isSharedCheck_4857_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4818_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4857_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
if (lean_obj_tag(v_a_4819_) == 1)
{
lean_object* v_val_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4833_; 
lean_dec_ref(v_exportPath_4815_);
v_val_4823_ = lean_ctor_get(v_a_4819_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v_a_4819_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4825_ = v_a_4819_;
v_isShared_4826_ = v_isSharedCheck_4833_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_val_4823_);
lean_dec(v_a_4819_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4833_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4828_; 
if (v_isShared_4826_ == 0)
{
lean_ctor_set_tag(v___x_4825_, 18);
v___x_4828_ = v___x_4825_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_val_4823_);
v___x_4828_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
lean_object* v___x_4830_; 
if (v_isShared_4822_ == 0)
{
lean_ctor_set_tag(v___x_4821_, 1);
lean_ctor_set(v___x_4821_, 0, v___x_4828_);
v___x_4830_ = v___x_4821_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v___x_4828_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
}
}
else
{
uint8_t v___x_4834_; lean_object* v___x_4835_; 
lean_del_object(v___x_4821_);
lean_dec(v_a_4819_);
v___x_4834_ = 0;
v___x_4835_ = lean_io_prim_handle_mk(v_exportPath_4815_, v___x_4834_);
lean_dec_ref(v_exportPath_4815_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
lean_inc(v_a_4836_);
lean_dec_ref_known(v___x_4835_, 1);
v___x_4837_ = lean_stream_of_handle(v_a_4836_);
v___x_4838_ = l_LeanExport_parseStream(v___x_4837_);
if (lean_obj_tag(v___x_4838_) == 0)
{
lean_object* v_a_4839_; lean_object* v___x_4840_; 
v_a_4839_ = lean_ctor_get(v___x_4838_, 0);
lean_inc(v_a_4839_);
lean_dec_ref_known(v___x_4838_, 1);
v___x_4840_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_a_4839_);
return v___x_4840_;
}
else
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4848_; 
v_a_4841_ = lean_ctor_get(v___x_4838_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4843_ = v___x_4838_;
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___x_4838_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___x_4846_; 
if (v_isShared_4844_ == 0)
{
v___x_4846_ = v___x_4843_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
else
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4856_; 
v_a_4849_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4851_ = v___x_4835_;
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4835_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4854_; 
if (v_isShared_4852_ == 0)
{
v___x_4854_ = v___x_4851_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4849_);
v___x_4854_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
return v___x_4854_;
}
}
}
}
}
}
else
{
lean_object* v_a_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4865_; 
lean_dec_ref(v_exportPath_4815_);
v_a_4858_ = lean_ctor_get(v___x_4818_, 0);
v_isSharedCheck_4865_ = !lean_is_exclusive(v___x_4818_);
if (v_isSharedCheck_4865_ == 0)
{
v___x_4860_ = v___x_4818_;
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_a_4858_);
lean_dec(v___x_4818_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v___x_4863_; 
if (v_isShared_4861_ == 0)
{
v___x_4863_ = v___x_4860_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_a_4858_);
v___x_4863_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
return v___x_4863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0___boxed(lean_object* v_exportPath_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(v_exportPath_4866_, v___y_4867_);
lean_dec_ref(v___y_4867_);
return v_res_4869_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject(lean_object* v_a_4871_){
_start:
{
lean_object* v___x_4873_; 
v___x_4873_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_4871_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v___f_4874_; lean_object* v___x_4875_; 
lean_dec_ref_known(v___x_4873_, 1);
v___f_4874_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkProject___closed__0));
v___x_4875_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v___f_4874_, v_a_4871_);
return v___x_4875_;
}
else
{
return v___x_4873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___boxed(lean_object* v_a_4876_, lean_object* v_a_4877_){
_start:
{
lean_object* v_res_4878_; 
v_res_4878_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v_a_4876_);
lean_dec_ref(v_a_4876_);
return v_res_4878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(size_t v_sz_4879_, size_t v_i_4880_, lean_object* v_bs_4881_){
_start:
{
uint8_t v___x_4882_; 
v___x_4882_ = lean_usize_dec_lt(v_i_4880_, v_sz_4879_);
if (v___x_4882_ == 0)
{
return v_bs_4881_;
}
else
{
lean_object* v_v_4883_; lean_object* v___x_4884_; lean_object* v_bs_x27_4885_; lean_object* v___x_4886_; size_t v___x_4887_; size_t v___x_4888_; lean_object* v___x_4889_; 
v_v_4883_ = lean_array_uget(v_bs_4881_, v_i_4880_);
v___x_4884_ = lean_unsigned_to_nat(0u);
v_bs_x27_4885_ = lean_array_uset(v_bs_4881_, v_i_4880_, v___x_4884_);
v___x_4886_ = l_String_toName(v_v_4883_);
v___x_4887_ = ((size_t)1ULL);
v___x_4888_ = lean_usize_add(v_i_4880_, v___x_4887_);
v___x_4889_ = lean_array_uset(v_bs_x27_4885_, v_i_4880_, v___x_4886_);
v_i_4880_ = v___x_4888_;
v_bs_4881_ = v___x_4889_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0___boxed(lean_object* v_sz_4891_, lean_object* v_i_4892_, lean_object* v_bs_4893_){
_start:
{
size_t v_sz_boxed_4894_; size_t v_i_boxed_4895_; lean_object* v_res_4896_; 
v_sz_boxed_4894_ = lean_unbox_usize(v_sz_4891_);
lean_dec(v_sz_4891_);
v_i_boxed_4895_ = lean_unbox_usize(v_i_4892_);
lean_dec(v_i_4892_);
v_res_4896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_boxed_4894_, v_i_boxed_4895_, v_bs_4893_);
return v_res_4896_;
}
}
static lean_object* _init_l_Lake_Check_runChallenge___boxed__const__1(void){
_start:
{
uint32_t v___x_4903_; lean_object* v___x_4904_; 
v___x_4903_ = 1;
v___x_4904_ = lean_box_uint32(v___x_4903_);
return v___x_4904_;
}
}
static lean_object* _init_l_Lake_Check_runChallenge___boxed__const__2(void){
_start:
{
uint32_t v___x_4905_; lean_object* v___x_4906_; 
v___x_4905_ = 0;
v___x_4906_ = lean_box_uint32(v___x_4905_);
return v___x_4906_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runChallenge(lean_object* v_configFile_x3f_4907_, lean_object* v_lean_4908_, lean_object* v_lake_4909_, lean_object* v_projectDir_4910_){
_start:
{
lean_object* v_a_4913_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4935_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__0));
v___x_4936_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_4935_, v_lean_4908_, v_lake_4909_, v_projectDir_4910_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_5074_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_4939_ = v___x_4936_;
v_isShared_4940_ = v_isSharedCheck_5074_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4936_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_5074_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
if (lean_obj_tag(v_a_4937_) == 0)
{
lean_object* v_a_4941_; lean_object* v___x_4943_; 
v_a_4941_ = lean_ctor_get(v_a_4937_, 0);
lean_inc(v_a_4941_);
lean_dec_ref_known(v_a_4937_, 1);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 0, v_a_4941_);
v___x_4943_ = v___x_4939_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4941_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
else
{
lean_del_object(v___x_4939_);
if (lean_obj_tag(v_configFile_x3f_4907_) == 1)
{
lean_object* v_a_4945_; lean_object* v_val_4946_; lean_object* v___x_4947_; 
v_a_4945_ = lean_ctor_get(v_a_4937_, 0);
lean_inc(v_a_4945_);
lean_dec_ref_known(v_a_4937_, 1);
v_val_4946_ = lean_ctor_get(v_configFile_x3f_4907_, 0);
v___x_4947_ = l_IO_FS_readFile(v_val_4946_);
if (lean_obj_tag(v___x_4947_) == 0)
{
lean_object* v_a_4948_; lean_object* v_a_4950_; lean_object* v___x_4957_; 
v_a_4948_ = lean_ctor_get(v___x_4947_, 0);
lean_inc(v_a_4948_);
lean_dec_ref_known(v___x_4947_, 1);
v___x_4957_ = l_Lean_Json_parse(v_a_4948_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4958_; 
lean_dec(v_a_4945_);
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4958_);
lean_dec_ref_known(v___x_4957_, 1);
v_a_4950_ = v_a_4958_;
goto v___jp_4949_;
}
else
{
lean_object* v_a_4959_; lean_object* v___x_4960_; 
v_a_4959_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4959_);
lean_dec_ref_known(v___x_4957_, 1);
v___x_4960_ = l_Lake_Check_instFromJsonConfig_fromJson(v_a_4959_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; 
lean_dec(v_a_4945_);
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4960_, 1);
v_a_4950_ = v_a_4961_;
goto v___jp_4949_;
}
else
{
lean_object* v_a_4962_; lean_object* v_challenge__module_4963_; lean_object* v_solution__module_4964_; lean_object* v_theorem__names_4965_; lean_object* v_definition__names_4966_; lean_object* v_permitted__axioms_4967_; size_t v_sz_4968_; size_t v___x_4969_; lean_object* v___x_4970_; lean_object* v___y_4972_; lean_object* v___y_5055_; 
v_a_4962_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4962_);
lean_dec_ref_known(v___x_4960_, 1);
v_challenge__module_4963_ = lean_ctor_get(v_a_4962_, 0);
lean_inc_ref(v_challenge__module_4963_);
v_solution__module_4964_ = lean_ctor_get(v_a_4962_, 1);
lean_inc_ref(v_solution__module_4964_);
v_theorem__names_4965_ = lean_ctor_get(v_a_4962_, 2);
v_definition__names_4966_ = lean_ctor_get(v_a_4962_, 3);
v_permitted__axioms_4967_ = lean_ctor_get(v_a_4962_, 4);
lean_inc_ref(v_permitted__axioms_4967_);
v_sz_4968_ = lean_array_size(v_theorem__names_4965_);
v___x_4969_ = ((size_t)0ULL);
lean_inc_ref(v_theorem__names_4965_);
v___x_4970_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_4968_, v___x_4969_, v_theorem__names_4965_);
if (lean_obj_tag(v_definition__names_4966_) == 0)
{
lean_object* v___x_5065_; 
v___x_5065_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___y_5055_ = v___x_5065_;
goto v___jp_5054_;
}
else
{
lean_object* v_val_5066_; 
v_val_5066_ = lean_ctor_get(v_definition__names_4966_, 0);
lean_inc(v_val_5066_);
v___y_5055_ = v_val_5066_;
goto v___jp_5054_;
}
v___jp_4971_:
{
lean_object* v___x_4973_; 
v___x_4973_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v_a_4962_);
if (lean_obj_tag(v___x_4973_) == 0)
{
lean_object* v_a_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_5045_; 
v_a_4974_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_5045_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_5045_ == 0)
{
v___x_4976_ = v___x_4973_;
v_isShared_4977_ = v_isSharedCheck_5045_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_a_4974_);
lean_dec(v___x_4973_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_5045_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
if (lean_obj_tag(v_a_4974_) == 0)
{
lean_object* v_a_4978_; lean_object* v___x_4980_; 
lean_dec_ref(v___y_4972_);
lean_dec_ref(v___x_4970_);
lean_dec_ref(v_permitted__axioms_4967_);
lean_dec_ref(v_solution__module_4964_);
lean_dec_ref(v_challenge__module_4963_);
lean_dec(v_a_4945_);
v_a_4978_ = lean_ctor_get(v_a_4974_, 0);
lean_inc(v_a_4978_);
lean_dec_ref_known(v_a_4974_, 1);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 0, v_a_4978_);
v___x_4980_ = v___x_4976_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4978_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
else
{
lean_object* v_a_4982_; lean_object* v_projectDir_4983_; lean_object* v_leanPrefix_4984_; lean_object* v_leanPath_4985_; lean_object* v_binPath_4986_; lean_object* v_whichSandbox_4987_; lean_object* v_whichLake_4988_; lean_object* v_lakeHome_4989_; lean_object* v_whichLean4Export_4990_; lean_object* v_whichLeanChecker_4991_; lean_object* v_whichEnvBin_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_5038_; 
lean_del_object(v___x_4976_);
v_a_4982_ = lean_ctor_get(v_a_4974_, 0);
lean_inc(v_a_4982_);
lean_dec_ref_known(v_a_4974_, 1);
v_projectDir_4983_ = lean_ctor_get(v_a_4945_, 0);
v_leanPrefix_4984_ = lean_ctor_get(v_a_4945_, 6);
v_leanPath_4985_ = lean_ctor_get(v_a_4945_, 7);
v_binPath_4986_ = lean_ctor_get(v_a_4945_, 8);
v_whichSandbox_4987_ = lean_ctor_get(v_a_4945_, 9);
v_whichLake_4988_ = lean_ctor_get(v_a_4945_, 10);
v_lakeHome_4989_ = lean_ctor_get(v_a_4945_, 11);
v_whichLean4Export_4990_ = lean_ctor_get(v_a_4945_, 12);
v_whichLeanChecker_4991_ = lean_ctor_get(v_a_4945_, 13);
v_whichEnvBin_4992_ = lean_ctor_get(v_a_4945_, 14);
v_isSharedCheck_5038_ = !lean_is_exclusive(v_a_4945_);
if (v_isSharedCheck_5038_ == 0)
{
lean_object* v_unused_5039_; lean_object* v_unused_5040_; lean_object* v_unused_5041_; lean_object* v_unused_5042_; lean_object* v_unused_5043_; lean_object* v_unused_5044_; 
v_unused_5039_ = lean_ctor_get(v_a_4945_, 15);
lean_dec(v_unused_5039_);
v_unused_5040_ = lean_ctor_get(v_a_4945_, 5);
lean_dec(v_unused_5040_);
v_unused_5041_ = lean_ctor_get(v_a_4945_, 4);
lean_dec(v_unused_5041_);
v_unused_5042_ = lean_ctor_get(v_a_4945_, 3);
lean_dec(v_unused_5042_);
v_unused_5043_ = lean_ctor_get(v_a_4945_, 2);
lean_dec(v_unused_5043_);
v_unused_5044_ = lean_ctor_get(v_a_4945_, 1);
lean_dec(v_unused_5044_);
v___x_4994_ = v_a_4945_;
v_isShared_4995_ = v_isSharedCheck_5038_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_whichEnvBin_4992_);
lean_inc(v_whichLeanChecker_4991_);
lean_inc(v_whichLean4Export_4990_);
lean_inc(v_lakeHome_4989_);
lean_inc(v_whichLake_4988_);
lean_inc(v_whichSandbox_4987_);
lean_inc(v_binPath_4986_);
lean_inc(v_leanPath_4985_);
lean_inc(v_leanPrefix_4984_);
lean_inc(v_projectDir_4983_);
lean_dec(v_a_4945_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_5038_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4996_; 
lean_inc_ref(v_projectDir_4983_);
v___x_4996_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_4935_, v_projectDir_4983_);
if (lean_obj_tag(v___x_4996_) == 0)
{
lean_object* v_a_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5029_; 
v_a_4997_ = lean_ctor_get(v___x_4996_, 0);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_4996_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_4999_ = v___x_4996_;
v_isShared_5000_ = v_isSharedCheck_5029_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_a_4997_);
lean_dec(v___x_4996_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5029_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
if (lean_obj_tag(v_a_4997_) == 1)
{
lean_object* v_val_5001_; lean_object* v___x_5003_; 
lean_del_object(v___x_4994_);
lean_dec_ref(v_whichEnvBin_4992_);
lean_dec_ref(v_whichLeanChecker_4991_);
lean_dec_ref(v_whichLean4Export_4990_);
lean_dec_ref(v_lakeHome_4989_);
lean_dec_ref(v_whichLake_4988_);
lean_dec_ref(v_whichSandbox_4987_);
lean_dec_ref(v_binPath_4986_);
lean_dec_ref(v_leanPath_4985_);
lean_dec_ref(v_leanPrefix_4984_);
lean_dec_ref(v_projectDir_4983_);
lean_dec(v_a_4982_);
lean_dec_ref(v___y_4972_);
lean_dec_ref(v___x_4970_);
lean_dec_ref(v_permitted__axioms_4967_);
lean_dec_ref(v_solution__module_4964_);
lean_dec_ref(v_challenge__module_4963_);
v_val_5001_ = lean_ctor_get(v_a_4997_, 0);
lean_inc(v_val_5001_);
lean_dec_ref_known(v_a_4997_, 1);
if (v_isShared_5000_ == 0)
{
lean_ctor_set(v___x_4999_, 0, v_val_5001_);
v___x_5003_ = v___x_4999_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_val_5001_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
}
}
else
{
lean_object* v___x_5005_; lean_object* v___x_5006_; size_t v_sz_5007_; lean_object* v___x_5008_; lean_object* v___x_5010_; 
lean_del_object(v___x_4999_);
lean_dec(v_a_4997_);
v___x_5005_ = l_String_toName(v_challenge__module_4963_);
v___x_5006_ = l_String_toName(v_solution__module_4964_);
v_sz_5007_ = lean_array_size(v_permitted__axioms_4967_);
v___x_5008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_5007_, v___x_4969_, v_permitted__axioms_4967_);
lean_inc(v_a_4982_);
lean_inc_ref(v_whichEnvBin_4992_);
lean_inc_ref(v_whichLeanChecker_4991_);
lean_inc_ref(v_whichLean4Export_4990_);
lean_inc_ref(v_lakeHome_4989_);
lean_inc_ref(v_whichLake_4988_);
lean_inc_ref(v_whichSandbox_4987_);
lean_inc_ref(v_leanPrefix_4984_);
lean_inc_ref(v___x_5008_);
lean_inc_ref(v___y_4972_);
lean_inc_ref(v___x_4970_);
lean_inc(v___x_5006_);
lean_inc(v___x_5005_);
lean_inc_ref(v_projectDir_4983_);
if (v_isShared_4995_ == 0)
{
lean_ctor_set(v___x_4994_, 15, v_a_4982_);
lean_ctor_set(v___x_4994_, 5, v___x_5008_);
lean_ctor_set(v___x_4994_, 4, v___y_4972_);
lean_ctor_set(v___x_4994_, 3, v___x_4970_);
lean_ctor_set(v___x_4994_, 2, v___x_5006_);
lean_ctor_set(v___x_4994_, 1, v___x_5005_);
v___x_5010_ = v___x_4994_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_projectDir_4983_);
lean_ctor_set(v_reuseFailAlloc_5028_, 1, v___x_5005_);
lean_ctor_set(v_reuseFailAlloc_5028_, 2, v___x_5006_);
lean_ctor_set(v_reuseFailAlloc_5028_, 3, v___x_4970_);
lean_ctor_set(v_reuseFailAlloc_5028_, 4, v___y_4972_);
lean_ctor_set(v_reuseFailAlloc_5028_, 5, v___x_5008_);
lean_ctor_set(v_reuseFailAlloc_5028_, 6, v_leanPrefix_4984_);
lean_ctor_set(v_reuseFailAlloc_5028_, 7, v_leanPath_4985_);
lean_ctor_set(v_reuseFailAlloc_5028_, 8, v_binPath_4986_);
lean_ctor_set(v_reuseFailAlloc_5028_, 9, v_whichSandbox_4987_);
lean_ctor_set(v_reuseFailAlloc_5028_, 10, v_whichLake_4988_);
lean_ctor_set(v_reuseFailAlloc_5028_, 11, v_lakeHome_4989_);
lean_ctor_set(v_reuseFailAlloc_5028_, 12, v_whichLean4Export_4990_);
lean_ctor_set(v_reuseFailAlloc_5028_, 13, v_whichLeanChecker_4991_);
lean_ctor_set(v_reuseFailAlloc_5028_, 14, v_whichEnvBin_4992_);
lean_ctor_set(v_reuseFailAlloc_5028_, 15, v_a_4982_);
v___x_5010_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
lean_object* v___x_5011_; 
v___x_5011_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v___x_5010_);
lean_dec_ref(v___x_5010_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5012_; lean_object* v_fst_5013_; lean_object* v_snd_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
lean_inc(v_a_5012_);
lean_dec_ref_known(v___x_5011_, 1);
v_fst_5013_ = lean_ctor_get(v_a_5012_, 0);
lean_inc(v_fst_5013_);
v_snd_5014_ = lean_ctor_get(v_a_5012_, 1);
lean_inc(v_snd_5014_);
lean_dec(v_a_5012_);
v___x_5015_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_5015_, 0, v_projectDir_4983_);
lean_ctor_set(v___x_5015_, 1, v___x_5005_);
lean_ctor_set(v___x_5015_, 2, v___x_5006_);
lean_ctor_set(v___x_5015_, 3, v___x_4970_);
lean_ctor_set(v___x_5015_, 4, v___y_4972_);
lean_ctor_set(v___x_5015_, 5, v___x_5008_);
lean_ctor_set(v___x_5015_, 6, v_leanPrefix_4984_);
lean_ctor_set(v___x_5015_, 7, v_fst_5013_);
lean_ctor_set(v___x_5015_, 8, v_snd_5014_);
lean_ctor_set(v___x_5015_, 9, v_whichSandbox_4987_);
lean_ctor_set(v___x_5015_, 10, v_whichLake_4988_);
lean_ctor_set(v___x_5015_, 11, v_lakeHome_4989_);
lean_ctor_set(v___x_5015_, 12, v_whichLean4Export_4990_);
lean_ctor_set(v___x_5015_, 13, v_whichLeanChecker_4991_);
lean_ctor_set(v___x_5015_, 14, v_whichEnvBin_4992_);
lean_ctor_set(v___x_5015_, 15, v_a_4982_);
v___x_5016_ = l_Lake_Check_compareIt(v___x_5015_);
lean_dec_ref_known(v___x_5015_, 16);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5024_; 
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5024_ == 0)
{
lean_object* v_unused_5025_; 
v_unused_5025_ = lean_ctor_get(v___x_5016_, 0);
lean_dec(v_unused_5025_);
v___x_5018_ = v___x_5016_;
v_isShared_5019_ = v_isSharedCheck_5024_;
goto v_resetjp_5017_;
}
else
{
lean_dec(v___x_5016_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5024_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5020_; lean_object* v___x_5022_; 
v___x_5020_ = l_Lake_Check_runChallenge___boxed__const__2;
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 0, v___x_5020_);
v___x_5022_ = v___x_5018_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v___x_5020_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
return v___x_5022_;
}
}
}
else
{
lean_object* v_a_5026_; 
v_a_5026_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_a_5026_);
lean_dec_ref_known(v___x_5016_, 1);
v_a_4913_ = v_a_5026_;
goto v___jp_4912_;
}
}
else
{
lean_object* v_a_5027_; 
lean_dec_ref(v___x_5008_);
lean_dec(v___x_5006_);
lean_dec(v___x_5005_);
lean_dec_ref(v_whichEnvBin_4992_);
lean_dec_ref(v_whichLeanChecker_4991_);
lean_dec_ref(v_whichLean4Export_4990_);
lean_dec_ref(v_lakeHome_4989_);
lean_dec_ref(v_whichLake_4988_);
lean_dec_ref(v_whichSandbox_4987_);
lean_dec_ref(v_leanPrefix_4984_);
lean_dec_ref(v_projectDir_4983_);
lean_dec(v_a_4982_);
lean_dec_ref(v___y_4972_);
lean_dec_ref(v___x_4970_);
v_a_5027_ = lean_ctor_get(v___x_5011_, 0);
lean_inc(v_a_5027_);
lean_dec_ref_known(v___x_5011_, 1);
v_a_4913_ = v_a_5027_;
goto v___jp_4912_;
}
}
}
}
}
else
{
lean_object* v_a_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5037_; 
lean_del_object(v___x_4994_);
lean_dec_ref(v_whichEnvBin_4992_);
lean_dec_ref(v_whichLeanChecker_4991_);
lean_dec_ref(v_whichLean4Export_4990_);
lean_dec_ref(v_lakeHome_4989_);
lean_dec_ref(v_whichLake_4988_);
lean_dec_ref(v_whichSandbox_4987_);
lean_dec_ref(v_binPath_4986_);
lean_dec_ref(v_leanPath_4985_);
lean_dec_ref(v_leanPrefix_4984_);
lean_dec_ref(v_projectDir_4983_);
lean_dec(v_a_4982_);
lean_dec_ref(v___y_4972_);
lean_dec_ref(v___x_4970_);
lean_dec_ref(v_permitted__axioms_4967_);
lean_dec_ref(v_solution__module_4964_);
lean_dec_ref(v_challenge__module_4963_);
v_a_5030_ = lean_ctor_get(v___x_4996_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___x_4996_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5032_ = v___x_4996_;
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_a_5030_);
lean_dec(v___x_4996_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5035_; 
if (v_isShared_5033_ == 0)
{
v___x_5035_ = v___x_5032_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_a_5030_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
return v___x_5035_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5046_; lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5053_; 
lean_dec_ref(v___y_4972_);
lean_dec_ref(v___x_4970_);
lean_dec_ref(v_permitted__axioms_4967_);
lean_dec_ref(v_solution__module_4964_);
lean_dec_ref(v_challenge__module_4963_);
lean_dec(v_a_4945_);
v_a_5046_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_5053_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_5048_ = v___x_4973_;
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
else
{
lean_inc(v_a_5046_);
lean_dec(v___x_4973_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
lean_object* v___x_5051_; 
if (v_isShared_5049_ == 0)
{
v___x_5051_ = v___x_5048_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_a_5046_);
v___x_5051_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
return v___x_5051_;
}
}
}
}
v___jp_5054_:
{
size_t v_sz_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; uint8_t v___x_5060_; 
v_sz_5056_ = lean_array_size(v___y_5055_);
v___x_5057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runChallenge_spec__0(v_sz_5056_, v___x_4969_, v___y_5055_);
v___x_5058_ = lean_array_get_size(v___x_4970_);
v___x_5059_ = lean_unsigned_to_nat(0u);
v___x_5060_ = lean_nat_dec_eq(v___x_5058_, v___x_5059_);
if (v___x_5060_ == 0)
{
v___y_4972_ = v___x_5057_;
goto v___jp_4971_;
}
else
{
lean_object* v___x_5061_; uint8_t v___x_5062_; 
v___x_5061_ = lean_array_get_size(v___x_5057_);
v___x_5062_ = lean_nat_dec_eq(v___x_5061_, v___x_5059_);
if (v___x_5062_ == 0)
{
v___y_4972_ = v___x_5057_;
goto v___jp_4971_;
}
else
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
lean_dec_ref(v___x_5057_);
lean_dec_ref(v___x_4970_);
lean_dec_ref(v_permitted__axioms_4967_);
lean_dec_ref(v_solution__module_4964_);
lean_dec_ref(v_challenge__module_4963_);
lean_dec(v_a_4962_);
lean_dec(v_a_4945_);
v___x_5063_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__3));
v___x_5064_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5063_);
return v___x_5064_;
}
}
}
}
}
v___jp_4949_:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; 
v___x_4951_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__1));
v___x_4952_ = lean_string_append(v___x_4951_, v_val_4946_);
v___x_4953_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__2));
v___x_4954_ = lean_string_append(v___x_4952_, v___x_4953_);
v___x_4955_ = lean_string_append(v___x_4954_, v_a_4950_);
lean_dec_ref(v_a_4950_);
v___x_4956_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4955_);
lean_dec_ref(v___x_4955_);
return v___x_4956_;
}
}
else
{
lean_object* v_a_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; 
lean_dec(v_a_4945_);
v_a_5067_ = lean_ctor_get(v___x_4947_, 0);
lean_inc(v_a_5067_);
lean_dec_ref_known(v___x_4947_, 1);
v___x_5068_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__4));
v___x_5069_ = lean_io_error_to_string(v_a_5067_);
v___x_5070_ = lean_string_append(v___x_5068_, v___x_5069_);
lean_dec_ref(v___x_5069_);
v___x_5071_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5070_);
lean_dec_ref(v___x_5070_);
return v___x_5071_;
}
}
else
{
lean_object* v___x_5072_; lean_object* v___x_5073_; 
lean_dec_ref_known(v_a_4937_, 1);
v___x_5072_ = ((lean_object*)(l_Lake_Check_runChallenge___closed__5));
v___x_5073_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5072_);
return v___x_5073_;
}
}
}
}
else
{
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5082_; 
v_a_5075_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5077_ = v___x_4936_;
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v___x_4936_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5080_; 
if (v_isShared_5078_ == 0)
{
v___x_5080_ = v___x_5077_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5075_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
v___jp_4912_:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4914_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_4915_ = lean_io_error_to_string(v_a_4913_);
v___x_4916_ = lean_string_append(v___x_4914_, v___x_4915_);
lean_dec_ref(v___x_4915_);
v___x_4917_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_4916_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4925_; 
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4925_ == 0)
{
lean_object* v_unused_4926_; 
v_unused_4926_ = lean_ctor_get(v___x_4917_, 0);
lean_dec(v_unused_4926_);
v___x_4919_ = v___x_4917_;
v_isShared_4920_ = v_isSharedCheck_4925_;
goto v_resetjp_4918_;
}
else
{
lean_dec(v___x_4917_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4925_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4921_; lean_object* v___x_4923_; 
v___x_4921_ = l_Lake_Check_runChallenge___boxed__const__1;
if (v_isShared_4920_ == 0)
{
lean_ctor_set(v___x_4919_, 0, v___x_4921_);
v___x_4923_ = v___x_4919_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v___x_4921_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
else
{
lean_object* v_a_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4934_; 
v_a_4927_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4929_ = v___x_4917_;
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_a_4927_);
lean_dec(v___x_4917_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4932_; 
if (v_isShared_4930_ == 0)
{
v___x_4932_ = v___x_4929_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v_a_4927_);
v___x_4932_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
return v___x_4932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runChallenge___boxed(lean_object* v_configFile_x3f_5083_, lean_object* v_lean_5084_, lean_object* v_lake_5085_, lean_object* v_projectDir_5086_, lean_object* v_a_5087_){
_start:
{
lean_object* v_res_5088_; 
v_res_5088_ = l_Lake_Check_runChallenge(v_configFile_x3f_5083_, v_lean_5084_, v_lake_5085_, v_projectDir_5086_);
lean_dec_ref(v_lake_5085_);
lean_dec(v_configFile_x3f_5083_);
return v_res_5088_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runCheck(lean_object* v_lean_5089_, lean_object* v_lake_5090_, lean_object* v_projectDir_5091_){
_start:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___lam__0___closed__0));
v___x_5094_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_5093_, v_lean_5089_, v_lake_5090_, v_projectDir_5091_);
if (lean_obj_tag(v___x_5094_) == 0)
{
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5155_; 
v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5097_ = v___x_5094_;
v_isShared_5098_ = v_isSharedCheck_5155_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5094_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5155_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
if (lean_obj_tag(v_a_5095_) == 0)
{
lean_object* v_a_5099_; lean_object* v___x_5101_; 
v_a_5099_ = lean_ctor_get(v_a_5095_, 0);
lean_inc(v_a_5099_);
lean_dec_ref_known(v_a_5095_, 1);
if (v_isShared_5098_ == 0)
{
lean_ctor_set(v___x_5097_, 0, v_a_5099_);
v___x_5101_ = v___x_5097_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v_a_5099_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
return v___x_5101_;
}
}
else
{
lean_object* v_a_5103_; lean_object* v_projectDir_5104_; lean_object* v___x_5105_; 
lean_del_object(v___x_5097_);
v_a_5103_ = lean_ctor_get(v_a_5095_, 0);
lean_inc(v_a_5103_);
lean_dec_ref_known(v_a_5095_, 1);
v_projectDir_5104_ = lean_ctor_get(v_a_5103_, 0);
lean_inc_ref(v_projectDir_5104_);
v___x_5105_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_5093_, v_projectDir_5104_);
if (lean_obj_tag(v___x_5105_) == 0)
{
lean_object* v_a_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5146_; 
v_a_5106_ = lean_ctor_get(v___x_5105_, 0);
v_isSharedCheck_5146_ = !lean_is_exclusive(v___x_5105_);
if (v_isSharedCheck_5146_ == 0)
{
v___x_5108_ = v___x_5105_;
v_isShared_5109_ = v_isSharedCheck_5146_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_a_5106_);
lean_dec(v___x_5105_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5146_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
if (lean_obj_tag(v_a_5106_) == 1)
{
lean_object* v_val_5110_; lean_object* v___x_5112_; 
lean_dec(v_a_5103_);
v_val_5110_ = lean_ctor_get(v_a_5106_, 0);
lean_inc(v_val_5110_);
lean_dec_ref_known(v_a_5106_, 1);
if (v_isShared_5109_ == 0)
{
lean_ctor_set(v___x_5108_, 0, v_val_5110_);
v___x_5112_ = v___x_5108_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_val_5110_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
else
{
lean_object* v___x_5114_; 
lean_del_object(v___x_5108_);
lean_dec(v_a_5106_);
v___x_5114_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v_a_5103_);
lean_dec(v_a_5103_);
if (lean_obj_tag(v___x_5114_) == 0)
{
lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5122_; 
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5114_);
if (v_isSharedCheck_5122_ == 0)
{
lean_object* v_unused_5123_; 
v_unused_5123_ = lean_ctor_get(v___x_5114_, 0);
lean_dec(v_unused_5123_);
v___x_5116_ = v___x_5114_;
v_isShared_5117_ = v_isSharedCheck_5122_;
goto v_resetjp_5115_;
}
else
{
lean_dec(v___x_5114_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5122_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5118_; lean_object* v___x_5120_; 
v___x_5118_ = l_Lake_Check_runChallenge___boxed__const__2;
if (v_isShared_5117_ == 0)
{
lean_ctor_set(v___x_5116_, 0, v___x_5118_);
v___x_5120_ = v___x_5116_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v___x_5118_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
return v___x_5120_;
}
}
}
else
{
lean_object* v_a_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
v_a_5124_ = lean_ctor_get(v___x_5114_, 0);
lean_inc(v_a_5124_);
lean_dec_ref_known(v___x_5114_, 1);
v___x_5125_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_5126_ = lean_io_error_to_string(v_a_5124_);
v___x_5127_ = lean_string_append(v___x_5125_, v___x_5126_);
lean_dec_ref(v___x_5126_);
v___x_5128_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_5127_);
if (lean_obj_tag(v___x_5128_) == 0)
{
lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5136_; 
v_isSharedCheck_5136_ = !lean_is_exclusive(v___x_5128_);
if (v_isSharedCheck_5136_ == 0)
{
lean_object* v_unused_5137_; 
v_unused_5137_ = lean_ctor_get(v___x_5128_, 0);
lean_dec(v_unused_5137_);
v___x_5130_ = v___x_5128_;
v_isShared_5131_ = v_isSharedCheck_5136_;
goto v_resetjp_5129_;
}
else
{
lean_dec(v___x_5128_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5136_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
lean_object* v___x_5132_; lean_object* v___x_5134_; 
v___x_5132_ = l_Lake_Check_runChallenge___boxed__const__1;
if (v_isShared_5131_ == 0)
{
lean_ctor_set(v___x_5130_, 0, v___x_5132_);
v___x_5134_ = v___x_5130_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v___x_5132_);
v___x_5134_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
return v___x_5134_;
}
}
}
else
{
lean_object* v_a_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5145_; 
v_a_5138_ = lean_ctor_get(v___x_5128_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_5128_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_5140_ = v___x_5128_;
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_a_5138_);
lean_dec(v___x_5128_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v___x_5143_; 
if (v_isShared_5141_ == 0)
{
v___x_5143_ = v___x_5140_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_a_5138_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5154_; 
lean_dec(v_a_5103_);
v_a_5147_ = lean_ctor_get(v___x_5105_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5105_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5149_ = v___x_5105_;
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5105_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5147_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
}
}
else
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5163_; 
v_a_5156_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5158_ = v___x_5094_;
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5094_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5161_; 
if (v_isShared_5159_ == 0)
{
v___x_5161_ = v___x_5158_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5156_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runCheck___boxed(lean_object* v_lean_5164_, lean_object* v_lake_5165_, lean_object* v_projectDir_5166_, lean_object* v_a_5167_){
_start:
{
lean_object* v_res_5168_; 
v_res_5168_ = l_Lake_Check_runCheck(v_lean_5164_, v_lake_5165_, v_projectDir_5166_);
lean_dec_ref(v_lake_5165_);
return v_res_5168_;
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
