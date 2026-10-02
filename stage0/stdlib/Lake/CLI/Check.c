// Lean compiler output
// Module: Lake.CLI.Check
// Imports: public import Lake.Check.Axioms public import Lake.Check.Compare public import Lake.Config.InstallPath public import Lake.Util.Exit public import Lean.Data.Json.FromToJson import Lean.Environment import Lean.Replay import Init.Data.String.Search import Init.Data.String.TakeDrop import Init.Data.ToString.Macro import Init.System.IO import Init.System.Platform import Std.Internal.UV.System
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
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_prim_handle_read(lean_object*, size_t);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_get_stdout();
lean_object* lean_io_create_tempfile();
lean_object* lean_io_remove_file(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_uv_os_tmpdir();
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_String_compare___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* l_LeanExport_parseStream(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lake_Check_usedAxioms(lean_object*);
lean_object* l_Lake_Check_compareAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Check_checkAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_io_create_dir(lean_object*);
lean_object* l_String_toName(lean_object*);
extern uint8_t l_System_Platform_isLinux;
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_noSandbox_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_noSandbox_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_path_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_path_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ofNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_instDecidableEqModuleKind(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instDecidableEqModuleKind___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lake.CLI.Check.0.Lake.Check.ModuleKind.check"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__0_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__0_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "_private.Lake.CLI.Check.0.Lake.Check.ModuleKind.solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__2_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__2_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "_private.Lake.CLI.Check.0.Lake.Check.ModuleKind.challenge"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__4_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__4_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__5_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind___closed__0_value;
LEAN_EXPORT uint64_t l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind___closed__0_value;
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
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 310, .m_capacity = 310, .m_length = 309, .m_data = "` to sandbox the code it checks, and it was not found.\n\n  Install `bubblewrap` from your distribution and put `bwrap` on PATH, or set\n  COMPARATOR_BWRAP to its full path. It needs either unprivileged user\n  namespaces or a `bwrap` installed setuid root, which is how distributions\n  that disable them ship it."};
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
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "check"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__0_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "LAKE_CHECK_EXPORT"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__2_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__10_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__3_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__3_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Building and exporting"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " kernel rejected the solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " exited with "};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " kernel accepts the solution"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__3_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "export_file_path"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "permitted_axioms"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unpermitted_axiom_hard_error"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__12_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__8_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "num_threads"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "nat_extension"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__18_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__20 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__20_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "string_extension"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__21_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__19_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23_value;
static const lean_ctor_object l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__20_value),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__23_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24_value;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runKernels(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runKernels___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Your solution is okay!"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lake_Check_instFromJsonConfig_fromJson___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(67, 66, 102, 170, 71, 166, 115, 173)}};
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
static const lean_ctor_object l_Lake_Check_instReprConfig_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11_value)}};
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean paranoid"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "leanchecker-paranoid"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lean4lean"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__2_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--import"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nanoda"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "nanoda_bin"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "con-leche"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__6 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "con-ron"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__7 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "`: '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "' does not exist"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "' is a directory"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1;
static lean_once_cell_t l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leanexport"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leanchecker"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2_value;
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` needs `env` on PATH to build inside the sandbox"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` needs `git` on PATH to build inside the sandbox"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "` sandboxes the code it checks with `bwrap`, which needs Linux namespaces."};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "COMPARATOR_BWRAP"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "bwrap"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__8 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__8_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "WARNING: Sandbox disabled, this run is not trustworthy."};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__9 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__5_value)}};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0_value;
static const lean_string_object l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "cannot use `enable_nanoda` and `external_kernels` at the same time; register nanoda in the list instead"};
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__1 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__1_value;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_CLI_Check_0__Lake_Check_checkProject___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___closed__0 = (const lean_object*)&l___private_Lake_CLI_Check_0__Lake_Check_checkProject___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1;
static lean_once_cell_t l_Lake_Check_runComparator___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_runComparator___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Check_runComparator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "malformed configuration in '"};
static const lean_object* l_Lake_Check_runComparator___closed__0 = (const lean_object*)&l_Lake_Check_runComparator___closed__0_value;
static const lean_string_object l_Lake_Check_runComparator___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "': "};
static const lean_object* l_Lake_Check_runComparator___closed__1 = (const lean_object*)&l_Lake_Check_runComparator___closed__1_value;
static const lean_string_object l_Lake_Check_runComparator___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "comparator"};
static const lean_object* l_Lake_Check_runComparator___closed__2 = (const lean_object*)&l_Lake_Check_runComparator___closed__2_value;
static const lean_string_object l_Lake_Check_runComparator___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "--challenge-from-export"};
static const lean_object* l_Lake_Check_runComparator___closed__3 = (const lean_object*)&l_Lake_Check_runComparator___closed__3_value;
static const lean_string_object l_Lake_Check_runComparator___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "--solution-from-export"};
static const lean_object* l_Lake_Check_runComparator___closed__4 = (const lean_object*)&l_Lake_Check_runComparator___closed__4_value;
static const lean_string_object l_Lake_Check_runComparator___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "nothing to check: the configuration names no theorems or definitions"};
static const lean_object* l_Lake_Check_runComparator___closed__5 = (const lean_object*)&l_Lake_Check_runComparator___closed__5_value;
static const lean_string_object l_Lake_Check_runComparator___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "could not read the configuration: "};
static const lean_object* l_Lake_Check_runComparator___closed__6 = (const lean_object*)&l_Lake_Check_runComparator___closed__6_value;
static const lean_string_object l_Lake_Check_runComparator___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "comparator.json"};
static const lean_object* l_Lake_Check_runComparator___closed__7 = (const lean_object*)&l_Lake_Check_runComparator___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Check_runComparator(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runCheck(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
return v_k_7_;
}
else
{
lean_object* v_path_8_; lean_object* v___x_9_; 
v_path_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_path_8_);
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_path_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_noSandbox_elim___redArg(lean_object* v_t_22_, lean_object* v_noSandbox_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(v_t_22_, v_noSandbox_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_noSandbox_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_noSandbox_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(v_t_26_, v_noSandbox_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_path_elim___redArg(lean_object* v_t_30_, lean_object* v_path_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(v_t_30_, v_path_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_path_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_path_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(v_t_34_, v_path_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(uint8_t v_x_38_){
_start:
{
switch(v_x_38_)
{
case 0:
{
lean_object* v___x_39_; 
v___x_39_ = lean_unsigned_to_nat(0u);
return v___x_39_;
}
case 1:
{
lean_object* v___x_40_; 
v___x_40_ = lean_unsigned_to_nat(1u);
return v___x_40_;
}
default: 
{
lean_object* v___x_41_; 
v___x_41_ = lean_unsigned_to_nat(2u);
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx___boxed(lean_object* v_x_42_){
_start:
{
uint8_t v_x_boxed_43_; lean_object* v_res_44_; 
v_x_boxed_43_ = lean_unbox(v_x_42_);
v_res_44_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v_x_boxed_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___redArg(lean_object* v_k_45_){
_start:
{
lean_inc(v_k_45_);
return v_k_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___redArg___boxed(lean_object* v_k_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___redArg(v_k_46_);
lean_dec(v_k_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim(lean_object* v_motive_48_, lean_object* v_ctorIdx_49_, uint8_t v_t_50_, lean_object* v_h_51_, lean_object* v_k_52_){
_start:
{
lean_inc(v_k_52_);
return v_k_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___boxed(lean_object* v_motive_53_, lean_object* v_ctorIdx_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_k_57_){
_start:
{
uint8_t v_t_boxed_58_; lean_object* v_res_59_; 
v_t_boxed_58_ = lean_unbox(v_t_55_);
v_res_59_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim(v_motive_53_, v_ctorIdx_54_, v_t_boxed_58_, v_h_56_, v_k_57_);
lean_dec(v_k_57_);
lean_dec(v_ctorIdx_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim___redArg(lean_object* v_check_60_){
_start:
{
lean_inc(v_check_60_);
return v_check_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim___redArg___boxed(lean_object* v_check_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim___redArg(v_check_61_);
lean_dec(v_check_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim(lean_object* v_motive_63_, uint8_t v_t_64_, lean_object* v_h_65_, lean_object* v_check_66_){
_start:
{
lean_inc(v_check_66_);
return v_check_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim___boxed(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_check_70_){
_start:
{
uint8_t v_t_boxed_71_; lean_object* v_res_72_; 
v_t_boxed_71_ = lean_unbox(v_t_68_);
v_res_72_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim(v_motive_67_, v_t_boxed_71_, v_h_69_, v_check_70_);
lean_dec(v_check_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___redArg(lean_object* v_solution_73_){
_start:
{
lean_inc(v_solution_73_);
return v_solution_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___redArg___boxed(lean_object* v_solution_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___redArg(v_solution_74_);
lean_dec(v_solution_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim(lean_object* v_motive_76_, uint8_t v_t_77_, lean_object* v_h_78_, lean_object* v_solution_79_){
_start:
{
lean_inc(v_solution_79_);
return v_solution_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___boxed(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_solution_83_){
_start:
{
uint8_t v_t_boxed_84_; lean_object* v_res_85_; 
v_t_boxed_84_ = lean_unbox(v_t_81_);
v_res_85_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim(v_motive_80_, v_t_boxed_84_, v_h_82_, v_solution_83_);
lean_dec(v_solution_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___redArg(lean_object* v_challenge_86_){
_start:
{
lean_inc(v_challenge_86_);
return v_challenge_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___redArg___boxed(lean_object* v_challenge_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___redArg(v_challenge_87_);
lean_dec(v_challenge_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim(lean_object* v_motive_89_, uint8_t v_t_90_, lean_object* v_h_91_, lean_object* v_challenge_92_){
_start:
{
lean_inc(v_challenge_92_);
return v_challenge_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___boxed(lean_object* v_motive_93_, lean_object* v_t_94_, lean_object* v_h_95_, lean_object* v_challenge_96_){
_start:
{
uint8_t v_t_boxed_97_; lean_object* v_res_98_; 
v_t_boxed_97_ = lean_unbox(v_t_94_);
v_res_98_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim(v_motive_93_, v_t_boxed_97_, v_h_95_, v_challenge_96_);
lean_dec(v_challenge_96_);
return v_res_98_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ofNat(lean_object* v_n_99_){
_start:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_nat_dec_le(v_n_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_dec_le(v_n_99_, v___x_102_);
if (v___x_103_ == 0)
{
uint8_t v___x_104_; 
v___x_104_ = 2;
return v___x_104_;
}
else
{
uint8_t v___x_105_; 
v___x_105_ = 1;
return v___x_105_;
}
}
else
{
uint8_t v___x_106_; 
v___x_106_ = 0;
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ofNat___boxed(lean_object* v_n_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ofNat(v_n_107_);
lean_dec(v_n_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_instDecidableEqModuleKind(uint8_t v_x_110_, uint8_t v_y_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_112_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v_x_110_);
v___x_113_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v_y_111_);
v___x_114_ = lean_nat_dec_eq(v___x_112_, v___x_113_);
lean_dec(v___x_113_);
lean_dec(v___x_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instDecidableEqModuleKind___boxed(lean_object* v_x_115_, lean_object* v_y_116_){
_start:
{
uint8_t v_x_20__boxed_117_; uint8_t v_y_21__boxed_118_; uint8_t v_res_119_; lean_object* v_r_120_; 
v_x_20__boxed_117_ = lean_unbox(v_x_115_);
v_y_21__boxed_118_ = lean_unbox(v_y_116_);
v_res_119_ = l___private_Lake_CLI_Check_0__Lake_Check_instDecidableEqModuleKind(v_x_20__boxed_117_, v_y_21__boxed_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(2u);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_to_int(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr(uint8_t v_x_134_, lean_object* v_prec_135_){
_start:
{
lean_object* v___y_137_; lean_object* v___y_144_; lean_object* v___y_151_; 
switch(v_x_134_)
{
case 0:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(1024u);
v___x_158_ = lean_nat_dec_le(v___x_157_, v_prec_135_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6, &l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6);
v___y_137_ = v___x_159_;
goto v___jp_136_;
}
else
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7, &l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7);
v___y_137_ = v___x_160_;
goto v___jp_136_;
}
}
case 1:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(1024u);
v___x_162_ = lean_nat_dec_le(v___x_161_, v_prec_135_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6, &l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6);
v___y_144_ = v___x_163_;
goto v___jp_143_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7, &l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7);
v___y_144_ = v___x_164_;
goto v___jp_143_;
}
}
default: 
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(1024u);
v___x_166_ = lean_nat_dec_le(v___x_165_, v_prec_135_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6, &l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6);
v___y_151_ = v___x_167_;
goto v___jp_150_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7, &l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7);
v___y_151_ = v___x_168_;
goto v___jp_150_;
}
}
}
v___jp_136_:
{
lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_138_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__1));
lean_inc(v___y_137_);
v___x_139_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_139_, 0, v___y_137_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
v___x_140_ = 0;
v___x_141_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_141_, 0, v___x_139_);
lean_ctor_set_uint8(v___x_141_, sizeof(void*)*1, v___x_140_);
v___x_142_ = l_Repr_addAppParen(v___x_141_, v_prec_135_);
return v___x_142_;
}
v___jp_143_:
{
lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_145_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__3));
lean_inc(v___y_144_);
v___x_146_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_146_, 0, v___y_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = 0;
v___x_148_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*1, v___x_147_);
v___x_149_ = l_Repr_addAppParen(v___x_148_, v_prec_135_);
return v___x_149_;
}
v___jp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_152_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__5));
lean_inc(v___y_151_);
v___x_153_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_153_, 0, v___y_151_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = 0;
v___x_155_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*1, v___x_154_);
v___x_156_ = l_Repr_addAppParen(v___x_155_, v_prec_135_);
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___boxed(lean_object* v_x_169_, lean_object* v_prec_170_){
_start:
{
uint8_t v_x_171__boxed_171_; lean_object* v_res_172_; 
v_x_171__boxed_171_ = lean_unbox(v_x_169_);
v_res_172_ = l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr(v_x_171__boxed_171_, v_prec_170_);
lean_dec(v_prec_170_);
return v_res_172_;
}
}
LEAN_EXPORT uint64_t l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(uint8_t v_x_175_){
_start:
{
switch(v_x_175_)
{
case 0:
{
uint64_t v___x_176_; 
v___x_176_ = 0ULL;
return v___x_176_;
}
case 1:
{
uint64_t v___x_177_; 
v___x_177_ = 1ULL;
return v___x_177_;
}
default: 
{
uint64_t v___x_178_; 
v___x_178_ = 2ULL;
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash___boxed(lean_object* v_x_179_){
_start:
{
uint8_t v_x_40__boxed_180_; uint64_t v_res_181_; lean_object* v_r_182_; 
v_x_40__boxed_180_ = lean_unbox(v_x_179_);
v_res_181_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_x_40__boxed_180_);
v_r_182_ = lean_box_uint64(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels(lean_object* v_a_185_){
_start:
{
lean_object* v_externalKernels_187_; lean_object* v___x_188_; 
v_externalKernels_187_ = lean_ctor_get(v_a_185_, 15);
lean_inc(v_externalKernels_187_);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v_externalKernels_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels___boxed(lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels(v_a_189_);
lean_dec_ref(v_a_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getTheoremNames(lean_object* v_a_192_){
_start:
{
lean_object* v_theoremNames_194_; lean_object* v___x_195_; 
v_theoremNames_194_ = lean_ctor_get(v_a_192_, 3);
lean_inc_ref(v_theoremNames_194_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v_theoremNames_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getTheoremNames___boxed(lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lake_CLI_Check_0__Lake_Check_getTheoremNames(v_a_196_);
lean_dec_ref(v_a_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getDefinitionNames(lean_object* v_a_199_){
_start:
{
lean_object* v_definitionNames_201_; lean_object* v___x_202_; 
v_definitionNames_201_ = lean_ctor_get(v_a_199_, 4);
lean_inc_ref(v_definitionNames_201_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v_definitionNames_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getDefinitionNames___boxed(lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lake_CLI_Check_0__Lake_Check_getDefinitionNames(v_a_203_);
lean_dec_ref(v_a_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getProjectDir(lean_object* v_a_206_){
_start:
{
lean_object* v_projectDir_208_; lean_object* v___x_209_; 
v_projectDir_208_ = lean_ctor_get(v_a_206_, 0);
lean_inc_ref(v_projectDir_208_);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v_projectDir_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getProjectDir___boxed(lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lake_CLI_Check_0__Lake_Check_getProjectDir(v_a_210_);
lean_dec_ref(v_a_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLeanPrefix(lean_object* v_a_213_){
_start:
{
lean_object* v_leanPrefix_215_; lean_object* v___x_216_; 
v_leanPrefix_215_ = lean_ctor_get(v_a_213_, 6);
lean_inc_ref(v_leanPrefix_215_);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v_leanPrefix_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLeanPrefix___boxed(lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Lake_CLI_Check_0__Lake_Check_getLeanPrefix(v_a_217_);
lean_dec_ref(v_a_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLakeHome(lean_object* v_a_220_){
_start:
{
lean_object* v_lakeHome_222_; lean_object* v___x_223_; 
v_lakeHome_222_ = lean_ctor_get(v_a_220_, 11);
lean_inc_ref(v_lakeHome_222_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v_lakeHome_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLakeHome___boxed(lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lake_CLI_Check_0__Lake_Check_getLakeHome(v_a_224_);
lean_dec_ref(v_a_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule(lean_object* v_a_227_){
_start:
{
lean_object* v_challengeModule_229_; lean_object* v___x_230_; 
v_challengeModule_229_ = lean_ctor_get(v_a_227_, 1);
lean_inc(v_challengeModule_229_);
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v_challengeModule_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule___boxed(lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule(v_a_231_);
lean_dec_ref(v_a_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule(lean_object* v_a_234_){
_start:
{
lean_object* v_solutionModule_236_; lean_object* v___x_237_; 
v_solutionModule_236_ = lean_ctor_get(v_a_234_, 2);
lean_inc(v_solutionModule_236_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v_solutionModule_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule___boxed(lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule(v_a_238_);
lean_dec_ref(v_a_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms(lean_object* v_a_241_){
_start:
{
lean_object* v_legalAxioms_243_; lean_object* v___x_244_; 
v_legalAxioms_243_ = lean_ctor_get(v_a_241_, 5);
lean_inc_ref(v_legalAxioms_243_);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v_legalAxioms_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms___boxed(lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms(v_a_245_);
lean_dec_ref(v_a_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_whichExe(lean_object* v_exe_253_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_255_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v___x_256_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__1));
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_mk_empty_array_with_capacity(v___x_257_);
v___x_259_ = lean_array_push(v___x_258_, v_exe_253_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__2));
v___x_263_ = 1;
v___x_264_ = 0;
v___x_265_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_265_, 0, v___x_255_);
lean_ctor_set(v___x_265_, 1, v___x_256_);
lean_ctor_set(v___x_265_, 2, v___x_259_);
lean_ctor_set(v___x_265_, 3, v___x_260_);
lean_ctor_set(v___x_265_, 4, v___x_262_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*5, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*5 + 1, v___x_264_);
v___x_266_ = l_IO_Process_output(v___x_265_, v___x_260_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_291_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_291_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_291_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_291_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
uint32_t v_exitCode_271_; lean_object* v_stdout_272_; uint32_t v___x_273_; uint8_t v___x_274_; 
v_exitCode_271_ = lean_ctor_get_uint32(v_a_267_, sizeof(void*)*2);
v_stdout_272_ = lean_ctor_get(v_a_267_, 0);
lean_inc_ref(v_stdout_272_);
lean_dec(v_a_267_);
v___x_273_ = 0;
v___x_274_ = lean_uint32_dec_eq(v_exitCode_271_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_276_; 
lean_dec_ref(v_stdout_272_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_260_);
v___x_276_ = v___x_269_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_260_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_278_ = lean_string_utf8_byte_size(v_stdout_272_);
v___x_279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_279_, 0, v_stdout_272_);
lean_ctor_set(v___x_279_, 1, v___x_261_);
lean_ctor_set(v___x_279_, 2, v___x_278_);
v___x_280_ = l_String_Slice_trimAscii(v___x_279_);
v___x_281_ = l_String_Slice_toString(v___x_280_);
lean_dec_ref(v___x_280_);
v___x_282_ = lean_string_utf8_byte_size(v___x_281_);
v___x_283_ = lean_nat_dec_eq(v___x_282_, v___x_261_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_281_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_284_);
v___x_286_ = v___x_269_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
else
{
lean_object* v___x_289_; 
lean_dec_ref(v___x_281_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_260_);
v___x_289_ = v___x_269_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_260_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
else
{
lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v___x_266_, 0);
lean_dec(v_unused_299_);
v___x_293_ = v___x_266_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_dec(v___x_266_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 0);
lean_ctor_set(v___x_293_, 0, v___x_260_);
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_260_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_whichExe___boxed(lean_object* v_exe_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v_exe_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError(lean_object* v_cmd_306_, lean_object* v_exe_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_308_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_309_ = lean_string_append(v___x_308_, v_cmd_306_);
v___x_310_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__1));
v___x_311_ = lean_string_append(v___x_309_, v___x_310_);
v___x_312_ = lean_string_append(v___x_311_, v_exe_307_);
v___x_313_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__2));
v___x_314_ = lean_string_append(v___x_312_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___boxed(lean_object* v_cmd_315_, lean_object* v_exe_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError(v_cmd_315_, v_exe_316_);
lean_dec_ref(v_exe_316_);
lean_dec_ref(v_cmd_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1(lean_object* v_as_318_, size_t v_sz_319_, size_t v_i_320_, lean_object* v_b_321_){
_start:
{
lean_object* v_a_324_; uint8_t v___x_328_; 
v___x_328_ = lean_usize_dec_lt(v_i_320_, v_sz_319_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v_b_321_);
return v___x_329_;
}
else
{
lean_object* v_a_330_; lean_object* v___x_331_; 
v_a_330_ = lean_array_uget_borrowed(v_as_318_, v_i_320_);
v___x_331_ = lean_io_getenv(v_a_330_);
if (lean_obj_tag(v___x_331_) == 1)
{
lean_object* v_val_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_val_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v___x_331_, 1);
lean_inc(v_a_330_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v_a_330_);
lean_ctor_set(v___x_333_, 1, v_val_332_);
v___x_334_ = lean_array_push(v_b_321_, v___x_333_);
v_a_324_ = v___x_334_;
goto v___jp_323_;
}
else
{
lean_dec(v___x_331_);
v_a_324_ = v_b_321_;
goto v___jp_323_;
}
}
v___jp_323_:
{
size_t v___x_325_; size_t v___x_326_; 
v___x_325_ = ((size_t)1ULL);
v___x_326_ = lean_usize_add(v_i_320_, v___x_325_);
v_i_320_ = v___x_326_;
v_b_321_ = v_a_324_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1___boxed(lean_object* v_as_335_, lean_object* v_sz_336_, lean_object* v_i_337_, lean_object* v_b_338_, lean_object* v___y_339_){
_start:
{
size_t v_sz_boxed_340_; size_t v_i_boxed_341_; lean_object* v_res_342_; 
v_sz_boxed_340_ = lean_unbox_usize(v_sz_336_);
lean_dec(v_sz_336_);
v_i_boxed_341_ = lean_unbox_usize(v_i_337_);
lean_dec(v_i_337_);
v_res_342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1(v_as_335_, v_sz_boxed_340_, v_i_boxed_341_, v_b_338_);
lean_dec_ref(v_as_335_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(lean_object* v_fst_343_, lean_object* v_as_344_, size_t v_i_345_, size_t v_stop_346_, lean_object* v_b_347_){
_start:
{
lean_object* v___y_349_; uint8_t v___x_353_; 
v___x_353_ = lean_usize_dec_eq(v_i_345_, v_stop_346_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v_fst_355_; uint8_t v___x_356_; 
v___x_354_ = lean_array_uget_borrowed(v_as_344_, v_i_345_);
v_fst_355_ = lean_ctor_get(v___x_354_, 0);
v___x_356_ = lean_string_dec_eq(v_fst_355_, v_fst_343_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
lean_inc(v___x_354_);
v___x_357_ = lean_array_push(v_b_347_, v___x_354_);
v___y_349_ = v___x_357_;
goto v___jp_348_;
}
else
{
v___y_349_ = v_b_347_;
goto v___jp_348_;
}
}
else
{
return v_b_347_;
}
v___jp_348_:
{
size_t v___x_350_; size_t v___x_351_; 
v___x_350_ = ((size_t)1ULL);
v___x_351_ = lean_usize_add(v_i_345_, v___x_350_);
v_i_345_ = v___x_351_;
v_b_347_ = v___y_349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0___boxed(lean_object* v_fst_358_, lean_object* v_as_359_, lean_object* v_i_360_, lean_object* v_stop_361_, lean_object* v_b_362_){
_start:
{
size_t v_i_boxed_363_; size_t v_stop_boxed_364_; lean_object* v_res_365_; 
v_i_boxed_363_ = lean_unbox_usize(v_i_360_);
lean_dec(v_i_360_);
v_stop_boxed_364_ = lean_unbox_usize(v_stop_361_);
lean_dec(v_stop_361_);
v_res_365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(v_fst_358_, v_as_359_, v_i_boxed_363_, v_stop_boxed_364_, v_b_362_);
lean_dec_ref(v_as_359_);
lean_dec_ref(v_fst_358_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2(lean_object* v_as_368_, size_t v_sz_369_, size_t v_i_370_, lean_object* v_b_371_){
_start:
{
lean_object* v_a_374_; uint8_t v___x_378_; 
v___x_378_ = lean_usize_dec_lt(v_i_370_, v_sz_369_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v_b_371_);
return v___x_379_;
}
else
{
lean_object* v_a_380_; lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_404_; 
v_a_380_ = lean_array_uget(v_as_368_, v_i_370_);
v_fst_381_ = lean_ctor_get(v_a_380_, 0);
v_snd_382_ = lean_ctor_get(v_a_380_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_a_380_);
if (v_isSharedCheck_404_ == 0)
{
v___x_384_ = v_a_380_;
v_isShared_385_ = v_isSharedCheck_404_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_snd_382_);
lean_inc(v_fst_381_);
lean_dec(v_a_380_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_404_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___y_387_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_array_get_size(v_b_371_);
v___x_395_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___closed__0));
v___x_396_ = lean_nat_dec_lt(v___x_393_, v___x_394_);
if (v___x_396_ == 0)
{
lean_dec_ref(v_b_371_);
v___y_387_ = v___x_395_;
goto v___jp_386_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = lean_nat_dec_le(v___x_394_, v___x_394_);
if (v___x_397_ == 0)
{
if (v___x_396_ == 0)
{
lean_dec_ref(v_b_371_);
v___y_387_ = v___x_395_;
goto v___jp_386_;
}
else
{
size_t v___x_398_; size_t v___x_399_; lean_object* v___x_400_; 
v___x_398_ = ((size_t)0ULL);
v___x_399_ = lean_usize_of_nat(v___x_394_);
v___x_400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(v_fst_381_, v_b_371_, v___x_398_, v___x_399_, v___x_395_);
lean_dec_ref(v_b_371_);
v___y_387_ = v___x_400_;
goto v___jp_386_;
}
}
else
{
size_t v___x_401_; size_t v___x_402_; lean_object* v___x_403_; 
v___x_401_ = ((size_t)0ULL);
v___x_402_ = lean_usize_of_nat(v___x_394_);
v___x_403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(v_fst_381_, v_b_371_, v___x_401_, v___x_402_, v___x_395_);
lean_dec_ref(v_b_371_);
v___y_387_ = v___x_403_;
goto v___jp_386_;
}
}
v___jp_386_:
{
if (lean_obj_tag(v_snd_382_) == 1)
{
lean_object* v_val_388_; lean_object* v___x_390_; 
v_val_388_ = lean_ctor_get(v_snd_382_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v_snd_382_, 1);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 1, v_val_388_);
v___x_390_ = v___x_384_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_fst_381_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_val_388_);
v___x_390_ = v_reuseFailAlloc_392_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; 
v___x_391_ = lean_array_push(v___y_387_, v___x_390_);
v_a_374_ = v___x_391_;
goto v___jp_373_;
}
}
else
{
lean_del_object(v___x_384_);
lean_dec(v_snd_382_);
lean_dec(v_fst_381_);
v_a_374_ = v___y_387_;
goto v___jp_373_;
}
}
}
}
v___jp_373_:
{
size_t v___x_375_; size_t v___x_376_; 
v___x_375_ = ((size_t)1ULL);
v___x_376_ = lean_usize_add(v_i_370_, v___x_375_);
v_i_370_ = v___x_376_;
v_b_371_ = v_a_374_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___boxed(lean_object* v_as_405_, lean_object* v_sz_406_, lean_object* v_i_407_, lean_object* v_b_408_, lean_object* v___y_409_){
_start:
{
size_t v_sz_boxed_410_; size_t v_i_boxed_411_; lean_object* v_res_412_; 
v_sz_boxed_410_ = lean_unbox_usize(v_sz_406_);
lean_dec(v_sz_406_);
v_i_boxed_411_ = lean_unbox_usize(v_i_407_);
lean_dec(v_i_407_);
v_res_412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2(v_as_405_, v_sz_boxed_410_, v_i_boxed_411_, v_b_408_);
lean_dec_ref(v_as_405_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(lean_object* v_spawnArgs_413_){
_start:
{
lean_object* v_envPass_415_; lean_object* v_envOverride_416_; lean_object* v_env_417_; size_t v_sz_418_; size_t v___x_419_; lean_object* v___x_420_; 
v_envPass_415_ = lean_ctor_get(v_spawnArgs_413_, 2);
v_envOverride_416_ = lean_ctor_get(v_spawnArgs_413_, 3);
v_env_417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___closed__0));
v_sz_418_ = lean_array_size(v_envPass_415_);
v___x_419_ = ((size_t)0ULL);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1(v_envPass_415_, v_sz_418_, v___x_419_, v_env_417_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; size_t v_sz_422_; lean_object* v___x_423_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_420_, 1);
v_sz_422_ = lean_array_size(v_envOverride_416_);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2(v_envOverride_416_, v_sz_422_, v___x_419_, v_a_421_);
return v___x_423_;
}
else
{
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv___boxed(lean_object* v_spawnArgs_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(v_spawnArgs_424_);
lean_dec_ref(v_spawnArgs_424_);
return v_res_426_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_428_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_429_ = lean_unsigned_to_nat(2u);
v___x_430_ = lean_mk_empty_array_with_capacity(v___x_429_);
v___x_431_ = lean_array_push(v___x_430_, v___x_428_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(lean_object* v_as_432_, size_t v_i_433_, size_t v_stop_434_, lean_object* v_b_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = lean_usize_dec_eq(v_i_433_, v_stop_434_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; size_t v___x_441_; size_t v___x_442_; 
v___x_437_ = lean_array_uget_borrowed(v_as_432_, v_i_433_);
v___x_438_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1);
lean_inc(v___x_437_);
v___x_439_ = lean_array_push(v___x_438_, v___x_437_);
v___x_440_ = l_Array_append___redArg(v_b_435_, v___x_439_);
lean_dec_ref(v___x_439_);
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_add(v_i_433_, v___x_441_);
v_i_433_ = v___x_442_;
v_b_435_ = v___x_440_;
goto _start;
}
else
{
return v_b_435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___boxed(lean_object* v_as_444_, lean_object* v_i_445_, lean_object* v_stop_446_, lean_object* v_b_447_){
_start:
{
size_t v_i_boxed_448_; size_t v_stop_boxed_449_; lean_object* v_res_450_; 
v_i_boxed_448_ = lean_unbox_usize(v_i_445_);
lean_dec(v_i_445_);
v_stop_boxed_449_ = lean_unbox_usize(v_stop_446_);
lean_dec(v_stop_446_);
v_res_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(v_as_444_, v_i_boxed_448_, v_stop_boxed_449_, v_b_447_);
lean_dec_ref(v_as_444_);
return v_res_450_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__0));
v___x_453_ = lean_unsigned_to_nat(3u);
v___x_454_ = lean_mk_empty_array_with_capacity(v___x_453_);
v___x_455_ = lean_array_push(v___x_454_, v___x_452_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(lean_object* v_as_456_, size_t v_i_457_, size_t v_stop_458_, lean_object* v_b_459_){
_start:
{
uint8_t v___x_460_; 
v___x_460_ = lean_usize_dec_eq(v_i_457_, v_stop_458_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; size_t v___x_466_; size_t v___x_467_; 
v___x_461_ = lean_array_uget_borrowed(v_as_456_, v_i_457_);
v___x_462_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1);
lean_inc_n(v___x_461_, 2);
v___x_463_ = lean_array_push(v___x_462_, v___x_461_);
v___x_464_ = lean_array_push(v___x_463_, v___x_461_);
v___x_465_ = l_Array_append___redArg(v_b_459_, v___x_464_);
lean_dec_ref(v___x_464_);
v___x_466_ = ((size_t)1ULL);
v___x_467_ = lean_usize_add(v_i_457_, v___x_466_);
v_i_457_ = v___x_467_;
v_b_459_ = v___x_465_;
goto _start;
}
else
{
return v_b_459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___boxed(lean_object* v_as_469_, lean_object* v_i_470_, lean_object* v_stop_471_, lean_object* v_b_472_){
_start:
{
size_t v_i_boxed_473_; size_t v_stop_boxed_474_; lean_object* v_res_475_; 
v_i_boxed_473_ = lean_unbox_usize(v_i_470_);
lean_dec(v_i_470_);
v_stop_boxed_474_ = lean_unbox_usize(v_stop_471_);
lean_dec(v_stop_471_);
v_res_475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(v_as_469_, v_i_boxed_473_, v_stop_boxed_474_, v_b_472_);
lean_dec_ref(v_as_469_);
return v_res_475_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__0));
v___x_478_ = lean_unsigned_to_nat(3u);
v___x_479_ = lean_mk_empty_array_with_capacity(v___x_478_);
v___x_480_ = lean_array_push(v___x_479_, v___x_477_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(lean_object* v_as_481_, size_t v_i_482_, size_t v_stop_483_, lean_object* v_b_484_){
_start:
{
uint8_t v___x_485_; 
v___x_485_ = lean_usize_dec_eq(v_i_482_, v_stop_483_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; size_t v___x_491_; size_t v___x_492_; 
v___x_486_ = lean_array_uget_borrowed(v_as_481_, v_i_482_);
v___x_487_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1);
lean_inc_n(v___x_486_, 2);
v___x_488_ = lean_array_push(v___x_487_, v___x_486_);
v___x_489_ = lean_array_push(v___x_488_, v___x_486_);
v___x_490_ = l_Array_append___redArg(v_b_484_, v___x_489_);
lean_dec_ref(v___x_489_);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_482_, v___x_491_);
v_i_482_ = v___x_492_;
v_b_484_ = v___x_490_;
goto _start;
}
else
{
return v_b_484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___boxed(lean_object* v_as_494_, lean_object* v_i_495_, lean_object* v_stop_496_, lean_object* v_b_497_){
_start:
{
size_t v_i_boxed_498_; size_t v_stop_boxed_499_; lean_object* v_res_500_; 
v_i_boxed_498_ = lean_unbox_usize(v_i_495_);
lean_dec(v_i_495_);
v_stop_boxed_499_ = lean_unbox_usize(v_stop_496_);
lean_dec(v_stop_496_);
v_res_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(v_as_494_, v_i_boxed_498_, v_stop_boxed_499_, v_b_497_);
lean_dec_ref(v_as_494_);
return v_res_500_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__0));
v___x_503_ = lean_unsigned_to_nat(3u);
v___x_504_ = lean_mk_empty_array_with_capacity(v___x_503_);
v___x_505_ = lean_array_push(v___x_504_, v___x_502_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(lean_object* v_as_506_, size_t v_i_507_, size_t v_stop_508_, lean_object* v_b_509_){
_start:
{
uint8_t v___x_510_; 
v___x_510_ = lean_usize_dec_eq(v_i_507_, v_stop_508_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v_fst_512_; lean_object* v_snd_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; size_t v___x_518_; size_t v___x_519_; 
v___x_511_ = lean_array_uget_borrowed(v_as_506_, v_i_507_);
v_fst_512_ = lean_ctor_get(v___x_511_, 0);
v_snd_513_ = lean_ctor_get(v___x_511_, 1);
v___x_514_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1);
lean_inc(v_fst_512_);
v___x_515_ = lean_array_push(v___x_514_, v_fst_512_);
lean_inc(v_snd_513_);
v___x_516_ = lean_array_push(v___x_515_, v_snd_513_);
v___x_517_ = l_Array_append___redArg(v_b_509_, v___x_516_);
lean_dec_ref(v___x_516_);
v___x_518_ = ((size_t)1ULL);
v___x_519_ = lean_usize_add(v_i_507_, v___x_518_);
v_i_507_ = v___x_519_;
v_b_509_ = v___x_517_;
goto _start;
}
else
{
return v_b_509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___boxed(lean_object* v_as_521_, lean_object* v_i_522_, lean_object* v_stop_523_, lean_object* v_b_524_){
_start:
{
size_t v_i_boxed_525_; size_t v_stop_boxed_526_; lean_object* v_res_527_; 
v_i_boxed_525_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_stop_boxed_526_ = lean_unbox_usize(v_stop_523_);
lean_dec(v_stop_523_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(v_as_521_, v_i_boxed_525_, v_stop_boxed_526_, v_b_524_);
lean_dec_ref(v_as_521_);
return v_res_527_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__0));
v___x_531_ = lean_unsigned_to_nat(18u);
v___x_532_ = lean_mk_empty_array_with_capacity(v___x_531_);
v___x_533_ = lean_array_push(v___x_532_, v___x_530_);
return v___x_533_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__0));
v___x_535_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2);
v___x_536_ = lean_array_push(v___x_535_, v___x_534_);
return v___x_536_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__0));
v___x_538_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3);
v___x_539_ = lean_array_push(v___x_538_, v___x_537_);
return v___x_539_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_541_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4);
v___x_542_ = lean_array_push(v___x_541_, v___x_540_);
return v___x_542_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__1));
v___x_544_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5);
v___x_545_ = lean_array_push(v___x_544_, v___x_543_);
return v___x_545_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_547_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6);
v___x_548_ = lean_array_push(v___x_547_, v___x_546_);
return v___x_548_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_550_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__8));
v___x_551_ = lean_unsigned_to_nat(2u);
v___x_552_ = lean_mk_empty_array_with_capacity(v___x_551_);
v___x_553_ = lean_array_push(v___x_552_, v___x_550_);
return v___x_553_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_555_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__10));
v___x_556_ = lean_unsigned_to_nat(2u);
v___x_557_ = lean_mk_empty_array_with_capacity(v___x_556_);
v___x_558_ = lean_array_push(v___x_557_, v___x_555_);
return v___x_558_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__12));
v___x_561_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7);
v___x_562_ = lean_array_push(v___x_561_, v___x_560_);
return v___x_562_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_564_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13);
v___x_565_ = lean_array_push(v___x_564_, v___x_563_);
return v___x_565_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__15));
v___x_599_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14);
v___x_600_ = lean_array_push(v___x_599_, v___x_598_);
return v___x_600_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_602_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31);
v___x_603_ = lean_array_push(v___x_602_, v___x_601_);
return v___x_603_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__16));
v___x_605_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32);
v___x_606_ = lean_array_push(v___x_605_, v___x_604_);
return v___x_606_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__17));
v___x_608_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33);
v___x_609_ = lean_array_push(v___x_608_, v___x_607_);
return v___x_609_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__18));
v___x_611_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34);
v___x_612_ = lean_array_push(v___x_611_, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__26));
v___x_614_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35);
v___x_615_ = lean_array_push(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_616_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__27));
v___x_617_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36);
v___x_618_ = lean_array_push(v___x_617_, v___x_616_);
return v___x_618_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__28));
v___x_620_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37);
v___x_621_ = lean_array_push(v___x_620_, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__29));
v___x_623_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38);
v___x_624_ = lean_array_push(v___x_623_, v___x_622_);
return v___x_624_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v_args_627_; 
v___x_625_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__30));
v___x_626_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39);
v_args_627_ = lean_array_push(v___x_626_, v___x_625_);
return v_args_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs(lean_object* v_spawnArgs_628_, lean_object* v_env_629_, lean_object* v_projectDir_630_){
_start:
{
lean_object* v_cmd_631_; lean_object* v_args_632_; lean_object* v_readablePaths_633_; lean_object* v_writablePaths_634_; lean_object* v_tmpfsPaths_635_; uint8_t v_network_636_; lean_object* v_cwd_637_; lean_object* v___y_639_; lean_object* v___y_645_; lean_object* v___y_654_; lean_object* v_args_659_; lean_object* v___x_660_; lean_object* v___y_662_; lean_object* v___y_673_; lean_object* v___y_684_; lean_object* v___x_694_; uint8_t v___x_695_; 
v_cmd_631_ = lean_ctor_get(v_spawnArgs_628_, 0);
lean_inc_ref(v_cmd_631_);
v_args_632_ = lean_ctor_get(v_spawnArgs_628_, 1);
lean_inc_ref(v_args_632_);
v_readablePaths_633_ = lean_ctor_get(v_spawnArgs_628_, 4);
lean_inc_ref(v_readablePaths_633_);
v_writablePaths_634_ = lean_ctor_get(v_spawnArgs_628_, 5);
lean_inc_ref(v_writablePaths_634_);
v_tmpfsPaths_635_ = lean_ctor_get(v_spawnArgs_628_, 6);
lean_inc_ref(v_tmpfsPaths_635_);
v_network_636_ = lean_ctor_get_uint8(v_spawnArgs_628_, sizeof(void*)*8);
v_cwd_637_ = lean_ctor_get(v_spawnArgs_628_, 7);
lean_inc(v_cwd_637_);
lean_dec_ref(v_spawnArgs_628_);
v_args_659_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_array_get_size(v_tmpfsPaths_635_);
v___x_695_ = lean_nat_dec_lt(v___x_660_, v___x_694_);
if (v___x_695_ == 0)
{
lean_dec_ref(v_tmpfsPaths_635_);
v___y_684_ = v_args_659_;
goto v___jp_683_;
}
else
{
uint8_t v___x_696_; 
v___x_696_ = lean_nat_dec_le(v___x_694_, v___x_694_);
if (v___x_696_ == 0)
{
if (v___x_695_ == 0)
{
lean_dec_ref(v_tmpfsPaths_635_);
v___y_684_ = v_args_659_;
goto v___jp_683_;
}
else
{
size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; 
v___x_697_ = ((size_t)0ULL);
v___x_698_ = lean_usize_of_nat(v___x_694_);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(v_tmpfsPaths_635_, v___x_697_, v___x_698_, v_args_659_);
lean_dec_ref(v_tmpfsPaths_635_);
v___y_684_ = v___x_699_;
goto v___jp_683_;
}
}
else
{
size_t v___x_700_; size_t v___x_701_; lean_object* v___x_702_; 
v___x_700_ = ((size_t)0ULL);
v___x_701_ = lean_usize_of_nat(v___x_694_);
v___x_702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(v_tmpfsPaths_635_, v___x_700_, v___x_701_, v_args_659_);
lean_dec_ref(v_tmpfsPaths_635_);
v___y_684_ = v___x_702_;
goto v___jp_683_;
}
}
v___jp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_640_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9);
v___x_641_ = lean_array_push(v___x_640_, v_cmd_631_);
v___x_642_ = l_Array_append___redArg(v___y_639_, v___x_641_);
lean_dec_ref(v___x_641_);
v___x_643_ = l_Array_append___redArg(v___x_642_, v_args_632_);
lean_dec_ref(v_args_632_);
return v___x_643_;
}
v___jp_644_:
{
if (lean_obj_tag(v_cwd_637_) == 1)
{
lean_object* v_val_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec_ref(v_projectDir_630_);
v_val_646_ = lean_ctor_get(v_cwd_637_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v_cwd_637_, 1);
v___x_647_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11);
v___x_648_ = lean_array_push(v___x_647_, v_val_646_);
v___x_649_ = l_Array_append___redArg(v___y_645_, v___x_648_);
lean_dec_ref(v___x_648_);
v___y_639_ = v___x_649_;
goto v___jp_638_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec(v_cwd_637_);
v___x_650_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11);
v___x_651_ = lean_array_push(v___x_650_, v_projectDir_630_);
v___x_652_ = l_Array_append___redArg(v___y_645_, v___x_651_);
lean_dec_ref(v___x_651_);
v___y_639_ = v___x_652_;
goto v___jp_638_;
}
}
v___jp_653_:
{
lean_object* v___x_655_; lean_object* v_args_656_; 
v___x_655_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__23));
v_args_656_ = l_Array_append___redArg(v___y_654_, v___x_655_);
if (v_network_636_ == 0)
{
v___y_645_ = v_args_656_;
goto v___jp_644_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__25));
v___x_658_ = l_Array_append___redArg(v_args_656_, v___x_657_);
v___y_645_ = v___x_658_;
goto v___jp_644_;
}
}
v___jp_661_:
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = lean_array_get_size(v_env_629_);
v___x_664_ = lean_nat_dec_lt(v___x_660_, v___x_663_);
if (v___x_664_ == 0)
{
v___y_654_ = v___y_662_;
goto v___jp_653_;
}
else
{
uint8_t v___x_665_; 
v___x_665_ = lean_nat_dec_le(v___x_663_, v___x_663_);
if (v___x_665_ == 0)
{
if (v___x_664_ == 0)
{
v___y_654_ = v___y_662_;
goto v___jp_653_;
}
else
{
size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
v___x_666_ = ((size_t)0ULL);
v___x_667_ = lean_usize_of_nat(v___x_663_);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(v_env_629_, v___x_666_, v___x_667_, v___y_662_);
v___y_654_ = v___x_668_;
goto v___jp_653_;
}
}
else
{
size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; 
v___x_669_ = ((size_t)0ULL);
v___x_670_ = lean_usize_of_nat(v___x_663_);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(v_env_629_, v___x_669_, v___x_670_, v___y_662_);
v___y_654_ = v___x_671_;
goto v___jp_653_;
}
}
}
v___jp_672_:
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = lean_array_get_size(v_writablePaths_634_);
v___x_675_ = lean_nat_dec_lt(v___x_660_, v___x_674_);
if (v___x_675_ == 0)
{
lean_dec_ref(v_writablePaths_634_);
v___y_662_ = v___y_673_;
goto v___jp_661_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = lean_nat_dec_le(v___x_674_, v___x_674_);
if (v___x_676_ == 0)
{
if (v___x_675_ == 0)
{
lean_dec_ref(v_writablePaths_634_);
v___y_662_ = v___y_673_;
goto v___jp_661_;
}
else
{
size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; 
v___x_677_ = ((size_t)0ULL);
v___x_678_ = lean_usize_of_nat(v___x_674_);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(v_writablePaths_634_, v___x_677_, v___x_678_, v___y_673_);
lean_dec_ref(v_writablePaths_634_);
v___y_662_ = v___x_679_;
goto v___jp_661_;
}
}
else
{
size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v___x_680_ = ((size_t)0ULL);
v___x_681_ = lean_usize_of_nat(v___x_674_);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(v_writablePaths_634_, v___x_680_, v___x_681_, v___y_673_);
lean_dec_ref(v_writablePaths_634_);
v___y_662_ = v___x_682_;
goto v___jp_661_;
}
}
}
v___jp_683_:
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_array_get_size(v_readablePaths_633_);
v___x_686_ = lean_nat_dec_lt(v___x_660_, v___x_685_);
if (v___x_686_ == 0)
{
lean_dec_ref(v_readablePaths_633_);
v___y_673_ = v___y_684_;
goto v___jp_672_;
}
else
{
uint8_t v___x_687_; 
v___x_687_ = lean_nat_dec_le(v___x_685_, v___x_685_);
if (v___x_687_ == 0)
{
if (v___x_686_ == 0)
{
lean_dec_ref(v_readablePaths_633_);
v___y_673_ = v___y_684_;
goto v___jp_672_;
}
else
{
size_t v___x_688_; size_t v___x_689_; lean_object* v___x_690_; 
v___x_688_ = ((size_t)0ULL);
v___x_689_ = lean_usize_of_nat(v___x_685_);
v___x_690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(v_readablePaths_633_, v___x_688_, v___x_689_, v___y_684_);
lean_dec_ref(v_readablePaths_633_);
v___y_673_ = v___x_690_;
goto v___jp_672_;
}
}
else
{
size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v___x_691_ = ((size_t)0ULL);
v___x_692_ = lean_usize_of_nat(v___x_685_);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(v_readablePaths_633_, v___x_691_, v___x_692_, v___y_684_);
lean_dec_ref(v_readablePaths_633_);
v___y_673_ = v___x_693_;
goto v___jp_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___boxed(lean_object* v_spawnArgs_703_, lean_object* v_env_704_, lean_object* v_projectDir_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs(v_spawnArgs_703_, v_env_704_, v_projectDir_705_);
lean_dec_ref(v_env_704_);
return v_res_706_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_708_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__0));
v___x_709_ = lean_unsigned_to_nat(2u);
v___x_710_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___x_711_ = lean_array_push(v___x_710_, v___x_708_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(lean_object* v_spawnArgs_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_whichSandbox_715_; 
v_whichSandbox_715_ = lean_ctor_get(v_a_713_, 9);
if (lean_obj_tag(v_whichSandbox_715_) == 0)
{
lean_object* v_projectDir_716_; lean_object* v___x_717_; lean_object* v_cmd_718_; lean_object* v_args_719_; lean_object* v_envOverride_720_; lean_object* v_cwd_721_; lean_object* v___y_723_; 
v_projectDir_716_ = lean_ctor_get(v_a_713_, 0);
v___x_717_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v_cmd_718_ = lean_ctor_get(v_spawnArgs_712_, 0);
lean_inc_ref(v_cmd_718_);
v_args_719_ = lean_ctor_get(v_spawnArgs_712_, 1);
lean_inc_ref(v_args_719_);
v_envOverride_720_ = lean_ctor_get(v_spawnArgs_712_, 3);
lean_inc_ref(v_envOverride_720_);
v_cwd_721_ = lean_ctor_get(v_spawnArgs_712_, 7);
lean_inc(v_cwd_721_);
lean_dec_ref(v_spawnArgs_712_);
if (lean_obj_tag(v_cwd_721_) == 1)
{
v___y_723_ = v_cwd_721_;
goto v___jp_722_;
}
else
{
lean_object* v___x_728_; 
lean_dec(v_cwd_721_);
lean_inc_ref(v_projectDir_716_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_projectDir_716_);
v___y_723_ = v___x_728_;
goto v___jp_722_;
}
v___jp_722_:
{
uint8_t v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_724_ = 1;
v___x_725_ = 0;
v___x_726_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_726_, 0, v___x_717_);
lean_ctor_set(v___x_726_, 1, v_cmd_718_);
lean_ctor_set(v___x_726_, 2, v_args_719_);
lean_ctor_set(v___x_726_, 3, v___y_723_);
lean_ctor_set(v___x_726_, 4, v_envOverride_720_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*5, v___x_724_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*5 + 1, v___x_725_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
else
{
lean_object* v_projectDir_729_; lean_object* v_whichEnvBin_730_; lean_object* v_path_731_; lean_object* v___x_732_; 
v_projectDir_729_ = lean_ctor_get(v_a_713_, 0);
v_whichEnvBin_730_ = lean_ctor_get(v_a_713_, 14);
v_path_731_ = lean_ctor_get(v_whichSandbox_715_, 0);
v___x_732_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(v_spawnArgs_712_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_750_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_750_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_750_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_750_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_737_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v___x_738_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1, &l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1);
lean_inc_ref(v_path_731_);
v___x_739_ = lean_array_push(v___x_738_, v_path_731_);
lean_inc_ref_n(v_projectDir_729_, 2);
v___x_740_ = l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs(v_spawnArgs_712_, v_a_733_, v_projectDir_729_);
lean_dec(v_a_733_);
v___x_741_ = l_Array_append___redArg(v___x_739_, v___x_740_);
lean_dec_ref(v___x_740_);
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v_projectDir_729_);
v___x_743_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__2));
v___x_744_ = 1;
v___x_745_ = 0;
lean_inc_ref(v_whichEnvBin_730_);
v___x_746_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_746_, 0, v___x_737_);
lean_ctor_set(v___x_746_, 1, v_whichEnvBin_730_);
lean_ctor_set(v___x_746_, 2, v___x_741_);
lean_ctor_set(v___x_746_, 3, v___x_742_);
lean_ctor_set(v___x_746_, 4, v___x_743_);
lean_ctor_set_uint8(v___x_746_, sizeof(void*)*5, v___x_744_);
lean_ctor_set_uint8(v___x_746_, sizeof(void*)*5 + 1, v___x_745_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_746_);
v___x_748_ = v___x_735_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v_spawnArgs_712_);
v_a_751_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_732_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_732_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___boxed(lean_object* v_spawnArgs_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_759_, v_a_760_);
lean_dec_ref(v_a_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(lean_object* v_handle_763_, lean_object* v_child_764_){
_start:
{
lean_object* v_stdout_766_; size_t v___x_767_; lean_object* v___x_768_; 
v_stdout_766_ = lean_ctor_get(v_child_764_, 1);
v___x_767_ = ((size_t)4096ULL);
v___x_768_ = lean_io_prim_handle_read(v_stdout_766_, v___x_767_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; uint8_t v___x_770_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = l_ByteArray_isEmpty(v_a_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
v___x_771_ = lean_io_prim_handle_write(v_handle_763_, v_a_769_);
lean_dec(v_a_769_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_dec_ref_known(v___x_771_, 1);
goto _start;
}
else
{
return v___x_771_;
}
}
else
{
lean_object* v___x_773_; 
lean_dec(v_a_769_);
v___x_773_ = lean_io_prim_handle_flush(v_handle_763_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_781_; 
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v___x_773_, 0);
lean_dec(v_unused_782_);
v___x_775_ = v___x_773_;
v_isShared_776_ = v_isSharedCheck_781_;
goto v_resetjp_774_;
}
else
{
lean_dec(v___x_773_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_781_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = lean_box(0);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_777_);
v___x_779_ = v___x_775_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
else
{
return v___x_773_;
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
v_a_783_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_768_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_768_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg___boxed(lean_object* v_handle_791_, lean_object* v_child_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(v_handle_791_, v_child_792_);
lean_dec_ref(v_child_792_);
lean_dec(v_handle_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop(lean_object* v_handle_795_, lean_object* v_args_796_, lean_object* v_child_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(v_handle_795_, v_child_797_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___boxed(lean_object* v_handle_800_, lean_object* v_args_801_, lean_object* v_child_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop(v_handle_800_, v_args_801_, v_child_802_);
lean_dec_ref(v_child_802_);
lean_dec_ref(v_args_801_);
lean_dec(v_handle_800_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(lean_object* v_e_805_){
_start:
{
if (lean_obj_tag(v_e_805_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_816_; 
v_a_807_ = lean_ctor_get(v_e_805_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v_e_805_);
if (v_isSharedCheck_816_ == 0)
{
v___x_809_ = v_e_805_;
v_isShared_810_ = v_isSharedCheck_816_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v_e_805_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_816_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_811_ = lean_io_error_to_string(v_a_807_);
v___x_812_ = lean_mk_io_user_error(v___x_811_);
if (v_isShared_810_ == 0)
{
lean_ctor_set_tag(v___x_809_, 1);
lean_ctor_set(v___x_809_, 0, v___x_812_);
v___x_814_ = v___x_809_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
v_a_817_ = lean_ctor_get(v_e_805_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_e_805_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v_e_805_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v_e_805_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 0);
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg___boxed(lean_object* v_e_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(v_e_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0(lean_object* v_00_u03b1_828_, lean_object* v_e_829_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(v_e_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___boxed(lean_object* v_00_u03b1_832_, lean_object* v_e_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0(v_00_u03b1_832_, v_e_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0(lean_object* v_handle_836_, lean_object* v_a_837_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(v_handle_836_, v_a_837_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set_tag(v___x_842_, 1);
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
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_a_848_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_839_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_839_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set_tag(v___x_850_, 0);
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0___boxed(lean_object* v_handle_856_, lean_object* v_a_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0(v_handle_856_, v_a_857_);
lean_dec_ref(v_a_857_);
lean_dec(v_handle_856_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(lean_object* v_handle_863_, lean_object* v_args_864_){
_start:
{
lean_object* v___x_866_; lean_object* v_cmd_867_; lean_object* v_args_868_; lean_object* v_cwd_869_; lean_object* v_env_870_; uint8_t v_inheritEnv_871_; uint8_t v_setsid_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_932_; 
v___x_866_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___closed__0));
v_cmd_867_ = lean_ctor_get(v_args_864_, 1);
v_args_868_ = lean_ctor_get(v_args_864_, 2);
v_cwd_869_ = lean_ctor_get(v_args_864_, 3);
v_env_870_ = lean_ctor_get(v_args_864_, 4);
v_inheritEnv_871_ = lean_ctor_get_uint8(v_args_864_, sizeof(void*)*5);
v_setsid_872_ = lean_ctor_get_uint8(v_args_864_, sizeof(void*)*5 + 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v_args_864_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v_args_864_, 0);
lean_dec(v_unused_933_);
v___x_874_ = v_args_864_;
v_isShared_875_ = v_isSharedCheck_932_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_env_870_);
lean_inc(v_cwd_869_);
lean_inc(v_args_868_);
lean_inc(v_cmd_867_);
lean_dec(v_args_864_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_932_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_866_);
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_cmd_867_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_args_868_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v_cwd_869_);
lean_ctor_set(v_reuseFailAlloc_931_, 4, v_env_870_);
lean_ctor_set_uint8(v_reuseFailAlloc_931_, sizeof(void*)*5, v_inheritEnv_871_);
lean_ctor_set_uint8(v_reuseFailAlloc_931_, sizeof(void*)*5 + 1, v_setsid_872_);
v___x_877_ = v_reuseFailAlloc_931_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; 
v___x_878_ = lean_io_process_spawn(v___x_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___f_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v_stderr_883_; lean_object* v___x_884_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc_n(v_a_879_, 2);
lean_dec_ref_known(v___x_878_, 1);
v___f_880_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0___boxed), 3, 2);
lean_closure_set(v___f_880_, 0, v_handle_863_);
lean_closure_set(v___f_880_, 1, v_a_879_);
v___x_881_ = lean_unsigned_to_nat(9u);
v___x_882_ = lean_io_as_task(v___f_880_, v___x_881_);
v_stderr_883_ = lean_ctor_get(v_a_879_, 2);
v___x_884_ = l_IO_FS_Handle_readToEnd(v_stderr_883_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_886_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v___x_886_ = lean_io_process_child_wait(v___x_866_, v_a_879_);
lean_dec(v_a_879_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_906_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_906_ == 0)
{
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_906_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_906_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_task_get_own(v___x_882_);
v___x_897_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(v___x_896_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_dec_ref_known(v___x_897_, 1);
goto v___jp_891_;
}
else
{
if (lean_obj_tag(v___x_897_) == 0)
{
lean_dec_ref_known(v___x_897_, 1);
goto v___jp_891_;
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_del_object(v___x_889_);
lean_dec(v_a_887_);
lean_dec(v_a_885_);
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
v___jp_891_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v_a_885_);
lean_ctor_set(v___x_892_, 1, v_a_887_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_892_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v_a_885_);
lean_dec_ref(v___x_882_);
v_a_907_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_886_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_886_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v___x_882_);
lean_dec(v_a_879_);
v_a_915_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_884_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_884_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec(v_handle_863_);
v_a_923_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_878_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_878_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___boxed(lean_object* v_handle_934_, lean_object* v_args_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(v_handle_934_, v_args_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(lean_object* v_s_938_){
_start:
{
lean_object* v___x_940_; lean_object* v_putStr_941_; lean_object* v___x_942_; 
v___x_940_ = lean_get_stderr();
v_putStr_941_ = lean_ctor_get(v___x_940_, 4);
lean_inc_ref(v_putStr_941_);
lean_dec_ref(v___x_940_);
v___x_942_ = lean_apply_2(v_putStr_941_, v_s_938_, lean_box(0));
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0___boxed(lean_object* v_s_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v_s_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(lean_object* v_handle_947_, lean_object* v_spawnArgs_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_948_, v_a_949_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_953_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(v_handle_947_, v_a_952_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v_fst_955_; lean_object* v_snd_956_; lean_object* v___x_957_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v_fst_955_ = lean_ctor_get(v_a_954_, 0);
lean_inc(v_fst_955_);
v_snd_956_ = lean_ctor_get(v_a_954_, 1);
lean_inc(v_snd_956_);
lean_dec(v_a_954_);
v___x_957_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v_fst_955_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_977_; 
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v___x_957_, 0);
lean_dec(v_unused_978_);
v___x_959_ = v___x_957_;
v_isShared_960_ = v_isSharedCheck_977_;
goto v_resetjp_958_;
}
else
{
lean_dec(v___x_957_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_977_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
uint32_t v___x_961_; uint32_t v___x_962_; uint8_t v___x_963_; 
v___x_961_ = 0;
v___x_962_ = lean_unbox_uint32(v_snd_956_);
v___x_963_ = lean_uint32_dec_eq(v___x_962_, v___x_961_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; uint32_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_964_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0));
v___x_965_ = lean_unbox_uint32(v_snd_956_);
lean_dec(v_snd_956_);
v___x_966_ = lean_uint32_to_nat(v___x_965_);
v___x_967_ = l_Nat_reprFast(v___x_966_);
v___x_968_ = lean_string_append(v___x_964_, v___x_967_);
lean_dec_ref(v___x_967_);
v___x_969_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 1);
lean_ctor_set(v___x_959_, 0, v___x_969_);
v___x_971_ = v___x_959_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
else
{
lean_object* v___x_973_; lean_object* v___x_975_; 
lean_dec(v_snd_956_);
v___x_973_ = lean_box(0);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_973_);
v___x_975_ = v___x_959_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
else
{
lean_dec(v_snd_956_);
return v___x_957_;
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
v_a_979_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_953_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_953_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec(v_handle_947_);
v_a_987_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_951_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_951_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___boxed(lean_object* v_handle_995_, lean_object* v_spawnArgs_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_handle_995_, v_spawnArgs_996_, v_a_997_);
lean_dec_ref(v_a_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(lean_object* v_spawnArgs_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_1000_, v_a_1001_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = lean_box(0);
v___x_1006_ = l_IO_Process_output(v_a_1004_, v___x_1005_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; uint32_t v_exitCode_1008_; lean_object* v_stdout_1009_; lean_object* v_stderr_1010_; lean_object* v___x_1011_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v_exitCode_1008_ = lean_ctor_get_uint32(v_a_1007_, sizeof(void*)*2);
v_stdout_1009_ = lean_ctor_get(v_a_1007_, 0);
lean_inc_ref(v_stdout_1009_);
v_stderr_1010_ = lean_ctor_get(v_a_1007_, 1);
lean_inc_ref(v_stderr_1010_);
lean_dec(v_a_1007_);
v___x_1011_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v_stderr_1010_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1028_; 
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v___x_1011_, 0);
lean_dec(v_unused_1029_);
v___x_1013_ = v___x_1011_;
v_isShared_1014_ = v_isSharedCheck_1028_;
goto v_resetjp_1012_;
}
else
{
lean_dec(v___x_1011_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1028_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
uint32_t v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = 0;
v___x_1016_ = lean_uint32_dec_eq(v_exitCode_1008_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
lean_dec_ref(v_stdout_1009_);
v___x_1017_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0));
v___x_1018_ = lean_uint32_to_nat(v_exitCode_1008_);
v___x_1019_ = l_Nat_reprFast(v___x_1018_);
v___x_1020_ = lean_string_append(v___x_1017_, v___x_1019_);
lean_dec_ref(v___x_1019_);
v___x_1021_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set_tag(v___x_1013_, 1);
lean_ctor_set(v___x_1013_, 0, v___x_1021_);
v___x_1023_ = v___x_1013_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
else
{
lean_object* v___x_1026_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v_stdout_1009_);
v___x_1026_ = v___x_1013_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_stdout_1009_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec_ref(v_stdout_1009_);
v_a_1030_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1011_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1011_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
v_a_1038_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1006_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1006_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
v_a_1046_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1003_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1003_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___boxed(lean_object* v_spawnArgs_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v_spawnArgs_1054_, v_a_1055_);
lean_dec_ref(v_a_1055_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(lean_object* v_spawnArgs_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_1058_, v_a_1059_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1063_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1061_, 1);
v___x_1063_ = lean_io_process_spawn(v_a_1062_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1065_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v___x_1066_ = lean_io_process_child_wait(v___x_1065_, v_a_1064_);
lean_dec(v_a_1064_);
return v___x_1066_;
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v_a_1067_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1063_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1063_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1061_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1061_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode___boxed(lean_object* v_spawnArgs_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v_spawnArgs_1083_, v_a_1084_);
lean_dec_ref(v_a_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(lean_object* v_spawnArgs_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v_spawnArgs_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1111_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1111_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1111_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
uint32_t v___x_1095_; uint32_t v___x_1096_; uint8_t v___x_1097_; 
v___x_1095_ = 0;
v___x_1096_ = lean_unbox_uint32(v_a_1091_);
v___x_1097_ = lean_uint32_dec_eq(v___x_1096_, v___x_1095_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; uint32_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1098_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0));
v___x_1099_ = lean_unbox_uint32(v_a_1091_);
lean_dec(v_a_1091_);
v___x_1100_ = lean_uint32_to_nat(v___x_1099_);
v___x_1101_ = l_Nat_reprFast(v___x_1100_);
v___x_1102_ = lean_string_append(v___x_1098_, v___x_1101_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 1);
lean_ctor_set(v___x_1093_, 0, v___x_1103_);
v___x_1105_ = v___x_1093_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
lean_dec(v_a_1091_);
v___x_1107_ = lean_box(0);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1107_);
v___x_1109_ = v___x_1093_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
v_a_1112_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1090_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1090_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed___boxed(lean_object* v_spawnArgs_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v_spawnArgs_1120_, v_a_1121_);
lean_dec_ref(v_a_1121_);
return v_res_1123_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0));
v___x_1126_ = lean_string_utf8_byte_size(v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(lean_object* v_s_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1128_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0));
v___x_1129_ = lean_string_utf8_byte_size(v_s_1127_);
v___x_1130_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__1);
v___x_1131_ = lean_nat_dec_le(v___x_1130_, v___x_1129_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref(v_s_1127_);
v___x_1132_ = lean_box(0);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_string_memcmp(v_s_1127_, v___x_1128_, v___x_1133_, v___x_1133_, v___x_1130_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_dec_ref(v_s_1127_);
v___x_1135_ = lean_box(0);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_inc_ref(v_s_1127_);
v___x_1136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1136_, 0, v_s_1127_);
lean_ctor_set(v___x_1136_, 1, v___x_1133_);
lean_ctor_set(v___x_1136_, 2, v___x_1129_);
v___x_1137_ = l_String_Slice_pos_x21(v___x_1136_, v___x_1130_);
lean_dec_ref_known(v___x_1136_, 3);
v___x_1138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1138_, 0, v_s_1127_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
lean_ctor_set(v___x_1138_, 2, v___x_1129_);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(lean_object* v_s_1140_, lean_object* v_pat_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_s_1140_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___boxed(lean_object* v_s_1143_, lean_object* v_pat_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(v_s_1143_, v_pat_1144_);
lean_dec_ref(v_pat_1144_);
return v_res_1145_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0));
v___x_1148_ = lean_string_utf8_byte_size(v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(lean_object* v_s_1149_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1150_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0));
v___x_1151_ = lean_string_utf8_byte_size(v_s_1149_);
v___x_1152_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__1);
v___x_1153_ = lean_nat_dec_le(v___x_1152_, v___x_1151_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
lean_dec_ref(v_s_1149_);
v___x_1154_ = lean_box(0);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = lean_string_memcmp(v_s_1149_, v___x_1150_, v___x_1155_, v___x_1155_, v___x_1152_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec_ref(v_s_1149_);
v___x_1157_ = lean_box(0);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_inc_ref(v_s_1149_);
v___x_1158_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1158_, 0, v_s_1149_);
lean_ctor_set(v___x_1158_, 1, v___x_1155_);
lean_ctor_set(v___x_1158_, 2, v___x_1151_);
v___x_1159_ = l_String_Slice_pos_x21(v___x_1158_, v___x_1152_);
lean_dec_ref_known(v___x_1158_, 3);
v___x_1160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1160_, 0, v_s_1149_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
lean_ctor_set(v___x_1160_, 2, v___x_1151_);
v___x_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(lean_object* v_s_1162_, lean_object* v_pat_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_s_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___boxed(lean_object* v_s_1165_, lean_object* v_pat_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(v_s_1165_, v_pat_1166_);
lean_dec_ref(v_pat_1166_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg(){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___closed__0));
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___boxed(lean_object* v___dummy_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg();
return v_res_1173_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg();
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(lean_object* v_s_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___boxed(lean_object* v_s_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(v_s_1177_);
lean_dec_ref(v_s_1177_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(lean_object* v_a_1179_, lean_object* v___x_1180_, lean_object* v___x_1181_, lean_object* v_a_1182_, lean_object* v_b_1183_){
_start:
{
lean_object* v_it_1185_; lean_object* v_startInclusive_1186_; lean_object* v_endExclusive_1187_; 
if (lean_obj_tag(v_a_1182_) == 0)
{
lean_object* v_currPos_1192_; lean_object* v_searcher_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1216_; 
v_currPos_1192_ = lean_ctor_get(v_a_1182_, 0);
v_searcher_1193_ = lean_ctor_get(v_a_1182_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_a_1182_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1195_ = v_a_1182_;
v_isShared_1196_ = v_isSharedCheck_1216_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_searcher_1193_);
lean_inc(v_currPos_1192_);
lean_dec(v_a_1182_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1216_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
uint8_t v_decide_1197_; 
v_decide_1197_ = lean_nat_dec_eq(v_searcher_1193_, v___x_1181_);
if (v_decide_1197_ == 0)
{
uint32_t v___x_1198_; uint32_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1198_ = 10;
v___x_1199_ = lean_string_utf8_get_fast(v_a_1179_, v_searcher_1193_);
v___x_1200_ = lean_uint32_dec_eq(v___x_1199_, v___x_1198_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = lean_string_utf8_next_fast(v_a_1179_, v_searcher_1193_);
lean_dec(v_searcher_1193_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v___x_1201_);
v___x_1203_ = v___x_1195_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_currPos_1192_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
v_a_1182_ = v___x_1203_;
goto _start;
}
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v_slice_1209_; lean_object* v_nextIt_1211_; 
v___x_1206_ = lean_string_utf8_next_fast(v_a_1179_, v_searcher_1193_);
v___x_1207_ = lean_nat_sub(v___x_1206_, v_searcher_1193_);
v___x_1208_ = lean_nat_add(v_searcher_1193_, v___x_1207_);
lean_dec(v___x_1207_);
v_slice_1209_ = l_String_Slice_subslice_x21(v___x_1180_, v_currPos_1192_, v_searcher_1193_);
lean_inc(v___x_1208_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v___x_1208_);
lean_ctor_set(v___x_1195_, 0, v___x_1208_);
v_nextIt_1211_ = v___x_1195_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1208_);
v_nextIt_1211_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v_startInclusive_1212_; lean_object* v_endExclusive_1213_; 
v_startInclusive_1212_ = lean_ctor_get(v_slice_1209_, 0);
lean_inc(v_startInclusive_1212_);
v_endExclusive_1213_ = lean_ctor_get(v_slice_1209_, 1);
lean_inc(v_endExclusive_1213_);
lean_dec_ref(v_slice_1209_);
v_it_1185_ = v_nextIt_1211_;
v_startInclusive_1186_ = v_startInclusive_1212_;
v_endExclusive_1187_ = v_endExclusive_1213_;
goto v___jp_1184_;
}
}
}
else
{
lean_object* v___x_1215_; 
lean_del_object(v___x_1195_);
lean_dec(v_searcher_1193_);
v___x_1215_ = lean_box(1);
lean_inc(v___x_1181_);
v_it_1185_ = v___x_1215_;
v_startInclusive_1186_ = v_currPos_1192_;
v_endExclusive_1187_ = v___x_1181_;
goto v___jp_1184_;
}
}
}
else
{
lean_dec(v___x_1181_);
lean_dec_ref(v_a_1179_);
return v_b_1183_;
}
v___jp_1184_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_inc_ref(v_a_1179_);
v___x_1188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1188_, 0, v_a_1179_);
lean_ctor_set(v___x_1188_, 1, v_startInclusive_1186_);
lean_ctor_set(v___x_1188_, 2, v_endExclusive_1187_);
v___x_1189_ = l_String_Slice_toString(v___x_1188_);
lean_dec_ref_known(v___x_1188_, 3);
v___x_1190_ = lean_array_push(v_b_1183_, v___x_1189_);
v_a_1182_ = v_it_1185_;
v_b_1183_ = v___x_1190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg___boxed(lean_object* v_a_1217_, lean_object* v___x_1218_, lean_object* v___x_1219_, lean_object* v_a_1220_, lean_object* v_b_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1217_, v___x_1218_, v___x_1219_, v_a_1220_, v_b_1221_);
lean_dec_ref(v___x_1218_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(lean_object* v_as_x27_1223_, lean_object* v_b_1224_){
_start:
{
if (lean_obj_tag(v_as_x27_1223_) == 0)
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v_b_1224_);
return v___x_1226_;
}
else
{
lean_object* v_head_1227_; lean_object* v_tail_1228_; lean_object* v_fst_1229_; lean_object* v_snd_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1252_; 
v_head_1227_ = lean_ctor_get(v_as_x27_1223_, 0);
v_tail_1228_ = lean_ctor_get(v_as_x27_1223_, 1);
v_fst_1229_ = lean_ctor_get(v_b_1224_, 0);
v_snd_1230_ = lean_ctor_get(v_b_1224_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_b_1224_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1232_ = v_b_1224_;
v_isShared_1233_ = v_isSharedCheck_1252_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_snd_1230_);
lean_inc(v_fst_1229_);
lean_dec(v_b_1224_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1252_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; 
lean_inc(v_head_1227_);
v___x_1234_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_head_1227_);
if (lean_obj_tag(v___x_1234_) == 1)
{
lean_object* v_val_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
lean_dec(v_fst_1229_);
v_val_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_val_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = l_String_Slice_toString(v_val_1235_);
lean_dec(v_val_1235_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1236_);
v___x_1238_ = v___x_1232_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_snd_1230_);
v___x_1238_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
v_as_x27_1223_ = v_tail_1228_;
v_b_1224_ = v___x_1238_;
goto _start;
}
}
else
{
lean_object* v___x_1241_; 
lean_dec(v___x_1234_);
lean_inc(v_head_1227_);
v___x_1241_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_head_1227_);
if (lean_obj_tag(v___x_1241_) == 1)
{
lean_object* v_val_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
lean_dec(v_snd_1230_);
v_val_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_val_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = l_String_Slice_toString(v_val_1242_);
lean_dec(v_val_1242_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v___x_1243_);
v___x_1245_ = v___x_1232_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_fst_1229_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
v_as_x27_1223_ = v_tail_1228_;
v_b_1224_ = v___x_1245_;
goto _start;
}
}
else
{
lean_object* v___x_1249_; 
lean_dec(v___x_1241_);
if (v_isShared_1233_ == 0)
{
v___x_1249_ = v___x_1232_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_fst_1229_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_snd_1230_);
v___x_1249_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
v_as_x27_1223_ = v_tail_1228_;
v_b_1224_ = v___x_1249_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg___boxed(lean_object* v_as_x27_1253_, lean_object* v_b_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_1253_, v_b_1254_);
lean_dec(v_as_x27_1253_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(lean_object* v_s_1257_){
_start:
{
lean_object* v___x_1259_; lean_object* v_putStr_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_get_stdout();
v_putStr_1260_ = lean_ctor_get(v___x_1259_, 4);
lean_inc_ref(v_putStr_1260_);
lean_dec_ref(v___x_1259_);
v___x_1261_ = lean_apply_2(v_putStr_1260_, v_s_1257_, lean_box(0));
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2___boxed(lean_object* v_s_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v_s_1262_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(lean_object* v_s_1265_){
_start:
{
uint32_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = 10;
v___x_1268_ = lean_string_push(v_s_1265_, v___x_1267_);
v___x_1269_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v___x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2___boxed(lean_object* v_s_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v_s_1270_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(lean_object* v_a_1306_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_1312_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1311_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_projectDir_1313_; lean_object* v_leanPrefix_1314_; lean_object* v_whichLake_1315_; lean_object* v_lakeHome_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___y_1320_; lean_object* v_leanPrefix_1321_; lean_object* v_whichLake_1322_; lean_object* v_lakeHome_1323_; uint8_t v___x_1378_; 
lean_dec_ref_known(v___x_1312_, 1);
v_projectDir_1313_ = lean_ctor_get(v_a_1306_, 0);
v_leanPrefix_1314_ = lean_ctor_get(v_a_1306_, 6);
v_whichLake_1315_ = lean_ctor_get(v_a_1306_, 10);
v_lakeHome_1316_ = lean_ctor_get(v_a_1306_, 11);
v___x_1317_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1313_);
v___x_1318_ = l_System_FilePath_join(v_projectDir_1313_, v___x_1317_);
v___x_1378_ = l_System_FilePath_pathExists(v___x_1318_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_io_create_dir(v___x_1318_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_dec_ref_known(v___x_1379_, 1);
v___y_1320_ = v_a_1306_;
v_leanPrefix_1321_ = v_leanPrefix_1314_;
v_whichLake_1322_ = v_whichLake_1315_;
v_lakeHome_1323_ = v_lakeHome_1316_;
goto v___jp_1319_;
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec_ref(v___x_1318_);
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
else
{
v___y_1320_ = v_a_1306_;
v_leanPrefix_1321_ = v_leanPrefix_1314_;
v_whichLake_1322_ = v_whichLake_1315_;
v_lakeHome_1323_ = v_lakeHome_1316_;
goto v___jp_1319_;
}
v___jp_1319_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1324_ = lean_unsigned_to_nat(1u);
v___x_1325_ = lean_mk_empty_array_with_capacity(v___x_1324_);
v___x_1326_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__5));
v___x_1327_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8));
v___x_1328_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1329_ = lean_unsigned_to_nat(3u);
v___x_1330_ = lean_mk_empty_array_with_capacity(v___x_1329_);
lean_inc_ref(v_projectDir_1313_);
v___x_1331_ = lean_array_push(v___x_1330_, v_projectDir_1313_);
lean_inc_ref(v_leanPrefix_1321_);
v___x_1332_ = lean_array_push(v___x_1331_, v_leanPrefix_1321_);
lean_inc_ref(v_lakeHome_1323_);
v___x_1333_ = lean_array_push(v___x_1332_, v_lakeHome_1323_);
v___x_1334_ = lean_array_push(v___x_1325_, v___x_1318_);
v___x_1335_ = lean_unsigned_to_nat(0u);
v___x_1336_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1337_ = 1;
v___x_1338_ = lean_box(0);
lean_inc_ref(v_whichLake_1322_);
v___x_1339_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1339_, 0, v_whichLake_1322_);
lean_ctor_set(v___x_1339_, 1, v___x_1326_);
lean_ctor_set(v___x_1339_, 2, v___x_1327_);
lean_ctor_set(v___x_1339_, 3, v___x_1328_);
lean_ctor_set(v___x_1339_, 4, v___x_1333_);
lean_ctor_set(v___x_1339_, 5, v___x_1334_);
lean_ctor_set(v___x_1339_, 6, v___x_1336_);
lean_ctor_set(v___x_1339_, 7, v___x_1338_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*8, v___x_1337_);
v___x_1340_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v___x_1339_, v___y_1320_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1369_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc_n(v_a_1341_, 2);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1342_ = lean_string_utf8_byte_size(v_a_1341_);
v___x_1343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1343_, 0, v_a_1341_);
lean_ctor_set(v___x_1343_, 1, v___x_1335_);
lean_ctor_set(v___x_1343_, 2, v___x_1342_);
v___x_1344_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0);
v___x_1345_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1341_, v___x_1343_, v___x_1342_, v___x_1344_, v___x_1336_);
lean_dec_ref_known(v___x_1343_, 3);
v___x_1346_ = lean_array_to_list(v___x_1345_);
v___x_1347_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__15));
v___x_1348_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v___x_1346_, v___x_1347_);
lean_dec(v___x_1346_);
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1369_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1369_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v_fst_1353_; lean_object* v_snd_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1368_; 
v_fst_1353_ = lean_ctor_get(v_a_1349_, 0);
v_snd_1354_ = lean_ctor_get(v_a_1349_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_a_1349_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1356_ = v_a_1349_;
v_isShared_1357_ = v_isSharedCheck_1368_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_snd_1354_);
lean_inc(v_fst_1353_);
lean_dec(v_a_1349_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1368_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = lean_string_utf8_byte_size(v_fst_1353_);
v___x_1359_ = lean_nat_dec_eq(v___x_1358_, v___x_1335_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = lean_string_utf8_byte_size(v_snd_1354_);
v___x_1361_ = lean_nat_dec_eq(v___x_1360_, v___x_1335_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1363_; 
if (v_isShared_1357_ == 0)
{
v___x_1363_ = v___x_1356_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_fst_1353_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_snd_1354_);
v___x_1363_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1363_);
v___x_1365_ = v___x_1351_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
lean_del_object(v___x_1356_);
lean_dec(v_snd_1354_);
lean_dec(v_fst_1353_);
lean_del_object(v___x_1351_);
goto v___jp_1308_;
}
}
else
{
lean_del_object(v___x_1356_);
lean_dec(v_snd_1354_);
lean_dec(v_fst_1353_);
lean_del_object(v___x_1351_);
goto v___jp_1308_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_a_1370_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1340_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1340_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
v_a_1388_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1312_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1312_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
v___jp_1308_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__1));
v___x_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___boxed(lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v_a_1396_);
lean_dec_ref(v_a_1396_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(lean_object* v_a_1399_, lean_object* v___x_1400_, lean_object* v___x_1401_, lean_object* v_inst_1402_, lean_object* v_R_1403_, lean_object* v_a_1404_, lean_object* v_b_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1399_, v___x_1400_, v___x_1401_, v_a_1404_, v_b_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___boxed(lean_object* v_a_1407_, lean_object* v___x_1408_, lean_object* v___x_1409_, lean_object* v_inst_1410_, lean_object* v_R_1411_, lean_object* v_a_1412_, lean_object* v_b_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(v_a_1407_, v___x_1408_, v___x_1409_, v_inst_1410_, v_R_1411_, v_a_1412_, v_b_1413_);
lean_dec_ref(v___x_1408_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(lean_object* v_as_1415_, lean_object* v_as_x27_1416_, lean_object* v_b_1417_, lean_object* v_a_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_1416_, v_b_1417_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___boxed(lean_object* v_as_1422_, lean_object* v_as_x27_1423_, lean_object* v_b_1424_, lean_object* v_a_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(v_as_1422_, v_as_x27_1423_, v_b_1424_, v_a_1425_, v___y_1426_);
lean_dec_ref(v___y_1426_);
lean_dec(v_as_x27_1423_);
lean_dec(v_as_1422_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(lean_object* v_a_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_1445_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1444_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_projectDir_1446_; lean_object* v_leanPrefix_1447_; lean_object* v_whichLake_1448_; lean_object* v_lakeHome_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___y_1453_; lean_object* v_leanPrefix_1454_; lean_object* v_whichLake_1455_; lean_object* v_lakeHome_1456_; uint8_t v___x_1473_; 
lean_dec_ref_known(v___x_1445_, 1);
v_projectDir_1446_ = lean_ctor_get(v_a_1442_, 0);
v_leanPrefix_1447_ = lean_ctor_get(v_a_1442_, 6);
v_whichLake_1448_ = lean_ctor_get(v_a_1442_, 10);
v_lakeHome_1449_ = lean_ctor_get(v_a_1442_, 11);
v___x_1450_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1446_);
v___x_1451_ = l_System_FilePath_join(v_projectDir_1446_, v___x_1450_);
v___x_1473_ = l_System_FilePath_pathExists(v___x_1451_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_io_create_dir(v___x_1451_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_dec_ref_known(v___x_1474_, 1);
v___y_1453_ = v_a_1442_;
v_leanPrefix_1454_ = v_leanPrefix_1447_;
v_whichLake_1455_ = v_whichLake_1448_;
v_lakeHome_1456_ = v_lakeHome_1449_;
goto v___jp_1452_;
}
else
{
lean_dec_ref(v___x_1451_);
return v___x_1474_;
}
}
else
{
v___y_1453_ = v_a_1442_;
v_leanPrefix_1454_ = v_leanPrefix_1447_;
v_whichLake_1455_ = v_whichLake_1448_;
v_lakeHome_1456_ = v_lakeHome_1449_;
goto v___jp_1452_;
}
v___jp_1452_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1457_ = lean_unsigned_to_nat(1u);
v___x_1458_ = lean_mk_empty_array_with_capacity(v___x_1457_);
v___x_1459_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__1));
v___x_1460_ = lean_unsigned_to_nat(3u);
v___x_1461_ = lean_mk_empty_array_with_capacity(v___x_1460_);
v___x_1462_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2));
v___x_1463_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
lean_inc_ref(v_projectDir_1446_);
v___x_1464_ = lean_array_push(v___x_1461_, v_projectDir_1446_);
lean_inc_ref(v_leanPrefix_1454_);
v___x_1465_ = lean_array_push(v___x_1464_, v_leanPrefix_1454_);
lean_inc_ref(v_lakeHome_1456_);
v___x_1466_ = lean_array_push(v___x_1465_, v_lakeHome_1456_);
v___x_1467_ = lean_array_push(v___x_1458_, v___x_1451_);
v___x_1468_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1469_ = 1;
v___x_1470_ = lean_box(0);
lean_inc_ref(v_whichLake_1455_);
v___x_1471_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1471_, 0, v_whichLake_1455_);
lean_ctor_set(v___x_1471_, 1, v___x_1459_);
lean_ctor_set(v___x_1471_, 2, v___x_1462_);
lean_ctor_set(v___x_1471_, 3, v___x_1463_);
lean_ctor_set(v___x_1471_, 4, v___x_1466_);
lean_ctor_set(v___x_1471_, 5, v___x_1467_);
lean_ctor_set(v___x_1471_, 6, v___x_1468_);
lean_ctor_set(v___x_1471_, 7, v___x_1470_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*8, v___x_1469_);
v___x_1472_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_1471_, v___y_1453_);
return v___x_1472_;
}
}
else
{
return v___x_1445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___boxed(lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_1475_);
lean_dec_ref(v_a_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(lean_object* v_f_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v_fst_1492_; lean_object* v_snd_1493_; lean_object* v_r_1494_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v_fst_1492_ = lean_ctor_get(v_a_1491_, 0);
lean_inc(v_fst_1492_);
v_snd_1493_ = lean_ctor_get(v_a_1491_, 1);
lean_inc_n(v_snd_1493_, 2);
lean_dec(v_a_1491_);
lean_inc_ref(v___y_1488_);
v_r_1494_ = lean_apply_4(v_f_1487_, v_fst_1492_, v_snd_1493_, v___y_1488_, lean_box(0));
if (lean_obj_tag(v_r_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1496_; 
v_a_1495_ = lean_ctor_get(v_r_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v_r_1494_, 1);
v___x_1496_ = lean_io_remove_file(v_snd_1493_);
lean_dec(v_snd_1493_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v___x_1496_, 0);
lean_dec(v_unused_1504_);
v___x_1498_ = v___x_1496_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_dec(v___x_1496_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v_a_1495_);
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1495_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_a_1495_);
v_a_1505_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1496_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1496_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_ctor_get(v_r_1494_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v_r_1494_, 1);
v___x_1514_ = lean_io_remove_file(v_snd_1493_);
lean_dec(v_snd_1493_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; 
v_unused_1522_ = lean_ctor_get(v___x_1514_, 0);
lean_dec(v_unused_1522_);
v___x_1516_ = v___x_1514_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_dec(v___x_1514_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set_tag(v___x_1516_, 1);
lean_ctor_set(v___x_1516_, 0, v_a_1513_);
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1513_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec(v_a_1513_);
v_a_1523_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1514_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1514_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec_ref(v_f_1487_);
v_a_1531_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1490_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1490_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg___boxed(lean_object* v_f_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v_f_1539_, v___y_1540_);
lean_dec_ref(v___y_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1(lean_object* v_00_u03b1_1543_, lean_object* v_f_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v_f_1544_, v___y_1545_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___boxed(lean_object* v_00_u03b1_1548_, lean_object* v_f_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1(v_00_u03b1_1548_, v_f_1549_, v___y_1550_);
lean_dec_ref(v___y_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0(lean_object* v_projectDir_1568_, lean_object* v_f_1569_, lean_object* v_handle_1570_, lean_object* v_path_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_leanPrefix_1574_; lean_object* v_whichLake_1575_; lean_object* v_lakeHome_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_leanPrefix_1574_ = lean_ctor_get(v___y_1572_, 6);
v_whichLake_1575_ = lean_ctor_get(v___y_1572_, 10);
v_lakeHome_1576_ = lean_ctor_get(v___y_1572_, 11);
v___x_1577_ = lean_unsigned_to_nat(1u);
v___x_1578_ = lean_mk_empty_array_with_capacity(v___x_1577_);
v___x_1579_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__1));
v___x_1580_ = lean_unsigned_to_nat(3u);
v___x_1581_ = lean_mk_empty_array_with_capacity(v___x_1580_);
v___x_1582_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2));
v___x_1583_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__4));
lean_inc_ref(v_projectDir_1568_);
v___x_1584_ = lean_array_push(v___x_1581_, v_projectDir_1568_);
lean_inc_ref(v_leanPrefix_1574_);
v___x_1585_ = lean_array_push(v___x_1584_, v_leanPrefix_1574_);
lean_inc_ref(v_lakeHome_1576_);
v___x_1586_ = lean_array_push(v___x_1585_, v_lakeHome_1576_);
v___x_1587_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
v___x_1588_ = l_System_FilePath_join(v_projectDir_1568_, v___x_1587_);
v___x_1589_ = lean_array_push(v___x_1578_, v___x_1588_);
v___x_1590_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1591_ = 0;
v___x_1592_ = lean_box(0);
lean_inc_ref(v_whichLake_1575_);
v___x_1593_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1593_, 0, v_whichLake_1575_);
lean_ctor_set(v___x_1593_, 1, v___x_1579_);
lean_ctor_set(v___x_1593_, 2, v___x_1582_);
lean_ctor_set(v___x_1593_, 3, v___x_1583_);
lean_ctor_set(v___x_1593_, 4, v___x_1586_);
lean_ctor_set(v___x_1593_, 5, v___x_1589_);
lean_ctor_set(v___x_1593_, 6, v___x_1590_);
lean_ctor_set(v___x_1593_, 7, v___x_1592_);
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*8, v___x_1591_);
v___x_1594_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_handle_1570_, v___x_1593_, v___y_1572_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v___x_1595_; 
lean_dec_ref_known(v___x_1594_, 1);
lean_inc_ref(v___y_1572_);
v___x_1595_ = lean_apply_3(v_f_1569_, v_path_1571_, v___y_1572_, lean_box(0));
return v___x_1595_;
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref(v_path_1571_);
lean_dec_ref(v_f_1569_);
v_a_1596_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1594_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1594_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___boxed(lean_object* v_projectDir_1604_, lean_object* v_f_1605_, lean_object* v_handle_1606_, lean_object* v_path_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0(v_projectDir_1604_, v_f_1605_, v_handle_1606_, v_path_1607_, v___y_1608_);
lean_dec_ref(v___y_1608_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(uint8_t v_a_1611_, lean_object* v_x_1612_){
_start:
{
if (lean_obj_tag(v_x_1612_) == 0)
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_box(0);
return v___x_1613_;
}
else
{
lean_object* v_key_1614_; lean_object* v_value_1615_; lean_object* v_tail_1616_; uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_key_1614_ = lean_ctor_get(v_x_1612_, 0);
v_value_1615_ = lean_ctor_get(v_x_1612_, 1);
v_tail_1616_ = lean_ctor_get(v_x_1612_, 2);
v___x_1617_ = lean_unbox(v_key_1614_);
v___x_1618_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v___x_1617_);
v___x_1619_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v_a_1611_);
v___x_1620_ = lean_nat_dec_eq(v___x_1618_, v___x_1619_);
lean_dec(v___x_1619_);
lean_dec(v___x_1618_);
if (v___x_1620_ == 0)
{
v_x_1612_ = v_tail_1616_;
goto _start;
}
else
{
lean_object* v___x_1622_; 
lean_inc(v_value_1615_);
v___x_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1622_, 0, v_value_1615_);
return v___x_1622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg___boxed(lean_object* v_a_1623_, lean_object* v_x_1624_){
_start:
{
uint8_t v_a_boxed_1625_; lean_object* v_res_1626_; 
v_a_boxed_1625_ = lean_unbox(v_a_1623_);
v_res_1626_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(v_a_boxed_1625_, v_x_1624_);
lean_dec(v_x_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(lean_object* v_m_1627_, uint8_t v_a_1628_){
_start:
{
lean_object* v_buckets_1629_; lean_object* v___x_1630_; uint64_t v___x_1631_; uint64_t v___x_1632_; uint64_t v___x_1633_; uint64_t v_fold_1634_; uint64_t v___x_1635_; uint64_t v___x_1636_; uint64_t v___x_1637_; size_t v___x_1638_; size_t v___x_1639_; size_t v___x_1640_; size_t v___x_1641_; size_t v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_buckets_1629_ = lean_ctor_get(v_m_1627_, 1);
v___x_1630_ = lean_array_get_size(v_buckets_1629_);
v___x_1631_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_a_1628_);
v___x_1632_ = 32ULL;
v___x_1633_ = lean_uint64_shift_right(v___x_1631_, v___x_1632_);
v_fold_1634_ = lean_uint64_xor(v___x_1631_, v___x_1633_);
v___x_1635_ = 16ULL;
v___x_1636_ = lean_uint64_shift_right(v_fold_1634_, v___x_1635_);
v___x_1637_ = lean_uint64_xor(v_fold_1634_, v___x_1636_);
v___x_1638_ = lean_uint64_to_usize(v___x_1637_);
v___x_1639_ = lean_usize_of_nat(v___x_1630_);
v___x_1640_ = ((size_t)1ULL);
v___x_1641_ = lean_usize_sub(v___x_1639_, v___x_1640_);
v___x_1642_ = lean_usize_land(v___x_1638_, v___x_1641_);
v___x_1643_ = lean_array_uget_borrowed(v_buckets_1629_, v___x_1642_);
v___x_1644_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(v_a_1628_, v___x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg___boxed(lean_object* v_m_1645_, lean_object* v_a_1646_){
_start:
{
uint8_t v_a_boxed_1647_; lean_object* v_res_1648_; 
v_a_boxed_1647_ = lean_unbox(v_a_1646_);
v_res_1648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_m_1645_, v_a_boxed_1647_);
lean_dec_ref(v_m_1645_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(lean_object* v_f_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_projectDir_1653_; lean_object* v_moduleStore_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; 
v_projectDir_1653_ = lean_ctor_get(v_a_1651_, 0);
v_moduleStore_1654_ = lean_ctor_get(v_a_1651_, 17);
v___x_1655_ = 0;
v___x_1656_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_moduleStore_1654_, v___x_1655_);
if (lean_obj_tag(v___x_1656_) == 1)
{
lean_object* v_val_1657_; lean_object* v___x_1658_; 
v_val_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v___x_1656_, 1);
lean_inc_ref(v_a_1651_);
v___x_1658_ = lean_apply_3(v_f_1650_, v_val_1657_, v_a_1651_, lean_box(0));
return v___x_1658_;
}
else
{
lean_object* v___f_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_dec(v___x_1656_);
lean_inc_ref(v_projectDir_1653_);
v___f_1659_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_1659_, 0, v_projectDir_1653_);
lean_closure_set(v___f_1659_, 1, v_f_1650_);
v___x_1660_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___closed__0));
v___x_1661_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1660_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v___x_1662_; 
lean_dec_ref_known(v___x_1661_, 1);
v___x_1662_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v___f_1659_, v_a_1651_);
return v___x_1662_;
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec_ref(v___f_1659_);
v_a_1663_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1661_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1661_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___boxed(lean_object* v_f_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v_f_1671_, v_a_1672_);
lean_dec_ref(v_a_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport(lean_object* v_00_u03b1_1675_, lean_object* v_f_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v_f_1676_, v_a_1677_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___boxed(lean_object* v_00_u03b1_1680_, lean_object* v_f_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport(v_00_u03b1_1680_, v_f_1681_, v_a_1682_);
lean_dec_ref(v_a_1682_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0(lean_object* v_00_u03b2_1685_, lean_object* v_m_1686_, uint8_t v_a_1687_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_m_1686_, v_a_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___boxed(lean_object* v_00_u03b2_1689_, lean_object* v_m_1690_, lean_object* v_a_1691_){
_start:
{
uint8_t v_a_boxed_1692_; lean_object* v_res_1693_; 
v_a_boxed_1692_ = lean_unbox(v_a_1691_);
v_res_1693_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0(v_00_u03b2_1689_, v_m_1690_, v_a_boxed_1692_);
lean_dec_ref(v_m_1690_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0(lean_object* v_00_u03b2_1694_, uint8_t v_a_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(v_a_1695_, v_x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1698_, lean_object* v_a_1699_, lean_object* v_x_1700_){
_start:
{
uint8_t v_a_boxed_1701_; lean_object* v_res_1702_; 
v_a_boxed_1701_ = lean_unbox(v_a_1699_);
v_res_1702_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0(v_00_u03b2_1698_, v_a_boxed_1701_, v_x_1700_);
lean_dec(v_x_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(size_t v_sz_1703_, size_t v_i_1704_, lean_object* v_bs_1705_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = lean_usize_dec_lt(v_i_1704_, v_sz_1703_);
if (v___x_1706_ == 0)
{
return v_bs_1705_;
}
else
{
lean_object* v_v_1707_; lean_object* v___x_1708_; lean_object* v_bs_x27_1709_; lean_object* v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; 
v_v_1707_ = lean_array_uget(v_bs_1705_, v_i_1704_);
v___x_1708_ = lean_unsigned_to_nat(0u);
v_bs_x27_1709_ = lean_array_uset(v_bs_1705_, v_i_1704_, v___x_1708_);
v___x_1710_ = l_Lean_Name_toString(v_v_1707_, v___x_1706_);
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = lean_usize_add(v_i_1704_, v___x_1711_);
v___x_1713_ = lean_array_uset(v_bs_x27_1709_, v_i_1704_, v___x_1710_);
v_i_1704_ = v___x_1712_;
v_bs_1705_ = v___x_1713_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0___boxed(lean_object* v_sz_1715_, lean_object* v_i_1716_, lean_object* v_bs_1717_){
_start:
{
size_t v_sz_boxed_1718_; size_t v_i_boxed_1719_; lean_object* v_res_1720_; 
v_sz_boxed_1718_ = lean_unbox_usize(v_sz_1715_);
lean_dec(v_sz_1715_);
v_i_boxed_1719_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_boxed_1718_, v_i_boxed_1719_, v_bs_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(lean_object* v_targets_1728_, lean_object* v_a_1729_){
_start:
{
size_t v_sz_1731_; size_t v___x_1732_; lean_object* v_targetArgs_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v_targetList_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_sz_1731_ = lean_array_size(v_targets_1728_);
v___x_1732_ = ((size_t)0ULL);
v_targetArgs_1733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_1731_, v___x_1732_, v_targets_1728_);
v___x_1734_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
lean_inc_ref(v_targetArgs_1733_);
v___x_1735_ = lean_array_to_list(v_targetArgs_1733_);
v_targetList_1736_ = l_String_intercalate(v___x_1734_, v___x_1735_);
v___x_1737_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1));
v___x_1738_ = lean_string_append(v___x_1737_, v_targetList_1736_);
lean_dec_ref(v_targetList_1736_);
v___x_1739_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1738_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_projectDir_1740_; lean_object* v_leanPrefix_1741_; lean_object* v_whichLake_1742_; lean_object* v_lakeHome_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___y_1747_; lean_object* v_leanPrefix_1748_; lean_object* v_whichLake_1749_; lean_object* v_lakeHome_1750_; uint8_t v___x_1768_; 
lean_dec_ref_known(v___x_1739_, 1);
v_projectDir_1740_ = lean_ctor_get(v_a_1729_, 0);
v_leanPrefix_1741_ = lean_ctor_get(v_a_1729_, 6);
v_whichLake_1742_ = lean_ctor_get(v_a_1729_, 10);
v_lakeHome_1743_ = lean_ctor_get(v_a_1729_, 11);
v___x_1744_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1740_);
v___x_1745_ = l_System_FilePath_join(v_projectDir_1740_, v___x_1744_);
v___x_1768_ = l_System_FilePath_pathExists(v___x_1745_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_io_create_dir(v___x_1745_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_dec_ref_known(v___x_1769_, 1);
v___y_1747_ = v_a_1729_;
v_leanPrefix_1748_ = v_leanPrefix_1741_;
v_whichLake_1749_ = v_whichLake_1742_;
v_lakeHome_1750_ = v_lakeHome_1743_;
goto v___jp_1746_;
}
else
{
lean_dec_ref(v___x_1745_);
lean_dec_ref(v_targetArgs_1733_);
return v___x_1769_;
}
}
else
{
v___y_1747_ = v_a_1729_;
v_leanPrefix_1748_ = v_leanPrefix_1741_;
v_whichLake_1749_ = v_whichLake_1742_;
v_lakeHome_1750_ = v_lakeHome_1743_;
goto v___jp_1746_;
}
v___jp_1746_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1751_ = lean_unsigned_to_nat(1u);
v___x_1752_ = lean_mk_empty_array_with_capacity(v___x_1751_);
v___x_1753_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3));
v___x_1754_ = l_Array_append___redArg(v___x_1753_, v_targetArgs_1733_);
lean_dec_ref(v_targetArgs_1733_);
v___x_1755_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8));
v___x_1756_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1757_ = lean_unsigned_to_nat(3u);
v___x_1758_ = lean_mk_empty_array_with_capacity(v___x_1757_);
lean_inc_ref(v_projectDir_1740_);
v___x_1759_ = lean_array_push(v___x_1758_, v_projectDir_1740_);
lean_inc_ref(v_leanPrefix_1748_);
v___x_1760_ = lean_array_push(v___x_1759_, v_leanPrefix_1748_);
lean_inc_ref(v_lakeHome_1750_);
v___x_1761_ = lean_array_push(v___x_1760_, v_lakeHome_1750_);
v___x_1762_ = lean_array_push(v___x_1752_, v___x_1745_);
v___x_1763_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1764_ = 0;
v___x_1765_ = lean_box(0);
lean_inc_ref(v_whichLake_1749_);
v___x_1766_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1766_, 0, v_whichLake_1749_);
lean_ctor_set(v___x_1766_, 1, v___x_1754_);
lean_ctor_set(v___x_1766_, 2, v___x_1755_);
lean_ctor_set(v___x_1766_, 3, v___x_1756_);
lean_ctor_set(v___x_1766_, 4, v___x_1761_);
lean_ctor_set(v___x_1766_, 5, v___x_1762_);
lean_ctor_set(v___x_1766_, 6, v___x_1763_);
lean_ctor_set(v___x_1766_, 7, v___x_1765_);
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*8, v___x_1764_);
v___x_1767_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_1766_, v___y_1747_);
return v___x_1767_;
}
}
else
{
lean_dec_ref(v_targetArgs_1733_);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___boxed(lean_object* v_targets_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v_targets_1770_, v_a_1771_);
lean_dec_ref(v_a_1771_);
return v_res_1773_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1783_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11));
v___x_1784_ = lean_unsigned_to_nat(3u);
v___x_1785_ = lean_mk_empty_array_with_capacity(v___x_1784_);
v___x_1786_ = lean_array_push(v___x_1785_, v___x_1783_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(lean_object* v_projectDir_1787_, lean_object* v_whichLean4Export_1788_, lean_object* v_args_1789_, lean_object* v_f_1790_, lean_object* v_exportHandle_1791_, lean_object* v_exportPath_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_leanPrefix_1795_; lean_object* v_leanPath_1796_; lean_object* v_binPath_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v_leanPrefix_1795_ = lean_ctor_get(v___y_1793_, 6);
v_leanPath_1796_ = lean_ctor_get(v___y_1793_, 7);
v_binPath_1797_ = lean_ctor_get(v___y_1793_, 8);
v___x_1798_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6));
v___x_1799_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__0));
v___x_1800_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__1));
lean_inc_ref(v_leanPath_1796_);
v___x_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_leanPath_1796_);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1799_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
lean_inc_ref(v_binPath_1797_);
v___x_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1803_, 0, v_binPath_1797_);
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1798_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2);
v___x_1806_ = lean_array_push(v___x_1805_, v___x_1802_);
v___x_1807_ = lean_array_push(v___x_1806_, v___x_1804_);
v___x_1808_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1787_);
v___x_1809_ = l_System_FilePath_join(v_projectDir_1787_, v___x_1808_);
v___x_1810_ = lean_unsigned_to_nat(4u);
v___x_1811_ = lean_mk_empty_array_with_capacity(v___x_1810_);
v___x_1812_ = lean_array_push(v___x_1811_, v_projectDir_1787_);
v___x_1813_ = lean_array_push(v___x_1812_, v___x_1809_);
lean_inc_ref(v_leanPrefix_1795_);
v___x_1814_ = lean_array_push(v___x_1813_, v_leanPrefix_1795_);
lean_inc_ref(v_whichLean4Export_1788_);
v___x_1815_ = lean_array_push(v___x_1814_, v_whichLean4Export_1788_);
v___x_1816_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1817_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1818_ = 0;
v___x_1819_ = lean_box(0);
v___x_1820_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1820_, 0, v_whichLean4Export_1788_);
lean_ctor_set(v___x_1820_, 1, v_args_1789_);
lean_ctor_set(v___x_1820_, 2, v___x_1800_);
lean_ctor_set(v___x_1820_, 3, v___x_1807_);
lean_ctor_set(v___x_1820_, 4, v___x_1815_);
lean_ctor_set(v___x_1820_, 5, v___x_1816_);
lean_ctor_set(v___x_1820_, 6, v___x_1817_);
lean_ctor_set(v___x_1820_, 7, v___x_1819_);
lean_ctor_set_uint8(v___x_1820_, sizeof(void*)*8, v___x_1818_);
v___x_1821_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_exportHandle_1791_, v___x_1820_, v___y_1793_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v___x_1822_; 
lean_dec_ref_known(v___x_1821_, 1);
lean_inc_ref(v___y_1793_);
v___x_1822_ = lean_apply_3(v_f_1790_, v_exportPath_1792_, v___y_1793_, lean_box(0));
return v___x_1822_;
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec_ref(v_exportPath_1792_);
lean_dec_ref(v_f_1790_);
v_a_1823_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1821_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1821_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___boxed(lean_object* v_projectDir_1831_, lean_object* v_whichLean4Export_1832_, lean_object* v_args_1833_, lean_object* v_f_1834_, lean_object* v_exportHandle_1835_, lean_object* v_exportPath_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(v_projectDir_1831_, v_whichLean4Export_1832_, v_args_1833_, v_f_1834_, v_exportHandle_1835_, v_exportPath_1836_, v___y_1837_);
lean_dec_ref(v___y_1837_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(lean_object* v_args_1840_, lean_object* v_f_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_projectDir_1844_; lean_object* v_whichLean4Export_1845_; lean_object* v___f_1846_; lean_object* v___x_1847_; 
v_projectDir_1844_ = lean_ctor_get(v_a_1842_, 0);
v_whichLean4Export_1845_ = lean_ctor_get(v_a_1842_, 12);
lean_inc_ref(v_whichLean4Export_1845_);
lean_inc_ref(v_projectDir_1844_);
v___f_1846_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_1846_, 0, v_projectDir_1844_);
lean_closure_set(v___f_1846_, 1, v_whichLean4Export_1845_);
lean_closure_set(v___f_1846_, 2, v_args_1840_);
lean_closure_set(v___f_1846_, 3, v_f_1841_);
v___x_1847_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v___f_1846_, v_a_1842_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___boxed(lean_object* v_args_1848_, lean_object* v_f_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v_args_1848_, v_f_1849_, v_a_1850_);
lean_dec_ref(v_a_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(lean_object* v_00_u03b1_1853_, lean_object* v_args_1854_, lean_object* v_f_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v_args_1854_, v_f_1855_, v_a_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___boxed(lean_object* v_00_u03b1_1859_, lean_object* v_args_1860_, lean_object* v_f_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(v_00_u03b1_1859_, v_args_1860_, v_f_1861_, v_a_1862_);
lean_dec_ref(v_a_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0(lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
if (lean_obj_tag(v_x_1867_) == 0)
{
return v_x_1866_;
}
else
{
lean_object* v_head_1868_; lean_object* v_tail_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_head_1868_ = lean_ctor_get(v_x_1867_, 0);
lean_inc(v_head_1868_);
v_tail_1869_ = lean_ctor_get(v_x_1867_, 1);
lean_inc(v_tail_1869_);
lean_dec_ref_known(v_x_1867_, 2);
v___x_1870_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0));
v___x_1871_ = lean_string_append(v_x_1866_, v___x_1870_);
v___x_1872_ = 1;
v___x_1873_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1868_, v___x_1872_);
v___x_1874_ = lean_string_append(v___x_1871_, v___x_1873_);
lean_dec_ref(v___x_1873_);
v_x_1866_ = v___x_1874_;
v_x_1867_ = v_tail_1869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0(lean_object* v_x_1879_){
_start:
{
if (lean_obj_tag(v_x_1879_) == 0)
{
lean_object* v___x_1880_; 
v___x_1880_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__0));
return v___x_1880_;
}
else
{
lean_object* v_tail_1881_; 
v_tail_1881_ = lean_ctor_get(v_x_1879_, 1);
if (lean_obj_tag(v_tail_1881_) == 0)
{
lean_object* v_head_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_head_1882_ = lean_ctor_get(v_x_1879_, 0);
lean_inc(v_head_1882_);
lean_dec_ref_known(v_x_1879_, 2);
v___x_1883_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_1884_ = 1;
v___x_1885_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1882_, v___x_1884_);
v___x_1886_ = lean_string_append(v___x_1883_, v___x_1885_);
lean_dec_ref(v___x_1885_);
v___x_1887_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__2));
v___x_1888_ = lean_string_append(v___x_1886_, v___x_1887_);
return v___x_1888_;
}
else
{
lean_object* v_head_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; uint32_t v___x_1895_; lean_object* v___x_1896_; 
lean_inc(v_tail_1881_);
v_head_1889_ = lean_ctor_get(v_x_1879_, 0);
lean_inc(v_head_1889_);
lean_dec_ref_known(v_x_1879_, 2);
v___x_1890_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_1891_ = 1;
v___x_1892_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1889_, v___x_1891_);
v___x_1893_ = lean_string_append(v___x_1890_, v___x_1892_);
lean_dec_ref(v___x_1892_);
v___x_1894_ = l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0(v___x_1893_, v_tail_1881_);
v___x_1895_ = 93;
v___x_1896_ = lean_string_push(v___x_1894_, v___x_1895_);
return v___x_1896_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(size_t v_sz_1897_, size_t v_i_1898_, lean_object* v_bs_1899_){
_start:
{
uint8_t v___x_1900_; 
v___x_1900_ = lean_usize_dec_lt(v_i_1898_, v_sz_1897_);
if (v___x_1900_ == 0)
{
return v_bs_1899_;
}
else
{
lean_object* v_v_1901_; lean_object* v___x_1902_; lean_object* v_bs_x27_1903_; lean_object* v___x_1904_; size_t v___x_1905_; size_t v___x_1906_; lean_object* v___x_1907_; 
v_v_1901_ = lean_array_uget(v_bs_1899_, v_i_1898_);
v___x_1902_ = lean_unsigned_to_nat(0u);
v_bs_x27_1903_ = lean_array_uset(v_bs_1899_, v_i_1898_, v___x_1902_);
v___x_1904_ = l_Lean_Name_toString(v_v_1901_, v___x_1900_);
v___x_1905_ = ((size_t)1ULL);
v___x_1906_ = lean_usize_add(v_i_1898_, v___x_1905_);
v___x_1907_ = lean_array_uset(v_bs_x27_1903_, v_i_1898_, v___x_1904_);
v_i_1898_ = v___x_1906_;
v_bs_1899_ = v___x_1907_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1___boxed(lean_object* v_sz_1909_, lean_object* v_i_1910_, lean_object* v_bs_1911_){
_start:
{
size_t v_sz_boxed_1912_; size_t v_i_boxed_1913_; lean_object* v_res_1914_; 
v_sz_boxed_1912_ = lean_unbox_usize(v_sz_1909_);
lean_dec(v_sz_1909_);
v_i_boxed_1913_ = lean_unbox_usize(v_i_1910_);
lean_dec(v_i_1910_);
v_res_1914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(v_sz_boxed_1912_, v_i_boxed_1913_, v_bs_1911_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(lean_object* v_module_1918_, lean_object* v_decls_1919_, lean_object* v_f_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1923_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__0));
v___x_1924_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__1));
lean_inc_ref(v_decls_1919_);
v___x_1925_ = lean_array_to_list(v_decls_1919_);
v___x_1926_ = l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0(v___x_1925_);
v___x_1927_ = lean_string_append(v___x_1924_, v___x_1926_);
lean_dec_ref(v___x_1926_);
v___x_1928_ = lean_string_append(v___x_1923_, v___x_1927_);
lean_dec_ref(v___x_1927_);
v___x_1929_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__2));
v___x_1930_ = lean_string_append(v___x_1928_, v___x_1929_);
v___x_1931_ = 1;
lean_inc(v_module_1918_);
v___x_1932_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_1918_, v___x_1931_);
v___x_1933_ = lean_string_append(v___x_1930_, v___x_1932_);
lean_dec_ref(v___x_1932_);
v___x_1934_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1933_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; size_t v_sz_1941_; size_t v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
lean_dec_ref_known(v___x_1934_, 1);
v___x_1935_ = l_Lean_Name_toString(v_module_1918_, v___x_1931_);
v___x_1936_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__8));
v___x_1937_ = lean_unsigned_to_nat(2u);
v___x_1938_ = lean_mk_empty_array_with_capacity(v___x_1937_);
v___x_1939_ = lean_array_push(v___x_1938_, v___x_1935_);
v___x_1940_ = lean_array_push(v___x_1939_, v___x_1936_);
v_sz_1941_ = lean_array_size(v_decls_1919_);
v___x_1942_ = ((size_t)0ULL);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(v_sz_1941_, v___x_1942_, v_decls_1919_);
v___x_1944_ = l_Array_append___redArg(v___x_1940_, v___x_1943_);
lean_dec_ref(v___x_1943_);
v___x_1945_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v___x_1944_, v_f_1920_, v_a_1921_);
return v___x_1945_;
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v_f_1920_);
lean_dec_ref(v_decls_1919_);
lean_dec(v_module_1918_);
v_a_1946_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1934_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1934_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___boxed(lean_object* v_module_1954_, lean_object* v_decls_1955_, lean_object* v_f_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1954_, v_decls_1955_, v_f_1956_, v_a_1957_);
lean_dec_ref(v_a_1957_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(lean_object* v_00_u03b1_1960_, lean_object* v_module_1961_, lean_object* v_decls_1962_, lean_object* v_f_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1961_, v_decls_1962_, v_f_1963_, v_a_1964_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___boxed(lean_object* v_00_u03b1_1967_, lean_object* v_module_1968_, lean_object* v_decls_1969_, lean_object* v_f_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(v_00_u03b1_1967_, v_module_1968_, v_decls_1969_, v_f_1970_, v_a_1971_);
lean_dec_ref(v_a_1971_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(uint8_t v_kind_1974_, lean_object* v_module_1975_, lean_object* v_decls_1976_, lean_object* v_f_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v_moduleStore_1980_; lean_object* v___x_1981_; 
v_moduleStore_1980_ = lean_ctor_get(v_a_1978_, 17);
v___x_1981_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_moduleStore_1980_, v_kind_1974_);
if (lean_obj_tag(v___x_1981_) == 1)
{
lean_object* v_val_1982_; lean_object* v___x_1983_; 
lean_dec_ref(v_decls_1976_);
lean_dec(v_module_1975_);
v_val_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_val_1982_);
lean_dec_ref_known(v___x_1981_, 1);
lean_inc_ref(v_a_1978_);
v___x_1983_ = lean_apply_3(v_f_1977_, v_val_1982_, v_a_1978_, lean_box(0));
return v___x_1983_;
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
lean_dec(v___x_1981_);
v___x_1984_ = lean_unsigned_to_nat(1u);
v___x_1985_ = lean_mk_empty_array_with_capacity(v___x_1984_);
lean_inc(v_module_1975_);
v___x_1986_ = lean_array_push(v___x_1985_, v_module_1975_);
v___x_1987_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v___x_1986_, v_a_1978_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v___x_1988_; 
lean_dec_ref_known(v___x_1987_, 1);
v___x_1988_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1975_, v_decls_1976_, v_f_1977_, v_a_1978_);
return v___x_1988_;
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec_ref(v_f_1977_);
lean_dec_ref(v_decls_1976_);
lean_dec(v_module_1975_);
v_a_1989_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1987_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1987_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___boxed(lean_object* v_kind_1997_, lean_object* v_module_1998_, lean_object* v_decls_1999_, lean_object* v_f_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
uint8_t v_kind_boxed_2003_; lean_object* v_res_2004_; 
v_kind_boxed_2003_ = lean_unbox(v_kind_1997_);
v_res_2004_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v_kind_boxed_2003_, v_module_1998_, v_decls_1999_, v_f_2000_, v_a_2001_);
lean_dec_ref(v_a_2001_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(lean_object* v_00_u03b1_2005_, uint8_t v_kind_2006_, lean_object* v_module_2007_, lean_object* v_decls_2008_, lean_object* v_f_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v_kind_2006_, v_module_2007_, v_decls_2008_, v_f_2009_, v_a_2010_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___boxed(lean_object* v_00_u03b1_2013_, lean_object* v_kind_2014_, lean_object* v_module_2015_, lean_object* v_decls_2016_, lean_object* v_f_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
uint8_t v_kind_boxed_2020_; lean_object* v_res_2021_; 
v_kind_boxed_2020_ = lean_unbox(v_kind_2014_);
v_res_2021_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(v_00_u03b1_2013_, v_kind_boxed_2020_, v_module_2015_, v_decls_2016_, v_f_2017_, v_a_2018_);
lean_dec_ref(v_a_2018_);
return v_res_2021_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(lean_object* v_s_2022_, lean_object* v_a_2023_, uint8_t v_b_2024_){
_start:
{
uint8_t v___x_2025_; 
v___x_2025_ = 0;
switch(lean_obj_tag(v_a_2023_))
{
case 0:
{
lean_object* v_pos_2026_; lean_object* v_startInclusive_2027_; lean_object* v_endExclusive_2028_; lean_object* v___x_2029_; uint8_t v_decide_2030_; 
v_pos_2026_ = lean_ctor_get(v_a_2023_, 0);
lean_inc(v_pos_2026_);
lean_dec_ref_known(v_a_2023_, 1);
v_startInclusive_2027_ = lean_ctor_get(v_s_2022_, 1);
v_endExclusive_2028_ = lean_ctor_get(v_s_2022_, 2);
v___x_2029_ = lean_nat_sub(v_endExclusive_2028_, v_startInclusive_2027_);
v_decide_2030_ = lean_nat_dec_eq(v_pos_2026_, v___x_2029_);
lean_dec(v___x_2029_);
lean_dec(v_pos_2026_);
if (v_decide_2030_ == 0)
{
uint8_t v___x_2031_; 
v___x_2031_ = 1;
return v___x_2031_;
}
else
{
return v_decide_2030_;
}
}
case 1:
{
lean_object* v_pos_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2045_; 
v_pos_2032_ = lean_ctor_get(v_a_2023_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_a_2023_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2034_ = v_a_2023_;
v_isShared_2035_ = v_isSharedCheck_2045_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_pos_2032_);
lean_dec(v_a_2023_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2045_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v_str_2036_; lean_object* v_startInclusive_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
v_str_2036_ = lean_ctor_get(v_s_2022_, 0);
v_startInclusive_2037_ = lean_ctor_get(v_s_2022_, 1);
v___x_2038_ = lean_nat_add(v_startInclusive_2037_, v_pos_2032_);
lean_dec(v_pos_2032_);
v___x_2039_ = lean_string_utf8_next_fast(v_str_2036_, v___x_2038_);
lean_dec(v___x_2038_);
v___x_2040_ = lean_nat_sub(v___x_2039_, v_startInclusive_2037_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set_tag(v___x_2034_, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2040_);
v___x_2042_ = v___x_2034_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
v_a_2023_ = v___x_2042_;
v_b_2024_ = v___x_2025_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2046_; lean_object* v_table_2047_; lean_object* v_stackPos_2048_; lean_object* v_needlePos_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2104_; 
v_needle_2046_ = lean_ctor_get(v_a_2023_, 0);
v_table_2047_ = lean_ctor_get(v_a_2023_, 1);
v_stackPos_2048_ = lean_ctor_get(v_a_2023_, 2);
v_needlePos_2049_ = lean_ctor_get(v_a_2023_, 3);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_a_2023_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2051_ = v_a_2023_;
v_isShared_2052_ = v_isSharedCheck_2104_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_needlePos_2049_);
lean_inc(v_stackPos_2048_);
lean_inc(v_table_2047_);
lean_inc(v_needle_2046_);
lean_dec(v_a_2023_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2104_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_str_2053_; lean_object* v_startInclusive_2054_; lean_object* v_endExclusive_2055_; lean_object* v_str_2056_; lean_object* v_startInclusive_2057_; lean_object* v_endExclusive_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v_str_2053_ = lean_ctor_get(v_needle_2046_, 0);
v_startInclusive_2054_ = lean_ctor_get(v_needle_2046_, 1);
v_endExclusive_2055_ = lean_ctor_get(v_needle_2046_, 2);
v_str_2056_ = lean_ctor_get(v_s_2022_, 0);
v_startInclusive_2057_ = lean_ctor_get(v_s_2022_, 1);
v_endExclusive_2058_ = lean_ctor_get(v_s_2022_, 2);
v___x_2059_ = lean_nat_sub(v_stackPos_2048_, v_needlePos_2049_);
v___x_2060_ = lean_nat_sub(v_endExclusive_2055_, v_startInclusive_2054_);
v___x_2061_ = lean_nat_add(v___x_2059_, v___x_2060_);
v___x_2062_ = lean_nat_sub(v_endExclusive_2058_, v_startInclusive_2057_);
v___x_2063_ = lean_nat_dec_le(v___x_2061_, v___x_2062_);
lean_dec(v___x_2061_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
lean_dec(v___x_2060_);
lean_del_object(v___x_2051_);
lean_dec(v_needlePos_2049_);
lean_dec(v_stackPos_2048_);
lean_dec_ref(v_table_2047_);
lean_dec_ref(v_needle_2046_);
v___x_2064_ = lean_unsigned_to_nat(1u);
v___x_2065_ = lean_nat_add(v___x_2059_, v___x_2064_);
lean_dec(v___x_2059_);
v___x_2066_ = lean_nat_dec_le(v___x_2065_, v___x_2062_);
lean_dec(v___x_2062_);
lean_dec(v___x_2065_);
if (v___x_2066_ == 0)
{
return v_b_2024_;
}
else
{
lean_object* v___x_2067_; 
v___x_2067_ = lean_box(3);
v_a_2023_ = v___x_2067_;
v_b_2024_ = v___x_2025_;
goto _start;
}
}
else
{
lean_object* v___x_2069_; uint8_t v_stackByte_2070_; lean_object* v___x_2071_; uint8_t v_patByte_2072_; uint8_t v___x_2073_; 
lean_dec(v___x_2062_);
lean_dec(v___x_2059_);
v___x_2069_ = lean_nat_add(v_startInclusive_2057_, v_stackPos_2048_);
v_stackByte_2070_ = lean_string_get_byte_fast(v_str_2056_, v___x_2069_);
v___x_2071_ = lean_nat_add(v_startInclusive_2054_, v_needlePos_2049_);
v_patByte_2072_ = lean_string_get_byte_fast(v_str_2053_, v___x_2071_);
v___x_2073_ = lean_uint8_dec_eq(v_stackByte_2070_, v_patByte_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; uint8_t v_decide_2075_; 
lean_dec(v___x_2060_);
v___x_2074_ = lean_unsigned_to_nat(0u);
v_decide_2075_ = lean_nat_dec_eq(v_needlePos_2049_, v___x_2074_);
if (v_decide_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v_newNeedlePos_2078_; uint8_t v___x_2079_; 
v___x_2076_ = lean_unsigned_to_nat(1u);
v___x_2077_ = lean_nat_sub(v_needlePos_2049_, v___x_2076_);
lean_dec(v_needlePos_2049_);
v_newNeedlePos_2078_ = lean_array_fget_borrowed(v_table_2047_, v___x_2077_);
lean_dec(v___x_2077_);
v___x_2079_ = lean_nat_dec_eq(v_newNeedlePos_2078_, v___x_2074_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2081_; 
lean_inc(v_newNeedlePos_2078_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 3, v_newNeedlePos_2078_);
v___x_2081_ = v___x_2051_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_needle_2046_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_table_2047_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_stackPos_2048_);
lean_ctor_set(v_reuseFailAlloc_2083_, 3, v_newNeedlePos_2078_);
v___x_2081_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
v_a_2023_ = v___x_2081_;
v_b_2024_ = v___x_2025_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2084_; lean_object* v___x_2086_; 
v_nextStackPos_2084_ = l_String_Slice_posGE___redArg(v_s_2022_, v_stackPos_2048_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 3, v___x_2074_);
lean_ctor_set(v___x_2051_, 2, v_nextStackPos_2084_);
v___x_2086_ = v___x_2051_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_needle_2046_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_table_2047_);
lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_nextStackPos_2084_);
lean_ctor_set(v_reuseFailAlloc_2088_, 3, v___x_2074_);
v___x_2086_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
v_a_2023_ = v___x_2086_;
v_b_2024_ = v___x_2025_;
goto _start;
}
}
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v_nextStackPos_2091_; lean_object* v___x_2093_; 
lean_dec(v_needlePos_2049_);
v___x_2089_ = lean_unsigned_to_nat(1u);
v___x_2090_ = lean_nat_add(v_stackPos_2048_, v___x_2089_);
lean_dec(v_stackPos_2048_);
v_nextStackPos_2091_ = l_String_Slice_posGE___redArg(v_s_2022_, v___x_2090_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 3, v___x_2074_);
lean_ctor_set(v___x_2051_, 2, v_nextStackPos_2091_);
v___x_2093_ = v___x_2051_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_needle_2046_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_table_2047_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v_nextStackPos_2091_);
lean_ctor_set(v_reuseFailAlloc_2095_, 3, v___x_2074_);
v___x_2093_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
v_a_2023_ = v___x_2093_;
v_b_2024_ = v___x_2025_;
goto _start;
}
}
}
else
{
lean_object* v___x_2096_; lean_object* v_nextNeedlePos_2097_; uint8_t v_decide_2098_; 
v___x_2096_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2097_ = lean_nat_add(v_needlePos_2049_, v___x_2096_);
lean_dec(v_needlePos_2049_);
v_decide_2098_ = lean_nat_dec_eq(v_nextNeedlePos_2097_, v___x_2060_);
lean_dec(v___x_2060_);
if (v_decide_2098_ == 0)
{
lean_object* v_nextStackPos_2099_; lean_object* v___x_2101_; 
v_nextStackPos_2099_ = lean_nat_add(v_stackPos_2048_, v___x_2096_);
lean_dec(v_stackPos_2048_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 3, v_nextNeedlePos_2097_);
lean_ctor_set(v___x_2051_, 2, v_nextStackPos_2099_);
v___x_2101_ = v___x_2051_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_needle_2046_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_table_2047_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_nextStackPos_2099_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_nextNeedlePos_2097_);
v___x_2101_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
v_a_2023_ = v___x_2101_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2097_);
lean_del_object(v___x_2051_);
lean_dec(v_stackPos_2048_);
lean_dec_ref(v_table_2047_);
lean_dec_ref(v_needle_2046_);
return v_decide_2098_;
}
}
}
}
}
default: 
{
return v_b_2024_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg___boxed(lean_object* v_s_2105_, lean_object* v_a_2106_, lean_object* v_b_2107_){
_start:
{
uint8_t v_b_boxed_2108_; uint8_t v_res_2109_; lean_object* v_r_2110_; 
v_b_boxed_2108_ = lean_unbox(v_b_2107_);
v_res_2109_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_2105_, v_a_2106_, v_b_boxed_2108_);
lean_dec_ref(v_s_2105_);
v_r_2110_ = lean_box(v_res_2109_);
return v_r_2110_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0));
v___x_2113_ = lean_string_utf8_byte_size(v___x_2112_);
return v___x_2113_;
}
}
static uint8_t _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2115_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1);
v___x_2116_ = lean_nat_dec_eq(v___x_2115_, v___x_2114_);
return v___x_2116_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2117_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1);
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0));
v___x_2120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v___x_2118_);
lean_ctor_set(v___x_2120_, 2, v___x_2117_);
return v___x_2120_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3);
v___x_2122_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2121_);
return v___x_2122_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2123_ = lean_unsigned_to_nat(0u);
v___x_2124_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__4);
v___x_2125_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3);
v___x_2126_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
lean_ctor_set(v___x_2126_, 1, v___x_2124_);
lean_ctor_set(v___x_2126_, 2, v___x_2123_);
lean_ctor_set(v___x_2126_, 3, v___x_2123_);
return v___x_2126_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(lean_object* v_s_2129_){
_start:
{
lean_object* v___y_2131_; uint8_t v___x_2134_; 
v___x_2134_ = lean_uint8_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; 
v___x_2135_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__5);
v___y_2131_ = v___x_2135_;
goto v___jp_2130_;
}
else
{
lean_object* v___x_2136_; 
v___x_2136_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__6));
v___y_2131_ = v___x_2136_;
goto v___jp_2130_;
}
v___jp_2130_:
{
uint8_t v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = 0;
lean_inc(v___y_2131_);
v___x_2133_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_2129_, v___y_2131_, v___x_2132_);
return v___x_2133_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___boxed(lean_object* v_s_2137_){
_start:
{
uint8_t v_res_2138_; lean_object* v_r_2139_; 
v_res_2138_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v_s_2137_);
lean_dec_ref(v_s_2137_);
v_r_2139_ = lean_box(v_res_2138_);
return v_r_2139_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(lean_object* v_kernelName_2140_){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2141_ = lean_unsigned_to_nat(0u);
v___x_2142_ = lean_string_utf8_byte_size(v_kernelName_2140_);
v___x_2143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2143_, 0, v_kernelName_2140_);
lean_ctor_set(v___x_2143_, 1, v___x_2141_);
lean_ctor_set(v___x_2143_, 2, v___x_2142_);
v___x_2144_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v___x_2143_);
lean_dec_ref_known(v___x_2143_, 3);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel___boxed(lean_object* v_kernelName_2145_){
_start:
{
uint8_t v_res_2146_; lean_object* v_r_2147_; 
v_res_2146_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_2145_);
v_r_2147_ = lean_box(v_res_2146_);
return v_r_2147_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(lean_object* v_s_2148_, lean_object* v_inst_2149_, lean_object* v_R_2150_, lean_object* v_a_2151_, uint8_t v_b_2152_, lean_object* v_c_2153_){
_start:
{
uint8_t v___x_2154_; 
v___x_2154_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_2148_, v_a_2151_, v_b_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___boxed(lean_object* v_s_2155_, lean_object* v_inst_2156_, lean_object* v_R_2157_, lean_object* v_a_2158_, lean_object* v_b_2159_, lean_object* v_c_2160_){
_start:
{
uint8_t v_b_boxed_2161_; uint8_t v_res_2162_; lean_object* v_r_2163_; 
v_b_boxed_2161_ = lean_unbox(v_b_2159_);
v_res_2162_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(v_s_2155_, v_inst_2156_, v_R_2157_, v_a_2158_, v_b_boxed_2161_, v_c_2160_);
lean_dec_ref(v_s_2155_);
v_r_2163_ = lean_box(v_res_2162_);
return v_r_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(lean_object* v_a_2164_, lean_object* v_b_2165_){
_start:
{
lean_object* v_array_2166_; lean_object* v_start_2167_; lean_object* v_stop_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2181_; 
v_array_2166_ = lean_ctor_get(v_a_2164_, 0);
v_start_2167_ = lean_ctor_get(v_a_2164_, 1);
v_stop_2168_ = lean_ctor_get(v_a_2164_, 2);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_a_2164_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2170_ = v_a_2164_;
v_isShared_2171_ = v_isSharedCheck_2181_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_stop_2168_);
lean_inc(v_start_2167_);
lean_inc(v_array_2166_);
lean_dec(v_a_2164_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2181_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_nat_dec_lt(v_start_2167_, v_stop_2168_);
if (v___x_2172_ == 0)
{
lean_del_object(v___x_2170_);
lean_dec(v_stop_2168_);
lean_dec(v_start_2167_);
lean_dec_ref(v_array_2166_);
return v_b_2165_;
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2173_ = lean_unsigned_to_nat(1u);
v___x_2174_ = lean_nat_add(v_start_2167_, v___x_2173_);
lean_inc_ref(v_array_2166_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 1, v___x_2174_);
v___x_2176_ = v___x_2170_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_array_2166_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_stop_2168_);
v___x_2176_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = lean_array_fget(v_array_2166_, v_start_2167_);
lean_dec(v_start_2167_);
lean_dec_ref(v_array_2166_);
v___x_2178_ = lean_array_push(v_b_2165_, v___x_2177_);
v_a_2164_ = v___x_2176_;
v_b_2165_ = v___x_2178_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(size_t v_sz_2182_, size_t v_i_2183_, lean_object* v_bs_2184_){
_start:
{
uint8_t v___x_2185_; 
v___x_2185_ = lean_usize_dec_lt(v_i_2183_, v_sz_2182_);
if (v___x_2185_ == 0)
{
return v_bs_2184_;
}
else
{
lean_object* v_v_2186_; lean_object* v___x_2187_; lean_object* v_bs_x27_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; size_t v___x_2191_; size_t v___x_2192_; lean_object* v___x_2193_; 
v_v_2186_ = lean_array_uget(v_bs_2184_, v_i_2183_);
v___x_2187_ = lean_unsigned_to_nat(0u);
v_bs_x27_2188_ = lean_array_uset(v_bs_2184_, v_i_2183_, v___x_2187_);
v___x_2189_ = l_Lean_Name_toString(v_v_2186_, v___x_2185_);
v___x_2190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
v___x_2191_ = ((size_t)1ULL);
v___x_2192_ = lean_usize_add(v_i_2183_, v___x_2191_);
v___x_2193_ = lean_array_uset(v_bs_x27_2188_, v_i_2183_, v___x_2190_);
v_i_2183_ = v___x_2192_;
v_bs_2184_ = v___x_2193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0___boxed(lean_object* v_sz_2195_, lean_object* v_i_2196_, lean_object* v_bs_2197_){
_start:
{
size_t v_sz_boxed_2198_; size_t v_i_boxed_2199_; lean_object* v_res_2200_; 
v_sz_boxed_2198_ = lean_unbox_usize(v_sz_2195_);
lean_dec(v_sz_2195_);
v_i_boxed_2199_ = lean_unbox_usize(v_i_2196_);
lean_dec(v_i_2196_);
v_res_2200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_boxed_2198_, v_i_boxed_2199_, v_bs_2197_);
return v_res_2200_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = lean_unsigned_to_nat(4u);
v___x_2225_ = l_Lean_JsonNumber_fromNat(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15);
v___x_2227_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
return v___x_2227_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2228_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16);
v___x_2229_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14));
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v___x_2228_);
return v___x_2230_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24));
v___x_2248_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17);
v___x_2249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v___x_2247_);
return v___x_2249_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25);
v___x_2251_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13));
v___x_2252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v___x_2250_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(lean_object* v_kernelName_2253_, lean_object* v_solutionPath_2254_, lean_object* v___x_2255_, lean_object* v_kernelCommand_2256_, lean_object* v_configHandle_2257_, lean_object* v_configPath_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_a_2262_; lean_object* v_legalAxioms_2289_; uint8_t v___x_2290_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v_kernelArgs_2364_; lean_object* v___y_2365_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; size_t v_sz_2376_; size_t v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_legalAxioms_2289_ = lean_ctor_get(v___y_2259_, 5);
v___x_2290_ = 0;
v___x_2371_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9));
v___x_2372_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10));
lean_inc_ref(v_solutionPath_2254_);
v___x_2373_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2373_, 0, v_solutionPath_2254_);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
v_sz_2376_ = lean_array_size(v_legalAxioms_2289_);
v___x_2377_ = ((size_t)0ULL);
lean_inc_ref(v_legalAxioms_2289_);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_2376_, v___x_2377_, v_legalAxioms_2289_);
v___x_2379_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
v___x_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2375_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26);
v___x_2382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2380_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2374_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2371_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = l_Lean_Json_mkObj(v___x_2384_);
lean_dec_ref_known(v___x_2384_, 2);
v___x_2386_ = l_Lean_Json_compress(v___x_2385_);
v___x_2387_ = lean_io_prim_handle_put_str(v_configHandle_2257_, v___x_2386_);
lean_dec_ref(v___x_2386_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v___x_2388_; 
lean_dec_ref_known(v___x_2387_, 1);
v___x_2388_ = lean_io_prim_handle_flush(v_configHandle_2257_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; 
lean_dec_ref_known(v___x_2388_, 1);
v___x_2389_ = lean_unsigned_to_nat(1u);
v___x_2390_ = lean_array_get_size(v_kernelCommand_2256_);
lean_inc_ref(v_kernelCommand_2256_);
v___x_2391_ = l_Array_toSubarray___redArg(v_kernelCommand_2256_, v___x_2389_, v___x_2390_);
v___x_2392_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_2393_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v___x_2391_, v___x_2392_);
lean_inc_ref(v_kernelName_2253_);
v___x_2394_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_2253_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; 
lean_inc_ref(v_solutionPath_2254_);
v___x_2395_ = lean_array_push(v___x_2393_, v_solutionPath_2254_);
v_kernelArgs_2364_ = v___x_2395_;
v___y_2365_ = v___y_2259_;
goto v___jp_2363_;
}
else
{
lean_object* v___x_2396_; 
lean_inc_ref(v_configPath_2258_);
v___x_2396_ = lean_array_push(v___x_2393_, v_configPath_2258_);
v_kernelArgs_2364_ = v___x_2396_;
v___y_2365_ = v___y_2259_;
goto v___jp_2363_;
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_configPath_2258_);
lean_dec_ref(v_kernelCommand_2256_);
lean_dec_ref(v_solutionPath_2254_);
lean_dec_ref(v_kernelName_2253_);
v_a_2397_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2388_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2388_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec_ref(v_configPath_2258_);
lean_dec_ref(v_kernelCommand_2256_);
lean_dec_ref(v_solutionPath_2254_);
lean_dec_ref(v_kernelName_2253_);
v_a_2405_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2387_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2387_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
v___jp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2263_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__0));
v___x_2264_ = lean_string_append(v___x_2263_, v_kernelName_2253_);
lean_dec_ref(v_kernelName_2253_);
v___x_2265_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__1));
lean_inc_ref(v___x_2264_);
v___x_2266_ = lean_string_append(v___x_2264_, v___x_2265_);
v___x_2267_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2266_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2279_; 
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2279_ == 0)
{
lean_object* v_unused_2280_; 
v_unused_2280_ = lean_ctor_get(v___x_2267_, 0);
lean_dec(v_unused_2280_);
v___x_2269_ = v___x_2267_;
v_isShared_2270_ = v_isSharedCheck_2279_;
goto v_resetjp_2268_;
}
else
{
lean_dec(v___x_2267_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2279_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2271_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__2));
v___x_2272_ = lean_string_append(v___x_2264_, v___x_2271_);
v___x_2273_ = lean_io_error_to_string(v_a_2262_);
v___x_2274_ = lean_string_append(v___x_2272_, v___x_2273_);
lean_dec_ref(v___x_2273_);
v___x_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2275_);
v___x_2277_ = v___x_2269_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_dec_ref(v___x_2264_);
lean_dec(v_a_2262_);
v_a_2281_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2267_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2267_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
v___jp_2291_:
{
lean_object* v_leanPrefix_2296_; lean_object* v___x_2297_; 
v_leanPrefix_2296_ = lean_ctor_get(v___y_2294_, 6);
v___x_2297_ = lean_uv_os_tmpdir();
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__4));
v___x_2300_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_2301_ = lean_unsigned_to_nat(4u);
v___x_2302_ = lean_mk_empty_array_with_capacity(v___x_2301_);
v___x_2303_ = lean_array_push(v___x_2302_, v_configPath_2258_);
v___x_2304_ = lean_array_push(v___x_2303_, v_solutionPath_2254_);
lean_inc_ref(v___y_2295_);
v___x_2305_ = lean_array_push(v___x_2304_, v___y_2295_);
lean_inc_ref(v_leanPrefix_2296_);
v___x_2306_ = lean_array_push(v___x_2305_, v_leanPrefix_2296_);
v___x_2307_ = lean_mk_empty_array_with_capacity(v___y_2293_);
v___x_2308_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2309_, 0, v_a_2298_);
v___x_2310_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_2310_, 0, v___y_2295_);
lean_ctor_set(v___x_2310_, 1, v___y_2292_);
lean_ctor_set(v___x_2310_, 2, v___x_2299_);
lean_ctor_set(v___x_2310_, 3, v___x_2300_);
lean_ctor_set(v___x_2310_, 4, v___x_2306_);
lean_ctor_set(v___x_2310_, 5, v___x_2307_);
lean_ctor_set(v___x_2310_, 6, v___x_2308_);
lean_ctor_set(v___x_2310_, 7, v___x_2309_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*8, v___x_2290_);
v___x_2311_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v___x_2310_, v___y_2294_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2353_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_2353_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2353_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
uint32_t v___x_2316_; uint32_t v___x_2317_; uint8_t v___x_2318_; 
v___x_2316_ = 0;
v___x_2317_ = lean_unbox_uint32(v_a_2312_);
v___x_2318_ = lean_uint32_dec_eq(v___x_2317_, v___x_2316_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5));
lean_inc_ref(v_kernelName_2253_);
v___x_2320_ = lean_string_append(v_kernelName_2253_, v___x_2319_);
v___x_2321_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2320_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2337_; 
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; 
v_unused_2338_ = lean_ctor_get(v___x_2321_, 0);
lean_dec(v_unused_2338_);
v___x_2323_ = v___x_2321_;
v_isShared_2324_ = v_isSharedCheck_2337_;
goto v_resetjp_2322_;
}
else
{
lean_dec(v___x_2321_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2337_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; uint32_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2325_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6));
v___x_2326_ = lean_string_append(v_kernelName_2253_, v___x_2325_);
v___x_2327_ = lean_unbox_uint32(v_a_2312_);
lean_dec(v_a_2312_);
v___x_2328_ = lean_uint32_to_nat(v___x_2327_);
v___x_2329_ = l_Nat_reprFast(v___x_2328_);
v___x_2330_ = lean_string_append(v___x_2326_, v___x_2329_);
lean_dec_ref(v___x_2329_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set_tag(v___x_2314_, 1);
lean_ctor_set(v___x_2314_, 0, v___x_2330_);
v___x_2332_ = v___x_2314_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2334_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2332_);
v___x_2334_ = v___x_2323_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
else
{
lean_object* v_a_2339_; 
lean_del_object(v___x_2314_);
lean_dec(v_a_2312_);
v_a_2339_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2321_, 1);
v_a_2262_ = v_a_2339_;
goto v___jp_2261_;
}
}
else
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_del_object(v___x_2314_);
lean_dec(v_a_2312_);
v___x_2340_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7));
lean_inc_ref(v_kernelName_2253_);
v___x_2341_ = lean_string_append(v_kernelName_2253_, v___x_2340_);
v___x_2342_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2341_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v_kernelName_2253_);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2350_ == 0)
{
lean_object* v_unused_2351_; 
v_unused_2351_ = lean_ctor_get(v___x_2342_, 0);
lean_dec(v_unused_2351_);
v___x_2344_ = v___x_2342_;
v_isShared_2345_ = v_isSharedCheck_2350_;
goto v_resetjp_2343_;
}
else
{
lean_dec(v___x_2342_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2350_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2346_ = lean_box(0);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2346_);
v___x_2348_ = v___x_2344_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
else
{
lean_object* v_a_2352_; 
v_a_2352_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2342_, 1);
v_a_2262_ = v_a_2352_;
goto v___jp_2261_;
}
}
}
}
else
{
lean_object* v_a_2354_; 
v_a_2354_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2311_, 1);
v_a_2262_ = v_a_2354_;
goto v___jp_2261_;
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec_ref(v___y_2295_);
lean_dec_ref(v___y_2292_);
lean_dec_ref(v_configPath_2258_);
lean_dec_ref(v_solutionPath_2254_);
lean_dec_ref(v_kernelName_2253_);
v_a_2355_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2297_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2297_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
v___jp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v_a_2369_; 
v___x_2366_ = lean_unsigned_to_nat(0u);
v___x_2367_ = lean_array_get(v___x_2255_, v_kernelCommand_2256_, v___x_2366_);
lean_dec_ref(v_kernelCommand_2256_);
lean_inc(v___x_2367_);
v___x_2368_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_2367_);
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref(v___x_2368_);
if (lean_obj_tag(v_a_2369_) == 0)
{
v___y_2292_ = v_kernelArgs_2364_;
v___y_2293_ = v___x_2366_;
v___y_2294_ = v___y_2365_;
v___y_2295_ = v___x_2367_;
goto v___jp_2291_;
}
else
{
lean_object* v_val_2370_; 
lean_dec(v___x_2367_);
v_val_2370_ = lean_ctor_get(v_a_2369_, 0);
lean_inc(v_val_2370_);
lean_dec_ref_known(v_a_2369_, 1);
v___y_2292_ = v_kernelArgs_2364_;
v___y_2293_ = v___x_2366_;
v___y_2294_ = v___y_2365_;
v___y_2295_ = v_val_2370_;
goto v___jp_2291_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed(lean_object* v_kernelName_2413_, lean_object* v_solutionPath_2414_, lean_object* v___x_2415_, lean_object* v_kernelCommand_2416_, lean_object* v_configHandle_2417_, lean_object* v_configPath_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(v_kernelName_2413_, v_solutionPath_2414_, v___x_2415_, v_kernelCommand_2416_, v_configHandle_2417_, v_configPath_2418_, v___y_2419_);
lean_dec_ref(v___y_2419_);
lean_dec(v_configHandle_2417_);
lean_dec_ref(v___x_2415_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(lean_object* v_kernelName_2424_, lean_object* v_kernelCommand_2425_, lean_object* v_solutionPath_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2429_; lean_object* v___f_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2429_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
lean_inc_ref(v_kernelName_2424_);
v___f_2430_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed), 8, 4);
lean_closure_set(v___f_2430_, 0, v_kernelName_2424_);
lean_closure_set(v___f_2430_, 1, v_solutionPath_2426_);
lean_closure_set(v___f_2430_, 2, v___x_2429_);
lean_closure_set(v___f_2430_, 3, v_kernelCommand_2425_);
v___x_2431_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0));
v___x_2432_ = lean_string_append(v___x_2431_, v_kernelName_2424_);
lean_dec_ref(v_kernelName_2424_);
v___x_2433_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1));
v___x_2434_ = lean_string_append(v___x_2432_, v___x_2433_);
v___x_2435_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2434_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v___x_2436_; 
lean_dec_ref_known(v___x_2435_, 1);
v___x_2436_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v___f_2430_, v_a_2427_);
return v___x_2436_;
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec_ref(v___f_2430_);
v_a_2437_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2435_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2435_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___boxed(lean_object* v_kernelName_2445_, lean_object* v_kernelCommand_2446_, lean_object* v_solutionPath_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_kernelName_2445_, v_kernelCommand_2446_, v_solutionPath_2447_, v_a_2448_);
lean_dec_ref(v_a_2448_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1(lean_object* v_inst_2451_, lean_object* v_R_2452_, lean_object* v_a_2453_, lean_object* v_b_2454_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v_a_2453_, v_b_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(lean_object* v_solutionPath_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_whichLeanChecker_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_whichLeanChecker_2462_ = lean_ctor_get(v_a_2460_, 13);
v___x_2463_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0));
v___x_2464_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_2465_ = lean_unsigned_to_nat(3u);
v___x_2466_ = lean_mk_empty_array_with_capacity(v___x_2465_);
lean_inc_ref(v_whichLeanChecker_2462_);
v___x_2467_ = lean_array_push(v___x_2466_, v_whichLeanChecker_2462_);
v___x_2468_ = lean_array_push(v___x_2467_, v___x_2463_);
v___x_2469_ = lean_array_push(v___x_2468_, v___x_2464_);
v___x_2470_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2));
v___x_2471_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v___x_2470_, v___x_2469_, v_solutionPath_2459_, v_a_2460_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___boxed(lean_object* v_solutionPath_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_solutionPath_2472_, v_a_2473_);
lean_dec_ref(v_a_2473_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(lean_object* v_exportPath_2476_, lean_object* v_as_2477_, size_t v_sz_2478_, size_t v_i_2479_, lean_object* v_b_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v_a_2484_; uint8_t v___x_2488_; 
v___x_2488_ = lean_usize_dec_lt(v_i_2479_, v_sz_2478_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; 
lean_dec_ref(v_exportPath_2476_);
v___x_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_b_2480_);
return v___x_2489_;
}
else
{
lean_object* v_a_2490_; lean_object* v_fst_2491_; lean_object* v_snd_2492_; lean_object* v___x_2493_; 
v_a_2490_ = lean_array_uget_borrowed(v_as_2477_, v_i_2479_);
v_fst_2491_ = lean_ctor_get(v_a_2490_, 0);
v_snd_2492_ = lean_ctor_get(v_a_2490_, 1);
lean_inc_ref(v_exportPath_2476_);
lean_inc(v_snd_2492_);
lean_inc(v_fst_2491_);
v___x_2493_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_fst_2491_, v_snd_2492_, v_exportPath_2476_, v___y_2481_);
if (lean_obj_tag(v___x_2493_) == 0)
{
if (lean_obj_tag(v_b_2480_) == 0)
{
lean_object* v_a_2494_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
v_a_2484_ = v_a_2494_;
goto v___jp_2483_;
}
else
{
lean_dec_ref_known(v___x_2493_, 1);
v_a_2484_ = v_b_2480_;
goto v___jp_2483_;
}
}
else
{
lean_dec(v_b_2480_);
lean_dec_ref(v_exportPath_2476_);
return v___x_2493_;
}
}
v___jp_2483_:
{
size_t v___x_2485_; size_t v___x_2486_; 
v___x_2485_ = ((size_t)1ULL);
v___x_2486_ = lean_usize_add(v_i_2479_, v___x_2485_);
v_i_2479_ = v___x_2486_;
v_b_2480_ = v_a_2484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0___boxed(lean_object* v_exportPath_2495_, lean_object* v_as_2496_, lean_object* v_sz_2497_, lean_object* v_i_2498_, lean_object* v_b_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
size_t v_sz_boxed_2502_; size_t v_i_boxed_2503_; lean_object* v_res_2504_; 
v_sz_boxed_2502_ = lean_unbox_usize(v_sz_2497_);
lean_dec(v_sz_2497_);
v_i_boxed_2503_ = lean_unbox_usize(v_i_2498_);
lean_dec(v_i_2498_);
v_res_2504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(v_exportPath_2495_, v_as_2496_, v_sz_boxed_2502_, v_i_boxed_2503_, v_b_2499_, v___y_2500_);
lean_dec_ref(v___y_2500_);
lean_dec_ref(v_as_2496_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(lean_object* v_exportPath_2505_, lean_object* v_init_2506_, lean_object* v_x_2507_, lean_object* v___y_2508_){
_start:
{
if (lean_obj_tag(v_x_2507_) == 0)
{
lean_object* v_k_2510_; lean_object* v_v_2511_; lean_object* v_l_2512_; lean_object* v_r_2513_; lean_object* v___x_2514_; 
v_k_2510_ = lean_ctor_get(v_x_2507_, 1);
lean_inc(v_k_2510_);
v_v_2511_ = lean_ctor_get(v_x_2507_, 2);
lean_inc(v_v_2511_);
v_l_2512_ = lean_ctor_get(v_x_2507_, 3);
lean_inc(v_l_2512_);
v_r_2513_ = lean_ctor_get(v_x_2507_, 4);
lean_inc(v_r_2513_);
lean_dec_ref_known(v_x_2507_, 5);
lean_inc_ref(v_exportPath_2505_);
v___x_2514_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(v_exportPath_2505_, v_init_2506_, v_l_2512_, v___y_2508_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v_a_2516_; lean_object* v___x_2517_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v_a_2516_ = lean_ctor_get(v_a_2515_, 0);
lean_inc(v_a_2516_);
lean_dec(v_a_2515_);
lean_inc_ref(v_exportPath_2505_);
v___x_2517_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_k_2510_, v_v_2511_, v_exportPath_2505_, v___y_2508_);
if (lean_obj_tag(v___x_2517_) == 0)
{
if (lean_obj_tag(v_a_2516_) == 0)
{
lean_object* v_a_2518_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
lean_dec_ref_known(v___x_2517_, 1);
v_init_2506_ = v_a_2518_;
v_x_2507_ = v_r_2513_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_2517_, 1);
v_init_2506_ = v_a_2516_;
v_x_2507_ = v_r_2513_;
goto _start;
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec(v_a_2516_);
lean_dec(v_r_2513_);
lean_dec_ref(v_exportPath_2505_);
v_a_2521_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2517_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2517_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
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
else
{
lean_dec(v_r_2513_);
lean_dec(v_v_2511_);
lean_dec(v_k_2510_);
lean_dec_ref(v_exportPath_2505_);
return v___x_2514_;
}
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec_ref(v_exportPath_2505_);
v___x_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_init_2506_);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
return v___x_2530_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1___boxed(lean_object* v_exportPath_2531_, lean_object* v_init_2532_, lean_object* v_x_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(v_exportPath_2531_, v_init_2532_, v_x_2533_, v___y_2534_);
lean_dec_ref(v___y_2534_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runKernels(lean_object* v_exportPath_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v_val_2541_; lean_object* v_externalKernels_2544_; lean_object* v_bundledKernels_2545_; lean_object* v_a_2547_; lean_object* v_result_2580_; lean_object* v___x_2581_; 
v_externalKernels_2544_ = lean_ctor_get(v_a_2538_, 15);
v_bundledKernels_2545_ = lean_ctor_get(v_a_2538_, 16);
v_result_2580_ = lean_box(0);
lean_inc(v_externalKernels_2544_);
lean_inc_ref(v_exportPath_2537_);
v___x_2581_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(v_exportPath_2537_, v_result_2580_, v_externalKernels_2544_, v_a_2538_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v_a_2583_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v_a_2583_ = lean_ctor_get(v_a_2582_, 0);
lean_inc(v_a_2583_);
lean_dec(v_a_2582_);
v_a_2547_ = v_a_2583_;
goto v___jp_2546_;
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec_ref(v_exportPath_2537_);
v_a_2584_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2581_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2581_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
v___jp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_mk_io_user_error(v_val_2541_);
v___x_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
return v___x_2543_;
}
v___jp_2546_:
{
size_t v_sz_2548_; size_t v___x_2549_; lean_object* v___x_2550_; 
v_sz_2548_ = lean_array_size(v_bundledKernels_2545_);
v___x_2549_ = ((size_t)0ULL);
lean_inc_ref(v_exportPath_2537_);
v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(v_exportPath_2537_, v_bundledKernels_2545_, v_sz_2548_, v___x_2549_, v_a_2547_, v_a_2538_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2552_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2550_, 1);
v___x_2552_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_exportPath_2537_, v_a_2538_);
if (lean_obj_tag(v___x_2552_) == 0)
{
if (lean_obj_tag(v_a_2551_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2562_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2562_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2562_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
if (lean_obj_tag(v_a_2553_) == 1)
{
lean_object* v_val_2557_; 
lean_del_object(v___x_2555_);
v_val_2557_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_val_2557_);
lean_dec_ref_known(v_a_2553_, 1);
v_val_2541_ = v_val_2557_;
goto v___jp_2540_;
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
lean_dec(v_a_2553_);
v___x_2558_ = lean_box(0);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2558_);
v___x_2560_ = v___x_2555_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v_val_2563_; 
lean_dec_ref_known(v___x_2552_, 1);
v_val_2563_ = lean_ctor_get(v_a_2551_, 0);
lean_inc(v_val_2563_);
lean_dec_ref_known(v_a_2551_, 1);
v_val_2541_ = v_val_2563_;
goto v___jp_2540_;
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec(v_a_2551_);
v_a_2564_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2552_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2552_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec_ref(v_exportPath_2537_);
v_a_2572_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2550_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2550_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runKernels___boxed(lean_object* v_exportPath_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l___private_Lake_CLI_Check_0__Lake_Check_runKernels(v_exportPath_2592_, v_a_2593_);
lean_dec_ref(v_a_2593_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg(){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__52));
v___x_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___boxed(lean_object* v_a_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(lean_object* v_a_2750_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___boxed(lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(v_a_2753_);
lean_dec_ref(v_a_2753_);
return v_res_2755_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(lean_object* v_a_2756_, lean_object* v_as_2757_, size_t v_i_2758_, size_t v_stop_2759_){
_start:
{
uint8_t v___x_2760_; 
v___x_2760_ = lean_usize_dec_eq(v_i_2758_, v_stop_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2761_ = lean_array_uget_borrowed(v_as_2757_, v_i_2758_);
v___x_2762_ = lean_name_eq(v_a_2756_, v___x_2761_);
if (v___x_2762_ == 0)
{
size_t v___x_2763_; size_t v___x_2764_; 
v___x_2763_ = ((size_t)1ULL);
v___x_2764_ = lean_usize_add(v_i_2758_, v___x_2763_);
v_i_2758_ = v___x_2764_;
goto _start;
}
else
{
return v___x_2762_;
}
}
else
{
uint8_t v___x_2766_; 
v___x_2766_ = 0;
return v___x_2766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0___boxed(lean_object* v_a_2767_, lean_object* v_as_2768_, lean_object* v_i_2769_, lean_object* v_stop_2770_){
_start:
{
size_t v_i_boxed_2771_; size_t v_stop_boxed_2772_; uint8_t v_res_2773_; lean_object* v_r_2774_; 
v_i_boxed_2771_ = lean_unbox_usize(v_i_2769_);
lean_dec(v_i_2769_);
v_stop_boxed_2772_ = lean_unbox_usize(v_stop_2770_);
lean_dec(v_stop_2770_);
v_res_2773_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_2767_, v_as_2768_, v_i_boxed_2771_, v_stop_boxed_2772_);
lean_dec_ref(v_as_2768_);
lean_dec(v_a_2767_);
v_r_2774_ = lean_box(v_res_2773_);
return v_r_2774_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(lean_object* v_as_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
v___x_2777_ = lean_unsigned_to_nat(0u);
v___x_2778_ = lean_array_get_size(v_as_2775_);
v___x_2779_ = lean_nat_dec_lt(v___x_2777_, v___x_2778_);
if (v___x_2779_ == 0)
{
return v___x_2779_;
}
else
{
if (v___x_2779_ == 0)
{
return v___x_2779_;
}
else
{
size_t v___x_2780_; size_t v___x_2781_; uint8_t v___x_2782_; 
v___x_2780_ = ((size_t)0ULL);
v___x_2781_ = lean_usize_of_nat(v___x_2778_);
v___x_2782_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_2776_, v_as_2775_, v___x_2780_, v___x_2781_);
return v___x_2782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0___boxed(lean_object* v_as_2783_, lean_object* v_a_2784_){
_start:
{
uint8_t v_res_2785_; lean_object* v_r_2786_; 
v_res_2785_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_as_2783_, v_a_2784_);
lean_dec(v_a_2784_);
lean_dec_ref(v_as_2783_);
v_r_2786_ = lean_box(v_res_2785_);
return v_r_2786_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11(void){
_start:
{
lean_object* v___x_2817_; lean_object* v_additional_2818_; lean_object* v___x_2819_; 
v___x_2817_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__10));
v_additional_2818_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_2819_ = l_Array_append___redArg(v_additional_2818_, v___x_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(lean_object* v_a_2820_){
_start:
{
lean_object* v_legalAxioms_2822_; lean_object* v_additional_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; 
v_legalAxioms_2822_ = lean_ctor_get(v_a_2820_, 5);
v_additional_2823_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_2824_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3));
v___x_2825_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_legalAxioms_2822_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; 
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v_additional_2823_);
return v___x_2826_;
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___boxed(lean_object* v_a_2829_, lean_object* v_a_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_2829_);
lean_dec_ref(v_a_2829_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(lean_object* v_e_2832_){
_start:
{
if (lean_obj_tag(v_e_2832_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2842_; 
v_a_2834_ = lean_ctor_get(v_e_2832_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_e_2832_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2836_ = v_e_2832_;
v_isShared_2837_ = v_isSharedCheck_2842_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v_e_2832_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2842_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2838_ = lean_mk_io_user_error(v_a_2834_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set_tag(v___x_2836_, 1);
lean_ctor_set(v___x_2836_, 0, v___x_2838_);
v___x_2840_ = v___x_2836_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
v_a_2843_ = lean_ctor_get(v_e_2832_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_e_2832_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v_e_2832_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v_e_2832_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 0);
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg___boxed(lean_object* v_e_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v_e_2851_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(lean_object* v_00_u03b1_2854_, lean_object* v_e_2855_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v_e_2855_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___boxed(lean_object* v_00_u03b1_2858_, lean_object* v_e_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(v_00_u03b1_2858_, v_e_2859_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(lean_object* v_challengeExportPath_2862_, lean_object* v_solutionExportPath_2863_, lean_object* v_a_2864_){
_start:
{
uint8_t v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = 0;
v___x_2867_ = lean_io_prim_handle_mk(v_challengeExportPath_2862_, v___x_2866_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v___x_2869_ = lean_stream_of_handle(v_a_2868_);
v___x_2870_ = l_LeanExport_parseStream(v___x_2869_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2872_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref_known(v___x_2870_, 1);
v___x_2872_ = lean_io_prim_handle_mk(v_solutionExportPath_2863_, v___x_2866_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
v___x_2874_ = lean_stream_of_handle(v_a_2873_);
v___x_2875_ = l_LeanExport_parseStream(v___x_2874_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v_theoremNames_2877_; lean_object* v_definitionNames_2878_; lean_object* v_legalAxioms_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v_a_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc_n(v_a_2876_, 2);
lean_dec_ref_known(v___x_2875_, 1);
v_theoremNames_2877_ = lean_ctor_get(v_a_2864_, 3);
v_definitionNames_2878_ = lean_ctor_get(v_a_2864_, 4);
v_legalAxioms_2879_ = lean_ctor_get(v_a_2864_, 5);
lean_inc_ref(v_theoremNames_2877_);
v___x_2880_ = l_Array_append___redArg(v_theoremNames_2877_, v_legalAxioms_2879_);
v___x_2881_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref(v___x_2881_);
v___x_2883_ = l_Lake_Check_compareAt(v_a_2871_, v_a_2876_, v___x_2880_, v_definitionNames_2878_, v_a_2882_);
lean_dec_ref(v___x_2880_);
v___x_2884_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v___x_2883_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec_ref_known(v___x_2884_, 1);
v___x_2885_ = l_Lake_Check_checkAxioms(v_a_2876_, v_theoremNames_2877_, v_definitionNames_2878_, v_legalAxioms_2879_);
v___x_2886_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v___x_2885_);
return v___x_2886_;
}
else
{
lean_dec(v_a_2876_);
return v___x_2884_;
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v_a_2871_);
v_a_2887_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2875_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2875_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec(v_a_2871_);
v_a_2895_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2872_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2872_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
v_a_2903_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2870_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2870_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
v_a_2911_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2867_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2867_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare___boxed(lean_object* v_challengeExportPath_2919_, lean_object* v_solutionExportPath_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(v_challengeExportPath_2919_, v_solutionExportPath_2920_, v_a_2921_);
lean_dec_ref(v_a_2921_);
lean_dec_ref(v_solutionExportPath_2920_);
lean_dec_ref(v_challengeExportPath_2919_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(lean_object* v_challengeExportPath_2924_, lean_object* v_solutionExportPath_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(v_challengeExportPath_2924_, v_solutionExportPath_2925_, v_a_2926_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v___x_2929_; 
lean_dec_ref_known(v___x_2928_, 1);
v___x_2929_ = l___private_Lake_CLI_Check_0__Lake_Check_runKernels(v_solutionExportPath_2925_, v_a_2926_);
return v___x_2929_;
}
else
{
lean_dec_ref(v_solutionExportPath_2925_);
return v___x_2928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch___boxed(lean_object* v_challengeExportPath_2930_, lean_object* v_solutionExportPath_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExportPath_2930_, v_solutionExportPath_2931_, v_a_2932_);
lean_dec_ref(v_a_2932_);
lean_dec_ref(v_challengeExportPath_2930_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0(lean_object* v_challengeExportPath_2936_, lean_object* v_solutionExportPath_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExportPath_2936_, v_solutionExportPath_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec_ref_known(v___x_2940_, 1);
v___x_2941_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___closed__0));
v___x_2942_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2941_);
return v___x_2942_;
}
else
{
return v___x_2940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___boxed(lean_object* v_challengeExportPath_2943_, lean_object* v_solutionExportPath_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0(v_challengeExportPath_2943_, v_solutionExportPath_2944_, v___y_2945_);
lean_dec_ref(v___y_2945_);
lean_dec_ref(v_challengeExportPath_2943_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1(lean_object* v___x_2948_, lean_object* v_challengeExportPath_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_solutionModule_2952_; lean_object* v___f_2953_; uint8_t v___x_2954_; lean_object* v___x_2955_; 
v_solutionModule_2952_ = lean_ctor_get(v___y_2950_, 2);
v___f_2953_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2953_, 0, v_challengeExportPath_2949_);
v___x_2954_ = 1;
lean_inc(v_solutionModule_2952_);
v___x_2955_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v___x_2954_, v_solutionModule_2952_, v___x_2948_, v___f_2953_, v___y_2950_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1___boxed(lean_object* v___x_2956_, lean_object* v_challengeExportPath_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1(v___x_2956_, v_challengeExportPath_2957_, v___y_2958_);
lean_dec_ref(v___y_2958_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt(lean_object* v_a_2961_){
_start:
{
lean_object* v___x_2963_; lean_object* v_a_2964_; lean_object* v_challengeModule_2965_; lean_object* v_theoremNames_2966_; lean_object* v_definitionNames_2967_; lean_object* v_legalAxioms_2968_; lean_object* v___x_2969_; lean_object* v_a_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___f_2975_; uint8_t v___x_2976_; lean_object* v___x_2977_; 
v___x_2963_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_2961_);
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref(v___x_2963_);
v_challengeModule_2965_ = lean_ctor_get(v_a_2961_, 1);
v_theoremNames_2966_ = lean_ctor_get(v_a_2961_, 3);
v_definitionNames_2967_ = lean_ctor_get(v_a_2961_, 4);
v_legalAxioms_2968_ = lean_ctor_get(v_a_2961_, 5);
v___x_2969_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref(v___x_2969_);
v___x_2971_ = l_Array_append___redArg(v_a_2964_, v_theoremNames_2966_);
v___x_2972_ = l_Array_append___redArg(v___x_2971_, v_legalAxioms_2968_);
v___x_2973_ = l_Array_append___redArg(v___x_2972_, v_a_2970_);
lean_dec(v_a_2970_);
v___x_2974_ = l_Array_append___redArg(v___x_2973_, v_definitionNames_2967_);
lean_inc_ref(v___x_2974_);
v___f_2975_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2975_, 0, v___x_2974_);
v___x_2976_ = 2;
lean_inc(v_challengeModule_2965_);
v___x_2977_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v___x_2976_, v_challengeModule_2965_, v___x_2974_, v___f_2975_, v_a_2961_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___boxed(lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt(v_a_2978_);
lean_dec_ref(v_a_2978_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(lean_object* v_j_2981_, lean_object* v_k_2982_){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = l_Lean_Json_getObjValD(v_j_2981_, v_k_2982_);
v___x_2984_ = l_Lean_Json_getStr_x3f(v___x_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0___boxed(lean_object* v_j_2985_, lean_object* v_k_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_j_2985_, v_k_2986_);
lean_dec_ref(v_k_2986_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(size_t v_sz_2988_, size_t v_i_2989_, lean_object* v_bs_2990_){
_start:
{
uint8_t v___x_2991_; 
v___x_2991_ = lean_usize_dec_lt(v_i_2989_, v_sz_2988_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2992_, 0, v_bs_2990_);
return v___x_2992_;
}
else
{
lean_object* v_v_2993_; lean_object* v___x_2994_; 
v_v_2993_ = lean_array_uget_borrowed(v_bs_2990_, v_i_2989_);
lean_inc(v_v_2993_);
v___x_2994_ = l_Lean_Json_getStr_x3f(v_v_2993_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec_ref(v_bs_2990_);
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3004_; lean_object* v_bs_x27_3005_; size_t v___x_3006_; size_t v___x_3007_; lean_object* v___x_3008_; 
v_a_3003_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_2994_, 1);
v___x_3004_ = lean_unsigned_to_nat(0u);
v_bs_x27_3005_ = lean_array_uset(v_bs_2990_, v_i_2989_, v___x_3004_);
v___x_3006_ = ((size_t)1ULL);
v___x_3007_ = lean_usize_add(v_i_2989_, v___x_3006_);
v___x_3008_ = lean_array_uset(v_bs_x27_3005_, v_i_2989_, v_a_3003_);
v_i_2989_ = v___x_3007_;
v_bs_2990_ = v___x_3008_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_3010_, lean_object* v_i_3011_, lean_object* v_bs_3012_){
_start:
{
size_t v_sz_boxed_3013_; size_t v_i_boxed_3014_; lean_object* v_res_3015_; 
v_sz_boxed_3013_ = lean_unbox_usize(v_sz_3010_);
lean_dec(v_sz_3010_);
v_i_boxed_3014_ = lean_unbox_usize(v_i_3011_);
lean_dec(v_i_3011_);
v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_3013_, v_i_boxed_3014_, v_bs_3012_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(lean_object* v_x_3018_){
_start:
{
if (lean_obj_tag(v_x_3018_) == 4)
{
lean_object* v_elems_3019_; size_t v_sz_3020_; size_t v___x_3021_; lean_object* v___x_3022_; 
v_elems_3019_ = lean_ctor_get(v_x_3018_, 0);
lean_inc_ref(v_elems_3019_);
lean_dec_ref_known(v_x_3018_, 1);
v_sz_3020_ = lean_array_size(v_elems_3019_);
v___x_3021_ = ((size_t)0ULL);
v___x_3022_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_3020_, v___x_3021_, v_elems_3019_);
return v___x_3022_;
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3023_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__0));
v___x_3024_ = lean_unsigned_to_nat(80u);
v___x_3025_ = l_Lean_Json_pretty(v_x_3018_, v___x_3024_);
v___x_3026_ = lean_string_append(v___x_3023_, v___x_3025_);
lean_dec_ref(v___x_3025_);
v___x_3027_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_3028_ = lean_string_append(v___x_3026_, v___x_3027_);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(lean_object* v_x_3032_){
_start:
{
if (lean_obj_tag(v_x_3032_) == 0)
{
lean_object* v___x_3033_; 
v___x_3033_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3___closed__0));
return v___x_3033_;
}
else
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_x_3032_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3034_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3034_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3051_; 
v_a_3043_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3045_ = v___x_3034_;
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3034_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_a_3043_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3047_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(lean_object* v_j_3052_, lean_object* v_k_3053_){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = l_Lean_Json_getObjValD(v_j_3052_, v_k_3053_);
v___x_3055_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2___boxed(lean_object* v_j_3056_, lean_object* v_k_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_j_3056_, v_k_3057_);
lean_dec_ref(v_k_3057_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(lean_object* v_x_3061_){
_start:
{
if (lean_obj_tag(v_x_3061_) == 0)
{
lean_object* v___x_3062_; 
v___x_3062_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___closed__0));
return v___x_3062_;
}
else
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_Json_getBool_x3f(v_x_3061_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3063_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3063_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3080_; 
v_a_3072_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3074_ = v___x_3063_;
v_isShared_3075_ = v_isSharedCheck_3080_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3063_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3080_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_a_3072_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 0, v___x_3076_);
v___x_3078_ = v___x_3074_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___boxed(lean_object* v_x_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v_x_3081_);
lean_dec(v_x_3081_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(lean_object* v_j_3083_, lean_object* v_k_3084_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = l_Lean_Json_getObjValD(v_j_3083_, v_k_3084_);
v___x_3086_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v___x_3085_);
lean_dec(v___x_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3___boxed(lean_object* v_j_3087_, lean_object* v_k_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_j_3087_, v_k_3088_);
lean_dec_ref(v_k_3088_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_cmp_3090_, lean_object* v_k_3091_, lean_object* v_v_3092_, lean_object* v_t_3093_){
_start:
{
if (lean_obj_tag(v_t_3093_) == 0)
{
lean_object* v_size_3094_; lean_object* v_k_3095_; lean_object* v_v_3096_; lean_object* v_l_3097_; lean_object* v_r_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3379_; 
v_size_3094_ = lean_ctor_get(v_t_3093_, 0);
v_k_3095_ = lean_ctor_get(v_t_3093_, 1);
v_v_3096_ = lean_ctor_get(v_t_3093_, 2);
v_l_3097_ = lean_ctor_get(v_t_3093_, 3);
v_r_3098_ = lean_ctor_get(v_t_3093_, 4);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_t_3093_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3100_ = v_t_3093_;
v_isShared_3101_ = v_isSharedCheck_3379_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_r_3098_);
lean_inc(v_l_3097_);
lean_inc(v_v_3096_);
lean_inc(v_k_3095_);
lean_inc(v_size_3094_);
lean_dec(v_t_3093_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3379_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; uint8_t v___x_3103_; 
lean_inc_ref(v_cmp_3090_);
lean_inc(v_k_3095_);
lean_inc_ref(v_k_3091_);
v___x_3102_ = lean_apply_2(v_cmp_3090_, v_k_3091_, v_k_3095_);
v___x_3103_ = lean_unbox(v___x_3102_);
switch(v___x_3103_)
{
case 0:
{
lean_object* v_impl_3104_; lean_object* v___x_3105_; 
lean_dec(v_size_3094_);
v_impl_3104_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3090_, v_k_3091_, v_v_3092_, v_l_3097_);
v___x_3105_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3098_) == 0)
{
lean_object* v_size_3106_; lean_object* v_size_3107_; lean_object* v_k_3108_; lean_object* v_v_3109_; lean_object* v_l_3110_; lean_object* v_r_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v_size_3106_ = lean_ctor_get(v_r_3098_, 0);
v_size_3107_ = lean_ctor_get(v_impl_3104_, 0);
lean_inc(v_size_3107_);
v_k_3108_ = lean_ctor_get(v_impl_3104_, 1);
lean_inc(v_k_3108_);
v_v_3109_ = lean_ctor_get(v_impl_3104_, 2);
lean_inc(v_v_3109_);
v_l_3110_ = lean_ctor_get(v_impl_3104_, 3);
lean_inc(v_l_3110_);
v_r_3111_ = lean_ctor_get(v_impl_3104_, 4);
lean_inc(v_r_3111_);
v___x_3112_ = lean_unsigned_to_nat(3u);
v___x_3113_ = lean_nat_mul(v___x_3112_, v_size_3106_);
v___x_3114_ = lean_nat_dec_lt(v___x_3113_, v_size_3107_);
lean_dec(v___x_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
lean_dec(v_r_3111_);
lean_dec(v_l_3110_);
lean_dec(v_v_3109_);
lean_dec(v_k_3108_);
v___x_3115_ = lean_nat_add(v___x_3105_, v_size_3107_);
lean_dec(v_size_3107_);
v___x_3116_ = lean_nat_add(v___x_3115_, v_size_3106_);
lean_dec(v___x_3115_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 3, v_impl_3104_);
lean_ctor_set(v___x_3100_, 0, v___x_3116_);
v___x_3118_ = v___x_3100_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3119_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3119_, 3, v_impl_3104_);
lean_ctor_set(v_reuseFailAlloc_3119_, 4, v_r_3098_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
else
{
lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3185_; 
v_isSharedCheck_3185_ = !lean_is_exclusive(v_impl_3104_);
if (v_isSharedCheck_3185_ == 0)
{
lean_object* v_unused_3186_; lean_object* v_unused_3187_; lean_object* v_unused_3188_; lean_object* v_unused_3189_; lean_object* v_unused_3190_; 
v_unused_3186_ = lean_ctor_get(v_impl_3104_, 4);
lean_dec(v_unused_3186_);
v_unused_3187_ = lean_ctor_get(v_impl_3104_, 3);
lean_dec(v_unused_3187_);
v_unused_3188_ = lean_ctor_get(v_impl_3104_, 2);
lean_dec(v_unused_3188_);
v_unused_3189_ = lean_ctor_get(v_impl_3104_, 1);
lean_dec(v_unused_3189_);
v_unused_3190_ = lean_ctor_get(v_impl_3104_, 0);
lean_dec(v_unused_3190_);
v___x_3121_ = v_impl_3104_;
v_isShared_3122_ = v_isSharedCheck_3185_;
goto v_resetjp_3120_;
}
else
{
lean_dec(v_impl_3104_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3185_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v_size_3123_; lean_object* v_size_3124_; lean_object* v_k_3125_; lean_object* v_v_3126_; lean_object* v_l_3127_; lean_object* v_r_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
v_size_3123_ = lean_ctor_get(v_l_3110_, 0);
v_size_3124_ = lean_ctor_get(v_r_3111_, 0);
v_k_3125_ = lean_ctor_get(v_r_3111_, 1);
v_v_3126_ = lean_ctor_get(v_r_3111_, 2);
v_l_3127_ = lean_ctor_get(v_r_3111_, 3);
v_r_3128_ = lean_ctor_get(v_r_3111_, 4);
v___x_3129_ = lean_unsigned_to_nat(2u);
v___x_3130_ = lean_nat_mul(v___x_3129_, v_size_3123_);
v___x_3131_ = lean_nat_dec_lt(v_size_3124_, v___x_3130_);
lean_dec(v___x_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3160_; 
lean_inc(v_r_3128_);
lean_inc(v_l_3127_);
lean_inc(v_v_3126_);
lean_inc(v_k_3125_);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_r_3111_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; lean_object* v_unused_3162_; lean_object* v_unused_3163_; lean_object* v_unused_3164_; lean_object* v_unused_3165_; 
v_unused_3161_ = lean_ctor_get(v_r_3111_, 4);
lean_dec(v_unused_3161_);
v_unused_3162_ = lean_ctor_get(v_r_3111_, 3);
lean_dec(v_unused_3162_);
v_unused_3163_ = lean_ctor_get(v_r_3111_, 2);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_r_3111_, 1);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_r_3111_, 0);
lean_dec(v_unused_3165_);
v___x_3133_ = v_r_3111_;
v_isShared_3134_ = v_isSharedCheck_3160_;
goto v_resetjp_3132_;
}
else
{
lean_dec(v_r_3111_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3160_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___x_3148_; lean_object* v___y_3150_; 
v___x_3135_ = lean_nat_add(v___x_3105_, v_size_3107_);
lean_dec(v_size_3107_);
v___x_3136_ = lean_nat_add(v___x_3135_, v_size_3106_);
lean_dec(v___x_3135_);
v___x_3148_ = lean_nat_add(v___x_3105_, v_size_3123_);
if (lean_obj_tag(v_l_3127_) == 0)
{
lean_object* v_size_3158_; 
v_size_3158_ = lean_ctor_get(v_l_3127_, 0);
lean_inc(v_size_3158_);
v___y_3150_ = v_size_3158_;
goto v___jp_3149_;
}
else
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_unsigned_to_nat(0u);
v___y_3150_ = v___x_3159_;
goto v___jp_3149_;
}
v___jp_3137_:
{
lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3141_ = lean_nat_add(v___y_3138_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec(v___y_3138_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 4, v_r_3098_);
lean_ctor_set(v___x_3133_, 3, v_r_3128_);
lean_ctor_set(v___x_3133_, 2, v_v_3096_);
lean_ctor_set(v___x_3133_, 1, v_k_3095_);
lean_ctor_set(v___x_3133_, 0, v___x_3141_);
v___x_3143_ = v___x_3133_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3147_, 3, v_r_3128_);
lean_ctor_set(v_reuseFailAlloc_3147_, 4, v_r_3098_);
v___x_3143_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
lean_object* v___x_3145_; 
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 4, v___x_3143_);
lean_ctor_set(v___x_3121_, 3, v___y_3139_);
lean_ctor_set(v___x_3121_, 2, v_v_3126_);
lean_ctor_set(v___x_3121_, 1, v_k_3125_);
lean_ctor_set(v___x_3121_, 0, v___x_3136_);
v___x_3145_ = v___x_3121_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v_k_3125_);
lean_ctor_set(v_reuseFailAlloc_3146_, 2, v_v_3126_);
lean_ctor_set(v_reuseFailAlloc_3146_, 3, v___y_3139_);
lean_ctor_set(v_reuseFailAlloc_3146_, 4, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
v___jp_3149_:
{
lean_object* v___x_3151_; lean_object* v___x_3153_; 
v___x_3151_ = lean_nat_add(v___x_3148_, v___y_3150_);
lean_dec(v___y_3150_);
lean_dec(v___x_3148_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v_l_3127_);
lean_ctor_set(v___x_3100_, 3, v_l_3110_);
lean_ctor_set(v___x_3100_, 2, v_v_3109_);
lean_ctor_set(v___x_3100_, 1, v_k_3108_);
lean_ctor_set(v___x_3100_, 0, v___x_3151_);
v___x_3153_ = v___x_3100_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v_k_3108_);
lean_ctor_set(v_reuseFailAlloc_3157_, 2, v_v_3109_);
lean_ctor_set(v_reuseFailAlloc_3157_, 3, v_l_3110_);
lean_ctor_set(v_reuseFailAlloc_3157_, 4, v_l_3127_);
v___x_3153_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; 
v___x_3154_ = lean_nat_add(v___x_3105_, v_size_3106_);
if (lean_obj_tag(v_r_3128_) == 0)
{
lean_object* v_size_3155_; 
v_size_3155_ = lean_ctor_get(v_r_3128_, 0);
lean_inc(v_size_3155_);
v___y_3138_ = v___x_3154_;
v___y_3139_ = v___x_3153_;
v___y_3140_ = v_size_3155_;
goto v___jp_3137_;
}
else
{
lean_object* v___x_3156_; 
v___x_3156_ = lean_unsigned_to_nat(0u);
v___y_3138_ = v___x_3154_;
v___y_3139_ = v___x_3153_;
v___y_3140_ = v___x_3156_;
goto v___jp_3137_;
}
}
}
}
}
else
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3171_; 
lean_del_object(v___x_3100_);
v___x_3166_ = lean_nat_add(v___x_3105_, v_size_3107_);
lean_dec(v_size_3107_);
v___x_3167_ = lean_nat_add(v___x_3166_, v_size_3106_);
lean_dec(v___x_3166_);
v___x_3168_ = lean_nat_add(v___x_3105_, v_size_3106_);
v___x_3169_ = lean_nat_add(v___x_3168_, v_size_3124_);
lean_dec(v___x_3168_);
lean_inc_ref(v_r_3098_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 4, v_r_3098_);
lean_ctor_set(v___x_3121_, 3, v_r_3111_);
lean_ctor_set(v___x_3121_, 2, v_v_3096_);
lean_ctor_set(v___x_3121_, 1, v_k_3095_);
lean_ctor_set(v___x_3121_, 0, v___x_3169_);
v___x_3171_ = v___x_3121_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3184_, 3, v_r_3111_);
lean_ctor_set(v_reuseFailAlloc_3184_, 4, v_r_3098_);
v___x_3171_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
v_isSharedCheck_3178_ = !lean_is_exclusive(v_r_3098_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; lean_object* v_unused_3180_; lean_object* v_unused_3181_; lean_object* v_unused_3182_; lean_object* v_unused_3183_; 
v_unused_3179_ = lean_ctor_get(v_r_3098_, 4);
lean_dec(v_unused_3179_);
v_unused_3180_ = lean_ctor_get(v_r_3098_, 3);
lean_dec(v_unused_3180_);
v_unused_3181_ = lean_ctor_get(v_r_3098_, 2);
lean_dec(v_unused_3181_);
v_unused_3182_ = lean_ctor_get(v_r_3098_, 1);
lean_dec(v_unused_3182_);
v_unused_3183_ = lean_ctor_get(v_r_3098_, 0);
lean_dec(v_unused_3183_);
v___x_3173_ = v_r_3098_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_dec(v_r_3098_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 4, v___x_3171_);
lean_ctor_set(v___x_3173_, 3, v_l_3110_);
lean_ctor_set(v___x_3173_, 2, v_v_3109_);
lean_ctor_set(v___x_3173_, 1, v_k_3108_);
lean_ctor_set(v___x_3173_, 0, v___x_3167_);
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_k_3108_);
lean_ctor_set(v_reuseFailAlloc_3177_, 2, v_v_3109_);
lean_ctor_set(v_reuseFailAlloc_3177_, 3, v_l_3110_);
lean_ctor_set(v_reuseFailAlloc_3177_, 4, v___x_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3191_; 
v_l_3191_ = lean_ctor_get(v_impl_3104_, 3);
lean_inc(v_l_3191_);
if (lean_obj_tag(v_l_3191_) == 0)
{
lean_object* v_r_3192_; lean_object* v_k_3193_; lean_object* v_v_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3205_; 
v_r_3192_ = lean_ctor_get(v_impl_3104_, 4);
v_k_3193_ = lean_ctor_get(v_impl_3104_, 1);
v_v_3194_ = lean_ctor_get(v_impl_3104_, 2);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_impl_3104_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; lean_object* v_unused_3207_; 
v_unused_3206_ = lean_ctor_get(v_impl_3104_, 3);
lean_dec(v_unused_3206_);
v_unused_3207_ = lean_ctor_get(v_impl_3104_, 0);
lean_dec(v_unused_3207_);
v___x_3196_ = v_impl_3104_;
v_isShared_3197_ = v_isSharedCheck_3205_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_r_3192_);
lean_inc(v_v_3194_);
lean_inc(v_k_3193_);
lean_dec(v_impl_3104_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3205_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
v___x_3198_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3192_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 3, v_r_3192_);
lean_ctor_set(v___x_3196_, 2, v_v_3096_);
lean_ctor_set(v___x_3196_, 1, v_k_3095_);
lean_ctor_set(v___x_3196_, 0, v___x_3105_);
v___x_3200_ = v___x_3196_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3204_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3204_, 3, v_r_3192_);
lean_ctor_set(v_reuseFailAlloc_3204_, 4, v_r_3192_);
v___x_3200_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3202_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v___x_3200_);
lean_ctor_set(v___x_3100_, 3, v_l_3191_);
lean_ctor_set(v___x_3100_, 2, v_v_3194_);
lean_ctor_set(v___x_3100_, 1, v_k_3193_);
lean_ctor_set(v___x_3100_, 0, v___x_3198_);
v___x_3202_ = v___x_3100_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3203_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3203_, 3, v_l_3191_);
lean_ctor_set(v_reuseFailAlloc_3203_, 4, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_r_3208_; 
v_r_3208_ = lean_ctor_get(v_impl_3104_, 4);
lean_inc(v_r_3208_);
if (lean_obj_tag(v_r_3208_) == 0)
{
lean_object* v_k_3209_; lean_object* v_v_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3233_; 
v_k_3209_ = lean_ctor_get(v_impl_3104_, 1);
v_v_3210_ = lean_ctor_get(v_impl_3104_, 2);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_impl_3104_);
if (v_isSharedCheck_3233_ == 0)
{
lean_object* v_unused_3234_; lean_object* v_unused_3235_; lean_object* v_unused_3236_; 
v_unused_3234_ = lean_ctor_get(v_impl_3104_, 4);
lean_dec(v_unused_3234_);
v_unused_3235_ = lean_ctor_get(v_impl_3104_, 3);
lean_dec(v_unused_3235_);
v_unused_3236_ = lean_ctor_get(v_impl_3104_, 0);
lean_dec(v_unused_3236_);
v___x_3212_ = v_impl_3104_;
v_isShared_3213_ = v_isSharedCheck_3233_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_v_3210_);
lean_inc(v_k_3209_);
lean_dec(v_impl_3104_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3233_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v_k_3214_; lean_object* v_v_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3229_; 
v_k_3214_ = lean_ctor_get(v_r_3208_, 1);
v_v_3215_ = lean_ctor_get(v_r_3208_, 2);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_r_3208_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; lean_object* v_unused_3231_; lean_object* v_unused_3232_; 
v_unused_3230_ = lean_ctor_get(v_r_3208_, 4);
lean_dec(v_unused_3230_);
v_unused_3231_ = lean_ctor_get(v_r_3208_, 3);
lean_dec(v_unused_3231_);
v_unused_3232_ = lean_ctor_get(v_r_3208_, 0);
lean_dec(v_unused_3232_);
v___x_3217_ = v_r_3208_;
v_isShared_3218_ = v_isSharedCheck_3229_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_v_3215_);
lean_inc(v_k_3214_);
lean_dec(v_r_3208_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3229_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3219_; lean_object* v___x_3221_; 
v___x_3219_ = lean_unsigned_to_nat(3u);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 4, v_l_3191_);
lean_ctor_set(v___x_3217_, 3, v_l_3191_);
lean_ctor_set(v___x_3217_, 2, v_v_3210_);
lean_ctor_set(v___x_3217_, 1, v_k_3209_);
lean_ctor_set(v___x_3217_, 0, v___x_3105_);
v___x_3221_ = v___x_3217_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v_k_3209_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_v_3210_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v_l_3191_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v_l_3191_);
v___x_3221_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3223_; 
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 4, v_l_3191_);
lean_ctor_set(v___x_3212_, 2, v_v_3096_);
lean_ctor_set(v___x_3212_, 1, v_k_3095_);
lean_ctor_set(v___x_3212_, 0, v___x_3105_);
v___x_3223_ = v___x_3212_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3227_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3227_, 3, v_l_3191_);
lean_ctor_set(v_reuseFailAlloc_3227_, 4, v_l_3191_);
v___x_3223_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
lean_object* v___x_3225_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v___x_3223_);
lean_ctor_set(v___x_3100_, 3, v___x_3221_);
lean_ctor_set(v___x_3100_, 2, v_v_3215_);
lean_ctor_set(v___x_3100_, 1, v_k_3214_);
lean_ctor_set(v___x_3100_, 0, v___x_3219_);
v___x_3225_ = v___x_3100_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_k_3214_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v_v_3215_);
lean_ctor_set(v_reuseFailAlloc_3226_, 3, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3226_, 4, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
}
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
v___x_3237_ = lean_unsigned_to_nat(2u);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v_r_3208_);
lean_ctor_set(v___x_3100_, 3, v_impl_3104_);
lean_ctor_set(v___x_3100_, 0, v___x_3237_);
v___x_3239_ = v___x_3100_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3240_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3240_, 3, v_impl_3104_);
lean_ctor_set(v_reuseFailAlloc_3240_, 4, v_r_3208_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3242_; 
lean_dec(v_v_3096_);
lean_dec(v_k_3095_);
lean_dec_ref(v_cmp_3090_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 2, v_v_3092_);
lean_ctor_set(v___x_3100_, 1, v_k_3091_);
v___x_3242_ = v___x_3100_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_size_3094_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v_k_3091_);
lean_ctor_set(v_reuseFailAlloc_3243_, 2, v_v_3092_);
lean_ctor_set(v_reuseFailAlloc_3243_, 3, v_l_3097_);
lean_ctor_set(v_reuseFailAlloc_3243_, 4, v_r_3098_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
default: 
{
lean_object* v_impl_3244_; lean_object* v___x_3245_; 
lean_dec(v_size_3094_);
v_impl_3244_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3090_, v_k_3091_, v_v_3092_, v_r_3098_);
v___x_3245_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3097_) == 0)
{
lean_object* v_size_3246_; lean_object* v_size_3247_; lean_object* v_k_3248_; lean_object* v_v_3249_; lean_object* v_l_3250_; lean_object* v_r_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; 
v_size_3246_ = lean_ctor_get(v_l_3097_, 0);
v_size_3247_ = lean_ctor_get(v_impl_3244_, 0);
lean_inc(v_size_3247_);
v_k_3248_ = lean_ctor_get(v_impl_3244_, 1);
lean_inc(v_k_3248_);
v_v_3249_ = lean_ctor_get(v_impl_3244_, 2);
lean_inc(v_v_3249_);
v_l_3250_ = lean_ctor_get(v_impl_3244_, 3);
lean_inc(v_l_3250_);
v_r_3251_ = lean_ctor_get(v_impl_3244_, 4);
lean_inc(v_r_3251_);
v___x_3252_ = lean_unsigned_to_nat(3u);
v___x_3253_ = lean_nat_mul(v___x_3252_, v_size_3246_);
v___x_3254_ = lean_nat_dec_lt(v___x_3253_, v_size_3247_);
lean_dec(v___x_3253_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3258_; 
lean_dec(v_r_3251_);
lean_dec(v_l_3250_);
lean_dec(v_v_3249_);
lean_dec(v_k_3248_);
v___x_3255_ = lean_nat_add(v___x_3245_, v_size_3246_);
v___x_3256_ = lean_nat_add(v___x_3255_, v_size_3247_);
lean_dec(v_size_3247_);
lean_dec(v___x_3255_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v_impl_3244_);
lean_ctor_set(v___x_3100_, 0, v___x_3256_);
v___x_3258_ = v___x_3100_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3256_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3259_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3259_, 3, v_l_3097_);
lean_ctor_set(v_reuseFailAlloc_3259_, 4, v_impl_3244_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
else
{
lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3323_; 
v_isSharedCheck_3323_ = !lean_is_exclusive(v_impl_3244_);
if (v_isSharedCheck_3323_ == 0)
{
lean_object* v_unused_3324_; lean_object* v_unused_3325_; lean_object* v_unused_3326_; lean_object* v_unused_3327_; lean_object* v_unused_3328_; 
v_unused_3324_ = lean_ctor_get(v_impl_3244_, 4);
lean_dec(v_unused_3324_);
v_unused_3325_ = lean_ctor_get(v_impl_3244_, 3);
lean_dec(v_unused_3325_);
v_unused_3326_ = lean_ctor_get(v_impl_3244_, 2);
lean_dec(v_unused_3326_);
v_unused_3327_ = lean_ctor_get(v_impl_3244_, 1);
lean_dec(v_unused_3327_);
v_unused_3328_ = lean_ctor_get(v_impl_3244_, 0);
lean_dec(v_unused_3328_);
v___x_3261_ = v_impl_3244_;
v_isShared_3262_ = v_isSharedCheck_3323_;
goto v_resetjp_3260_;
}
else
{
lean_dec(v_impl_3244_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3323_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v_size_3263_; lean_object* v_k_3264_; lean_object* v_v_3265_; lean_object* v_l_3266_; lean_object* v_r_3267_; lean_object* v_size_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; uint8_t v___x_3271_; 
v_size_3263_ = lean_ctor_get(v_l_3250_, 0);
v_k_3264_ = lean_ctor_get(v_l_3250_, 1);
v_v_3265_ = lean_ctor_get(v_l_3250_, 2);
v_l_3266_ = lean_ctor_get(v_l_3250_, 3);
v_r_3267_ = lean_ctor_get(v_l_3250_, 4);
v_size_3268_ = lean_ctor_get(v_r_3251_, 0);
v___x_3269_ = lean_unsigned_to_nat(2u);
v___x_3270_ = lean_nat_mul(v___x_3269_, v_size_3268_);
v___x_3271_ = lean_nat_dec_lt(v_size_3263_, v___x_3270_);
lean_dec(v___x_3270_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3299_; 
lean_inc(v_r_3267_);
lean_inc(v_l_3266_);
lean_inc(v_v_3265_);
lean_inc(v_k_3264_);
v_isSharedCheck_3299_ = !lean_is_exclusive(v_l_3250_);
if (v_isSharedCheck_3299_ == 0)
{
lean_object* v_unused_3300_; lean_object* v_unused_3301_; lean_object* v_unused_3302_; lean_object* v_unused_3303_; lean_object* v_unused_3304_; 
v_unused_3300_ = lean_ctor_get(v_l_3250_, 4);
lean_dec(v_unused_3300_);
v_unused_3301_ = lean_ctor_get(v_l_3250_, 3);
lean_dec(v_unused_3301_);
v_unused_3302_ = lean_ctor_get(v_l_3250_, 2);
lean_dec(v_unused_3302_);
v_unused_3303_ = lean_ctor_get(v_l_3250_, 1);
lean_dec(v_unused_3303_);
v_unused_3304_ = lean_ctor_get(v_l_3250_, 0);
lean_dec(v_unused_3304_);
v___x_3273_ = v_l_3250_;
v_isShared_3274_ = v_isSharedCheck_3299_;
goto v_resetjp_3272_;
}
else
{
lean_dec(v_l_3250_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3299_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3289_; 
v___x_3275_ = lean_nat_add(v___x_3245_, v_size_3246_);
v___x_3276_ = lean_nat_add(v___x_3275_, v_size_3247_);
lean_dec(v_size_3247_);
if (lean_obj_tag(v_l_3266_) == 0)
{
lean_object* v_size_3297_; 
v_size_3297_ = lean_ctor_get(v_l_3266_, 0);
lean_inc(v_size_3297_);
v___y_3289_ = v_size_3297_;
goto v___jp_3288_;
}
else
{
lean_object* v___x_3298_; 
v___x_3298_ = lean_unsigned_to_nat(0u);
v___y_3289_ = v___x_3298_;
goto v___jp_3288_;
}
v___jp_3277_:
{
lean_object* v___x_3281_; lean_object* v___x_3283_; 
v___x_3281_ = lean_nat_add(v___y_3278_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec(v___y_3278_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 4, v_r_3251_);
lean_ctor_set(v___x_3273_, 3, v_r_3267_);
lean_ctor_set(v___x_3273_, 2, v_v_3249_);
lean_ctor_set(v___x_3273_, 1, v_k_3248_);
lean_ctor_set(v___x_3273_, 0, v___x_3281_);
v___x_3283_ = v___x_3273_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3281_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_k_3248_);
lean_ctor_set(v_reuseFailAlloc_3287_, 2, v_v_3249_);
lean_ctor_set(v_reuseFailAlloc_3287_, 3, v_r_3267_);
lean_ctor_set(v_reuseFailAlloc_3287_, 4, v_r_3251_);
v___x_3283_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3285_; 
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 4, v___x_3283_);
lean_ctor_set(v___x_3261_, 3, v___y_3279_);
lean_ctor_set(v___x_3261_, 2, v_v_3265_);
lean_ctor_set(v___x_3261_, 1, v_k_3264_);
lean_ctor_set(v___x_3261_, 0, v___x_3276_);
v___x_3285_ = v___x_3261_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3276_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_k_3264_);
lean_ctor_set(v_reuseFailAlloc_3286_, 2, v_v_3265_);
lean_ctor_set(v_reuseFailAlloc_3286_, 3, v___y_3279_);
lean_ctor_set(v_reuseFailAlloc_3286_, 4, v___x_3283_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
v___jp_3288_:
{
lean_object* v___x_3290_; lean_object* v___x_3292_; 
v___x_3290_ = lean_nat_add(v___x_3275_, v___y_3289_);
lean_dec(v___y_3289_);
lean_dec(v___x_3275_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v_l_3266_);
lean_ctor_set(v___x_3100_, 0, v___x_3290_);
v___x_3292_ = v___x_3100_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3290_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3296_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3296_, 3, v_l_3097_);
lean_ctor_set(v_reuseFailAlloc_3296_, 4, v_l_3266_);
v___x_3292_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
lean_object* v___x_3293_; 
v___x_3293_ = lean_nat_add(v___x_3245_, v_size_3268_);
if (lean_obj_tag(v_r_3267_) == 0)
{
lean_object* v_size_3294_; 
v_size_3294_ = lean_ctor_get(v_r_3267_, 0);
lean_inc(v_size_3294_);
v___y_3278_ = v___x_3293_;
v___y_3279_ = v___x_3292_;
v___y_3280_ = v_size_3294_;
goto v___jp_3277_;
}
else
{
lean_object* v___x_3295_; 
v___x_3295_ = lean_unsigned_to_nat(0u);
v___y_3278_ = v___x_3293_;
v___y_3279_ = v___x_3292_;
v___y_3280_ = v___x_3295_;
goto v___jp_3277_;
}
}
}
}
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3309_; 
lean_del_object(v___x_3100_);
v___x_3305_ = lean_nat_add(v___x_3245_, v_size_3246_);
v___x_3306_ = lean_nat_add(v___x_3305_, v_size_3247_);
lean_dec(v_size_3247_);
v___x_3307_ = lean_nat_add(v___x_3305_, v_size_3263_);
lean_dec(v___x_3305_);
lean_inc_ref(v_l_3097_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 4, v_l_3250_);
lean_ctor_set(v___x_3261_, 3, v_l_3097_);
lean_ctor_set(v___x_3261_, 2, v_v_3096_);
lean_ctor_set(v___x_3261_, 1, v_k_3095_);
lean_ctor_set(v___x_3261_, 0, v___x_3307_);
v___x_3309_ = v___x_3261_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3307_);
lean_ctor_set(v_reuseFailAlloc_3322_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3322_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3322_, 3, v_l_3097_);
lean_ctor_set(v_reuseFailAlloc_3322_, 4, v_l_3250_);
v___x_3309_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
v_isSharedCheck_3316_ = !lean_is_exclusive(v_l_3097_);
if (v_isSharedCheck_3316_ == 0)
{
lean_object* v_unused_3317_; lean_object* v_unused_3318_; lean_object* v_unused_3319_; lean_object* v_unused_3320_; lean_object* v_unused_3321_; 
v_unused_3317_ = lean_ctor_get(v_l_3097_, 4);
lean_dec(v_unused_3317_);
v_unused_3318_ = lean_ctor_get(v_l_3097_, 3);
lean_dec(v_unused_3318_);
v_unused_3319_ = lean_ctor_get(v_l_3097_, 2);
lean_dec(v_unused_3319_);
v_unused_3320_ = lean_ctor_get(v_l_3097_, 1);
lean_dec(v_unused_3320_);
v_unused_3321_ = lean_ctor_get(v_l_3097_, 0);
lean_dec(v_unused_3321_);
v___x_3311_ = v_l_3097_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_dec(v_l_3097_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 4, v_r_3251_);
lean_ctor_set(v___x_3311_, 3, v___x_3309_);
lean_ctor_set(v___x_3311_, 2, v_v_3249_);
lean_ctor_set(v___x_3311_, 1, v_k_3248_);
lean_ctor_set(v___x_3311_, 0, v___x_3306_);
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3306_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_k_3248_);
lean_ctor_set(v_reuseFailAlloc_3315_, 2, v_v_3249_);
lean_ctor_set(v_reuseFailAlloc_3315_, 3, v___x_3309_);
lean_ctor_set(v_reuseFailAlloc_3315_, 4, v_r_3251_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3329_; 
v_l_3329_ = lean_ctor_get(v_impl_3244_, 3);
lean_inc(v_l_3329_);
if (lean_obj_tag(v_l_3329_) == 0)
{
lean_object* v_r_3330_; lean_object* v_k_3331_; lean_object* v_v_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3355_; 
v_r_3330_ = lean_ctor_get(v_impl_3244_, 4);
v_k_3331_ = lean_ctor_get(v_impl_3244_, 1);
v_v_3332_ = lean_ctor_get(v_impl_3244_, 2);
v_isSharedCheck_3355_ = !lean_is_exclusive(v_impl_3244_);
if (v_isSharedCheck_3355_ == 0)
{
lean_object* v_unused_3356_; lean_object* v_unused_3357_; 
v_unused_3356_ = lean_ctor_get(v_impl_3244_, 3);
lean_dec(v_unused_3356_);
v_unused_3357_ = lean_ctor_get(v_impl_3244_, 0);
lean_dec(v_unused_3357_);
v___x_3334_ = v_impl_3244_;
v_isShared_3335_ = v_isSharedCheck_3355_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_r_3330_);
lean_inc(v_v_3332_);
lean_inc(v_k_3331_);
lean_dec(v_impl_3244_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3355_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v_k_3336_; lean_object* v_v_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3351_; 
v_k_3336_ = lean_ctor_get(v_l_3329_, 1);
v_v_3337_ = lean_ctor_get(v_l_3329_, 2);
v_isSharedCheck_3351_ = !lean_is_exclusive(v_l_3329_);
if (v_isSharedCheck_3351_ == 0)
{
lean_object* v_unused_3352_; lean_object* v_unused_3353_; lean_object* v_unused_3354_; 
v_unused_3352_ = lean_ctor_get(v_l_3329_, 4);
lean_dec(v_unused_3352_);
v_unused_3353_ = lean_ctor_get(v_l_3329_, 3);
lean_dec(v_unused_3353_);
v_unused_3354_ = lean_ctor_get(v_l_3329_, 0);
lean_dec(v_unused_3354_);
v___x_3339_ = v_l_3329_;
v_isShared_3340_ = v_isSharedCheck_3351_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_v_3337_);
lean_inc(v_k_3336_);
lean_dec(v_l_3329_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3351_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3343_; 
v___x_3341_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3330_, 2);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 4, v_r_3330_);
lean_ctor_set(v___x_3339_, 3, v_r_3330_);
lean_ctor_set(v___x_3339_, 2, v_v_3096_);
lean_ctor_set(v___x_3339_, 1, v_k_3095_);
lean_ctor_set(v___x_3339_, 0, v___x_3245_);
v___x_3343_ = v___x_3339_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v_r_3330_);
lean_ctor_set(v_reuseFailAlloc_3350_, 4, v_r_3330_);
v___x_3343_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
lean_object* v___x_3345_; 
lean_inc(v_r_3330_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 3, v_r_3330_);
lean_ctor_set(v___x_3334_, 0, v___x_3245_);
v___x_3345_ = v___x_3334_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_k_3331_);
lean_ctor_set(v_reuseFailAlloc_3349_, 2, v_v_3332_);
lean_ctor_set(v_reuseFailAlloc_3349_, 3, v_r_3330_);
lean_ctor_set(v_reuseFailAlloc_3349_, 4, v_r_3330_);
v___x_3345_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3347_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v___x_3345_);
lean_ctor_set(v___x_3100_, 3, v___x_3343_);
lean_ctor_set(v___x_3100_, 2, v_v_3337_);
lean_ctor_set(v___x_3100_, 1, v_k_3336_);
lean_ctor_set(v___x_3100_, 0, v___x_3341_);
v___x_3347_ = v___x_3100_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_k_3336_);
lean_ctor_set(v_reuseFailAlloc_3348_, 2, v_v_3337_);
lean_ctor_set(v_reuseFailAlloc_3348_, 3, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3348_, 4, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
}
}
else
{
lean_object* v_r_3358_; 
v_r_3358_ = lean_ctor_get(v_impl_3244_, 4);
lean_inc(v_r_3358_);
if (lean_obj_tag(v_r_3358_) == 0)
{
lean_object* v_k_3359_; lean_object* v_v_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3371_; 
v_k_3359_ = lean_ctor_get(v_impl_3244_, 1);
v_v_3360_ = lean_ctor_get(v_impl_3244_, 2);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_impl_3244_);
if (v_isSharedCheck_3371_ == 0)
{
lean_object* v_unused_3372_; lean_object* v_unused_3373_; lean_object* v_unused_3374_; 
v_unused_3372_ = lean_ctor_get(v_impl_3244_, 4);
lean_dec(v_unused_3372_);
v_unused_3373_ = lean_ctor_get(v_impl_3244_, 3);
lean_dec(v_unused_3373_);
v_unused_3374_ = lean_ctor_get(v_impl_3244_, 0);
lean_dec(v_unused_3374_);
v___x_3362_ = v_impl_3244_;
v_isShared_3363_ = v_isSharedCheck_3371_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_v_3360_);
lean_inc(v_k_3359_);
lean_dec(v_impl_3244_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3371_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3364_ = lean_unsigned_to_nat(3u);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 4, v_l_3329_);
lean_ctor_set(v___x_3362_, 2, v_v_3096_);
lean_ctor_set(v___x_3362_, 1, v_k_3095_);
lean_ctor_set(v___x_3362_, 0, v___x_3245_);
v___x_3366_ = v___x_3362_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3370_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3370_, 3, v_l_3329_);
lean_ctor_set(v_reuseFailAlloc_3370_, 4, v_l_3329_);
v___x_3366_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3368_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v_r_3358_);
lean_ctor_set(v___x_3100_, 3, v___x_3366_);
lean_ctor_set(v___x_3100_, 2, v_v_3360_);
lean_ctor_set(v___x_3100_, 1, v_k_3359_);
lean_ctor_set(v___x_3100_, 0, v___x_3364_);
v___x_3368_ = v___x_3100_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3364_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_k_3359_);
lean_ctor_set(v_reuseFailAlloc_3369_, 2, v_v_3360_);
lean_ctor_set(v_reuseFailAlloc_3369_, 3, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3369_, 4, v_r_3358_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
else
{
lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3375_ = lean_unsigned_to_nat(2u);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v_impl_3244_);
lean_ctor_set(v___x_3100_, 3, v_r_3358_);
lean_ctor_set(v___x_3100_, 0, v___x_3375_);
v___x_3377_ = v___x_3100_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3378_, 3, v_r_3358_);
lean_ctor_set(v_reuseFailAlloc_3378_, 4, v_impl_3244_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
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
lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec_ref(v_cmp_3090_);
v___x_3380_ = lean_unsigned_to_nat(1u);
v___x_3381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
lean_ctor_set(v___x_3381_, 1, v_k_3091_);
lean_ctor_set(v___x_3381_, 2, v_v_3092_);
lean_ctor_set(v___x_3381_, 3, v_t_3093_);
lean_ctor_set(v___x_3381_, 4, v_t_3093_);
return v___x_3381_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(lean_object* v_cmp_3382_, lean_object* v_init_3383_, lean_object* v_x_3384_){
_start:
{
if (lean_obj_tag(v_x_3384_) == 0)
{
lean_object* v_k_3385_; lean_object* v_v_3386_; lean_object* v_l_3387_; lean_object* v_r_3388_; lean_object* v___x_3389_; 
v_k_3385_ = lean_ctor_get(v_x_3384_, 1);
lean_inc(v_k_3385_);
v_v_3386_ = lean_ctor_get(v_x_3384_, 2);
lean_inc(v_v_3386_);
v_l_3387_ = lean_ctor_get(v_x_3384_, 3);
lean_inc(v_l_3387_);
v_r_3388_ = lean_ctor_get(v_x_3384_, 4);
lean_inc(v_r_3388_);
lean_dec_ref_known(v_x_3384_, 5);
lean_inc_ref(v_cmp_3382_);
v___x_3389_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_3382_, v_init_3383_, v_l_3387_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_dec(v_r_3388_);
lean_dec(v_v_3386_);
lean_dec(v_k_3385_);
lean_dec_ref(v_cmp_3382_);
return v___x_3389_;
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3391_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref_known(v___x_3389_, 1);
v___x_3391_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_v_3386_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec(v_a_3390_);
lean_dec(v_r_3388_);
lean_dec(v_k_3385_);
lean_dec_ref(v_cmp_3382_);
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3401_; 
v_a_3400_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3391_, 1);
lean_inc_ref(v_cmp_3382_);
v___x_3401_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3382_, v_k_3385_, v_a_3400_, v_a_3390_);
v_init_3383_ = v___x_3401_;
v_x_3384_ = v_r_3388_;
goto _start;
}
}
}
else
{
lean_object* v___x_3403_; 
lean_dec_ref(v_cmp_3382_);
v___x_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3403_, 0, v_init_3383_);
return v___x_3403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(lean_object* v_cmp_3404_, lean_object* v_j_3405_){
_start:
{
lean_object* v___x_3406_; 
v___x_3406_ = l_Lean_Json_getObj_x3f(v_j_3405_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec_ref(v_cmp_3404_);
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v_a_3415_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3406_, 1);
v___x_3416_ = lean_box(1);
v___x_3417_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_3404_, v___x_3416_, v_a_3415_);
return v___x_3417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(lean_object* v_x_3421_){
_start:
{
if (lean_obj_tag(v_x_3421_) == 0)
{
lean_object* v___x_3422_; 
v___x_3422_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__0));
return v___x_3422_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__1));
v___x_3424_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(v___x_3423_, v_x_3421_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3424_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3424_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3441_; 
v_a_3433_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3435_ = v___x_3424_;
v_isShared_3436_ = v_isSharedCheck_3441_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3424_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3441_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3437_, 0, v_a_3433_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3437_);
v___x_3439_ = v___x_3435_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(lean_object* v_j_3442_, lean_object* v_k_3443_){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = l_Lean_Json_getObjValD(v_j_3442_, v_k_3443_);
v___x_3445_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(v___x_3444_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4___boxed(lean_object* v_j_3446_, lean_object* v_k_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_j_3446_, v_k_3447_);
lean_dec_ref(v_k_3447_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(lean_object* v_j_3449_, lean_object* v_k_3450_){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3451_ = l_Lean_Json_getObjValD(v_j_3449_, v_k_3450_);
v___x_3452_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v___x_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1___boxed(lean_object* v_j_3453_, lean_object* v_k_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_j_3453_, v_k_3454_);
lean_dec_ref(v_k_3454_);
return v_res_3455_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3464_ = 1;
v___x_3465_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__4));
v___x_3466_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3465_, v___x_3464_);
return v___x_3466_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__6));
v___x_3469_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__5, &l_Lake_Check_instFromJsonConfig_fromJson___closed__5_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5);
v___x_3470_ = lean_string_append(v___x_3469_, v___x_3468_);
return v___x_3470_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3473_ = 1;
v___x_3474_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__8));
v___x_3475_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3474_, v___x_3473_);
return v___x_3475_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3476_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__9, &l_Lake_Check_instFromJsonConfig_fromJson___closed__9_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9);
v___x_3477_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3478_ = lean_string_append(v___x_3477_, v___x_3476_);
return v___x_3478_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3480_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3481_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__10, &l_Lake_Check_instFromJsonConfig_fromJson___closed__10_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10);
v___x_3482_ = lean_string_append(v___x_3481_, v___x_3480_);
return v___x_3482_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15(void){
_start:
{
uint8_t v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = 1;
v___x_3487_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__14));
v___x_3488_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3487_, v___x_3486_);
return v___x_3488_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__15, &l_Lake_Check_instFromJsonConfig_fromJson___closed__15_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15);
v___x_3490_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3491_ = lean_string_append(v___x_3490_, v___x_3489_);
return v___x_3491_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3492_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3493_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__16, &l_Lake_Check_instFromJsonConfig_fromJson___closed__16_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16);
v___x_3494_ = lean_string_append(v___x_3493_, v___x_3492_);
return v___x_3494_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20(void){
_start:
{
uint8_t v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = 1;
v___x_3499_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__19));
v___x_3500_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3499_, v___x_3498_);
return v___x_3500_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__20, &l_Lake_Check_instFromJsonConfig_fromJson___closed__20_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20);
v___x_3502_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3503_ = lean_string_append(v___x_3502_, v___x_3501_);
return v___x_3503_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3505_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__21, &l_Lake_Check_instFromJsonConfig_fromJson___closed__21_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21);
v___x_3506_ = lean_string_append(v___x_3505_, v___x_3504_);
return v___x_3506_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25(void){
_start:
{
uint8_t v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3510_ = 1;
v___x_3511_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__24));
v___x_3512_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3511_, v___x_3510_);
return v___x_3512_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__25, &l_Lake_Check_instFromJsonConfig_fromJson___closed__25_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25);
v___x_3514_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3515_ = lean_string_append(v___x_3514_, v___x_3513_);
return v___x_3515_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3517_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__26, &l_Lake_Check_instFromJsonConfig_fromJson___closed__26_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26);
v___x_3518_ = lean_string_append(v___x_3517_, v___x_3516_);
return v___x_3518_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29(void){
_start:
{
uint8_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3521_ = 1;
v___x_3522_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__28));
v___x_3523_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3522_, v___x_3521_);
return v___x_3523_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30(void){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3524_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__29, &l_Lake_Check_instFromJsonConfig_fromJson___closed__29_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29);
v___x_3525_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3526_ = lean_string_append(v___x_3525_, v___x_3524_);
return v___x_3526_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3527_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3528_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__30, &l_Lake_Check_instFromJsonConfig_fromJson___closed__30_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30);
v___x_3529_ = lean_string_append(v___x_3528_, v___x_3527_);
return v___x_3529_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35(void){
_start:
{
uint8_t v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3534_ = 1;
v___x_3535_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__34));
v___x_3536_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3535_, v___x_3534_);
return v___x_3536_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3537_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__35, &l_Lake_Check_instFromJsonConfig_fromJson___closed__35_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35);
v___x_3538_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3539_ = lean_string_append(v___x_3538_, v___x_3537_);
return v___x_3539_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3540_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3541_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__36, &l_Lake_Check_instFromJsonConfig_fromJson___closed__36_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36);
v___x_3542_ = lean_string_append(v___x_3541_, v___x_3540_);
return v___x_3542_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41(void){
_start:
{
uint8_t v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3547_ = 1;
v___x_3548_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__40));
v___x_3549_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3548_, v___x_3547_);
return v___x_3549_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__41, &l_Lake_Check_instFromJsonConfig_fromJson___closed__41_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41);
v___x_3551_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3552_ = lean_string_append(v___x_3551_, v___x_3550_);
return v___x_3552_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3554_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__42, &l_Lake_Check_instFromJsonConfig_fromJson___closed__42_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42);
v___x_3555_ = lean_string_append(v___x_3554_, v___x_3553_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instFromJsonConfig_fromJson(lean_object* v_json_3556_){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
lean_inc(v_json_3556_);
v___x_3558_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_3556_, v___x_3557_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3568_; 
lean_dec(v_json_3556_);
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3561_ = v___x_3558_;
v_isShared_3562_ = v_isSharedCheck_3568_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3568_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3563_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__12, &l_Lake_Check_instFromJsonConfig_fromJson___closed__12_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12);
v___x_3564_ = lean_string_append(v___x_3563_, v_a_3559_);
lean_dec(v_a_3559_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v___x_3564_);
v___x_3566_ = v___x_3561_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
else
{
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v_json_3556_);
v_a_3569_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3558_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3558_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
lean_ctor_set_tag(v___x_3571_, 0);
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v_a_3577_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3558_, 1);
v___x_3578_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
lean_inc(v_json_3556_);
v___x_3579_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_3556_, v___x_3578_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3589_; 
lean_dec(v_a_3577_);
lean_dec(v_json_3556_);
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3582_ = v___x_3579_;
v_isShared_3583_ = v_isSharedCheck_3589_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3579_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3589_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3587_; 
v___x_3584_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__17, &l_Lake_Check_instFromJsonConfig_fromJson___closed__17_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17);
v___x_3585_ = lean_string_append(v___x_3584_, v_a_3580_);
lean_dec(v_a_3580_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 0, v___x_3585_);
v___x_3587_ = v___x_3582_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3585_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
else
{
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec(v_a_3577_);
lean_dec(v_json_3556_);
v_a_3590_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3579_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3579_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
lean_ctor_set_tag(v___x_3592_, 0);
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
else
{
lean_object* v_a_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v_a_3598_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___x_3579_, 1);
v___x_3599_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
lean_inc(v_json_3556_);
v___x_3600_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_3556_, v___x_3599_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3610_; 
lean_dec(v_a_3598_);
lean_dec(v_a_3577_);
lean_dec(v_json_3556_);
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3603_ = v___x_3600_;
v_isShared_3604_ = v_isSharedCheck_3610_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3600_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3610_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3605_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__22, &l_Lake_Check_instFromJsonConfig_fromJson___closed__22_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22);
v___x_3606_ = lean_string_append(v___x_3605_, v_a_3601_);
lean_dec(v_a_3601_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v___x_3606_);
v___x_3608_ = v___x_3603_;
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
else
{
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec(v_a_3598_);
lean_dec(v_a_3577_);
lean_dec(v_json_3556_);
v_a_3611_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3600_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3600_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
lean_ctor_set_tag(v___x_3613_, 0);
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v_a_3619_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3600_, 1);
v___x_3620_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
lean_inc(v_json_3556_);
v___x_3621_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_json_3556_, v___x_3620_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v_a_3619_);
lean_dec(v_a_3598_);
lean_dec(v_a_3577_);
lean_dec(v_json_3556_);
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3624_ = v___x_3621_;
v_isShared_3625_ = v_isSharedCheck_3631_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3621_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3631_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3629_; 
v___x_3626_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__27, &l_Lake_Check_instFromJsonConfig_fromJson___closed__27_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27);
v___x_3627_ = lean_string_append(v___x_3626_, v_a_3622_);
lean_dec(v_a_3622_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 0, v___x_3627_);
v___x_3629_ = v___x_3624_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3627_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
else
{
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v_a_3619_);
lean_dec(v_a_3598_);
lean_dec(v_a_3577_);
lean_dec(v_json_3556_);
v_a_3632_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3621_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3621_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set_tag(v___x_3634_, 0);
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v_a_3640_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___x_3621_, 1);
v___x_3641_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
lean_inc(v_json_3556_);
v___x_3642_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_3556_, v___x_3641_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3652_; 
lean_dec(v_a_3640_);
lean_dec(v_a_3619_);
lean_dec(v_a_3598_);
lean_dec(v_a_3577_);
lean_dec(v_json_3556_);
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3645_ = v___x_3642_;
v_isShared_3646_ = v_isSharedCheck_3652_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3642_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3652_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3647_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__31, &l_Lake_Check_instFromJsonConfig_fromJson___closed__31_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31);
v___x_3648_ = lean_string_append(v___x_3647_, v_a_3643_);
lean_dec(v_a_3643_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3648_);
v___x_3650_ = v___x_3645_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
else
{
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
lean_dec(v_a_3640_);
lean_dec(v_a_3619_);
lean_dec(v_a_3598_);
lean_dec(v_a_3577_);
lean_dec(v_json_3556_);
v_a_3653_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3642_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3642_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
lean_ctor_set_tag(v___x_3655_, 0);
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_a_3661_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v___x_3642_, 1);
v___x_3662_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
lean_inc(v_json_3556_);
v___x_3663_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_json_3556_, v___x_3662_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3673_; 
lean_dec(v_a_3661_);
lean_dec(v_a_3640_);
lean_dec(v_a_3619_);
lean_dec(v_a_3598_);
lean_dec(v_a_3577_);
lean_dec(v_json_3556_);
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3666_ = v___x_3663_;
v_isShared_3667_ = v_isSharedCheck_3673_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3663_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3673_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3671_; 
v___x_3668_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__37, &l_Lake_Check_instFromJsonConfig_fromJson___closed__37_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37);
v___x_3669_ = lean_string_append(v___x_3668_, v_a_3664_);
lean_dec(v_a_3664_);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 0, v___x_3669_);
v___x_3671_ = v___x_3666_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
else
{
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec(v_a_3661_);
lean_dec(v_a_3640_);
lean_dec(v_a_3619_);
lean_dec(v_a_3598_);
lean_dec(v_a_3577_);
lean_dec(v_json_3556_);
v_a_3674_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3663_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3663_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
lean_ctor_set_tag(v___x_3676_, 0);
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v_a_3682_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3682_);
lean_dec_ref_known(v___x_3663_, 1);
v___x_3683_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_3684_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_json_3556_, v___x_3683_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3694_; 
lean_dec(v_a_3682_);
lean_dec(v_a_3661_);
lean_dec(v_a_3640_);
lean_dec(v_a_3619_);
lean_dec(v_a_3598_);
lean_dec(v_a_3577_);
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3687_ = v___x_3684_;
v_isShared_3688_ = v_isSharedCheck_3694_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3684_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3694_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3689_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__43, &l_Lake_Check_instFromJsonConfig_fromJson___closed__43_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43);
v___x_3690_ = lean_string_append(v___x_3689_, v_a_3685_);
lean_dec(v_a_3685_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v___x_3690_);
v___x_3692_ = v___x_3687_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
else
{
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec(v_a_3682_);
lean_dec(v_a_3661_);
lean_dec(v_a_3640_);
lean_dec(v_a_3619_);
lean_dec(v_a_3598_);
lean_dec(v_a_3577_);
v_a_3695_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3684_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3684_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
lean_ctor_set_tag(v___x_3697_, 0);
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3711_; 
v_a_3703_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3705_ = v___x_3684_;
v_isShared_3706_ = v_isSharedCheck_3711_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3684_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3711_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; lean_object* v___x_3709_; 
v___x_3707_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3707_, 0, v_a_3577_);
lean_ctor_set(v___x_3707_, 1, v_a_3598_);
lean_ctor_set(v___x_3707_, 2, v_a_3619_);
lean_ctor_set(v___x_3707_, 3, v_a_3640_);
lean_ctor_set(v___x_3707_, 4, v_a_3661_);
lean_ctor_set(v___x_3707_, 5, v_a_3682_);
lean_ctor_set(v___x_3707_, 6, v_a_3703_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v___x_3707_);
v___x_3709_ = v___x_3705_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3707_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10(lean_object* v_cmp_3712_, lean_object* v_00_u03b2_3713_, lean_object* v_k_3714_, lean_object* v_v_3715_, lean_object* v_t_3716_, lean_object* v_hl_3717_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3712_, v_k_3714_, v_v_3715_, v_t_3716_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(lean_object* v_k_3721_, lean_object* v_x_3722_){
_start:
{
if (lean_obj_tag(v_x_3722_) == 0)
{
lean_object* v___x_3723_; 
lean_dec_ref(v_k_3721_);
v___x_3723_ = lean_box(0);
return v___x_3723_;
}
else
{
lean_object* v_val_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v_val_3724_ = lean_ctor_get(v_x_3722_, 0);
v___x_3725_ = lean_alloc_ctor(1, 0, 1);
v___x_3726_ = lean_unbox(v_val_3724_);
lean_ctor_set_uint8(v___x_3725_, 0, v___x_3726_);
v___x_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3727_, 0, v_k_3721_);
lean_ctor_set(v___x_3727_, 1, v___x_3725_);
v___x_3728_ = lean_box(0);
v___x_3729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
return v___x_3729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2___boxed(lean_object* v_k_3730_, lean_object* v_x_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v_k_3730_, v_x_3731_);
lean_dec(v_x_3731_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(size_t v_sz_3733_, size_t v_i_3734_, lean_object* v_bs_3735_){
_start:
{
uint8_t v___x_3736_; 
v___x_3736_ = lean_usize_dec_lt(v_i_3734_, v_sz_3733_);
if (v___x_3736_ == 0)
{
return v_bs_3735_;
}
else
{
lean_object* v_v_3737_; lean_object* v___x_3738_; lean_object* v_bs_x27_3739_; lean_object* v___x_3740_; size_t v___x_3741_; size_t v___x_3742_; lean_object* v___x_3743_; 
v_v_3737_ = lean_array_uget(v_bs_3735_, v_i_3734_);
v___x_3738_ = lean_unsigned_to_nat(0u);
v_bs_x27_3739_ = lean_array_uset(v_bs_3735_, v_i_3734_, v___x_3738_);
v___x_3740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3740_, 0, v_v_3737_);
v___x_3741_ = ((size_t)1ULL);
v___x_3742_ = lean_usize_add(v_i_3734_, v___x_3741_);
v___x_3743_ = lean_array_uset(v_bs_x27_3739_, v_i_3734_, v___x_3740_);
v_i_3734_ = v___x_3742_;
v_bs_3735_ = v___x_3743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3745_, lean_object* v_i_3746_, lean_object* v_bs_3747_){
_start:
{
size_t v_sz_boxed_3748_; size_t v_i_boxed_3749_; lean_object* v_res_3750_; 
v_sz_boxed_3748_ = lean_unbox_usize(v_sz_3745_);
lean_dec(v_sz_3745_);
v_i_boxed_3749_ = lean_unbox_usize(v_i_3746_);
lean_dec(v_i_3746_);
v_res_3750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_boxed_3748_, v_i_boxed_3749_, v_bs_3747_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(lean_object* v_a_3751_){
_start:
{
size_t v_sz_3752_; size_t v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v_sz_3752_ = lean_array_size(v_a_3751_);
v___x_3753_ = ((size_t)0ULL);
v___x_3754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_3752_, v___x_3753_, v_a_3751_);
v___x_3755_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(lean_object* v_x_3756_){
_start:
{
if (lean_obj_tag(v_x_3756_) == 0)
{
lean_object* v___x_3757_; 
v___x_3757_ = lean_box(0);
return v___x_3757_;
}
else
{
lean_object* v_val_3758_; lean_object* v___x_3759_; 
v_val_3758_ = lean_ctor_get(v_x_3756_, 0);
lean_inc(v_val_3758_);
lean_dec_ref_known(v_x_3756_, 1);
v___x_3759_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_val_3758_);
return v___x_3759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(lean_object* v_a_3760_, lean_object* v_a_3761_){
_start:
{
if (lean_obj_tag(v_a_3760_) == 0)
{
lean_object* v___x_3762_; 
v___x_3762_ = lean_array_to_list(v_a_3761_);
return v___x_3762_;
}
else
{
lean_object* v_head_3763_; lean_object* v_tail_3764_; lean_object* v___x_3765_; 
v_head_3763_ = lean_ctor_get(v_a_3760_, 0);
lean_inc(v_head_3763_);
v_tail_3764_ = lean_ctor_get(v_a_3760_, 1);
lean_inc(v_tail_3764_);
lean_dec_ref_known(v_a_3760_, 2);
v___x_3765_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_3761_, v_head_3763_);
v_a_3760_ = v_tail_3764_;
v_a_3761_ = v___x_3765_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(lean_object* v_t_3767_){
_start:
{
if (lean_obj_tag(v_t_3767_) == 0)
{
lean_object* v_size_3768_; lean_object* v_k_3769_; lean_object* v_v_3770_; lean_object* v_l_3771_; lean_object* v_r_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3782_; 
v_size_3768_ = lean_ctor_get(v_t_3767_, 0);
v_k_3769_ = lean_ctor_get(v_t_3767_, 1);
v_v_3770_ = lean_ctor_get(v_t_3767_, 2);
v_l_3771_ = lean_ctor_get(v_t_3767_, 3);
v_r_3772_ = lean_ctor_get(v_t_3767_, 4);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_t_3767_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3774_ = v_t_3767_;
v_isShared_3775_ = v_isSharedCheck_3782_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_r_3772_);
lean_inc(v_l_3771_);
lean_inc(v_v_3770_);
lean_inc(v_k_3769_);
lean_inc(v_size_3768_);
lean_dec(v_t_3767_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3782_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3780_; 
v___x_3776_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_v_3770_);
v___x_3777_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_l_3771_);
v___x_3778_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_r_3772_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 4, v___x_3778_);
lean_ctor_set(v___x_3774_, 3, v___x_3777_);
lean_ctor_set(v___x_3774_, 2, v___x_3776_);
v___x_3780_ = v___x_3774_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_size_3768_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_k_3769_);
lean_ctor_set(v_reuseFailAlloc_3781_, 2, v___x_3776_);
lean_ctor_set(v_reuseFailAlloc_3781_, 3, v___x_3777_);
lean_ctor_set(v_reuseFailAlloc_3781_, 4, v___x_3778_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
else
{
lean_object* v___x_3783_; 
v___x_3783_ = lean_box(1);
return v___x_3783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(lean_object* v_map_3784_){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_map_3784_);
v___x_3786_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(lean_object* v_k_3787_, lean_object* v_x_3788_){
_start:
{
if (lean_obj_tag(v_x_3788_) == 0)
{
lean_object* v___x_3789_; 
lean_dec_ref(v_k_3787_);
v___x_3789_ = lean_box(0);
return v___x_3789_;
}
else
{
lean_object* v_val_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v_val_3790_ = lean_ctor_get(v_x_3788_, 0);
lean_inc(v_val_3790_);
lean_dec_ref_known(v_x_3788_, 1);
v___x_3791_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(v_val_3790_);
v___x_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3792_, 0, v_k_3787_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = lean_box(0);
v___x_3794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3792_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
return v___x_3794_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instToJsonConfig_toJson(lean_object* v_x_3797_){
_start:
{
lean_object* v_challenge__module_3798_; lean_object* v_solution__module_3799_; lean_object* v_theorem__names_3800_; lean_object* v_definition__names_3801_; lean_object* v_permitted__axioms_3802_; lean_object* v_enable__nanoda_x3f_3803_; lean_object* v_external__kernels_x3f_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v_challenge__module_3798_ = lean_ctor_get(v_x_3797_, 0);
lean_inc_ref(v_challenge__module_3798_);
v_solution__module_3799_ = lean_ctor_get(v_x_3797_, 1);
lean_inc_ref(v_solution__module_3799_);
v_theorem__names_3800_ = lean_ctor_get(v_x_3797_, 2);
lean_inc_ref(v_theorem__names_3800_);
v_definition__names_3801_ = lean_ctor_get(v_x_3797_, 3);
lean_inc(v_definition__names_3801_);
v_permitted__axioms_3802_ = lean_ctor_get(v_x_3797_, 4);
lean_inc_ref(v_permitted__axioms_3802_);
v_enable__nanoda_x3f_3803_ = lean_ctor_get(v_x_3797_, 5);
lean_inc(v_enable__nanoda_x3f_3803_);
v_external__kernels_x3f_3804_ = lean_ctor_get(v_x_3797_, 6);
lean_inc(v_external__kernels_x3f_3804_);
lean_dec_ref(v_x_3797_);
v___x_3805_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
v___x_3806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3806_, 0, v_challenge__module_3798_);
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3805_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_box(0);
v___x_3809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
v___x_3811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3811_, 0, v_solution__module_3799_);
v___x_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
lean_ctor_set(v___x_3813_, 1, v___x_3808_);
v___x_3814_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
v___x_3815_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_theorem__names_3800_);
v___x_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3814_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
v___x_3817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
lean_ctor_set(v___x_3817_, 1, v___x_3808_);
v___x_3818_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
v___x_3819_ = l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(v_definition__names_3801_);
v___x_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3818_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
lean_ctor_set(v___x_3821_, 1, v___x_3808_);
v___x_3822_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
v___x_3823_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_permitted__axioms_3802_);
v___x_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3822_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
lean_ctor_set(v___x_3825_, 1, v___x_3808_);
v___x_3826_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
v___x_3827_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v___x_3826_, v_enable__nanoda_x3f_3803_);
lean_dec(v_enable__nanoda_x3f_3803_);
v___x_3828_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_3829_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(v___x_3828_, v_external__kernels_x3f_3804_);
v___x_3830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
lean_ctor_set(v___x_3830_, 1, v___x_3808_);
v___x_3831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3827_);
lean_ctor_set(v___x_3831_, 1, v___x_3830_);
v___x_3832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3825_);
lean_ctor_set(v___x_3832_, 1, v___x_3831_);
v___x_3833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3821_);
lean_ctor_set(v___x_3833_, 1, v___x_3832_);
v___x_3834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3817_);
lean_ctor_set(v___x_3834_, 1, v___x_3833_);
v___x_3835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3813_);
lean_ctor_set(v___x_3835_, 1, v___x_3834_);
v___x_3836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3809_);
lean_ctor_set(v___x_3836_, 1, v___x_3835_);
v___x_3837_ = ((lean_object*)(l_Lake_Check_instToJsonConfig_toJson___closed__0));
v___x_3838_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(v___x_3836_, v___x_3837_);
v___x_3839_ = l_Lean_Json_mkObj(v___x_3838_);
lean_dec(v___x_3838_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(lean_object* v_x_3848_, lean_object* v_x_3849_){
_start:
{
if (lean_obj_tag(v_x_3848_) == 0)
{
lean_object* v___x_3850_; 
v___x_3850_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3850_;
}
else
{
lean_object* v_val_3851_; lean_object* v___x_3852_; uint8_t v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v_val_3851_ = lean_ctor_get(v_x_3848_, 0);
v___x_3852_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3853_ = lean_unbox(v_val_3851_);
v___x_3854_ = l_Bool_repr___redArg(v___x_3853_);
v___x_3855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3852_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
v___x_3856_ = l_Repr_addAppParen(v___x_3855_, v_x_3849_);
return v___x_3856_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___boxed(lean_object* v_x_3857_, lean_object* v_x_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_x_3857_, v_x_3858_);
lean_dec(v_x_3858_);
lean_dec(v_x_3857_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_Check_instReprConfig_repr_spec__4(lean_object* v_a_3860_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_nat_to_int(v_a_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(lean_object* v_x_3862_, lean_object* v_x_3863_, lean_object* v_x_3864_){
_start:
{
if (lean_obj_tag(v_x_3864_) == 0)
{
lean_dec(v_x_3862_);
return v_x_3863_;
}
else
{
lean_object* v_head_3865_; lean_object* v_tail_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3877_; 
v_head_3865_ = lean_ctor_get(v_x_3864_, 0);
v_tail_3866_ = lean_ctor_get(v_x_3864_, 1);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_x_3864_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3868_ = v_x_3864_;
v_isShared_3869_ = v_isSharedCheck_3877_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_tail_3866_);
lean_inc(v_head_3865_);
lean_dec(v_x_3864_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3877_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
lean_inc(v_x_3862_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set_tag(v___x_3868_, 5);
lean_ctor_set(v___x_3868_, 1, v_x_3862_);
lean_ctor_set(v___x_3868_, 0, v_x_3863_);
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_x_3863_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v_x_3862_);
v___x_3871_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3872_ = l_String_quote(v_head_3865_);
v___x_3873_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3872_);
v___x_3874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3871_);
lean_ctor_set(v___x_3874_, 1, v___x_3873_);
v_x_3863_ = v___x_3874_;
v_x_3864_ = v_tail_3866_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_3878_, lean_object* v_x_3879_, lean_object* v_x_3880_){
_start:
{
if (lean_obj_tag(v_x_3880_) == 0)
{
lean_dec(v_x_3878_);
return v_x_3879_;
}
else
{
lean_object* v_head_3881_; lean_object* v_tail_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3893_; 
v_head_3881_ = lean_ctor_get(v_x_3880_, 0);
v_tail_3882_ = lean_ctor_get(v_x_3880_, 1);
v_isSharedCheck_3893_ = !lean_is_exclusive(v_x_3880_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3884_ = v_x_3880_;
v_isShared_3885_ = v_isSharedCheck_3893_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_tail_3882_);
lean_inc(v_head_3881_);
lean_dec(v_x_3880_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3893_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
lean_inc(v_x_3878_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set_tag(v___x_3884_, 5);
lean_ctor_set(v___x_3884_, 1, v_x_3878_);
lean_ctor_set(v___x_3884_, 0, v_x_3879_);
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_x_3879_);
lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_x_3878_);
v___x_3887_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3888_ = l_String_quote(v_head_3881_);
v___x_3889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
v___x_3890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3887_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(v_x_3878_, v___x_3890_, v_tail_3882_);
return v___x_3891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(lean_object* v___y_3894_){
_start:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3895_ = l_String_quote(v___y_3894_);
v___x_3896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(lean_object* v_x_3897_, lean_object* v_x_3898_){
_start:
{
if (lean_obj_tag(v_x_3897_) == 0)
{
lean_object* v___x_3899_; 
lean_dec(v_x_3898_);
v___x_3899_ = lean_box(0);
return v___x_3899_;
}
else
{
lean_object* v_tail_3900_; 
v_tail_3900_ = lean_ctor_get(v_x_3897_, 1);
if (lean_obj_tag(v_tail_3900_) == 0)
{
lean_object* v_head_3901_; lean_object* v___x_3902_; 
lean_dec(v_x_3898_);
v_head_3901_ = lean_ctor_get(v_x_3897_, 0);
lean_inc(v_head_3901_);
lean_dec_ref_known(v_x_3897_, 2);
v___x_3902_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3901_);
return v___x_3902_;
}
else
{
lean_object* v_head_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
lean_inc(v_tail_3900_);
v_head_3903_ = lean_ctor_get(v_x_3897_, 0);
lean_inc(v_head_3903_);
lean_dec_ref_known(v_x_3897_, 2);
v___x_3904_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3903_);
v___x_3905_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(v_x_3898_, v___x_3904_, v_tail_3900_);
return v___x_3905_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__0));
v___x_3914_ = lean_string_length(v___x_3913_);
return v___x_3914_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4);
v___x_3916_ = lean_nat_to_int(v___x_3915_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(lean_object* v_xs_3924_){
_start:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; uint8_t v___x_3927_; 
v___x_3925_ = lean_array_get_size(v_xs_3924_);
v___x_3926_ = lean_unsigned_to_nat(0u);
v___x_3927_ = lean_nat_dec_eq(v___x_3925_, v___x_3926_);
if (v___x_3927_ == 0)
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3928_ = lean_array_to_list(v_xs_3924_);
v___x_3929_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3930_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(v___x_3928_, v___x_3929_);
v___x_3931_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5);
v___x_3932_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__6));
v___x_3933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
lean_ctor_set(v___x_3933_, 1, v___x_3930_);
v___x_3934_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_3935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3933_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
v___x_3936_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3931_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = l_Std_Format_fill(v___x_3936_);
return v___x_3937_;
}
else
{
lean_object* v___x_3938_; 
lean_dec_ref(v_xs_3924_);
v___x_3938_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__9));
return v___x_3938_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(lean_object* v_x_3939_, lean_object* v_x_3940_){
_start:
{
if (lean_obj_tag(v_x_3939_) == 0)
{
lean_object* v___x_3941_; 
v___x_3941_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3941_;
}
else
{
lean_object* v_val_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v_val_3942_ = lean_ctor_get(v_x_3939_, 0);
lean_inc(v_val_3942_);
lean_dec_ref_known(v_x_3939_, 1);
v___x_3943_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3944_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_val_3942_);
v___x_3945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3943_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = l_Repr_addAppParen(v___x_3945_, v_x_3940_);
return v___x_3946_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1___boxed(lean_object* v_x_3947_, lean_object* v_x_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_x_3947_, v_x_3948_);
lean_dec(v_x_3948_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(lean_object* v_init_3950_, lean_object* v_x_3951_){
_start:
{
if (lean_obj_tag(v_x_3951_) == 0)
{
lean_object* v_k_3952_; lean_object* v_v_3953_; lean_object* v_l_3954_; lean_object* v_r_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v_k_3952_ = lean_ctor_get(v_x_3951_, 1);
v_v_3953_ = lean_ctor_get(v_x_3951_, 2);
v_l_3954_ = lean_ctor_get(v_x_3951_, 3);
v_r_3955_ = lean_ctor_get(v_x_3951_, 4);
v___x_3956_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_3950_, v_r_3955_);
lean_inc(v_v_3953_);
lean_inc(v_k_3952_);
v___x_3957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3957_, 0, v_k_3952_);
lean_ctor_set(v___x_3957_, 1, v_v_3953_);
v___x_3958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
lean_ctor_set(v___x_3958_, 1, v___x_3956_);
v_init_3950_ = v___x_3958_;
v_x_3951_ = v_l_3954_;
goto _start;
}
else
{
return v_init_3950_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4___boxed(lean_object* v_init_3960_, lean_object* v_x_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_3960_, v_x_3961_);
lean_dec(v_x_3961_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(lean_object* v_x_3963_, lean_object* v_x_3964_, lean_object* v_x_3965_){
_start:
{
if (lean_obj_tag(v_x_3965_) == 0)
{
lean_dec(v_x_3963_);
return v_x_3964_;
}
else
{
lean_object* v_head_3966_; lean_object* v_tail_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3976_; 
v_head_3966_ = lean_ctor_get(v_x_3965_, 0);
v_tail_3967_ = lean_ctor_get(v_x_3965_, 1);
v_isSharedCheck_3976_ = !lean_is_exclusive(v_x_3965_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3969_ = v_x_3965_;
v_isShared_3970_ = v_isSharedCheck_3976_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_tail_3967_);
lean_inc(v_head_3966_);
lean_dec(v_x_3965_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3976_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
lean_inc(v_x_3963_);
if (v_isShared_3970_ == 0)
{
lean_ctor_set_tag(v___x_3969_, 5);
lean_ctor_set(v___x_3969_, 1, v_x_3963_);
lean_ctor_set(v___x_3969_, 0, v_x_3964_);
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_x_3964_);
lean_ctor_set(v_reuseFailAlloc_3975_, 1, v_x_3963_);
v___x_3972_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
lean_object* v___x_3973_; 
v___x_3973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
lean_ctor_set(v___x_3973_, 1, v_head_3966_);
v_x_3964_ = v___x_3973_;
v_x_3965_ = v_tail_3967_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(lean_object* v_x_3977_, lean_object* v_x_3978_){
_start:
{
if (lean_obj_tag(v_x_3977_) == 0)
{
lean_object* v___x_3979_; 
lean_dec(v_x_3978_);
v___x_3979_ = lean_box(0);
return v___x_3979_;
}
else
{
lean_object* v_tail_3980_; 
v_tail_3980_ = lean_ctor_get(v_x_3977_, 1);
if (lean_obj_tag(v_tail_3980_) == 0)
{
lean_object* v_head_3981_; 
lean_dec(v_x_3978_);
v_head_3981_ = lean_ctor_get(v_x_3977_, 0);
lean_inc(v_head_3981_);
lean_dec_ref_known(v_x_3977_, 2);
return v_head_3981_;
}
else
{
lean_object* v_head_3982_; lean_object* v___x_3983_; 
lean_inc(v_tail_3980_);
v_head_3982_ = lean_ctor_get(v_x_3977_, 0);
lean_inc(v_head_3982_);
lean_dec_ref_known(v_x_3977_, 2);
v___x_3983_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(v_x_3978_, v_head_3982_, v_tail_3980_);
return v___x_3983_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3986_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__0));
v___x_3987_ = lean_string_length(v___x_3986_);
return v___x_3987_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2);
v___x_3989_ = lean_nat_to_int(v___x_3988_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(lean_object* v_x_3994_){
_start:
{
lean_object* v_fst_3995_; lean_object* v_snd_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4019_; 
v_fst_3995_ = lean_ctor_get(v_x_3994_, 0);
v_snd_3996_ = lean_ctor_get(v_x_3994_, 1);
v_isSharedCheck_4019_ = !lean_is_exclusive(v_x_3994_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_3998_ = v_x_3994_;
v_isShared_3999_ = v_isSharedCheck_4019_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_snd_3996_);
lean_inc(v_fst_3995_);
lean_dec(v_x_3994_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4019_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4004_; 
v___x_4000_ = l_String_quote(v_fst_3995_);
v___x_4001_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
v___x_4002_ = lean_box(0);
if (v_isShared_3999_ == 0)
{
lean_ctor_set_tag(v___x_3998_, 1);
lean_ctor_set(v___x_3998_, 1, v___x_4002_);
lean_ctor_set(v___x_3998_, 0, v___x_4001_);
v___x_4004_ = v___x_3998_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v___x_4001_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v___x_4002_);
v___x_4004_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; uint8_t v___x_4016_; lean_object* v___x_4017_; 
v___x_4005_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_snd_3996_);
v___x_4006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
lean_ctor_set(v___x_4006_, 1, v___x_4004_);
v___x_4007_ = l_List_reverse___redArg(v___x_4006_);
v___x_4008_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_4009_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(v___x_4007_, v___x_4008_);
v___x_4010_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3);
v___x_4011_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__4));
v___x_4012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
lean_ctor_set(v___x_4012_, 1, v___x_4009_);
v___x_4013_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__5));
v___x_4014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4012_);
lean_ctor_set(v___x_4014_, 1, v___x_4013_);
v___x_4015_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4010_);
lean_ctor_set(v___x_4015_, 1, v___x_4014_);
v___x_4016_ = 0;
v___x_4017_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4017_, 0, v___x_4015_);
lean_ctor_set_uint8(v___x_4017_, sizeof(void*)*1, v___x_4016_);
return v___x_4017_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(lean_object* v_x_4020_, lean_object* v_x_4021_, lean_object* v_x_4022_){
_start:
{
if (lean_obj_tag(v_x_4022_) == 0)
{
lean_dec(v_x_4020_);
return v_x_4021_;
}
else
{
lean_object* v_head_4023_; lean_object* v_tail_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4034_; 
v_head_4023_ = lean_ctor_get(v_x_4022_, 0);
v_tail_4024_ = lean_ctor_get(v_x_4022_, 1);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_x_4022_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4026_ = v_x_4022_;
v_isShared_4027_ = v_isSharedCheck_4034_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_tail_4024_);
lean_inc(v_head_4023_);
lean_dec(v_x_4022_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4034_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
lean_inc(v_x_4020_);
if (v_isShared_4027_ == 0)
{
lean_ctor_set_tag(v___x_4026_, 5);
lean_ctor_set(v___x_4026_, 1, v_x_4020_);
lean_ctor_set(v___x_4026_, 0, v_x_4021_);
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_x_4021_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v_x_4020_);
v___x_4029_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4030_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_4023_);
v___x_4031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4029_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
v_x_4021_ = v___x_4031_;
v_x_4022_ = v_tail_4024_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(lean_object* v_x_4035_, lean_object* v_x_4036_, lean_object* v_x_4037_){
_start:
{
if (lean_obj_tag(v_x_4037_) == 0)
{
lean_dec(v_x_4035_);
return v_x_4036_;
}
else
{
lean_object* v_head_4038_; lean_object* v_tail_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4049_; 
v_head_4038_ = lean_ctor_get(v_x_4037_, 0);
v_tail_4039_ = lean_ctor_get(v_x_4037_, 1);
v_isSharedCheck_4049_ = !lean_is_exclusive(v_x_4037_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4041_ = v_x_4037_;
v_isShared_4042_ = v_isSharedCheck_4049_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_tail_4039_);
lean_inc(v_head_4038_);
lean_dec(v_x_4037_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4049_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
lean_inc(v_x_4035_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set_tag(v___x_4041_, 5);
lean_ctor_set(v___x_4041_, 1, v_x_4035_);
lean_ctor_set(v___x_4041_, 0, v_x_4036_);
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_x_4036_);
lean_ctor_set(v_reuseFailAlloc_4048_, 1, v_x_4035_);
v___x_4044_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4045_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_4038_);
v___x_4046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4044_);
lean_ctor_set(v___x_4046_, 1, v___x_4045_);
v___x_4047_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(v_x_4035_, v___x_4046_, v_tail_4039_);
return v___x_4047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(lean_object* v_x_4050_, lean_object* v_x_4051_){
_start:
{
if (lean_obj_tag(v_x_4050_) == 0)
{
lean_object* v___x_4052_; 
lean_dec(v_x_4051_);
v___x_4052_ = lean_box(0);
return v___x_4052_;
}
else
{
lean_object* v_tail_4053_; 
v_tail_4053_ = lean_ctor_get(v_x_4050_, 1);
if (lean_obj_tag(v_tail_4053_) == 0)
{
lean_object* v_head_4054_; lean_object* v___x_4055_; 
lean_dec(v_x_4051_);
v_head_4054_ = lean_ctor_get(v_x_4050_, 0);
lean_inc(v_head_4054_);
lean_dec_ref_known(v_x_4050_, 2);
v___x_4055_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_4054_);
return v___x_4055_;
}
else
{
lean_object* v_head_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
lean_inc(v_tail_4053_);
v_head_4056_ = lean_ctor_get(v_x_4050_, 0);
lean_inc(v_head_4056_);
lean_dec_ref_known(v_x_4050_, 2);
v___x_4057_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_4056_);
v___x_4058_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(v_x_4051_, v___x_4057_, v_tail_4053_);
return v___x_4058_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_4062_ = lean_string_length(v___x_4061_);
return v___x_4062_;
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1);
v___x_4064_ = lean_nat_to_int(v___x_4063_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(lean_object* v_a_4067_){
_start:
{
if (lean_obj_tag(v_a_4067_) == 0)
{
lean_object* v___x_4068_; 
v___x_4068_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0));
return v___x_4068_;
}
else
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; lean_object* v___x_4078_; 
v___x_4069_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_4070_ = l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(v_a_4067_, v___x_4069_);
v___x_4071_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2);
v___x_4072_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__3));
v___x_4073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
lean_ctor_set(v___x_4073_, 1, v___x_4070_);
v___x_4074_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_4075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4073_);
lean_ctor_set(v___x_4075_, 1, v___x_4074_);
v___x_4076_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4071_);
lean_ctor_set(v___x_4076_, 1, v___x_4075_);
v___x_4077_ = 0;
v___x_4078_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4078_, 0, v___x_4076_);
lean_ctor_set_uint8(v___x_4078_, sizeof(void*)*1, v___x_4077_);
return v___x_4078_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(lean_object* v_x_4082_, lean_object* v_x_4083_){
_start:
{
if (lean_obj_tag(v_x_4082_) == 0)
{
lean_object* v___x_4084_; 
v___x_4084_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_4084_;
}
else
{
lean_object* v_val_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v_val_4085_ = lean_ctor_get(v_x_4082_, 0);
v___x_4086_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_4087_ = lean_unsigned_to_nat(1024u);
v___x_4088_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__1));
v___x_4089_ = lean_box(0);
v___x_4090_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v___x_4089_, v_val_4085_);
v___x_4091_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v___x_4090_);
v___x_4092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4088_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___x_4093_ = l_Repr_addAppParen(v___x_4092_, v___x_4087_);
v___x_4094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4086_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = l_Repr_addAppParen(v___x_4094_, v_x_4083_);
return v___x_4095_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___boxed(lean_object* v_x_4096_, lean_object* v_x_4097_){
_start:
{
lean_object* v_res_4098_; 
v_res_4098_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_x_4096_, v_x_4097_);
lean_dec(v_x_4097_);
lean_dec(v_x_4096_);
return v_res_4098_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4111_ = lean_unsigned_to_nat(20u);
v___x_4112_ = lean_nat_to_int(v___x_4111_);
return v___x_4112_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4115_ = lean_unsigned_to_nat(19u);
v___x_4116_ = lean_nat_to_int(v___x_4115_);
return v___x_4116_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4119_ = lean_unsigned_to_nat(17u);
v___x_4120_ = lean_nat_to_int(v___x_4119_);
return v___x_4120_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4127_ = lean_unsigned_to_nat(18u);
v___x_4128_ = lean_nat_to_int(v___x_4127_);
return v___x_4128_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4131_ = lean_unsigned_to_nat(21u);
v___x_4132_ = lean_nat_to_int(v___x_4131_);
return v___x_4132_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__0));
v___x_4135_ = lean_string_length(v___x_4134_);
return v___x_4135_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4136_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__18, &l_Lake_Check_instReprConfig_repr___redArg___closed__18_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18);
v___x_4137_ = lean_nat_to_int(v___x_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___redArg(lean_object* v_x_4142_){
_start:
{
lean_object* v_challenge__module_4143_; lean_object* v_solution__module_4144_; lean_object* v_theorem__names_4145_; lean_object* v_definition__names_4146_; lean_object* v_permitted__axioms_4147_; lean_object* v_enable__nanoda_x3f_4148_; lean_object* v_external__kernels_x3f_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v_challenge__module_4143_ = lean_ctor_get(v_x_4142_, 0);
lean_inc_ref(v_challenge__module_4143_);
v_solution__module_4144_ = lean_ctor_get(v_x_4142_, 1);
lean_inc_ref(v_solution__module_4144_);
v_theorem__names_4145_ = lean_ctor_get(v_x_4142_, 2);
lean_inc_ref(v_theorem__names_4145_);
v_definition__names_4146_ = lean_ctor_get(v_x_4142_, 3);
lean_inc(v_definition__names_4146_);
v_permitted__axioms_4147_ = lean_ctor_get(v_x_4142_, 4);
lean_inc_ref(v_permitted__axioms_4147_);
v_enable__nanoda_x3f_4148_ = lean_ctor_get(v_x_4142_, 5);
lean_inc(v_enable__nanoda_x3f_4148_);
v_external__kernels_x3f_4149_ = lean_ctor_get(v_x_4142_, 6);
lean_inc(v_external__kernels_x3f_4149_);
lean_dec_ref(v_x_4142_);
v___x_4150_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__4));
v___x_4151_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__5));
v___x_4152_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__6, &l_Lake_Check_instReprConfig_repr___redArg___closed__6_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6);
v___x_4153_ = l_String_quote(v_challenge__module_4143_);
v___x_4154_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4153_);
v___x_4155_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4152_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
v___x_4156_ = 0;
v___x_4157_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4157_, 0, v___x_4155_);
lean_ctor_set_uint8(v___x_4157_, sizeof(void*)*1, v___x_4156_);
v___x_4158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4151_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__2));
v___x_4160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4158_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
v___x_4161_ = lean_box(1);
v___x_4162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4160_);
lean_ctor_set(v___x_4162_, 1, v___x_4161_);
v___x_4163_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__7));
v___x_4164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4162_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
lean_ctor_set(v___x_4165_, 1, v___x_4150_);
v___x_4166_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__8, &l_Lake_Check_instReprConfig_repr___redArg___closed__8_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8);
v___x_4167_ = l_String_quote(v_solution__module_4144_);
v___x_4168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
v___x_4169_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4166_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
lean_ctor_set_uint8(v___x_4170_, sizeof(void*)*1, v___x_4156_);
v___x_4171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4165_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
lean_ctor_set(v___x_4172_, 1, v___x_4159_);
v___x_4173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4172_);
lean_ctor_set(v___x_4173_, 1, v___x_4161_);
v___x_4174_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__9));
v___x_4175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4173_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
v___x_4176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
lean_ctor_set(v___x_4176_, 1, v___x_4150_);
v___x_4177_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__10, &l_Lake_Check_instReprConfig_repr___redArg___closed__10_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10);
v___x_4178_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_theorem__names_4145_);
v___x_4179_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4177_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
lean_ctor_set_uint8(v___x_4180_, sizeof(void*)*1, v___x_4156_);
v___x_4181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4176_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
lean_ctor_set(v___x_4182_, 1, v___x_4159_);
v___x_4183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
lean_ctor_set(v___x_4183_, 1, v___x_4161_);
v___x_4184_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__11));
v___x_4185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4183_);
lean_ctor_set(v___x_4185_, 1, v___x_4184_);
v___x_4186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
lean_ctor_set(v___x_4186_, 1, v___x_4150_);
v___x_4187_ = lean_unsigned_to_nat(0u);
v___x_4188_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_definition__names_4146_, v___x_4187_);
v___x_4189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4152_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
lean_ctor_set_uint8(v___x_4190_, sizeof(void*)*1, v___x_4156_);
v___x_4191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4186_);
lean_ctor_set(v___x_4191_, 1, v___x_4190_);
v___x_4192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
lean_ctor_set(v___x_4192_, 1, v___x_4159_);
v___x_4193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4192_);
lean_ctor_set(v___x_4193_, 1, v___x_4161_);
v___x_4194_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__12));
v___x_4195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4193_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
v___x_4196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
lean_ctor_set(v___x_4196_, 1, v___x_4150_);
v___x_4197_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_permitted__axioms_4147_);
v___x_4198_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4152_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
v___x_4199_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
lean_ctor_set_uint8(v___x_4199_, sizeof(void*)*1, v___x_4156_);
v___x_4200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4196_);
lean_ctor_set(v___x_4200_, 1, v___x_4199_);
v___x_4201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4200_);
lean_ctor_set(v___x_4201_, 1, v___x_4159_);
v___x_4202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
lean_ctor_set(v___x_4202_, 1, v___x_4161_);
v___x_4203_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__13));
v___x_4204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4202_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
lean_ctor_set(v___x_4205_, 1, v___x_4150_);
v___x_4206_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__14, &l_Lake_Check_instReprConfig_repr___redArg___closed__14_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14);
v___x_4207_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_enable__nanoda_x3f_4148_, v___x_4187_);
lean_dec(v_enable__nanoda_x3f_4148_);
v___x_4208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4206_);
lean_ctor_set(v___x_4208_, 1, v___x_4207_);
v___x_4209_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
lean_ctor_set_uint8(v___x_4209_, sizeof(void*)*1, v___x_4156_);
v___x_4210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4205_);
lean_ctor_set(v___x_4210_, 1, v___x_4209_);
v___x_4211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4210_);
lean_ctor_set(v___x_4211_, 1, v___x_4159_);
v___x_4212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4211_);
lean_ctor_set(v___x_4212_, 1, v___x_4161_);
v___x_4213_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__15));
v___x_4214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4212_);
lean_ctor_set(v___x_4214_, 1, v___x_4213_);
v___x_4215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
lean_ctor_set(v___x_4215_, 1, v___x_4150_);
v___x_4216_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__16, &l_Lake_Check_instReprConfig_repr___redArg___closed__16_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16);
v___x_4217_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_external__kernels_x3f_4149_, v___x_4187_);
lean_dec(v_external__kernels_x3f_4149_);
v___x_4218_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4216_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
v___x_4219_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4219_, 0, v___x_4218_);
lean_ctor_set_uint8(v___x_4219_, sizeof(void*)*1, v___x_4156_);
v___x_4220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4215_);
lean_ctor_set(v___x_4220_, 1, v___x_4219_);
v___x_4221_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__19, &l_Lake_Check_instReprConfig_repr___redArg___closed__19_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19);
v___x_4222_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__20));
v___x_4223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4222_);
lean_ctor_set(v___x_4223_, 1, v___x_4220_);
v___x_4224_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__21));
v___x_4225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4223_);
lean_ctor_set(v___x_4225_, 1, v___x_4224_);
v___x_4226_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4221_);
lean_ctor_set(v___x_4226_, 1, v___x_4225_);
v___x_4227_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4227_, 0, v___x_4226_);
lean_ctor_set_uint8(v___x_4227_, sizeof(void*)*1, v___x_4156_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr(lean_object* v_x_4228_, lean_object* v_prec_4229_){
_start:
{
lean_object* v___x_4230_; 
v___x_4230_ = l_Lake_Check_instReprConfig_repr___redArg(v_x_4228_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___boxed(lean_object* v_x_4231_, lean_object* v_prec_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Lake_Check_instReprConfig_repr(v_x_4231_, v_prec_4232_);
lean_dec(v_prec_4232_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(lean_object* v_a_4234_, lean_object* v_n_4235_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v_a_4234_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___boxed(lean_object* v_a_4237_, lean_object* v_n_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(v_a_4237_, v_n_4238_);
lean_dec(v_n_4238_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(lean_object* v_x_4240_, lean_object* v_x_4241_){
_start:
{
lean_object* v___x_4242_; 
v___x_4242_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_x_4240_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___boxed(lean_object* v_x_4243_, lean_object* v_x_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(v_x_4243_, v_x_4244_);
lean_dec(v_x_4244_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(lean_object* v_s_4248_){
_start:
{
uint32_t v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4250_ = 10;
v___x_4251_ = lean_string_push(v_s_4248_, v___x_4250_);
v___x_4252_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v___x_4251_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0___boxed(lean_object* v_s_4253_, lean_object* v_a_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v_s_4253_);
return v_res_4255_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1(void){
_start:
{
uint32_t v___x_4257_; lean_object* v___x_4258_; 
v___x_4257_ = 2;
v___x_4258_ = lean_box_uint32(v___x_4257_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(lean_object* v_msg_4259_){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4261_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_4262_ = lean_string_append(v___x_4261_, v_msg_4259_);
v___x_4263_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_4262_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4271_; 
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4271_ == 0)
{
lean_object* v_unused_4272_; 
v_unused_4272_ = lean_ctor_get(v___x_4263_, 0);
lean_dec(v_unused_4272_);
v___x_4265_ = v___x_4263_;
v_isShared_4266_ = v_isSharedCheck_4271_;
goto v_resetjp_4264_;
}
else
{
lean_dec(v___x_4263_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4271_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4267_; lean_object* v___x_4269_; 
v___x_4267_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1;
if (v_isShared_4266_ == 0)
{
lean_ctor_set(v___x_4265_, 0, v___x_4267_);
v___x_4269_ = v___x_4265_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v___x_4267_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
v_a_4273_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4263_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4263_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed(lean_object* v_msg_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v_msg_4281_);
lean_dec_ref(v_msg_4281_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(lean_object* v_cmd_4287_, lean_object* v_projectDir_4288_){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; uint8_t v___x_4292_; 
v___x_4290_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__0));
lean_inc_ref(v_projectDir_4288_);
v___x_4291_ = l_System_FilePath_join(v_projectDir_4288_, v___x_4290_);
v___x_4292_ = l_System_FilePath_pathExists(v___x_4291_);
lean_dec_ref(v___x_4291_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4293_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_4294_ = lean_string_append(v___x_4293_, v_projectDir_4288_);
lean_dec_ref(v_projectDir_4288_);
v___x_4295_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__1));
v___x_4296_ = lean_string_append(v___x_4294_, v___x_4295_);
v___x_4297_ = lean_string_append(v___x_4296_, v_cmd_4287_);
v___x_4298_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__2));
v___x_4299_ = lean_string_append(v___x_4297_, v___x_4298_);
v___x_4300_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4299_);
lean_dec_ref(v___x_4299_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4309_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4303_ = v___x_4300_;
v_isShared_4304_ = v_isSharedCheck_4309_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4300_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4309_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4305_; lean_object* v___x_4307_; 
v___x_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4305_, 0, v_a_4301_);
if (v_isShared_4304_ == 0)
{
lean_ctor_set(v___x_4303_, 0, v___x_4305_);
v___x_4307_ = v___x_4303_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4305_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
v_a_4310_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4300_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4300_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
else
{
lean_object* v___x_4318_; lean_object* v___x_4319_; 
lean_dec_ref(v_projectDir_4288_);
v___x_4318_ = lean_box(0);
v___x_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4318_);
return v___x_4319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___boxed(lean_object* v_cmd_4320_, lean_object* v_projectDir_4321_, lean_object* v_a_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v_cmd_4320_, v_projectDir_4321_);
lean_dec_ref(v_cmd_4320_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(lean_object* v_lean_4324_, lean_object* v_name_4325_){
_start:
{
lean_object* v_binDir_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v_binDir_4326_ = lean_ctor_get(v_lean_4324_, 6);
lean_inc_ref(v_binDir_4326_);
lean_dec_ref(v_lean_4324_);
v___x_4327_ = l_System_FilePath_join(v_binDir_4326_, v_name_4325_);
v___x_4328_ = l_System_FilePath_exeExtension;
v___x_4329_ = l_System_FilePath_addExtension(v___x_4327_, v___x_4328_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels(lean_object* v_lean_4338_){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4339_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__0));
v___x_4340_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__1));
lean_inc_ref_n(v_lean_4338_, 4);
v___x_4341_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4338_, v___x_4340_);
v___x_4342_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0));
v___x_4343_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_4344_ = lean_unsigned_to_nat(3u);
v___x_4345_ = lean_mk_empty_array_with_capacity(v___x_4344_);
v___x_4346_ = lean_array_push(v___x_4345_, v___x_4341_);
v___x_4347_ = lean_array_push(v___x_4346_, v___x_4342_);
v___x_4348_ = lean_array_push(v___x_4347_, v___x_4343_);
v___x_4349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4339_);
lean_ctor_set(v___x_4349_, 1, v___x_4348_);
v___x_4350_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__2));
v___x_4351_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4338_, v___x_4350_);
v___x_4352_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__3));
v___x_4353_ = lean_unsigned_to_nat(2u);
v___x_4354_ = lean_mk_empty_array_with_capacity(v___x_4353_);
v___x_4355_ = lean_array_push(v___x_4354_, v___x_4351_);
v___x_4356_ = lean_array_push(v___x_4355_, v___x_4352_);
v___x_4357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4350_);
lean_ctor_set(v___x_4357_, 1, v___x_4356_);
v___x_4358_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__4));
v___x_4359_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__5));
v___x_4360_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4338_, v___x_4359_);
v___x_4361_ = lean_unsigned_to_nat(1u);
v___x_4362_ = lean_mk_empty_array_with_capacity(v___x_4361_);
lean_inc_ref_n(v___x_4362_, 2);
v___x_4363_ = lean_array_push(v___x_4362_, v___x_4360_);
v___x_4364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4358_);
lean_ctor_set(v___x_4364_, 1, v___x_4363_);
v___x_4365_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__6));
v___x_4366_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4338_, v___x_4365_);
v___x_4367_ = lean_array_push(v___x_4362_, v___x_4366_);
v___x_4368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4365_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
v___x_4369_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__7));
v___x_4370_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4338_, v___x_4369_);
v___x_4371_ = lean_array_push(v___x_4362_, v___x_4370_);
v___x_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4369_);
lean_ctor_set(v___x_4372_, 1, v___x_4371_);
v___x_4373_ = lean_unsigned_to_nat(5u);
v___x_4374_ = lean_mk_empty_array_with_capacity(v___x_4373_);
v___x_4375_ = lean_array_push(v___x_4374_, v___x_4349_);
v___x_4376_ = lean_array_push(v___x_4375_, v___x_4357_);
v___x_4377_ = lean_array_push(v___x_4376_, v___x_4364_);
v___x_4378_ = lean_array_push(v___x_4377_, v___x_4368_);
v___x_4379_ = lean_array_push(v___x_4378_, v___x_4372_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(uint8_t v_a_4380_, lean_object* v_b_4381_, lean_object* v_x_4382_){
_start:
{
if (lean_obj_tag(v_x_4382_) == 0)
{
lean_dec(v_b_4381_);
return v_x_4382_;
}
else
{
lean_object* v_key_4383_; lean_object* v_value_4384_; lean_object* v_tail_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4401_; 
v_key_4383_ = lean_ctor_get(v_x_4382_, 0);
v_value_4384_ = lean_ctor_get(v_x_4382_, 1);
v_tail_4385_ = lean_ctor_get(v_x_4382_, 2);
v_isSharedCheck_4401_ = !lean_is_exclusive(v_x_4382_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4387_ = v_x_4382_;
v_isShared_4388_ = v_isSharedCheck_4401_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_tail_4385_);
lean_inc(v_value_4384_);
lean_inc(v_key_4383_);
lean_dec(v_x_4382_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4401_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
uint8_t v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; uint8_t v___x_4392_; 
v___x_4389_ = lean_unbox(v_key_4383_);
v___x_4390_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v___x_4389_);
v___x_4391_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v_a_4380_);
v___x_4392_ = lean_nat_dec_eq(v___x_4390_, v___x_4391_);
lean_dec(v___x_4391_);
lean_dec(v___x_4390_);
if (v___x_4392_ == 0)
{
lean_object* v___x_4393_; lean_object* v___x_4395_; 
v___x_4393_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_4380_, v_b_4381_, v_tail_4385_);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 2, v___x_4393_);
v___x_4395_ = v___x_4387_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_key_4383_);
lean_ctor_set(v_reuseFailAlloc_4396_, 1, v_value_4384_);
lean_ctor_set(v_reuseFailAlloc_4396_, 2, v___x_4393_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
else
{
lean_object* v___x_4397_; lean_object* v___x_4399_; 
lean_dec(v_value_4384_);
lean_dec(v_key_4383_);
v___x_4397_ = lean_box(v_a_4380_);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 1, v_b_4381_);
lean_ctor_set(v___x_4387_, 0, v___x_4397_);
v___x_4399_ = v___x_4387_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4397_);
lean_ctor_set(v_reuseFailAlloc_4400_, 1, v_b_4381_);
lean_ctor_set(v_reuseFailAlloc_4400_, 2, v_tail_4385_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg___boxed(lean_object* v_a_4402_, lean_object* v_b_4403_, lean_object* v_x_4404_){
_start:
{
uint8_t v_a_boxed_4405_; lean_object* v_res_4406_; 
v_a_boxed_4405_ = lean_unbox(v_a_4402_);
v_res_4406_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_boxed_4405_, v_b_4403_, v_x_4404_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_4407_, lean_object* v_x_4408_){
_start:
{
if (lean_obj_tag(v_x_4408_) == 0)
{
return v_x_4407_;
}
else
{
lean_object* v_key_4409_; lean_object* v_value_4410_; lean_object* v_tail_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4435_; 
v_key_4409_ = lean_ctor_get(v_x_4408_, 0);
v_value_4410_ = lean_ctor_get(v_x_4408_, 1);
v_tail_4411_ = lean_ctor_get(v_x_4408_, 2);
v_isSharedCheck_4435_ = !lean_is_exclusive(v_x_4408_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4413_ = v_x_4408_;
v_isShared_4414_ = v_isSharedCheck_4435_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_tail_4411_);
lean_inc(v_value_4410_);
lean_inc(v_key_4409_);
lean_dec(v_x_4408_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4435_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4415_; uint8_t v___x_4416_; uint64_t v___x_4417_; uint64_t v___x_4418_; uint64_t v___x_4419_; uint64_t v_fold_4420_; uint64_t v___x_4421_; uint64_t v___x_4422_; uint64_t v___x_4423_; size_t v___x_4424_; size_t v___x_4425_; size_t v___x_4426_; size_t v___x_4427_; size_t v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4431_; 
v___x_4415_ = lean_array_get_size(v_x_4407_);
v___x_4416_ = lean_unbox(v_key_4409_);
v___x_4417_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v___x_4416_);
v___x_4418_ = 32ULL;
v___x_4419_ = lean_uint64_shift_right(v___x_4417_, v___x_4418_);
v_fold_4420_ = lean_uint64_xor(v___x_4417_, v___x_4419_);
v___x_4421_ = 16ULL;
v___x_4422_ = lean_uint64_shift_right(v_fold_4420_, v___x_4421_);
v___x_4423_ = lean_uint64_xor(v_fold_4420_, v___x_4422_);
v___x_4424_ = lean_uint64_to_usize(v___x_4423_);
v___x_4425_ = lean_usize_of_nat(v___x_4415_);
v___x_4426_ = ((size_t)1ULL);
v___x_4427_ = lean_usize_sub(v___x_4425_, v___x_4426_);
v___x_4428_ = lean_usize_land(v___x_4424_, v___x_4427_);
v___x_4429_ = lean_array_uget_borrowed(v_x_4407_, v___x_4428_);
lean_inc(v___x_4429_);
if (v_isShared_4414_ == 0)
{
lean_ctor_set(v___x_4413_, 2, v___x_4429_);
v___x_4431_ = v___x_4413_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_key_4409_);
lean_ctor_set(v_reuseFailAlloc_4434_, 1, v_value_4410_);
lean_ctor_set(v_reuseFailAlloc_4434_, 2, v___x_4429_);
v___x_4431_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
lean_object* v___x_4432_; 
v___x_4432_ = lean_array_uset(v_x_4407_, v___x_4428_, v___x_4431_);
v_x_4407_ = v___x_4432_;
v_x_4408_ = v_tail_4411_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2___redArg(lean_object* v_i_4436_, lean_object* v_source_4437_, lean_object* v_target_4438_){
_start:
{
lean_object* v___x_4439_; uint8_t v___x_4440_; 
v___x_4439_ = lean_array_get_size(v_source_4437_);
v___x_4440_ = lean_nat_dec_lt(v_i_4436_, v___x_4439_);
if (v___x_4440_ == 0)
{
lean_dec_ref(v_source_4437_);
lean_dec(v_i_4436_);
return v_target_4438_;
}
else
{
lean_object* v_es_4441_; lean_object* v___x_4442_; lean_object* v_source_4443_; lean_object* v_target_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v_es_4441_ = lean_array_fget(v_source_4437_, v_i_4436_);
v___x_4442_ = lean_box(0);
v_source_4443_ = lean_array_fset(v_source_4437_, v_i_4436_, v___x_4442_);
v_target_4444_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4___redArg(v_target_4438_, v_es_4441_);
v___x_4445_ = lean_unsigned_to_nat(1u);
v___x_4446_ = lean_nat_add(v_i_4436_, v___x_4445_);
lean_dec(v_i_4436_);
v_i_4436_ = v___x_4446_;
v_source_4437_ = v_source_4443_;
v_target_4438_ = v_target_4444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1___redArg(lean_object* v_data_4448_){
_start:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v_nbuckets_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4449_ = lean_array_get_size(v_data_4448_);
v___x_4450_ = lean_unsigned_to_nat(2u);
v_nbuckets_4451_ = lean_nat_mul(v___x_4449_, v___x_4450_);
v___x_4452_ = lean_unsigned_to_nat(0u);
v___x_4453_ = lean_box(0);
v___x_4454_ = lean_mk_array(v_nbuckets_4451_, v___x_4453_);
v___x_4455_ = lean_array_propagate_mark(v_data_4448_, v___x_4454_);
v___x_4456_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2___redArg(v___x_4452_, v_data_4448_, v___x_4455_);
return v___x_4456_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(uint8_t v_a_4457_, lean_object* v_x_4458_){
_start:
{
if (lean_obj_tag(v_x_4458_) == 0)
{
uint8_t v___x_4459_; 
v___x_4459_ = 0;
return v___x_4459_;
}
else
{
lean_object* v_key_4460_; lean_object* v_tail_4461_; uint8_t v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; uint8_t v___x_4465_; 
v_key_4460_ = lean_ctor_get(v_x_4458_, 0);
v_tail_4461_ = lean_ctor_get(v_x_4458_, 2);
v___x_4462_ = lean_unbox(v_key_4460_);
v___x_4463_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v___x_4462_);
v___x_4464_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v_a_4457_);
v___x_4465_ = lean_nat_dec_eq(v___x_4463_, v___x_4464_);
lean_dec(v___x_4464_);
lean_dec(v___x_4463_);
if (v___x_4465_ == 0)
{
v_x_4458_ = v_tail_4461_;
goto _start;
}
else
{
return v___x_4465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg___boxed(lean_object* v_a_4467_, lean_object* v_x_4468_){
_start:
{
uint8_t v_a_boxed_4469_; uint8_t v_res_4470_; lean_object* v_r_4471_; 
v_a_boxed_4469_ = lean_unbox(v_a_4467_);
v_res_4470_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_boxed_4469_, v_x_4468_);
lean_dec(v_x_4468_);
v_r_4471_ = lean_box(v_res_4470_);
return v_r_4471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(lean_object* v_m_4472_, uint8_t v_a_4473_, lean_object* v_b_4474_){
_start:
{
lean_object* v_size_4475_; lean_object* v_buckets_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4520_; 
v_size_4475_ = lean_ctor_get(v_m_4472_, 0);
v_buckets_4476_ = lean_ctor_get(v_m_4472_, 1);
v_isSharedCheck_4520_ = !lean_is_exclusive(v_m_4472_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4478_ = v_m_4472_;
v_isShared_4479_ = v_isSharedCheck_4520_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_buckets_4476_);
lean_inc(v_size_4475_);
lean_dec(v_m_4472_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4520_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4480_; uint64_t v___x_4481_; uint64_t v___x_4482_; uint64_t v___x_4483_; uint64_t v_fold_4484_; uint64_t v___x_4485_; uint64_t v___x_4486_; uint64_t v___x_4487_; size_t v___x_4488_; size_t v___x_4489_; size_t v___x_4490_; size_t v___x_4491_; size_t v___x_4492_; lean_object* v_bkt_4493_; uint8_t v___x_4494_; 
v___x_4480_ = lean_array_get_size(v_buckets_4476_);
v___x_4481_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_a_4473_);
v___x_4482_ = 32ULL;
v___x_4483_ = lean_uint64_shift_right(v___x_4481_, v___x_4482_);
v_fold_4484_ = lean_uint64_xor(v___x_4481_, v___x_4483_);
v___x_4485_ = 16ULL;
v___x_4486_ = lean_uint64_shift_right(v_fold_4484_, v___x_4485_);
v___x_4487_ = lean_uint64_xor(v_fold_4484_, v___x_4486_);
v___x_4488_ = lean_uint64_to_usize(v___x_4487_);
v___x_4489_ = lean_usize_of_nat(v___x_4480_);
v___x_4490_ = ((size_t)1ULL);
v___x_4491_ = lean_usize_sub(v___x_4489_, v___x_4490_);
v___x_4492_ = lean_usize_land(v___x_4488_, v___x_4491_);
v_bkt_4493_ = lean_array_uget_borrowed(v_buckets_4476_, v___x_4492_);
v___x_4494_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_4473_, v_bkt_4493_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4495_; lean_object* v_size_x27_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v_buckets_x27_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4495_ = lean_unsigned_to_nat(1u);
v_size_x27_4496_ = lean_nat_add(v_size_4475_, v___x_4495_);
lean_dec(v_size_4475_);
v___x_4497_ = lean_box(v_a_4473_);
lean_inc(v_bkt_4493_);
v___x_4498_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
lean_ctor_set(v___x_4498_, 1, v_b_4474_);
lean_ctor_set(v___x_4498_, 2, v_bkt_4493_);
v_buckets_x27_4499_ = lean_array_uset(v_buckets_4476_, v___x_4492_, v___x_4498_);
v___x_4500_ = lean_unsigned_to_nat(4u);
v___x_4501_ = lean_nat_mul(v_size_x27_4496_, v___x_4500_);
v___x_4502_ = lean_unsigned_to_nat(3u);
v___x_4503_ = lean_nat_div(v___x_4501_, v___x_4502_);
lean_dec(v___x_4501_);
v___x_4504_ = lean_array_get_size(v_buckets_x27_4499_);
v___x_4505_ = lean_nat_dec_le(v___x_4503_, v___x_4504_);
lean_dec(v___x_4503_);
if (v___x_4505_ == 0)
{
lean_object* v_val_4506_; lean_object* v___x_4508_; 
v_val_4506_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1___redArg(v_buckets_x27_4499_);
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 1, v_val_4506_);
lean_ctor_set(v___x_4478_, 0, v_size_x27_4496_);
v___x_4508_ = v___x_4478_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_size_x27_4496_);
lean_ctor_set(v_reuseFailAlloc_4509_, 1, v_val_4506_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
}
}
else
{
lean_object* v___x_4511_; 
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 1, v_buckets_x27_4499_);
lean_ctor_set(v___x_4478_, 0, v_size_x27_4496_);
v___x_4511_ = v___x_4478_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_size_x27_4496_);
lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_buckets_x27_4499_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
else
{
lean_object* v___x_4513_; lean_object* v_buckets_x27_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4518_; 
lean_inc(v_bkt_4493_);
v___x_4513_ = lean_box(0);
v_buckets_x27_4514_ = lean_array_uset(v_buckets_4476_, v___x_4492_, v___x_4513_);
v___x_4515_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_4473_, v_b_4474_, v_bkt_4493_);
v___x_4516_ = lean_array_uset(v_buckets_x27_4514_, v___x_4492_, v___x_4515_);
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 1, v___x_4516_);
v___x_4518_ = v___x_4478_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_size_4475_);
lean_ctor_set(v_reuseFailAlloc_4519_, 1, v___x_4516_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg___boxed(lean_object* v_m_4521_, lean_object* v_a_4522_, lean_object* v_b_4523_){
_start:
{
uint8_t v_a_boxed_4524_; lean_object* v_res_4525_; 
v_a_boxed_4524_ = lean_unbox(v_a_4522_);
v_res_4525_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(v_m_4521_, v_a_boxed_4524_, v_b_4523_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(lean_object* v_cmd_4529_, lean_object* v_as_4530_, size_t v_sz_4531_, size_t v_i_4532_, lean_object* v_b_4533_){
_start:
{
lean_object* v_a_4536_; uint8_t v___x_4540_; 
v___x_4540_ = lean_usize_dec_lt(v_i_4532_, v_sz_4531_);
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; 
v___x_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4541_, 0, v_b_4533_);
return v___x_4541_;
}
else
{
lean_object* v_a_4542_; lean_object* v_snd_4543_; lean_object* v_fst_4544_; lean_object* v_fst_4545_; lean_object* v_snd_4546_; lean_object* v_snd_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4645_; 
v_a_4542_ = lean_array_uget_borrowed(v_as_4530_, v_i_4532_);
v_snd_4543_ = lean_ctor_get(v_a_4542_, 1);
v_fst_4544_ = lean_ctor_get(v_a_4542_, 0);
v_fst_4545_ = lean_ctor_get(v_snd_4543_, 0);
v_snd_4546_ = lean_ctor_get(v_snd_4543_, 1);
lean_inc(v_snd_4546_);
v_snd_4547_ = lean_ctor_get(v_b_4533_, 1);
v_isSharedCheck_4645_ = !lean_is_exclusive(v_b_4533_);
if (v_isSharedCheck_4645_ == 0)
{
lean_object* v_unused_4646_; 
v_unused_4646_ = lean_ctor_get(v_b_4533_, 0);
lean_dec(v_unused_4646_);
v___x_4549_ = v_b_4533_;
v_isShared_4550_ = v_isSharedCheck_4645_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_snd_4547_);
lean_dec(v_b_4533_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4645_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4551_; 
v___x_4551_ = lean_box(0);
if (lean_obj_tag(v_snd_4546_) == 1)
{
lean_object* v_val_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4641_; 
v_val_4552_ = lean_ctor_get(v_snd_4546_, 0);
v_isSharedCheck_4641_ = !lean_is_exclusive(v_snd_4546_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4554_ = v_snd_4546_;
v_isShared_4555_ = v_isSharedCheck_4641_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_val_4552_);
lean_dec(v_snd_4546_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4641_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
uint8_t v___x_4556_; 
v___x_4556_ = l_System_FilePath_pathExists(v_val_4552_);
if (v___x_4556_ == 0)
{
lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4557_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4558_ = lean_string_append(v___x_4557_, v_cmd_4529_);
v___x_4559_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
v___x_4560_ = lean_string_append(v___x_4558_, v___x_4559_);
v___x_4561_ = lean_string_append(v___x_4560_, v_fst_4544_);
v___x_4562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__0));
v___x_4563_ = lean_string_append(v___x_4561_, v___x_4562_);
v___x_4564_ = lean_string_append(v___x_4563_, v_val_4552_);
lean_dec(v_val_4552_);
v___x_4565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__1));
v___x_4566_ = lean_string_append(v___x_4564_, v___x_4565_);
v___x_4567_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4566_);
lean_dec_ref(v___x_4566_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4582_; 
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4570_ = v___x_4567_;
v_isShared_4571_ = v_isSharedCheck_4582_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4567_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4582_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4572_; lean_object* v___x_4574_; 
v___x_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4572_, 0, v_a_4568_);
if (v_isShared_4555_ == 0)
{
lean_ctor_set(v___x_4554_, 0, v___x_4572_);
v___x_4574_ = v___x_4554_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4572_);
v___x_4574_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
lean_object* v___x_4576_; 
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 0, v___x_4574_);
v___x_4576_ = v___x_4549_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v___x_4574_);
lean_ctor_set(v_reuseFailAlloc_4580_, 1, v_snd_4547_);
v___x_4576_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
lean_object* v___x_4578_; 
if (v_isShared_4571_ == 0)
{
lean_ctor_set(v___x_4570_, 0, v___x_4576_);
v___x_4578_ = v___x_4570_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v___x_4576_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
}
}
}
else
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
lean_del_object(v___x_4554_);
lean_del_object(v___x_4549_);
lean_dec(v_snd_4547_);
v_a_4583_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v___x_4567_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4567_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
else
{
uint8_t v___x_4591_; 
v___x_4591_ = l_System_FilePath_isDir(v_val_4552_);
if (v___x_4591_ == 0)
{
lean_object* v___x_4592_; 
lean_del_object(v___x_4554_);
v___x_4592_ = lean_io_realpath(v_val_4552_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_object* v_a_4593_; uint8_t v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4597_; 
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_a_4593_);
lean_dec_ref_known(v___x_4592_, 1);
v___x_4594_ = lean_unbox(v_fst_4545_);
v___x_4595_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(v_snd_4547_, v___x_4594_, v_a_4593_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 1, v___x_4595_);
lean_ctor_set(v___x_4549_, 0, v___x_4551_);
v___x_4597_ = v___x_4549_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4551_);
lean_ctor_set(v_reuseFailAlloc_4598_, 1, v___x_4595_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
v_a_4536_ = v___x_4597_;
goto v___jp_4535_;
}
}
else
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4606_; 
lean_del_object(v___x_4549_);
lean_dec(v_snd_4547_);
v_a_4599_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4601_ = v___x_4592_;
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4592_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4604_; 
if (v_isShared_4602_ == 0)
{
v___x_4604_ = v___x_4601_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4599_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
}
else
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4607_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4608_ = lean_string_append(v___x_4607_, v_cmd_4529_);
v___x_4609_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
v___x_4610_ = lean_string_append(v___x_4608_, v___x_4609_);
v___x_4611_ = lean_string_append(v___x_4610_, v_fst_4544_);
v___x_4612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__0));
v___x_4613_ = lean_string_append(v___x_4611_, v___x_4612_);
v___x_4614_ = lean_string_append(v___x_4613_, v_val_4552_);
lean_dec(v_val_4552_);
v___x_4615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__2));
v___x_4616_ = lean_string_append(v___x_4614_, v___x_4615_);
v___x_4617_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4616_);
lean_dec_ref(v___x_4616_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4632_; 
v_a_4618_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4620_ = v___x_4617_;
v_isShared_4621_ = v_isSharedCheck_4632_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4617_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4632_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4622_; lean_object* v___x_4624_; 
v___x_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4622_, 0, v_a_4618_);
if (v_isShared_4555_ == 0)
{
lean_ctor_set(v___x_4554_, 0, v___x_4622_);
v___x_4624_ = v___x_4554_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4622_);
v___x_4624_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
lean_object* v___x_4626_; 
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 0, v___x_4624_);
v___x_4626_ = v___x_4549_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4624_);
lean_ctor_set(v_reuseFailAlloc_4630_, 1, v_snd_4547_);
v___x_4626_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
lean_object* v___x_4628_; 
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 0, v___x_4626_);
v___x_4628_ = v___x_4620_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4626_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4640_; 
lean_del_object(v___x_4554_);
lean_del_object(v___x_4549_);
lean_dec(v_snd_4547_);
v_a_4633_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4635_ = v___x_4617_;
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_a_4633_);
lean_dec(v___x_4617_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4638_; 
if (v_isShared_4636_ == 0)
{
v___x_4638_ = v___x_4635_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4643_; 
lean_dec(v_snd_4546_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 0, v___x_4551_);
v___x_4643_ = v___x_4549_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4551_);
lean_ctor_set(v_reuseFailAlloc_4644_, 1, v_snd_4547_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
v_a_4536_ = v___x_4643_;
goto v___jp_4535_;
}
}
}
}
v___jp_4535_:
{
size_t v___x_4537_; size_t v___x_4538_; 
v___x_4537_ = ((size_t)1ULL);
v___x_4538_ = lean_usize_add(v_i_4532_, v___x_4537_);
v_i_4532_ = v___x_4538_;
v_b_4533_ = v_a_4536_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___boxed(lean_object* v_cmd_4647_, lean_object* v_as_4648_, lean_object* v_sz_4649_, lean_object* v_i_4650_, lean_object* v_b_4651_, lean_object* v___y_4652_){
_start:
{
size_t v_sz_boxed_4653_; size_t v_i_boxed_4654_; lean_object* v_res_4655_; 
v_sz_boxed_4653_ = lean_unbox_usize(v_sz_4649_);
lean_dec(v_sz_4649_);
v_i_boxed_4654_ = lean_unbox_usize(v_i_4650_);
lean_dec(v_i_4650_);
v_res_4655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(v_cmd_4647_, v_as_4648_, v_sz_boxed_4653_, v_i_boxed_4654_, v_b_4651_);
lean_dec_ref(v_as_4648_);
lean_dec_ref(v_cmd_4647_);
return v_res_4655_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0(void){
_start:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4656_ = lean_box(0);
v___x_4657_ = lean_unsigned_to_nat(16u);
v___x_4658_ = lean_mk_array(v___x_4657_, v___x_4656_);
return v___x_4658_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1(void){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v_store_4661_; 
v___x_4659_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0, &l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0);
v___x_4660_ = lean_unsigned_to_nat(0u);
v_store_4661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_store_4661_, 0, v___x_4660_);
lean_ctor_set(v_store_4661_, 1, v___x_4659_);
return v_store_4661_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2(void){
_start:
{
lean_object* v_store_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v_store_4662_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1, &l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1);
v___x_4663_ = lean_box(0);
v___x_4664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4663_);
lean_ctor_set(v___x_4664_, 1, v_store_4662_);
return v___x_4664_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(lean_object* v_cmd_4665_, lean_object* v_entries_4666_){
_start:
{
lean_object* v___x_4668_; size_t v_sz_4669_; size_t v___x_4670_; lean_object* v___x_4671_; 
v___x_4668_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2);
v_sz_4669_ = lean_array_size(v_entries_4666_);
v___x_4670_ = ((size_t)0ULL);
v___x_4671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(v_cmd_4665_, v_entries_4666_, v_sz_4669_, v___x_4670_, v___x_4668_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4686_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4674_ = v___x_4671_;
v_isShared_4675_ = v_isSharedCheck_4686_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4671_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4686_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v_fst_4676_; 
v_fst_4676_ = lean_ctor_get(v_a_4672_, 0);
if (lean_obj_tag(v_fst_4676_) == 0)
{
lean_object* v_snd_4677_; lean_object* v___x_4678_; lean_object* v___x_4680_; 
v_snd_4677_ = lean_ctor_get(v_a_4672_, 1);
lean_inc(v_snd_4677_);
lean_dec(v_a_4672_);
v___x_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4678_, 0, v_snd_4677_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 0, v___x_4678_);
v___x_4680_ = v___x_4674_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v___x_4678_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
else
{
lean_object* v_val_4682_; lean_object* v___x_4684_; 
lean_inc_ref(v_fst_4676_);
lean_dec(v_a_4672_);
v_val_4682_ = lean_ctor_get(v_fst_4676_, 0);
lean_inc(v_val_4682_);
lean_dec_ref_known(v_fst_4676_, 1);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 0, v_val_4682_);
v___x_4684_ = v___x_4674_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_val_4682_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
v_a_4687_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4671_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4671_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___boxed(lean_object* v_cmd_4695_, lean_object* v_entries_4696_, lean_object* v_a_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(v_cmd_4695_, v_entries_4696_);
lean_dec_ref(v_entries_4696_);
lean_dec_ref(v_cmd_4695_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0(lean_object* v_00_u03b2_4699_, lean_object* v_m_4700_, uint8_t v_a_4701_, lean_object* v_b_4702_){
_start:
{
lean_object* v___x_4703_; 
v___x_4703_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(v_m_4700_, v_a_4701_, v_b_4702_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___boxed(lean_object* v_00_u03b2_4704_, lean_object* v_m_4705_, lean_object* v_a_4706_, lean_object* v_b_4707_){
_start:
{
uint8_t v_a_boxed_4708_; lean_object* v_res_4709_; 
v_a_boxed_4708_ = lean_unbox(v_a_4706_);
v_res_4709_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0(v_00_u03b2_4704_, v_m_4705_, v_a_boxed_4708_, v_b_4707_);
return v_res_4709_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0(lean_object* v_00_u03b2_4710_, uint8_t v_a_4711_, lean_object* v_x_4712_){
_start:
{
uint8_t v___x_4713_; 
v___x_4713_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_4711_, v_x_4712_);
return v___x_4713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4714_, lean_object* v_a_4715_, lean_object* v_x_4716_){
_start:
{
uint8_t v_a_boxed_4717_; uint8_t v_res_4718_; lean_object* v_r_4719_; 
v_a_boxed_4717_ = lean_unbox(v_a_4715_);
v_res_4718_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0(v_00_u03b2_4714_, v_a_boxed_4717_, v_x_4716_);
lean_dec(v_x_4716_);
v_r_4719_ = lean_box(v_res_4718_);
return v_r_4719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1(lean_object* v_00_u03b2_4720_, lean_object* v_data_4721_){
_start:
{
lean_object* v___x_4722_; 
v___x_4722_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1___redArg(v_data_4721_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2(lean_object* v_00_u03b2_4723_, uint8_t v_a_4724_, lean_object* v_b_4725_, lean_object* v_x_4726_){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_4724_, v_b_4725_, v_x_4726_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4728_, lean_object* v_a_4729_, lean_object* v_b_4730_, lean_object* v_x_4731_){
_start:
{
uint8_t v_a_boxed_4732_; lean_object* v_res_4733_; 
v_a_boxed_4732_ = lean_unbox(v_a_4729_);
v_res_4733_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2(v_00_u03b2_4728_, v_a_boxed_4732_, v_b_4730_, v_x_4731_);
return v_res_4733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4734_, lean_object* v_i_4735_, lean_object* v_source_4736_, lean_object* v_target_4737_){
_start:
{
lean_object* v___x_4738_; 
v___x_4738_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2___redArg(v_i_4735_, v_source_4736_, v_target_4737_);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4739_, lean_object* v_x_4740_, lean_object* v_x_4741_){
_start:
{
lean_object* v___x_4742_; 
v___x_4742_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4___redArg(v_x_4740_, v_x_4741_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext(lean_object* v_cmd_4754_, uint8_t v_paranoid_4755_, uint8_t v_inadvisablyNoSandbox_4756_, lean_object* v_lean_4757_, lean_object* v_lake_4758_, lean_object* v_projectDir_4759_, lean_object* v_moduleStore_4760_){
_start:
{
lean_object* v___y_4763_; lean_object* v___y_4764_; lean_object* v___y_4765_; lean_object* v___y_4766_; lean_object* v___y_4767_; lean_object* v___y_4768_; lean_object* v_whichSandbox_4795_; 
if (v_inadvisablyNoSandbox_4756_ == 0)
{
uint8_t v___x_4871_; 
v___x_4871_ = l_System_Platform_isLinux;
if (v___x_4871_ == 0)
{
lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; 
lean_dec_ref(v_moduleStore_4760_);
lean_dec_ref(v_projectDir_4759_);
lean_dec_ref(v_lean_4757_);
v___x_4872_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4873_ = lean_string_append(v___x_4872_, v_cmd_4754_);
v___x_4874_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6));
v___x_4875_ = lean_string_append(v___x_4873_, v___x_4874_);
v___x_4876_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4875_);
lean_dec_ref(v___x_4875_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4885_; 
v_a_4877_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4879_ = v___x_4876_;
v_isShared_4880_ = v_isSharedCheck_4885_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4876_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4885_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4881_; lean_object* v___x_4883_; 
v___x_4881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4881_, 0, v_a_4877_);
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 0, v___x_4881_);
v___x_4883_ = v___x_4879_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4881_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
else
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4893_; 
v_a_4886_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4888_ = v___x_4876_;
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4876_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4891_; 
if (v_isShared_4889_ == 0)
{
v___x_4891_ = v___x_4888_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_a_4886_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
else
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___y_4897_; 
v___x_4894_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7));
v___x_4895_ = lean_io_getenv(v___x_4894_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v___x_4933_; 
v___x_4933_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__8));
v___y_4897_ = v___x_4933_;
goto v___jp_4896_;
}
else
{
lean_object* v_val_4934_; 
v_val_4934_ = lean_ctor_get(v___x_4895_, 0);
lean_inc(v_val_4934_);
lean_dec_ref_known(v___x_4895_, 1);
v___y_4897_ = v_val_4934_;
goto v___jp_4896_;
}
v___jp_4896_:
{
lean_object* v___x_4898_; lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4932_; 
lean_inc_ref(v___y_4897_);
v___x_4898_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___y_4897_);
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4901_ = v___x_4898_;
v_isShared_4902_ = v_isSharedCheck_4932_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4898_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4932_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
if (lean_obj_tag(v_a_4899_) == 1)
{
lean_object* v_val_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4910_; 
lean_del_object(v___x_4901_);
lean_dec_ref(v___y_4897_);
v_val_4903_ = lean_ctor_get(v_a_4899_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v_a_4899_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4905_ = v_a_4899_;
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_val_4903_);
lean_dec(v_a_4899_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4908_; 
if (v_isShared_4906_ == 0)
{
v___x_4908_ = v___x_4905_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_val_4903_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
v_whichSandbox_4795_ = v___x_4908_;
goto v___jp_4794_;
}
}
}
else
{
lean_object* v___x_4911_; lean_object* v___x_4912_; 
lean_dec(v_a_4899_);
lean_dec_ref(v_moduleStore_4760_);
lean_dec_ref(v_projectDir_4759_);
lean_dec_ref(v_lean_4757_);
v___x_4911_ = l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError(v_cmd_4754_, v___y_4897_);
lean_dec_ref(v___y_4897_);
v___x_4912_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4911_);
lean_dec_ref(v___x_4911_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4923_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4915_ = v___x_4912_;
v_isShared_4916_ = v_isSharedCheck_4923_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4912_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4923_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 0, v_a_4913_);
v___x_4918_ = v___x_4901_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4913_);
v___x_4918_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
lean_object* v___x_4920_; 
if (v_isShared_4916_ == 0)
{
lean_ctor_set(v___x_4915_, 0, v___x_4918_);
v___x_4920_ = v___x_4915_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4918_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
else
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4931_; 
lean_del_object(v___x_4901_);
v_a_4924_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4926_ = v___x_4912_;
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___x_4912_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4929_; 
if (v_isShared_4927_ == 0)
{
v___x_4929_ = v___x_4926_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v_a_4924_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
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
lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4935_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__9));
v___x_4936_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_4935_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v___x_4937_; 
lean_dec_ref_known(v___x_4936_, 1);
v___x_4937_ = lean_box(0);
v_whichSandbox_4795_ = v___x_4937_;
goto v___jp_4794_;
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
lean_dec_ref(v_moduleStore_4760_);
lean_dec_ref(v_projectDir_4759_);
lean_dec_ref(v_lean_4757_);
v_a_4938_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4936_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4936_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
v___jp_4762_:
{
lean_object* v___x_4769_; 
v___x_4769_ = lean_io_realpath(v_projectDir_4759_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4785_; 
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4772_ = v___x_4769_;
v_isShared_4773_ = v_isSharedCheck_4785_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4769_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4785_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v_home_4774_; lean_object* v_lake_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4783_; 
v_home_4774_ = lean_ctor_get(v_lake_4758_, 0);
v_lake_4775_ = lean_ctor_get(v_lake_4758_, 5);
v___x_4776_ = lean_box(0);
v___x_4777_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_4778_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
v___x_4779_ = lean_box(1);
lean_inc_ref(v_home_4774_);
lean_inc_ref(v_lake_4775_);
v___x_4780_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_4780_, 0, v_a_4770_);
lean_ctor_set(v___x_4780_, 1, v___x_4776_);
lean_ctor_set(v___x_4780_, 2, v___x_4776_);
lean_ctor_set(v___x_4780_, 3, v___x_4777_);
lean_ctor_set(v___x_4780_, 4, v___x_4777_);
lean_ctor_set(v___x_4780_, 5, v___x_4777_);
lean_ctor_set(v___x_4780_, 6, v___y_4766_);
lean_ctor_set(v___x_4780_, 7, v___x_4778_);
lean_ctor_set(v___x_4780_, 8, v___x_4778_);
lean_ctor_set(v___x_4780_, 9, v___y_4763_);
lean_ctor_set(v___x_4780_, 10, v_lake_4775_);
lean_ctor_set(v___x_4780_, 11, v_home_4774_);
lean_ctor_set(v___x_4780_, 12, v___y_4767_);
lean_ctor_set(v___x_4780_, 13, v___y_4764_);
lean_ctor_set(v___x_4780_, 14, v___y_4765_);
lean_ctor_set(v___x_4780_, 15, v___x_4779_);
lean_ctor_set(v___x_4780_, 16, v___y_4768_);
lean_ctor_set(v___x_4780_, 17, v_moduleStore_4760_);
v___x_4781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4781_, 0, v___x_4780_);
if (v_isShared_4773_ == 0)
{
lean_ctor_set(v___x_4772_, 0, v___x_4781_);
v___x_4783_ = v___x_4772_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___x_4781_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
else
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4793_; 
lean_dec_ref(v___y_4768_);
lean_dec_ref(v___y_4767_);
lean_dec_ref(v___y_4766_);
lean_dec_ref(v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec(v___y_4763_);
lean_dec_ref(v_moduleStore_4760_);
v_a_4786_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4788_ = v___x_4769_;
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4769_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4791_; 
if (v_isShared_4789_ == 0)
{
v___x_4791_ = v___x_4788_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_a_4786_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
v___jp_4794_:
{
lean_object* v_sysroot_4796_; lean_object* v_binDir_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v_whichLean4Export_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v_whichLeanChecker_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4870_; 
v_sysroot_4796_ = lean_ctor_get(v_lean_4757_, 0);
lean_inc_ref(v_sysroot_4796_);
v_binDir_4797_ = lean_ctor_get(v_lean_4757_, 6);
v___x_4798_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0));
lean_inc_ref_n(v_binDir_4797_, 2);
v___x_4799_ = l_System_FilePath_join(v_binDir_4797_, v___x_4798_);
v___x_4800_ = l_System_FilePath_exeExtension;
v_whichLean4Export_4801_ = l_System_FilePath_addExtension(v___x_4799_, v___x_4800_);
v___x_4802_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1));
v___x_4803_ = l_System_FilePath_join(v_binDir_4797_, v___x_4802_);
v_whichLeanChecker_4804_ = l_System_FilePath_addExtension(v___x_4803_, v___x_4800_);
v___x_4805_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2));
v___x_4806_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4805_);
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4809_ = v___x_4806_;
v_isShared_4810_ = v_isSharedCheck_4870_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4806_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4870_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
if (lean_obj_tag(v_a_4807_) == 1)
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4845_; 
lean_dec_ref_known(v_a_4807_, 1);
lean_del_object(v___x_4809_);
v___x_4811_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__4));
v___x_4812_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4811_);
v_a_4813_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4815_ = v___x_4812_;
v_isShared_4816_ = v_isSharedCheck_4845_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4812_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4845_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
if (lean_obj_tag(v_a_4813_) == 1)
{
lean_del_object(v___x_4815_);
if (v_paranoid_4755_ == 0)
{
lean_object* v_val_4817_; lean_object* v___x_4818_; 
lean_dec_ref(v_lean_4757_);
v_val_4817_ = lean_ctor_get(v_a_4813_, 0);
lean_inc(v_val_4817_);
lean_dec_ref_known(v_a_4813_, 1);
v___x_4818_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3));
v___y_4763_ = v_whichSandbox_4795_;
v___y_4764_ = v_whichLeanChecker_4804_;
v___y_4765_ = v_val_4817_;
v___y_4766_ = v_sysroot_4796_;
v___y_4767_ = v_whichLean4Export_4801_;
v___y_4768_ = v___x_4818_;
goto v___jp_4762_;
}
else
{
lean_object* v_val_4819_; lean_object* v___x_4820_; 
v_val_4819_ = lean_ctor_get(v_a_4813_, 0);
lean_inc(v_val_4819_);
lean_dec_ref_known(v_a_4813_, 1);
v___x_4820_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels(v_lean_4757_);
v___y_4763_ = v_whichSandbox_4795_;
v___y_4764_ = v_whichLeanChecker_4804_;
v___y_4765_ = v_val_4819_;
v___y_4766_ = v_sysroot_4796_;
v___y_4767_ = v_whichLean4Export_4801_;
v___y_4768_ = v___x_4820_;
goto v___jp_4762_;
}
}
else
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
lean_dec(v_a_4813_);
lean_dec_ref(v_whichLeanChecker_4804_);
lean_dec_ref(v_whichLean4Export_4801_);
lean_dec_ref(v_sysroot_4796_);
lean_dec(v_whichSandbox_4795_);
lean_dec_ref(v_moduleStore_4760_);
lean_dec_ref(v_projectDir_4759_);
lean_dec_ref(v_lean_4757_);
v___x_4821_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4822_ = lean_string_append(v___x_4821_, v_cmd_4754_);
v___x_4823_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4));
v___x_4824_ = lean_string_append(v___x_4822_, v___x_4823_);
v___x_4825_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4824_);
lean_dec_ref(v___x_4824_);
if (lean_obj_tag(v___x_4825_) == 0)
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4836_; 
v_a_4826_ = lean_ctor_get(v___x_4825_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4825_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4828_ = v___x_4825_;
v_isShared_4829_ = v_isSharedCheck_4836_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___x_4825_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4836_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 0, v_a_4826_);
v___x_4831_ = v___x_4815_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4826_);
v___x_4831_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
lean_object* v___x_4833_; 
if (v_isShared_4829_ == 0)
{
lean_ctor_set(v___x_4828_, 0, v___x_4831_);
v___x_4833_ = v___x_4828_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v___x_4831_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
else
{
lean_object* v_a_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4844_; 
lean_del_object(v___x_4815_);
v_a_4837_ = lean_ctor_get(v___x_4825_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4825_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4839_ = v___x_4825_;
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_a_4837_);
lean_dec(v___x_4825_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4842_; 
if (v_isShared_4840_ == 0)
{
v___x_4842_ = v___x_4839_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_a_4837_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
}
}
}
}
else
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
lean_dec(v_a_4807_);
lean_dec_ref(v_whichLeanChecker_4804_);
lean_dec_ref(v_whichLean4Export_4801_);
lean_dec_ref(v_sysroot_4796_);
lean_dec(v_whichSandbox_4795_);
lean_dec_ref(v_moduleStore_4760_);
lean_dec_ref(v_projectDir_4759_);
lean_dec_ref(v_lean_4757_);
v___x_4846_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4847_ = lean_string_append(v___x_4846_, v_cmd_4754_);
v___x_4848_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5));
v___x_4849_ = lean_string_append(v___x_4847_, v___x_4848_);
v___x_4850_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4849_);
lean_dec_ref(v___x_4849_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4861_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4853_ = v___x_4850_;
v_isShared_4854_ = v_isSharedCheck_4861_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_a_4851_);
lean_dec(v___x_4850_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4861_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4856_; 
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v_a_4851_);
v___x_4856_ = v___x_4809_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4851_);
v___x_4856_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
lean_object* v___x_4858_; 
if (v_isShared_4854_ == 0)
{
lean_ctor_set(v___x_4853_, 0, v___x_4856_);
v___x_4858_ = v___x_4853_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4856_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
else
{
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4869_; 
lean_del_object(v___x_4809_);
v_a_4862_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4864_ = v___x_4850_;
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v___x_4850_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4867_; 
if (v_isShared_4865_ == 0)
{
v___x_4867_ = v___x_4864_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_a_4862_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___boxed(lean_object* v_cmd_4946_, lean_object* v_paranoid_4947_, lean_object* v_inadvisablyNoSandbox_4948_, lean_object* v_lean_4949_, lean_object* v_lake_4950_, lean_object* v_projectDir_4951_, lean_object* v_moduleStore_4952_, lean_object* v_a_4953_){
_start:
{
uint8_t v_paranoid_boxed_4954_; uint8_t v_inadvisablyNoSandbox_boxed_4955_; lean_object* v_res_4956_; 
v_paranoid_boxed_4954_ = lean_unbox(v_paranoid_4947_);
v_inadvisablyNoSandbox_boxed_4955_ = lean_unbox(v_inadvisablyNoSandbox_4948_);
v_res_4956_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v_cmd_4946_, v_paranoid_boxed_4954_, v_inadvisablyNoSandbox_boxed_4955_, v_lean_4949_, v_lake_4950_, v_projectDir_4951_, v_moduleStore_4952_);
lean_dec_ref(v_lake_4950_);
lean_dec_ref(v_cmd_4946_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(lean_object* v_init_4963_, lean_object* v_x_4964_){
_start:
{
lean_object* v_d_4967_; 
if (lean_obj_tag(v_x_4964_) == 0)
{
lean_object* v_k_4970_; lean_object* v_v_4971_; lean_object* v_l_4972_; lean_object* v_r_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v_k_4970_ = lean_ctor_get(v_x_4964_, 1);
v_v_4971_ = lean_ctor_get(v_x_4964_, 2);
v_l_4972_ = lean_ctor_get(v_x_4964_, 3);
v_r_4973_ = lean_ctor_get(v_x_4964_, 4);
v___x_4974_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
v___x_4975_ = lean_box(0);
v___x_4976_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_4977_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_4963_, v_l_4972_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v_a_4978_; 
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_a_4978_);
lean_dec_ref_known(v___x_4977_, 1);
if (lean_obj_tag(v_a_4978_) == 0)
{
lean_object* v_a_4979_; 
v_a_4979_ = lean_ctor_get(v_a_4978_, 0);
lean_inc(v_a_4979_);
lean_dec_ref_known(v_a_4978_, 1);
v_d_4967_ = v_a_4979_;
goto v___jp_4966_;
}
else
{
lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_5016_; 
v_isSharedCheck_5016_ = !lean_is_exclusive(v_a_4978_);
if (v_isSharedCheck_5016_ == 0)
{
lean_object* v_unused_5017_; 
v_unused_5017_ = lean_ctor_get(v_a_4978_, 0);
lean_dec(v_unused_5017_);
v___x_4981_ = v_a_4978_;
v_isShared_4982_ = v_isSharedCheck_5016_;
goto v_resetjp_4980_;
}
else
{
lean_dec(v_a_4978_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_5016_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v_a_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_5015_; 
v___x_4983_ = lean_unsigned_to_nat(0u);
v___x_4984_ = lean_array_get_borrowed(v___x_4974_, v_v_4971_, v___x_4983_);
lean_inc(v___x_4984_);
v___x_4985_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4984_);
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_4988_ = v___x_4985_;
v_isShared_4989_ = v_isSharedCheck_5015_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_a_4986_);
lean_dec(v___x_4985_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_5015_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
if (lean_obj_tag(v_a_4986_) == 0)
{
lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; 
v___x_4990_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1));
v___x_4991_ = lean_string_append(v___x_4990_, v_k_4970_);
v___x_4992_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2));
v___x_4993_ = lean_string_append(v___x_4991_, v___x_4992_);
v___x_4994_ = lean_string_append(v___x_4993_, v___x_4984_);
v___x_4995_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v___x_4996_ = lean_string_append(v___x_4994_, v___x_4995_);
v___x_4997_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4996_);
lean_dec_ref(v___x_4996_);
if (lean_obj_tag(v___x_4997_) == 0)
{
lean_object* v_a_4998_; lean_object* v___x_5000_; 
v_a_4998_ = lean_ctor_get(v___x_4997_, 0);
lean_inc(v_a_4998_);
lean_dec_ref_known(v___x_4997_, 1);
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 0, v_a_4998_);
v___x_5000_ = v___x_4988_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4998_);
v___x_5000_ = v_reuseFailAlloc_5005_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
lean_object* v___x_5002_; 
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 0, v___x_5000_);
v___x_5002_ = v___x_4981_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v___x_5000_);
v___x_5002_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
lean_object* v___x_5003_; 
v___x_5003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5003_, 0, v___x_5002_);
lean_ctor_set(v___x_5003_, 1, v___x_4975_);
v_d_4967_ = v___x_5003_;
goto v___jp_4966_;
}
}
}
else
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5013_; 
lean_del_object(v___x_4988_);
lean_del_object(v___x_4981_);
v_a_5006_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5008_ = v___x_4997_;
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_4997_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5011_; 
if (v_isShared_5009_ == 0)
{
v___x_5011_ = v___x_5008_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_a_5006_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_4986_, 1);
lean_del_object(v___x_4988_);
lean_del_object(v___x_4981_);
v_init_4963_ = v___x_4976_;
v_x_4964_ = v_r_4973_;
goto _start;
}
}
}
}
}
else
{
return v___x_4977_;
}
}
else
{
lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5018_, 0, v_init_4963_);
v___x_5019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
return v___x_5019_;
}
v___jp_4966_:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4968_, 0, v_d_4967_);
v___x_4969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4968_);
return v___x_4969_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___boxed(lean_object* v_init_5020_, lean_object* v_x_5021_, lean_object* v___y_5022_){
_start:
{
lean_object* v_res_5023_; 
v_res_5023_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_5020_, v_x_5021_);
lean_dec(v_x_5021_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(lean_object* v_k_5024_, lean_object* v_v_5025_, lean_object* v_t_5026_){
_start:
{
if (lean_obj_tag(v_t_5026_) == 0)
{
lean_object* v_size_5027_; lean_object* v_k_5028_; lean_object* v_v_5029_; lean_object* v_l_5030_; lean_object* v_r_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5311_; 
v_size_5027_ = lean_ctor_get(v_t_5026_, 0);
v_k_5028_ = lean_ctor_get(v_t_5026_, 1);
v_v_5029_ = lean_ctor_get(v_t_5026_, 2);
v_l_5030_ = lean_ctor_get(v_t_5026_, 3);
v_r_5031_ = lean_ctor_get(v_t_5026_, 4);
v_isSharedCheck_5311_ = !lean_is_exclusive(v_t_5026_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5033_ = v_t_5026_;
v_isShared_5034_ = v_isSharedCheck_5311_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_r_5031_);
lean_inc(v_l_5030_);
lean_inc(v_v_5029_);
lean_inc(v_k_5028_);
lean_inc(v_size_5027_);
lean_dec(v_t_5026_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5311_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
uint8_t v___x_5035_; 
v___x_5035_ = lean_string_compare(v_k_5024_, v_k_5028_);
switch(v___x_5035_)
{
case 0:
{
lean_object* v_impl_5036_; lean_object* v___x_5037_; 
lean_dec(v_size_5027_);
v_impl_5036_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_5024_, v_v_5025_, v_l_5030_);
v___x_5037_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5031_) == 0)
{
lean_object* v_size_5038_; lean_object* v_size_5039_; lean_object* v_k_5040_; lean_object* v_v_5041_; lean_object* v_l_5042_; lean_object* v_r_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; uint8_t v___x_5046_; 
v_size_5038_ = lean_ctor_get(v_r_5031_, 0);
v_size_5039_ = lean_ctor_get(v_impl_5036_, 0);
lean_inc(v_size_5039_);
v_k_5040_ = lean_ctor_get(v_impl_5036_, 1);
lean_inc(v_k_5040_);
v_v_5041_ = lean_ctor_get(v_impl_5036_, 2);
lean_inc(v_v_5041_);
v_l_5042_ = lean_ctor_get(v_impl_5036_, 3);
lean_inc(v_l_5042_);
v_r_5043_ = lean_ctor_get(v_impl_5036_, 4);
lean_inc(v_r_5043_);
v___x_5044_ = lean_unsigned_to_nat(3u);
v___x_5045_ = lean_nat_mul(v___x_5044_, v_size_5038_);
v___x_5046_ = lean_nat_dec_lt(v___x_5045_, v_size_5039_);
lean_dec(v___x_5045_);
if (v___x_5046_ == 0)
{
lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5050_; 
lean_dec(v_r_5043_);
lean_dec(v_l_5042_);
lean_dec(v_v_5041_);
lean_dec(v_k_5040_);
v___x_5047_ = lean_nat_add(v___x_5037_, v_size_5039_);
lean_dec(v_size_5039_);
v___x_5048_ = lean_nat_add(v___x_5047_, v_size_5038_);
lean_dec(v___x_5047_);
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 3, v_impl_5036_);
lean_ctor_set(v___x_5033_, 0, v___x_5048_);
v___x_5050_ = v___x_5033_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v___x_5048_);
lean_ctor_set(v_reuseFailAlloc_5051_, 1, v_k_5028_);
lean_ctor_set(v_reuseFailAlloc_5051_, 2, v_v_5029_);
lean_ctor_set(v_reuseFailAlloc_5051_, 3, v_impl_5036_);
lean_ctor_set(v_reuseFailAlloc_5051_, 4, v_r_5031_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
else
{
lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5117_; 
v_isSharedCheck_5117_ = !lean_is_exclusive(v_impl_5036_);
if (v_isSharedCheck_5117_ == 0)
{
lean_object* v_unused_5118_; lean_object* v_unused_5119_; lean_object* v_unused_5120_; lean_object* v_unused_5121_; lean_object* v_unused_5122_; 
v_unused_5118_ = lean_ctor_get(v_impl_5036_, 4);
lean_dec(v_unused_5118_);
v_unused_5119_ = lean_ctor_get(v_impl_5036_, 3);
lean_dec(v_unused_5119_);
v_unused_5120_ = lean_ctor_get(v_impl_5036_, 2);
lean_dec(v_unused_5120_);
v_unused_5121_ = lean_ctor_get(v_impl_5036_, 1);
lean_dec(v_unused_5121_);
v_unused_5122_ = lean_ctor_get(v_impl_5036_, 0);
lean_dec(v_unused_5122_);
v___x_5053_ = v_impl_5036_;
v_isShared_5054_ = v_isSharedCheck_5117_;
goto v_resetjp_5052_;
}
else
{
lean_dec(v_impl_5036_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5117_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v_size_5055_; lean_object* v_size_5056_; lean_object* v_k_5057_; lean_object* v_v_5058_; lean_object* v_l_5059_; lean_object* v_r_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; uint8_t v___x_5063_; 
v_size_5055_ = lean_ctor_get(v_l_5042_, 0);
v_size_5056_ = lean_ctor_get(v_r_5043_, 0);
v_k_5057_ = lean_ctor_get(v_r_5043_, 1);
v_v_5058_ = lean_ctor_get(v_r_5043_, 2);
v_l_5059_ = lean_ctor_get(v_r_5043_, 3);
v_r_5060_ = lean_ctor_get(v_r_5043_, 4);
v___x_5061_ = lean_unsigned_to_nat(2u);
v___x_5062_ = lean_nat_mul(v___x_5061_, v_size_5055_);
v___x_5063_ = lean_nat_dec_lt(v_size_5056_, v___x_5062_);
lean_dec(v___x_5062_);
if (v___x_5063_ == 0)
{
lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5092_; 
lean_inc(v_r_5060_);
lean_inc(v_l_5059_);
lean_inc(v_v_5058_);
lean_inc(v_k_5057_);
v_isSharedCheck_5092_ = !lean_is_exclusive(v_r_5043_);
if (v_isSharedCheck_5092_ == 0)
{
lean_object* v_unused_5093_; lean_object* v_unused_5094_; lean_object* v_unused_5095_; lean_object* v_unused_5096_; lean_object* v_unused_5097_; 
v_unused_5093_ = lean_ctor_get(v_r_5043_, 4);
lean_dec(v_unused_5093_);
v_unused_5094_ = lean_ctor_get(v_r_5043_, 3);
lean_dec(v_unused_5094_);
v_unused_5095_ = lean_ctor_get(v_r_5043_, 2);
lean_dec(v_unused_5095_);
v_unused_5096_ = lean_ctor_get(v_r_5043_, 1);
lean_dec(v_unused_5096_);
v_unused_5097_ = lean_ctor_get(v_r_5043_, 0);
lean_dec(v_unused_5097_);
v___x_5065_ = v_r_5043_;
v_isShared_5066_ = v_isSharedCheck_5092_;
goto v_resetjp_5064_;
}
else
{
lean_dec(v_r_5043_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5092_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___y_5072_; lean_object* v___x_5080_; lean_object* v___y_5082_; 
v___x_5067_ = lean_nat_add(v___x_5037_, v_size_5039_);
lean_dec(v_size_5039_);
v___x_5068_ = lean_nat_add(v___x_5067_, v_size_5038_);
lean_dec(v___x_5067_);
v___x_5080_ = lean_nat_add(v___x_5037_, v_size_5055_);
if (lean_obj_tag(v_l_5059_) == 0)
{
lean_object* v_size_5090_; 
v_size_5090_ = lean_ctor_get(v_l_5059_, 0);
lean_inc(v_size_5090_);
v___y_5082_ = v_size_5090_;
goto v___jp_5081_;
}
else
{
lean_object* v___x_5091_; 
v___x_5091_ = lean_unsigned_to_nat(0u);
v___y_5082_ = v___x_5091_;
goto v___jp_5081_;
}
v___jp_5069_:
{
lean_object* v___x_5073_; lean_object* v___x_5075_; 
v___x_5073_ = lean_nat_add(v___y_5071_, v___y_5072_);
lean_dec(v___y_5072_);
lean_dec(v___y_5071_);
if (v_isShared_5066_ == 0)
{
lean_ctor_set(v___x_5065_, 4, v_r_5031_);
lean_ctor_set(v___x_5065_, 3, v_r_5060_);
lean_ctor_set(v___x_5065_, 2, v_v_5029_);
lean_ctor_set(v___x_5065_, 1, v_k_5028_);
lean_ctor_set(v___x_5065_, 0, v___x_5073_);
v___x_5075_ = v___x_5065_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v___x_5073_);
lean_ctor_set(v_reuseFailAlloc_5079_, 1, v_k_5028_);
lean_ctor_set(v_reuseFailAlloc_5079_, 2, v_v_5029_);
lean_ctor_set(v_reuseFailAlloc_5079_, 3, v_r_5060_);
lean_ctor_set(v_reuseFailAlloc_5079_, 4, v_r_5031_);
v___x_5075_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
lean_object* v___x_5077_; 
if (v_isShared_5054_ == 0)
{
lean_ctor_set(v___x_5053_, 4, v___x_5075_);
lean_ctor_set(v___x_5053_, 3, v___y_5070_);
lean_ctor_set(v___x_5053_, 2, v_v_5058_);
lean_ctor_set(v___x_5053_, 1, v_k_5057_);
lean_ctor_set(v___x_5053_, 0, v___x_5068_);
v___x_5077_ = v___x_5053_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v___x_5068_);
lean_ctor_set(v_reuseFailAlloc_5078_, 1, v_k_5057_);
lean_ctor_set(v_reuseFailAlloc_5078_, 2, v_v_5058_);
lean_ctor_set(v_reuseFailAlloc_5078_, 3, v___y_5070_);
lean_ctor_set(v_reuseFailAlloc_5078_, 4, v___x_5075_);
v___x_5077_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
return v___x_5077_;
}
}
}
v___jp_5081_:
{
lean_object* v___x_5083_; lean_object* v___x_5085_; 
v___x_5083_ = lean_nat_add(v___x_5080_, v___y_5082_);
lean_dec(v___y_5082_);
lean_dec(v___x_5080_);
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 4, v_l_5059_);
lean_ctor_set(v___x_5033_, 3, v_l_5042_);
lean_ctor_set(v___x_5033_, 2, v_v_5041_);
lean_ctor_set(v___x_5033_, 1, v_k_5040_);
lean_ctor_set(v___x_5033_, 0, v___x_5083_);
v___x_5085_ = v___x_5033_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5083_);
lean_ctor_set(v_reuseFailAlloc_5089_, 1, v_k_5040_);
lean_ctor_set(v_reuseFailAlloc_5089_, 2, v_v_5041_);
lean_ctor_set(v_reuseFailAlloc_5089_, 3, v_l_5042_);
lean_ctor_set(v_reuseFailAlloc_5089_, 4, v_l_5059_);
v___x_5085_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
lean_object* v___x_5086_; 
v___x_5086_ = lean_nat_add(v___x_5037_, v_size_5038_);
if (lean_obj_tag(v_r_5060_) == 0)
{
lean_object* v_size_5087_; 
v_size_5087_ = lean_ctor_get(v_r_5060_, 0);
lean_inc(v_size_5087_);
v___y_5070_ = v___x_5085_;
v___y_5071_ = v___x_5086_;
v___y_5072_ = v_size_5087_;
goto v___jp_5069_;
}
else
{
lean_object* v___x_5088_; 
v___x_5088_ = lean_unsigned_to_nat(0u);
v___y_5070_ = v___x_5085_;
v___y_5071_ = v___x_5086_;
v___y_5072_ = v___x_5088_;
goto v___jp_5069_;
}
}
}
}
}
else
{
lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5103_; 
lean_del_object(v___x_5033_);
v___x_5098_ = lean_nat_add(v___x_5037_, v_size_5039_);
lean_dec(v_size_5039_);
v___x_5099_ = lean_nat_add(v___x_5098_, v_size_5038_);
lean_dec(v___x_5098_);
v___x_5100_ = lean_nat_add(v___x_5037_, v_size_5038_);
v___x_5101_ = lean_nat_add(v___x_5100_, v_size_5056_);
lean_dec(v___x_5100_);
lean_inc_ref(v_r_5031_);
if (v_isShared_5054_ == 0)
{
lean_ctor_set(v___x_5053_, 4, v_r_5031_);
lean_ctor_set(v___x_5053_, 3, v_r_5043_);
lean_ctor_set(v___x_5053_, 2, v_v_5029_);
lean_ctor_set(v___x_5053_, 1, v_k_5028_);
lean_ctor_set(v___x_5053_, 0, v___x_5101_);
v___x_5103_ = v___x_5053_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5101_);
lean_ctor_set(v_reuseFailAlloc_5116_, 1, v_k_5028_);
lean_ctor_set(v_reuseFailAlloc_5116_, 2, v_v_5029_);
lean_ctor_set(v_reuseFailAlloc_5116_, 3, v_r_5043_);
lean_ctor_set(v_reuseFailAlloc_5116_, 4, v_r_5031_);
v___x_5103_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
v_isSharedCheck_5110_ = !lean_is_exclusive(v_r_5031_);
if (v_isSharedCheck_5110_ == 0)
{
lean_object* v_unused_5111_; lean_object* v_unused_5112_; lean_object* v_unused_5113_; lean_object* v_unused_5114_; lean_object* v_unused_5115_; 
v_unused_5111_ = lean_ctor_get(v_r_5031_, 4);
lean_dec(v_unused_5111_);
v_unused_5112_ = lean_ctor_get(v_r_5031_, 3);
lean_dec(v_unused_5112_);
v_unused_5113_ = lean_ctor_get(v_r_5031_, 2);
lean_dec(v_unused_5113_);
v_unused_5114_ = lean_ctor_get(v_r_5031_, 1);
lean_dec(v_unused_5114_);
v_unused_5115_ = lean_ctor_get(v_r_5031_, 0);
lean_dec(v_unused_5115_);
v___x_5105_ = v_r_5031_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_dec(v_r_5031_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
lean_ctor_set(v___x_5105_, 4, v___x_5103_);
lean_ctor_set(v___x_5105_, 3, v_l_5042_);
lean_ctor_set(v___x_5105_, 2, v_v_5041_);
lean_ctor_set(v___x_5105_, 1, v_k_5040_);
lean_ctor_set(v___x_5105_, 0, v___x_5099_);
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v___x_5099_);
lean_ctor_set(v_reuseFailAlloc_5109_, 1, v_k_5040_);
lean_ctor_set(v_reuseFailAlloc_5109_, 2, v_v_5041_);
lean_ctor_set(v_reuseFailAlloc_5109_, 3, v_l_5042_);
lean_ctor_set(v_reuseFailAlloc_5109_, 4, v___x_5103_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5123_; 
v_l_5123_ = lean_ctor_get(v_impl_5036_, 3);
lean_inc(v_l_5123_);
if (lean_obj_tag(v_l_5123_) == 0)
{
lean_object* v_r_5124_; lean_object* v_k_5125_; lean_object* v_v_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5137_; 
v_r_5124_ = lean_ctor_get(v_impl_5036_, 4);
v_k_5125_ = lean_ctor_get(v_impl_5036_, 1);
v_v_5126_ = lean_ctor_get(v_impl_5036_, 2);
v_isSharedCheck_5137_ = !lean_is_exclusive(v_impl_5036_);
if (v_isSharedCheck_5137_ == 0)
{
lean_object* v_unused_5138_; lean_object* v_unused_5139_; 
v_unused_5138_ = lean_ctor_get(v_impl_5036_, 3);
lean_dec(v_unused_5138_);
v_unused_5139_ = lean_ctor_get(v_impl_5036_, 0);
lean_dec(v_unused_5139_);
v___x_5128_ = v_impl_5036_;
v_isShared_5129_ = v_isSharedCheck_5137_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_r_5124_);
lean_inc(v_v_5126_);
lean_inc(v_k_5125_);
lean_dec(v_impl_5036_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5137_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v___x_5130_; lean_object* v___x_5132_; 
v___x_5130_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5124_);
if (v_isShared_5129_ == 0)
{
lean_ctor_set(v___x_5128_, 3, v_r_5124_);
lean_ctor_set(v___x_5128_, 2, v_v_5029_);
lean_ctor_set(v___x_5128_, 1, v_k_5028_);
lean_ctor_set(v___x_5128_, 0, v___x_5037_);
v___x_5132_ = v___x_5128_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v___x_5037_);
lean_ctor_set(v_reuseFailAlloc_5136_, 1, v_k_5028_);
lean_ctor_set(v_reuseFailAlloc_5136_, 2, v_v_5029_);
lean_ctor_set(v_reuseFailAlloc_5136_, 3, v_r_5124_);
lean_ctor_set(v_reuseFailAlloc_5136_, 4, v_r_5124_);
v___x_5132_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
lean_object* v___x_5134_; 
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 4, v___x_5132_);
lean_ctor_set(v___x_5033_, 3, v_l_5123_);
lean_ctor_set(v___x_5033_, 2, v_v_5126_);
lean_ctor_set(v___x_5033_, 1, v_k_5125_);
lean_ctor_set(v___x_5033_, 0, v___x_5130_);
v___x_5134_ = v___x_5033_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v___x_5130_);
lean_ctor_set(v_reuseFailAlloc_5135_, 1, v_k_5125_);
lean_ctor_set(v_reuseFailAlloc_5135_, 2, v_v_5126_);
lean_ctor_set(v_reuseFailAlloc_5135_, 3, v_l_5123_);
lean_ctor_set(v_reuseFailAlloc_5135_, 4, v___x_5132_);
v___x_5134_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
return v___x_5134_;
}
}
}
}
else
{
lean_object* v_r_5140_; 
v_r_5140_ = lean_ctor_get(v_impl_5036_, 4);
lean_inc(v_r_5140_);
if (lean_obj_tag(v_r_5140_) == 0)
{
lean_object* v_k_5141_; lean_object* v_v_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5165_; 
v_k_5141_ = lean_ctor_get(v_impl_5036_, 1);
v_v_5142_ = lean_ctor_get(v_impl_5036_, 2);
v_isSharedCheck_5165_ = !lean_is_exclusive(v_impl_5036_);
if (v_isSharedCheck_5165_ == 0)
{
lean_object* v_unused_5166_; lean_object* v_unused_5167_; lean_object* v_unused_5168_; 
v_unused_5166_ = lean_ctor_get(v_impl_5036_, 4);
lean_dec(v_unused_5166_);
v_unused_5167_ = lean_ctor_get(v_impl_5036_, 3);
lean_dec(v_unused_5167_);
v_unused_5168_ = lean_ctor_get(v_impl_5036_, 0);
lean_dec(v_unused_5168_);
v___x_5144_ = v_impl_5036_;
v_isShared_5145_ = v_isSharedCheck_5165_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_v_5142_);
lean_inc(v_k_5141_);
lean_dec(v_impl_5036_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5165_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v_k_5146_; lean_object* v_v_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5161_; 
v_k_5146_ = lean_ctor_get(v_r_5140_, 1);
v_v_5147_ = lean_ctor_get(v_r_5140_, 2);
v_isSharedCheck_5161_ = !lean_is_exclusive(v_r_5140_);
if (v_isSharedCheck_5161_ == 0)
{
lean_object* v_unused_5162_; lean_object* v_unused_5163_; lean_object* v_unused_5164_; 
v_unused_5162_ = lean_ctor_get(v_r_5140_, 4);
lean_dec(v_unused_5162_);
v_unused_5163_ = lean_ctor_get(v_r_5140_, 3);
lean_dec(v_unused_5163_);
v_unused_5164_ = lean_ctor_get(v_r_5140_, 0);
lean_dec(v_unused_5164_);
v___x_5149_ = v_r_5140_;
v_isShared_5150_ = v_isSharedCheck_5161_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_v_5147_);
lean_inc(v_k_5146_);
lean_dec(v_r_5140_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5161_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5151_; lean_object* v___x_5153_; 
v___x_5151_ = lean_unsigned_to_nat(3u);
if (v_isShared_5150_ == 0)
{
lean_ctor_set(v___x_5149_, 4, v_l_5123_);
lean_ctor_set(v___x_5149_, 3, v_l_5123_);
lean_ctor_set(v___x_5149_, 2, v_v_5142_);
lean_ctor_set(v___x_5149_, 1, v_k_5141_);
lean_ctor_set(v___x_5149_, 0, v___x_5037_);
v___x_5153_ = v___x_5149_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v___x_5037_);
lean_ctor_set(v_reuseFailAlloc_5160_, 1, v_k_5141_);
lean_ctor_set(v_reuseFailAlloc_5160_, 2, v_v_5142_);
lean_ctor_set(v_reuseFailAlloc_5160_, 3, v_l_5123_);
lean_ctor_set(v_reuseFailAlloc_5160_, 4, v_l_5123_);
v___x_5153_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
lean_object* v___x_5155_; 
if (v_isShared_5145_ == 0)
{
lean_ctor_set(v___x_5144_, 4, v_l_5123_);
lean_ctor_set(v___x_5144_, 2, v_v_5029_);
lean_ctor_set(v___x_5144_, 1, v_k_5028_);
lean_ctor_set(v___x_5144_, 0, v___x_5037_);
v___x_5155_ = v___x_5144_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v___x_5037_);
lean_ctor_set(v_reuseFailAlloc_5159_, 1, v_k_5028_);
lean_ctor_set(v_reuseFailAlloc_5159_, 2, v_v_5029_);
lean_ctor_set(v_reuseFailAlloc_5159_, 3, v_l_5123_);
lean_ctor_set(v_reuseFailAlloc_5159_, 4, v_l_5123_);
v___x_5155_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
lean_object* v___x_5157_; 
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 4, v___x_5155_);
lean_ctor_set(v___x_5033_, 3, v___x_5153_);
lean_ctor_set(v___x_5033_, 2, v_v_5147_);
lean_ctor_set(v___x_5033_, 1, v_k_5146_);
lean_ctor_set(v___x_5033_, 0, v___x_5151_);
v___x_5157_ = v___x_5033_;
goto v_reusejp_5156_;
}
else
{
lean_object* v_reuseFailAlloc_5158_; 
v_reuseFailAlloc_5158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5158_, 0, v___x_5151_);
lean_ctor_set(v_reuseFailAlloc_5158_, 1, v_k_5146_);
lean_ctor_set(v_reuseFailAlloc_5158_, 2, v_v_5147_);
lean_ctor_set(v_reuseFailAlloc_5158_, 3, v___x_5153_);
lean_ctor_set(v_reuseFailAlloc_5158_, 4, v___x_5155_);
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
lean_object* v___x_5169_; lean_object* v___x_5171_; 
v___x_5169_ = lean_unsigned_to_nat(2u);
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 4, v_r_5140_);
lean_ctor_set(v___x_5033_, 3, v_impl_5036_);
lean_ctor_set(v___x_5033_, 0, v___x_5169_);
v___x_5171_ = v___x_5033_;
goto v_reusejp_5170_;
}
else
{
lean_object* v_reuseFailAlloc_5172_; 
v_reuseFailAlloc_5172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5172_, 0, v___x_5169_);
lean_ctor_set(v_reuseFailAlloc_5172_, 1, v_k_5028_);
lean_ctor_set(v_reuseFailAlloc_5172_, 2, v_v_5029_);
lean_ctor_set(v_reuseFailAlloc_5172_, 3, v_impl_5036_);
lean_ctor_set(v_reuseFailAlloc_5172_, 4, v_r_5140_);
v___x_5171_ = v_reuseFailAlloc_5172_;
goto v_reusejp_5170_;
}
v_reusejp_5170_:
{
return v___x_5171_;
}
}
}
}
}
case 1:
{
lean_object* v___x_5174_; 
lean_dec(v_v_5029_);
lean_dec(v_k_5028_);
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 2, v_v_5025_);
lean_ctor_set(v___x_5033_, 1, v_k_5024_);
v___x_5174_ = v___x_5033_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_size_5027_);
lean_ctor_set(v_reuseFailAlloc_5175_, 1, v_k_5024_);
lean_ctor_set(v_reuseFailAlloc_5175_, 2, v_v_5025_);
lean_ctor_set(v_reuseFailAlloc_5175_, 3, v_l_5030_);
lean_ctor_set(v_reuseFailAlloc_5175_, 4, v_r_5031_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
default: 
{
lean_object* v_impl_5176_; lean_object* v___x_5177_; 
lean_dec(v_size_5027_);
v_impl_5176_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_5024_, v_v_5025_, v_r_5031_);
v___x_5177_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5030_) == 0)
{
lean_object* v_size_5178_; lean_object* v_size_5179_; lean_object* v_k_5180_; lean_object* v_v_5181_; lean_object* v_l_5182_; lean_object* v_r_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; uint8_t v___x_5186_; 
v_size_5178_ = lean_ctor_get(v_l_5030_, 0);
v_size_5179_ = lean_ctor_get(v_impl_5176_, 0);
lean_inc(v_size_5179_);
v_k_5180_ = lean_ctor_get(v_impl_5176_, 1);
lean_inc(v_k_5180_);
v_v_5181_ = lean_ctor_get(v_impl_5176_, 2);
lean_inc(v_v_5181_);
v_l_5182_ = lean_ctor_get(v_impl_5176_, 3);
lean_inc(v_l_5182_);
v_r_5183_ = lean_ctor_get(v_impl_5176_, 4);
lean_inc(v_r_5183_);
v___x_5184_ = lean_unsigned_to_nat(3u);
v___x_5185_ = lean_nat_mul(v___x_5184_, v_size_5178_);
v___x_5186_ = lean_nat_dec_lt(v___x_5185_, v_size_5179_);
lean_dec(v___x_5185_);
if (v___x_5186_ == 0)
{
lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5190_; 
lean_dec(v_r_5183_);
lean_dec(v_l_5182_);
lean_dec(v_v_5181_);
lean_dec(v_k_5180_);
v___x_5187_ = lean_nat_add(v___x_5177_, v_size_5178_);
v___x_5188_ = lean_nat_add(v___x_5187_, v_size_5179_);
lean_dec(v_size_5179_);
lean_dec(v___x_5187_);
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 4, v_impl_5176_);
lean_ctor_set(v___x_5033_, 0, v___x_5188_);
v___x_5190_ = v___x_5033_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5188_);
lean_ctor_set(v_reuseFailAlloc_5191_, 1, v_k_5028_);
lean_ctor_set(v_reuseFailAlloc_5191_, 2, v_v_5029_);
lean_ctor_set(v_reuseFailAlloc_5191_, 3, v_l_5030_);
lean_ctor_set(v_reuseFailAlloc_5191_, 4, v_impl_5176_);
v___x_5190_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
return v___x_5190_;
}
}
else
{
lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5255_; 
v_isSharedCheck_5255_ = !lean_is_exclusive(v_impl_5176_);
if (v_isSharedCheck_5255_ == 0)
{
lean_object* v_unused_5256_; lean_object* v_unused_5257_; lean_object* v_unused_5258_; lean_object* v_unused_5259_; lean_object* v_unused_5260_; 
v_unused_5256_ = lean_ctor_get(v_impl_5176_, 4);
lean_dec(v_unused_5256_);
v_unused_5257_ = lean_ctor_get(v_impl_5176_, 3);
lean_dec(v_unused_5257_);
v_unused_5258_ = lean_ctor_get(v_impl_5176_, 2);
lean_dec(v_unused_5258_);
v_unused_5259_ = lean_ctor_get(v_impl_5176_, 1);
lean_dec(v_unused_5259_);
v_unused_5260_ = lean_ctor_get(v_impl_5176_, 0);
lean_dec(v_unused_5260_);
v___x_5193_ = v_impl_5176_;
v_isShared_5194_ = v_isSharedCheck_5255_;
goto v_resetjp_5192_;
}
else
{
lean_dec(v_impl_5176_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5255_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v_size_5195_; lean_object* v_k_5196_; lean_object* v_v_5197_; lean_object* v_l_5198_; lean_object* v_r_5199_; lean_object* v_size_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; uint8_t v___x_5203_; 
v_size_5195_ = lean_ctor_get(v_l_5182_, 0);
v_k_5196_ = lean_ctor_get(v_l_5182_, 1);
v_v_5197_ = lean_ctor_get(v_l_5182_, 2);
v_l_5198_ = lean_ctor_get(v_l_5182_, 3);
v_r_5199_ = lean_ctor_get(v_l_5182_, 4);
v_size_5200_ = lean_ctor_get(v_r_5183_, 0);
v___x_5201_ = lean_unsigned_to_nat(2u);
v___x_5202_ = lean_nat_mul(v___x_5201_, v_size_5200_);
v___x_5203_ = lean_nat_dec_lt(v_size_5195_, v___x_5202_);
lean_dec(v___x_5202_);
if (v___x_5203_ == 0)
{
lean_object* v___x_5205_; uint8_t v_isShared_5206_; uint8_t v_isSharedCheck_5231_; 
lean_inc(v_r_5199_);
lean_inc(v_l_5198_);
lean_inc(v_v_5197_);
lean_inc(v_k_5196_);
v_isSharedCheck_5231_ = !lean_is_exclusive(v_l_5182_);
if (v_isSharedCheck_5231_ == 0)
{
lean_object* v_unused_5232_; lean_object* v_unused_5233_; lean_object* v_unused_5234_; lean_object* v_unused_5235_; lean_object* v_unused_5236_; 
v_unused_5232_ = lean_ctor_get(v_l_5182_, 4);
lean_dec(v_unused_5232_);
v_unused_5233_ = lean_ctor_get(v_l_5182_, 3);
lean_dec(v_unused_5233_);
v_unused_5234_ = lean_ctor_get(v_l_5182_, 2);
lean_dec(v_unused_5234_);
v_unused_5235_ = lean_ctor_get(v_l_5182_, 1);
lean_dec(v_unused_5235_);
v_unused_5236_ = lean_ctor_get(v_l_5182_, 0);
lean_dec(v_unused_5236_);
v___x_5205_ = v_l_5182_;
v_isShared_5206_ = v_isSharedCheck_5231_;
goto v_resetjp_5204_;
}
else
{
lean_dec(v_l_5182_);
v___x_5205_ = lean_box(0);
v_isShared_5206_ = v_isSharedCheck_5231_;
goto v_resetjp_5204_;
}
v_resetjp_5204_:
{
lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___y_5210_; lean_object* v___y_5211_; lean_object* v___y_5212_; lean_object* v___y_5221_; 
v___x_5207_ = lean_nat_add(v___x_5177_, v_size_5178_);
v___x_5208_ = lean_nat_add(v___x_5207_, v_size_5179_);
lean_dec(v_size_5179_);
if (lean_obj_tag(v_l_5198_) == 0)
{
lean_object* v_size_5229_; 
v_size_5229_ = lean_ctor_get(v_l_5198_, 0);
lean_inc(v_size_5229_);
v___y_5221_ = v_size_5229_;
goto v___jp_5220_;
}
else
{
lean_object* v___x_5230_; 
v___x_5230_ = lean_unsigned_to_nat(0u);
v___y_5221_ = v___x_5230_;
goto v___jp_5220_;
}
v___jp_5209_:
{
lean_object* v___x_5213_; lean_object* v___x_5215_; 
v___x_5213_ = lean_nat_add(v___y_5211_, v___y_5212_);
lean_dec(v___y_5212_);
lean_dec(v___y_5211_);
if (v_isShared_5206_ == 0)
{
lean_ctor_set(v___x_5205_, 4, v_r_5183_);
lean_ctor_set(v___x_5205_, 3, v_r_5199_);
lean_ctor_set(v___x_5205_, 2, v_v_5181_);
lean_ctor_set(v___x_5205_, 1, v_k_5180_);
lean_ctor_set(v___x_5205_, 0, v___x_5213_);
v___x_5215_ = v___x_5205_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v___x_5213_);
lean_ctor_set(v_reuseFailAlloc_5219_, 1, v_k_5180_);
lean_ctor_set(v_reuseFailAlloc_5219_, 2, v_v_5181_);
lean_ctor_set(v_reuseFailAlloc_5219_, 3, v_r_5199_);
lean_ctor_set(v_reuseFailAlloc_5219_, 4, v_r_5183_);
v___x_5215_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
lean_object* v___x_5217_; 
if (v_isShared_5194_ == 0)
{
lean_ctor_set(v___x_5193_, 4, v___x_5215_);
lean_ctor_set(v___x_5193_, 3, v___y_5210_);
lean_ctor_set(v___x_5193_, 2, v_v_5197_);
lean_ctor_set(v___x_5193_, 1, v_k_5196_);
lean_ctor_set(v___x_5193_, 0, v___x_5208_);
v___x_5217_ = v___x_5193_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v___x_5208_);
lean_ctor_set(v_reuseFailAlloc_5218_, 1, v_k_5196_);
lean_ctor_set(v_reuseFailAlloc_5218_, 2, v_v_5197_);
lean_ctor_set(v_reuseFailAlloc_5218_, 3, v___y_5210_);
lean_ctor_set(v_reuseFailAlloc_5218_, 4, v___x_5215_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
return v___x_5217_;
}
}
}
v___jp_5220_:
{
lean_object* v___x_5222_; lean_object* v___x_5224_; 
v___x_5222_ = lean_nat_add(v___x_5207_, v___y_5221_);
lean_dec(v___y_5221_);
lean_dec(v___x_5207_);
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 4, v_l_5198_);
lean_ctor_set(v___x_5033_, 0, v___x_5222_);
v___x_5224_ = v___x_5033_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v___x_5222_);
lean_ctor_set(v_reuseFailAlloc_5228_, 1, v_k_5028_);
lean_ctor_set(v_reuseFailAlloc_5228_, 2, v_v_5029_);
lean_ctor_set(v_reuseFailAlloc_5228_, 3, v_l_5030_);
lean_ctor_set(v_reuseFailAlloc_5228_, 4, v_l_5198_);
v___x_5224_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
lean_object* v___x_5225_; 
v___x_5225_ = lean_nat_add(v___x_5177_, v_size_5200_);
if (lean_obj_tag(v_r_5199_) == 0)
{
lean_object* v_size_5226_; 
v_size_5226_ = lean_ctor_get(v_r_5199_, 0);
lean_inc(v_size_5226_);
v___y_5210_ = v___x_5224_;
v___y_5211_ = v___x_5225_;
v___y_5212_ = v_size_5226_;
goto v___jp_5209_;
}
else
{
lean_object* v___x_5227_; 
v___x_5227_ = lean_unsigned_to_nat(0u);
v___y_5210_ = v___x_5224_;
v___y_5211_ = v___x_5225_;
v___y_5212_ = v___x_5227_;
goto v___jp_5209_;
}
}
}
}
}
else
{
lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5241_; 
lean_del_object(v___x_5033_);
v___x_5237_ = lean_nat_add(v___x_5177_, v_size_5178_);
v___x_5238_ = lean_nat_add(v___x_5237_, v_size_5179_);
lean_dec(v_size_5179_);
v___x_5239_ = lean_nat_add(v___x_5237_, v_size_5195_);
lean_dec(v___x_5237_);
lean_inc_ref(v_l_5030_);
if (v_isShared_5194_ == 0)
{
lean_ctor_set(v___x_5193_, 4, v_l_5182_);
lean_ctor_set(v___x_5193_, 3, v_l_5030_);
lean_ctor_set(v___x_5193_, 2, v_v_5029_);
lean_ctor_set(v___x_5193_, 1, v_k_5028_);
lean_ctor_set(v___x_5193_, 0, v___x_5239_);
v___x_5241_ = v___x_5193_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___x_5239_);
lean_ctor_set(v_reuseFailAlloc_5254_, 1, v_k_5028_);
lean_ctor_set(v_reuseFailAlloc_5254_, 2, v_v_5029_);
lean_ctor_set(v_reuseFailAlloc_5254_, 3, v_l_5030_);
lean_ctor_set(v_reuseFailAlloc_5254_, 4, v_l_5182_);
v___x_5241_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5248_; 
v_isSharedCheck_5248_ = !lean_is_exclusive(v_l_5030_);
if (v_isSharedCheck_5248_ == 0)
{
lean_object* v_unused_5249_; lean_object* v_unused_5250_; lean_object* v_unused_5251_; lean_object* v_unused_5252_; lean_object* v_unused_5253_; 
v_unused_5249_ = lean_ctor_get(v_l_5030_, 4);
lean_dec(v_unused_5249_);
v_unused_5250_ = lean_ctor_get(v_l_5030_, 3);
lean_dec(v_unused_5250_);
v_unused_5251_ = lean_ctor_get(v_l_5030_, 2);
lean_dec(v_unused_5251_);
v_unused_5252_ = lean_ctor_get(v_l_5030_, 1);
lean_dec(v_unused_5252_);
v_unused_5253_ = lean_ctor_get(v_l_5030_, 0);
lean_dec(v_unused_5253_);
v___x_5243_ = v_l_5030_;
v_isShared_5244_ = v_isSharedCheck_5248_;
goto v_resetjp_5242_;
}
else
{
lean_dec(v_l_5030_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5248_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
lean_object* v___x_5246_; 
if (v_isShared_5244_ == 0)
{
lean_ctor_set(v___x_5243_, 4, v_r_5183_);
lean_ctor_set(v___x_5243_, 3, v___x_5241_);
lean_ctor_set(v___x_5243_, 2, v_v_5181_);
lean_ctor_set(v___x_5243_, 1, v_k_5180_);
lean_ctor_set(v___x_5243_, 0, v___x_5238_);
v___x_5246_ = v___x_5243_;
goto v_reusejp_5245_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v___x_5238_);
lean_ctor_set(v_reuseFailAlloc_5247_, 1, v_k_5180_);
lean_ctor_set(v_reuseFailAlloc_5247_, 2, v_v_5181_);
lean_ctor_set(v_reuseFailAlloc_5247_, 3, v___x_5241_);
lean_ctor_set(v_reuseFailAlloc_5247_, 4, v_r_5183_);
v___x_5246_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5245_;
}
v_reusejp_5245_:
{
return v___x_5246_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5261_; 
v_l_5261_ = lean_ctor_get(v_impl_5176_, 3);
lean_inc(v_l_5261_);
if (lean_obj_tag(v_l_5261_) == 0)
{
lean_object* v_r_5262_; lean_object* v_k_5263_; lean_object* v_v_5264_; lean_object* v___x_5266_; uint8_t v_isShared_5267_; uint8_t v_isSharedCheck_5287_; 
v_r_5262_ = lean_ctor_get(v_impl_5176_, 4);
v_k_5263_ = lean_ctor_get(v_impl_5176_, 1);
v_v_5264_ = lean_ctor_get(v_impl_5176_, 2);
v_isSharedCheck_5287_ = !lean_is_exclusive(v_impl_5176_);
if (v_isSharedCheck_5287_ == 0)
{
lean_object* v_unused_5288_; lean_object* v_unused_5289_; 
v_unused_5288_ = lean_ctor_get(v_impl_5176_, 3);
lean_dec(v_unused_5288_);
v_unused_5289_ = lean_ctor_get(v_impl_5176_, 0);
lean_dec(v_unused_5289_);
v___x_5266_ = v_impl_5176_;
v_isShared_5267_ = v_isSharedCheck_5287_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_r_5262_);
lean_inc(v_v_5264_);
lean_inc(v_k_5263_);
lean_dec(v_impl_5176_);
v___x_5266_ = lean_box(0);
v_isShared_5267_ = v_isSharedCheck_5287_;
goto v_resetjp_5265_;
}
v_resetjp_5265_:
{
lean_object* v_k_5268_; lean_object* v_v_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5283_; 
v_k_5268_ = lean_ctor_get(v_l_5261_, 1);
v_v_5269_ = lean_ctor_get(v_l_5261_, 2);
v_isSharedCheck_5283_ = !lean_is_exclusive(v_l_5261_);
if (v_isSharedCheck_5283_ == 0)
{
lean_object* v_unused_5284_; lean_object* v_unused_5285_; lean_object* v_unused_5286_; 
v_unused_5284_ = lean_ctor_get(v_l_5261_, 4);
lean_dec(v_unused_5284_);
v_unused_5285_ = lean_ctor_get(v_l_5261_, 3);
lean_dec(v_unused_5285_);
v_unused_5286_ = lean_ctor_get(v_l_5261_, 0);
lean_dec(v_unused_5286_);
v___x_5271_ = v_l_5261_;
v_isShared_5272_ = v_isSharedCheck_5283_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_v_5269_);
lean_inc(v_k_5268_);
lean_dec(v_l_5261_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5283_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5273_; lean_object* v___x_5275_; 
v___x_5273_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5262_, 2);
if (v_isShared_5272_ == 0)
{
lean_ctor_set(v___x_5271_, 4, v_r_5262_);
lean_ctor_set(v___x_5271_, 3, v_r_5262_);
lean_ctor_set(v___x_5271_, 2, v_v_5029_);
lean_ctor_set(v___x_5271_, 1, v_k_5028_);
lean_ctor_set(v___x_5271_, 0, v___x_5177_);
v___x_5275_ = v___x_5271_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5282_; 
v_reuseFailAlloc_5282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5282_, 0, v___x_5177_);
lean_ctor_set(v_reuseFailAlloc_5282_, 1, v_k_5028_);
lean_ctor_set(v_reuseFailAlloc_5282_, 2, v_v_5029_);
lean_ctor_set(v_reuseFailAlloc_5282_, 3, v_r_5262_);
lean_ctor_set(v_reuseFailAlloc_5282_, 4, v_r_5262_);
v___x_5275_ = v_reuseFailAlloc_5282_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
lean_object* v___x_5277_; 
lean_inc(v_r_5262_);
if (v_isShared_5267_ == 0)
{
lean_ctor_set(v___x_5266_, 3, v_r_5262_);
lean_ctor_set(v___x_5266_, 0, v___x_5177_);
v___x_5277_ = v___x_5266_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v___x_5177_);
lean_ctor_set(v_reuseFailAlloc_5281_, 1, v_k_5263_);
lean_ctor_set(v_reuseFailAlloc_5281_, 2, v_v_5264_);
lean_ctor_set(v_reuseFailAlloc_5281_, 3, v_r_5262_);
lean_ctor_set(v_reuseFailAlloc_5281_, 4, v_r_5262_);
v___x_5277_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
lean_object* v___x_5279_; 
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 4, v___x_5277_);
lean_ctor_set(v___x_5033_, 3, v___x_5275_);
lean_ctor_set(v___x_5033_, 2, v_v_5269_);
lean_ctor_set(v___x_5033_, 1, v_k_5268_);
lean_ctor_set(v___x_5033_, 0, v___x_5273_);
v___x_5279_ = v___x_5033_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v___x_5273_);
lean_ctor_set(v_reuseFailAlloc_5280_, 1, v_k_5268_);
lean_ctor_set(v_reuseFailAlloc_5280_, 2, v_v_5269_);
lean_ctor_set(v_reuseFailAlloc_5280_, 3, v___x_5275_);
lean_ctor_set(v_reuseFailAlloc_5280_, 4, v___x_5277_);
v___x_5279_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
return v___x_5279_;
}
}
}
}
}
}
else
{
lean_object* v_r_5290_; 
v_r_5290_ = lean_ctor_get(v_impl_5176_, 4);
lean_inc(v_r_5290_);
if (lean_obj_tag(v_r_5290_) == 0)
{
lean_object* v_k_5291_; lean_object* v_v_5292_; lean_object* v___x_5294_; uint8_t v_isShared_5295_; uint8_t v_isSharedCheck_5303_; 
v_k_5291_ = lean_ctor_get(v_impl_5176_, 1);
v_v_5292_ = lean_ctor_get(v_impl_5176_, 2);
v_isSharedCheck_5303_ = !lean_is_exclusive(v_impl_5176_);
if (v_isSharedCheck_5303_ == 0)
{
lean_object* v_unused_5304_; lean_object* v_unused_5305_; lean_object* v_unused_5306_; 
v_unused_5304_ = lean_ctor_get(v_impl_5176_, 4);
lean_dec(v_unused_5304_);
v_unused_5305_ = lean_ctor_get(v_impl_5176_, 3);
lean_dec(v_unused_5305_);
v_unused_5306_ = lean_ctor_get(v_impl_5176_, 0);
lean_dec(v_unused_5306_);
v___x_5294_ = v_impl_5176_;
v_isShared_5295_ = v_isSharedCheck_5303_;
goto v_resetjp_5293_;
}
else
{
lean_inc(v_v_5292_);
lean_inc(v_k_5291_);
lean_dec(v_impl_5176_);
v___x_5294_ = lean_box(0);
v_isShared_5295_ = v_isSharedCheck_5303_;
goto v_resetjp_5293_;
}
v_resetjp_5293_:
{
lean_object* v___x_5296_; lean_object* v___x_5298_; 
v___x_5296_ = lean_unsigned_to_nat(3u);
if (v_isShared_5295_ == 0)
{
lean_ctor_set(v___x_5294_, 4, v_l_5261_);
lean_ctor_set(v___x_5294_, 2, v_v_5029_);
lean_ctor_set(v___x_5294_, 1, v_k_5028_);
lean_ctor_set(v___x_5294_, 0, v___x_5177_);
v___x_5298_ = v___x_5294_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v___x_5177_);
lean_ctor_set(v_reuseFailAlloc_5302_, 1, v_k_5028_);
lean_ctor_set(v_reuseFailAlloc_5302_, 2, v_v_5029_);
lean_ctor_set(v_reuseFailAlloc_5302_, 3, v_l_5261_);
lean_ctor_set(v_reuseFailAlloc_5302_, 4, v_l_5261_);
v___x_5298_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
lean_object* v___x_5300_; 
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 4, v_r_5290_);
lean_ctor_set(v___x_5033_, 3, v___x_5298_);
lean_ctor_set(v___x_5033_, 2, v_v_5292_);
lean_ctor_set(v___x_5033_, 1, v_k_5291_);
lean_ctor_set(v___x_5033_, 0, v___x_5296_);
v___x_5300_ = v___x_5033_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v___x_5296_);
lean_ctor_set(v_reuseFailAlloc_5301_, 1, v_k_5291_);
lean_ctor_set(v_reuseFailAlloc_5301_, 2, v_v_5292_);
lean_ctor_set(v_reuseFailAlloc_5301_, 3, v___x_5298_);
lean_ctor_set(v_reuseFailAlloc_5301_, 4, v_r_5290_);
v___x_5300_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
return v___x_5300_;
}
}
}
}
else
{
lean_object* v___x_5307_; lean_object* v___x_5309_; 
v___x_5307_ = lean_unsigned_to_nat(2u);
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 4, v_impl_5176_);
lean_ctor_set(v___x_5033_, 3, v_r_5290_);
lean_ctor_set(v___x_5033_, 0, v___x_5307_);
v___x_5309_ = v___x_5033_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5310_; 
v_reuseFailAlloc_5310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5310_, 0, v___x_5307_);
lean_ctor_set(v_reuseFailAlloc_5310_, 1, v_k_5028_);
lean_ctor_set(v_reuseFailAlloc_5310_, 2, v_v_5029_);
lean_ctor_set(v_reuseFailAlloc_5310_, 3, v_r_5290_);
lean_ctor_set(v_reuseFailAlloc_5310_, 4, v_impl_5176_);
v___x_5309_ = v_reuseFailAlloc_5310_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
return v___x_5309_;
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
lean_object* v___x_5312_; lean_object* v___x_5313_; 
v___x_5312_ = lean_unsigned_to_nat(1u);
v___x_5313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5313_, 0, v___x_5312_);
lean_ctor_set(v___x_5313_, 1, v_k_5024_);
lean_ctor_set(v___x_5313_, 2, v_v_5025_);
lean_ctor_set(v___x_5313_, 3, v_t_5026_);
lean_ctor_set(v___x_5313_, 4, v_t_5026_);
return v___x_5313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(lean_object* v_init_5315_, lean_object* v_x_5316_){
_start:
{
lean_object* v_d_5319_; 
if (lean_obj_tag(v_x_5316_) == 0)
{
lean_object* v_k_5322_; lean_object* v_v_5323_; lean_object* v_l_5324_; lean_object* v_r_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; 
v_k_5322_ = lean_ctor_get(v_x_5316_, 1);
v_v_5323_ = lean_ctor_get(v_x_5316_, 2);
v_l_5324_ = lean_ctor_get(v_x_5316_, 3);
v_r_5325_ = lean_ctor_get(v_x_5316_, 4);
v___x_5326_ = lean_box(0);
v___x_5327_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_5328_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v_init_5315_, v_l_5324_);
if (lean_obj_tag(v___x_5328_) == 0)
{
lean_object* v_a_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5364_; 
v_a_5329_ = lean_ctor_get(v___x_5328_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5328_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5331_ = v___x_5328_;
v_isShared_5332_ = v_isSharedCheck_5364_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_a_5329_);
lean_dec(v___x_5328_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5364_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
if (lean_obj_tag(v_a_5329_) == 0)
{
lean_object* v_a_5333_; 
lean_del_object(v___x_5331_);
v_a_5333_ = lean_ctor_get(v_a_5329_, 0);
lean_inc(v_a_5333_);
lean_dec_ref_known(v_a_5329_, 1);
v_d_5319_ = v_a_5333_;
goto v___jp_5318_;
}
else
{
lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5362_; 
v_isSharedCheck_5362_ = !lean_is_exclusive(v_a_5329_);
if (v_isSharedCheck_5362_ == 0)
{
lean_object* v_unused_5363_; 
v_unused_5363_ = lean_ctor_get(v_a_5329_, 0);
lean_dec(v_unused_5363_);
v___x_5335_ = v_a_5329_;
v_isShared_5336_ = v_isSharedCheck_5362_;
goto v_resetjp_5334_;
}
else
{
lean_dec(v_a_5329_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5362_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v___x_5337_; lean_object* v___x_5338_; uint8_t v___x_5339_; 
v___x_5337_ = lean_array_get_size(v_v_5323_);
v___x_5338_ = lean_unsigned_to_nat(0u);
v___x_5339_ = lean_nat_dec_eq(v___x_5337_, v___x_5338_);
if (v___x_5339_ == 0)
{
lean_del_object(v___x_5335_);
lean_del_object(v___x_5331_);
v_init_5315_ = v___x_5327_;
v_x_5316_ = v_r_5325_;
goto _start;
}
else
{
lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; 
v___x_5341_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1));
v___x_5342_ = lean_string_append(v___x_5341_, v_k_5322_);
v___x_5343_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___closed__0));
v___x_5344_ = lean_string_append(v___x_5342_, v___x_5343_);
v___x_5345_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5344_);
lean_dec_ref(v___x_5344_);
if (lean_obj_tag(v___x_5345_) == 0)
{
lean_object* v_a_5346_; lean_object* v___x_5348_; 
v_a_5346_ = lean_ctor_get(v___x_5345_, 0);
lean_inc(v_a_5346_);
lean_dec_ref_known(v___x_5345_, 1);
if (v_isShared_5336_ == 0)
{
lean_ctor_set_tag(v___x_5335_, 0);
lean_ctor_set(v___x_5335_, 0, v_a_5346_);
v___x_5348_ = v___x_5335_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5346_);
v___x_5348_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
lean_object* v___x_5350_; 
if (v_isShared_5332_ == 0)
{
lean_ctor_set_tag(v___x_5331_, 1);
lean_ctor_set(v___x_5331_, 0, v___x_5348_);
v___x_5350_ = v___x_5331_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5348_);
v___x_5350_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
lean_object* v___x_5351_; 
v___x_5351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5351_, 0, v___x_5350_);
lean_ctor_set(v___x_5351_, 1, v___x_5326_);
v_d_5319_ = v___x_5351_;
goto v___jp_5318_;
}
}
}
else
{
lean_object* v_a_5354_; lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5361_; 
lean_del_object(v___x_5335_);
lean_del_object(v___x_5331_);
v_a_5354_ = lean_ctor_get(v___x_5345_, 0);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5345_);
if (v_isSharedCheck_5361_ == 0)
{
v___x_5356_ = v___x_5345_;
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
else
{
lean_inc(v_a_5354_);
lean_dec(v___x_5345_);
v___x_5356_ = lean_box(0);
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
v_resetjp_5355_:
{
lean_object* v___x_5359_; 
if (v_isShared_5357_ == 0)
{
v___x_5359_ = v___x_5356_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_a_5354_);
v___x_5359_ = v_reuseFailAlloc_5360_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
return v___x_5359_;
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
return v___x_5328_;
}
}
else
{
lean_object* v___x_5365_; lean_object* v___x_5366_; 
v___x_5365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5365_, 0, v_init_5315_);
v___x_5366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5366_, 0, v___x_5365_);
return v___x_5366_;
}
v___jp_5318_:
{
lean_object* v___x_5320_; lean_object* v___x_5321_; 
v___x_5320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5320_, 0, v_d_5319_);
v___x_5321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5321_, 0, v___x_5320_);
return v___x_5321_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___boxed(lean_object* v_init_5367_, lean_object* v_x_5368_, lean_object* v___y_5369_){
_start:
{
lean_object* v_res_5370_; 
v_res_5370_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v_init_5367_, v_x_5368_);
lean_dec(v_x_5368_);
return v_res_5370_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(lean_object* v_cfg_5376_){
_start:
{
lean_object* v___y_5379_; lean_object* v_a_5380_; lean_object* v___y_5393_; lean_object* v_externalKernels_5394_; uint8_t v___y_5407_; lean_object* v___y_5408_; lean_object* v___y_5409_; lean_object* v_a_5410_; uint8_t v___y_5424_; lean_object* v___y_5425_; lean_object* v_enable__nanoda_x3f_5438_; lean_object* v_external__kernels_x3f_5439_; lean_object* v___y_5441_; 
v_enable__nanoda_x3f_5438_ = lean_ctor_get(v_cfg_5376_, 5);
lean_inc(v_enable__nanoda_x3f_5438_);
v_external__kernels_x3f_5439_ = lean_ctor_get(v_cfg_5376_, 6);
lean_inc(v_external__kernels_x3f_5439_);
lean_dec_ref(v_cfg_5376_);
if (lean_obj_tag(v_external__kernels_x3f_5439_) == 0)
{
lean_object* v___x_5472_; 
v___x_5472_ = lean_box(1);
v___y_5441_ = v___x_5472_;
goto v___jp_5440_;
}
else
{
lean_object* v_val_5473_; 
v_val_5473_ = lean_ctor_get(v_external__kernels_x3f_5439_, 0);
lean_inc(v_val_5473_);
lean_dec_ref_known(v_external__kernels_x3f_5439_, 1);
v___y_5441_ = v_val_5473_;
goto v___jp_5440_;
}
v___jp_5378_:
{
lean_object* v_fst_5381_; 
v_fst_5381_ = lean_ctor_get(v_a_5380_, 0);
lean_inc(v_fst_5381_);
lean_dec_ref(v_a_5380_);
if (lean_obj_tag(v_fst_5381_) == 0)
{
lean_object* v___x_5382_; lean_object* v___x_5383_; 
v___x_5382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5382_, 0, v___y_5379_);
v___x_5383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5383_, 0, v___x_5382_);
return v___x_5383_;
}
else
{
lean_object* v_val_5384_; lean_object* v___x_5386_; uint8_t v_isShared_5387_; uint8_t v_isSharedCheck_5391_; 
lean_dec(v___y_5379_);
v_val_5384_ = lean_ctor_get(v_fst_5381_, 0);
v_isSharedCheck_5391_ = !lean_is_exclusive(v_fst_5381_);
if (v_isSharedCheck_5391_ == 0)
{
v___x_5386_ = v_fst_5381_;
v_isShared_5387_ = v_isSharedCheck_5391_;
goto v_resetjp_5385_;
}
else
{
lean_inc(v_val_5384_);
lean_dec(v_fst_5381_);
v___x_5386_ = lean_box(0);
v_isShared_5387_ = v_isSharedCheck_5391_;
goto v_resetjp_5385_;
}
v_resetjp_5385_:
{
lean_object* v___x_5389_; 
if (v_isShared_5387_ == 0)
{
lean_ctor_set_tag(v___x_5386_, 0);
v___x_5389_ = v___x_5386_;
goto v_reusejp_5388_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v_val_5384_);
v___x_5389_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5388_;
}
v_reusejp_5388_:
{
return v___x_5389_;
}
}
}
}
v___jp_5392_:
{
lean_object* v___x_5395_; 
v___x_5395_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v___y_5393_, v_externalKernels_5394_);
if (lean_obj_tag(v___x_5395_) == 0)
{
lean_object* v_a_5396_; lean_object* v_a_5397_; 
v_a_5396_ = lean_ctor_get(v___x_5395_, 0);
lean_inc(v_a_5396_);
lean_dec_ref_known(v___x_5395_, 1);
v_a_5397_ = lean_ctor_get(v_a_5396_, 0);
lean_inc(v_a_5397_);
lean_dec(v_a_5396_);
v___y_5379_ = v_externalKernels_5394_;
v_a_5380_ = v_a_5397_;
goto v___jp_5378_;
}
else
{
lean_object* v_a_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5405_; 
lean_dec(v_externalKernels_5394_);
v_a_5398_ = lean_ctor_get(v___x_5395_, 0);
v_isSharedCheck_5405_ = !lean_is_exclusive(v___x_5395_);
if (v_isSharedCheck_5405_ == 0)
{
v___x_5400_ = v___x_5395_;
v_isShared_5401_ = v_isSharedCheck_5405_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_a_5398_);
lean_dec(v___x_5395_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5405_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
lean_object* v___x_5403_; 
if (v_isShared_5401_ == 0)
{
v___x_5403_ = v___x_5400_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v_a_5398_);
v___x_5403_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
return v___x_5403_;
}
}
}
}
v___jp_5406_:
{
lean_object* v_fst_5411_; 
v_fst_5411_ = lean_ctor_get(v_a_5410_, 0);
lean_inc(v_fst_5411_);
lean_dec_ref(v_a_5410_);
if (lean_obj_tag(v_fst_5411_) == 0)
{
if (v___y_5407_ == 0)
{
v___y_5393_ = v___y_5408_;
v_externalKernels_5394_ = v___y_5409_;
goto v___jp_5392_;
}
else
{
lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; 
v___x_5412_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__4));
v___x_5413_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0));
v___x_5414_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v___x_5412_, v___x_5413_, v___y_5409_);
v___y_5393_ = v___y_5408_;
v_externalKernels_5394_ = v___x_5414_;
goto v___jp_5392_;
}
}
else
{
lean_object* v_val_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5422_; 
lean_dec(v___y_5409_);
lean_dec_ref(v___y_5408_);
v_val_5415_ = lean_ctor_get(v_fst_5411_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v_fst_5411_);
if (v_isSharedCheck_5422_ == 0)
{
v___x_5417_ = v_fst_5411_;
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_val_5415_);
lean_dec(v_fst_5411_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5420_; 
if (v_isShared_5418_ == 0)
{
lean_ctor_set_tag(v___x_5417_, 0);
v___x_5420_ = v___x_5417_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v_val_5415_);
v___x_5420_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
return v___x_5420_;
}
}
}
}
v___jp_5423_:
{
lean_object* v___x_5426_; lean_object* v___x_5427_; 
v___x_5426_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_5427_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v___x_5426_, v___y_5425_);
if (lean_obj_tag(v___x_5427_) == 0)
{
lean_object* v_a_5428_; lean_object* v_a_5429_; 
v_a_5428_ = lean_ctor_get(v___x_5427_, 0);
lean_inc(v_a_5428_);
lean_dec_ref_known(v___x_5427_, 1);
v_a_5429_ = lean_ctor_get(v_a_5428_, 0);
lean_inc(v_a_5429_);
lean_dec(v_a_5428_);
v___y_5407_ = v___y_5424_;
v___y_5408_ = v___x_5426_;
v___y_5409_ = v___y_5425_;
v_a_5410_ = v_a_5429_;
goto v___jp_5406_;
}
else
{
lean_object* v_a_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5437_; 
lean_dec(v___y_5425_);
v_a_5430_ = lean_ctor_get(v___x_5427_, 0);
v_isSharedCheck_5437_ = !lean_is_exclusive(v___x_5427_);
if (v_isSharedCheck_5437_ == 0)
{
v___x_5432_ = v___x_5427_;
v_isShared_5433_ = v_isSharedCheck_5437_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_a_5430_);
lean_dec(v___x_5427_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5437_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
lean_object* v___x_5435_; 
if (v_isShared_5433_ == 0)
{
v___x_5435_ = v___x_5432_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v_a_5430_);
v___x_5435_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
return v___x_5435_;
}
}
}
}
v___jp_5440_:
{
if (lean_obj_tag(v_enable__nanoda_x3f_5438_) == 0)
{
uint8_t v___x_5442_; 
v___x_5442_ = 0;
v___y_5424_ = v___x_5442_;
v___y_5425_ = v___y_5441_;
goto v___jp_5423_;
}
else
{
lean_object* v_val_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5471_; 
v_val_5443_ = lean_ctor_get(v_enable__nanoda_x3f_5438_, 0);
v_isSharedCheck_5471_ = !lean_is_exclusive(v_enable__nanoda_x3f_5438_);
if (v_isSharedCheck_5471_ == 0)
{
v___x_5445_ = v_enable__nanoda_x3f_5438_;
v_isShared_5446_ = v_isSharedCheck_5471_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_val_5443_);
lean_dec(v_enable__nanoda_x3f_5438_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5471_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
uint8_t v___x_5447_; 
v___x_5447_ = lean_unbox(v_val_5443_);
if (v___x_5447_ == 0)
{
uint8_t v___x_5448_; 
lean_del_object(v___x_5445_);
v___x_5448_ = lean_unbox(v_val_5443_);
lean_dec(v_val_5443_);
v___y_5424_ = v___x_5448_;
v___y_5425_ = v___y_5441_;
goto v___jp_5423_;
}
else
{
if (lean_obj_tag(v___y_5441_) == 0)
{
lean_object* v___x_5449_; lean_object* v___x_5450_; 
lean_dec_ref_known(v___y_5441_, 5);
lean_dec(v_val_5443_);
v___x_5449_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__1));
v___x_5450_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5449_);
if (lean_obj_tag(v___x_5450_) == 0)
{
lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5461_; 
v_a_5451_ = lean_ctor_get(v___x_5450_, 0);
v_isSharedCheck_5461_ = !lean_is_exclusive(v___x_5450_);
if (v_isSharedCheck_5461_ == 0)
{
v___x_5453_ = v___x_5450_;
v_isShared_5454_ = v_isSharedCheck_5461_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_dec(v___x_5450_);
v___x_5453_ = lean_box(0);
v_isShared_5454_ = v_isSharedCheck_5461_;
goto v_resetjp_5452_;
}
v_resetjp_5452_:
{
lean_object* v___x_5456_; 
if (v_isShared_5446_ == 0)
{
lean_ctor_set_tag(v___x_5445_, 0);
lean_ctor_set(v___x_5445_, 0, v_a_5451_);
v___x_5456_ = v___x_5445_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_a_5451_);
v___x_5456_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
lean_object* v___x_5458_; 
if (v_isShared_5454_ == 0)
{
lean_ctor_set(v___x_5453_, 0, v___x_5456_);
v___x_5458_ = v___x_5453_;
goto v_reusejp_5457_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v___x_5456_);
v___x_5458_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5457_;
}
v_reusejp_5457_:
{
return v___x_5458_;
}
}
}
}
else
{
lean_object* v_a_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5469_; 
lean_del_object(v___x_5445_);
v_a_5462_ = lean_ctor_get(v___x_5450_, 0);
v_isSharedCheck_5469_ = !lean_is_exclusive(v___x_5450_);
if (v_isSharedCheck_5469_ == 0)
{
v___x_5464_ = v___x_5450_;
v_isShared_5465_ = v_isSharedCheck_5469_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_a_5462_);
lean_dec(v___x_5450_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5469_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5467_; 
if (v_isShared_5465_ == 0)
{
v___x_5467_ = v___x_5464_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5468_; 
v_reuseFailAlloc_5468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_a_5462_);
v___x_5467_ = v_reuseFailAlloc_5468_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
return v___x_5467_;
}
}
}
}
else
{
uint8_t v___x_5470_; 
lean_del_object(v___x_5445_);
v___x_5470_ = lean_unbox(v_val_5443_);
lean_dec(v_val_5443_);
v___y_5424_ = v___x_5470_;
v___y_5425_ = v___y_5441_;
goto v___jp_5423_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___boxed(lean_object* v_cfg_5474_, lean_object* v_a_5475_){
_start:
{
lean_object* v_res_5476_; 
v_res_5476_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v_cfg_5474_);
return v_res_5476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(lean_object* v_00_u03b2_5477_, lean_object* v_k_5478_, lean_object* v_v_5479_, lean_object* v_t_5480_, lean_object* v_hl_5481_){
_start:
{
lean_object* v___x_5482_; 
v___x_5482_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_5478_, v_v_5479_, v_t_5480_);
return v___x_5482_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(lean_object* v_a_5500_, lean_object* v_a_5501_){
_start:
{
if (lean_obj_tag(v_a_5500_) == 0)
{
lean_object* v___x_5502_; 
v___x_5502_ = l_List_reverse___redArg(v_a_5501_);
return v___x_5502_;
}
else
{
lean_object* v_head_5503_; lean_object* v_tail_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5515_; 
v_head_5503_ = lean_ctor_get(v_a_5500_, 0);
v_tail_5504_ = lean_ctor_get(v_a_5500_, 1);
v_isSharedCheck_5515_ = !lean_is_exclusive(v_a_5500_);
if (v_isSharedCheck_5515_ == 0)
{
v___x_5506_ = v_a_5500_;
v_isShared_5507_ = v_isSharedCheck_5515_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_tail_5504_);
lean_inc(v_head_5503_);
lean_dec(v_a_5500_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5515_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v_fst_5508_; uint8_t v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5512_; 
v_fst_5508_ = lean_ctor_get(v_head_5503_, 0);
lean_inc(v_fst_5508_);
lean_dec(v_head_5503_);
v___x_5509_ = 1;
v___x_5510_ = l_Lean_Name_toString(v_fst_5508_, v___x_5509_);
if (v_isShared_5507_ == 0)
{
lean_ctor_set(v___x_5506_, 1, v_a_5501_);
lean_ctor_set(v___x_5506_, 0, v___x_5510_);
v___x_5512_ = v___x_5506_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v___x_5510_);
lean_ctor_set(v_reuseFailAlloc_5514_, 1, v_a_5501_);
v___x_5512_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
v_a_5500_ = v_tail_5504_;
v_a_5501_ = v___x_5512_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(lean_object* v_as_5516_, size_t v_i_5517_, size_t v_stop_5518_, lean_object* v_b_5519_){
_start:
{
lean_object* v___y_5521_; uint8_t v___x_5525_; 
v___x_5525_ = lean_usize_dec_eq(v_i_5517_, v_stop_5518_);
if (v___x_5525_ == 0)
{
lean_object* v___x_5526_; lean_object* v_fst_5527_; lean_object* v___x_5528_; uint8_t v___x_5529_; 
v___x_5526_ = lean_array_uget_borrowed(v_as_5516_, v_i_5517_);
v_fst_5527_ = lean_ctor_get(v___x_5526_, 0);
v___x_5528_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms));
v___x_5529_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v___x_5528_, v_fst_5527_);
if (v___x_5529_ == 0)
{
lean_object* v___x_5530_; 
lean_inc(v___x_5526_);
v___x_5530_ = lean_array_push(v_b_5519_, v___x_5526_);
v___y_5521_ = v___x_5530_;
goto v___jp_5520_;
}
else
{
v___y_5521_ = v_b_5519_;
goto v___jp_5520_;
}
}
else
{
return v_b_5519_;
}
v___jp_5520_:
{
size_t v___x_5522_; size_t v___x_5523_; 
v___x_5522_ = ((size_t)1ULL);
v___x_5523_ = lean_usize_add(v_i_5517_, v___x_5522_);
v_i_5517_ = v___x_5523_;
v_b_5519_ = v___y_5521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1___boxed(lean_object* v_as_5531_, lean_object* v_i_5532_, lean_object* v_stop_5533_, lean_object* v_b_5534_){
_start:
{
size_t v_i_boxed_5535_; size_t v_stop_boxed_5536_; lean_object* v_res_5537_; 
v_i_boxed_5535_ = lean_unbox_usize(v_i_5532_);
lean_dec(v_i_5532_);
v_stop_boxed_5536_ = lean_unbox_usize(v_stop_5533_);
lean_dec(v_stop_5533_);
v_res_5537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_as_5531_, v_i_boxed_5535_, v_stop_boxed_5536_, v_b_5534_);
lean_dec_ref(v_as_5531_);
return v_res_5537_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(lean_object* v_a_5540_, lean_object* v_a_5541_){
_start:
{
if (lean_obj_tag(v_a_5540_) == 0)
{
lean_object* v___x_5542_; 
v___x_5542_ = l_List_reverse___redArg(v_a_5541_);
return v___x_5542_;
}
else
{
lean_object* v_head_5543_; lean_object* v_tail_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5564_; 
v_head_5543_ = lean_ctor_get(v_a_5540_, 0);
v_tail_5544_ = lean_ctor_get(v_a_5540_, 1);
v_isSharedCheck_5564_ = !lean_is_exclusive(v_a_5540_);
if (v_isSharedCheck_5564_ == 0)
{
v___x_5546_ = v_a_5540_;
v_isShared_5547_ = v_isSharedCheck_5564_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_tail_5544_);
lean_inc(v_head_5543_);
lean_dec(v_a_5540_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5564_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v_fst_5548_; lean_object* v_snd_5549_; lean_object* v___x_5550_; uint8_t v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5561_; 
v_fst_5548_ = lean_ctor_get(v_head_5543_, 0);
lean_inc(v_fst_5548_);
v_snd_5549_ = lean_ctor_get(v_head_5543_, 1);
lean_inc(v_snd_5549_);
lean_dec(v_head_5543_);
v___x_5550_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__0));
v___x_5551_ = 1;
v___x_5552_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_5548_, v___x_5551_);
v___x_5553_ = lean_string_append(v___x_5550_, v___x_5552_);
lean_dec_ref(v___x_5552_);
v___x_5554_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__1));
v___x_5555_ = lean_string_append(v___x_5553_, v___x_5554_);
v___x_5556_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_snd_5549_, v___x_5551_);
v___x_5557_ = lean_string_append(v___x_5555_, v___x_5556_);
lean_dec_ref(v___x_5556_);
v___x_5558_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_5559_ = lean_string_append(v___x_5557_, v___x_5558_);
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 1, v_a_5541_);
lean_ctor_set(v___x_5546_, 0, v___x_5559_);
v___x_5561_ = v___x_5546_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v___x_5559_);
lean_ctor_set(v_reuseFailAlloc_5563_, 1, v_a_5541_);
v___x_5561_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
v_a_5540_ = v_tail_5544_;
v_a_5541_ = v___x_5561_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(lean_object* v_exported_5570_){
_start:
{
lean_object* v___y_5573_; lean_object* v_used_5586_; lean_object* v___x_5599_; lean_object* v___x_5600_; uint8_t v___x_5601_; 
v_used_5586_ = l_Lake_Check_usedAxioms(v_exported_5570_);
v___x_5599_ = lean_array_get_size(v_used_5586_);
v___x_5600_ = lean_unsigned_to_nat(0u);
v___x_5601_ = lean_nat_dec_eq(v___x_5599_, v___x_5600_);
if (v___x_5601_ == 0)
{
lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; 
v___x_5602_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__2));
v___x_5603_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0));
lean_inc_ref(v_used_5586_);
v___x_5604_ = lean_array_to_list(v_used_5586_);
v___x_5605_ = lean_box(0);
v___x_5606_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(v___x_5604_, v___x_5605_);
v___x_5607_ = l_String_intercalate(v___x_5603_, v___x_5606_);
v___x_5608_ = lean_string_append(v___x_5602_, v___x_5607_);
lean_dec_ref(v___x_5607_);
v___x_5609_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_5608_);
if (lean_obj_tag(v___x_5609_) == 0)
{
lean_dec_ref_known(v___x_5609_, 1);
goto v___jp_5587_;
}
else
{
lean_dec_ref(v_used_5586_);
return v___x_5609_;
}
}
else
{
lean_object* v___x_5610_; lean_object* v___x_5611_; 
v___x_5610_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__3));
v___x_5611_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_5610_);
if (lean_obj_tag(v___x_5611_) == 0)
{
lean_dec_ref_known(v___x_5611_, 1);
goto v___jp_5587_;
}
else
{
lean_dec_ref(v_used_5586_);
return v___x_5611_;
}
}
v___jp_5572_:
{
lean_object* v___x_5574_; lean_object* v___x_5575_; uint8_t v___x_5576_; 
v___x_5574_ = lean_array_get_size(v___y_5573_);
v___x_5575_ = lean_unsigned_to_nat(0u);
v___x_5576_ = lean_nat_dec_eq(v___x_5574_, v___x_5575_);
if (v___x_5576_ == 0)
{
lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; 
v___x_5577_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__0));
v___x_5578_ = lean_array_to_list(v___y_5573_);
v___x_5579_ = lean_box(0);
v___x_5580_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(v___x_5578_, v___x_5579_);
v___x_5581_ = l_String_intercalate(v___x_5577_, v___x_5580_);
v___x_5582_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5581_);
v___x_5583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5583_, 0, v___x_5582_);
return v___x_5583_;
}
else
{
lean_object* v___x_5584_; lean_object* v___x_5585_; 
lean_dec_ref(v___y_5573_);
v___x_5584_ = lean_box(0);
v___x_5585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5585_, 0, v___x_5584_);
return v___x_5585_;
}
}
v___jp_5587_:
{
lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; uint8_t v___x_5591_; 
v___x_5588_ = lean_unsigned_to_nat(0u);
v___x_5589_ = lean_array_get_size(v_used_5586_);
v___x_5590_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__1));
v___x_5591_ = lean_nat_dec_lt(v___x_5588_, v___x_5589_);
if (v___x_5591_ == 0)
{
lean_dec_ref(v_used_5586_);
v___y_5573_ = v___x_5590_;
goto v___jp_5572_;
}
else
{
uint8_t v___x_5592_; 
v___x_5592_ = lean_nat_dec_le(v___x_5589_, v___x_5589_);
if (v___x_5592_ == 0)
{
if (v___x_5591_ == 0)
{
lean_dec_ref(v_used_5586_);
v___y_5573_ = v___x_5590_;
goto v___jp_5572_;
}
else
{
size_t v___x_5593_; size_t v___x_5594_; lean_object* v___x_5595_; 
v___x_5593_ = ((size_t)0ULL);
v___x_5594_ = lean_usize_of_nat(v___x_5589_);
v___x_5595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_used_5586_, v___x_5593_, v___x_5594_, v___x_5590_);
lean_dec_ref(v_used_5586_);
v___y_5573_ = v___x_5595_;
goto v___jp_5572_;
}
}
else
{
size_t v___x_5596_; size_t v___x_5597_; lean_object* v___x_5598_; 
v___x_5596_ = ((size_t)0ULL);
v___x_5597_ = lean_usize_of_nat(v___x_5589_);
v___x_5598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_used_5586_, v___x_5596_, v___x_5597_, v___x_5590_);
lean_dec_ref(v_used_5586_);
v___y_5573_ = v___x_5598_;
goto v___jp_5572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___boxed(lean_object* v_exported_5612_, lean_object* v_a_5613_){
_start:
{
lean_object* v_res_5614_; 
v_res_5614_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_5612_);
return v_res_5614_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(lean_object* v_exported_5615_, lean_object* v_a_5616_){
_start:
{
lean_object* v___x_5618_; 
v___x_5618_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_5615_);
return v___x_5618_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___boxed(lean_object* v_exported_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_){
_start:
{
lean_object* v_res_5622_; 
v_res_5622_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(v_exported_5619_, v_a_5620_);
lean_dec_ref(v_a_5620_);
return v_res_5622_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(lean_object* v_exportPath_5623_, lean_object* v___y_5624_){
_start:
{
lean_object* v___x_5626_; 
lean_inc_ref(v_exportPath_5623_);
v___x_5626_ = l___private_Lake_CLI_Check_0__Lake_Check_runKernels(v_exportPath_5623_, v___y_5624_);
if (lean_obj_tag(v___x_5626_) == 0)
{
uint8_t v___x_5627_; lean_object* v___x_5628_; 
lean_dec_ref_known(v___x_5626_, 1);
v___x_5627_ = 0;
v___x_5628_ = lean_io_prim_handle_mk(v_exportPath_5623_, v___x_5627_);
lean_dec_ref(v_exportPath_5623_);
if (lean_obj_tag(v___x_5628_) == 0)
{
lean_object* v_a_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; 
v_a_5629_ = lean_ctor_get(v___x_5628_, 0);
lean_inc(v_a_5629_);
lean_dec_ref_known(v___x_5628_, 1);
v___x_5630_ = lean_stream_of_handle(v_a_5629_);
v___x_5631_ = l_LeanExport_parseStream(v___x_5630_);
if (lean_obj_tag(v___x_5631_) == 0)
{
lean_object* v_a_5632_; lean_object* v___x_5633_; 
v_a_5632_ = lean_ctor_get(v___x_5631_, 0);
lean_inc(v_a_5632_);
lean_dec_ref_known(v___x_5631_, 1);
v___x_5633_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_a_5632_);
return v___x_5633_;
}
else
{
lean_object* v_a_5634_; lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5641_; 
v_a_5634_ = lean_ctor_get(v___x_5631_, 0);
v_isSharedCheck_5641_ = !lean_is_exclusive(v___x_5631_);
if (v_isSharedCheck_5641_ == 0)
{
v___x_5636_ = v___x_5631_;
v_isShared_5637_ = v_isSharedCheck_5641_;
goto v_resetjp_5635_;
}
else
{
lean_inc(v_a_5634_);
lean_dec(v___x_5631_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5641_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v___x_5639_; 
if (v_isShared_5637_ == 0)
{
v___x_5639_ = v___x_5636_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v_a_5634_);
v___x_5639_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
return v___x_5639_;
}
}
}
}
else
{
lean_object* v_a_5642_; lean_object* v___x_5644_; uint8_t v_isShared_5645_; uint8_t v_isSharedCheck_5649_; 
v_a_5642_ = lean_ctor_get(v___x_5628_, 0);
v_isSharedCheck_5649_ = !lean_is_exclusive(v___x_5628_);
if (v_isSharedCheck_5649_ == 0)
{
v___x_5644_ = v___x_5628_;
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
else
{
lean_inc(v_a_5642_);
lean_dec(v___x_5628_);
v___x_5644_ = lean_box(0);
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
v_resetjp_5643_:
{
lean_object* v___x_5647_; 
if (v_isShared_5645_ == 0)
{
v___x_5647_ = v___x_5644_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_a_5642_);
v___x_5647_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
return v___x_5647_;
}
}
}
}
else
{
lean_dec_ref(v_exportPath_5623_);
return v___x_5626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0___boxed(lean_object* v_exportPath_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_){
_start:
{
lean_object* v_res_5653_; 
v_res_5653_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(v_exportPath_5650_, v___y_5651_);
lean_dec_ref(v___y_5651_);
return v_res_5653_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(lean_object* v_m_5654_, uint8_t v_a_5655_){
_start:
{
lean_object* v_buckets_5656_; lean_object* v___x_5657_; uint64_t v___x_5658_; uint64_t v___x_5659_; uint64_t v___x_5660_; uint64_t v_fold_5661_; uint64_t v___x_5662_; uint64_t v___x_5663_; uint64_t v___x_5664_; size_t v___x_5665_; size_t v___x_5666_; size_t v___x_5667_; size_t v___x_5668_; size_t v___x_5669_; lean_object* v___x_5670_; uint8_t v___x_5671_; 
v_buckets_5656_ = lean_ctor_get(v_m_5654_, 1);
v___x_5657_ = lean_array_get_size(v_buckets_5656_);
v___x_5658_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_a_5655_);
v___x_5659_ = 32ULL;
v___x_5660_ = lean_uint64_shift_right(v___x_5658_, v___x_5659_);
v_fold_5661_ = lean_uint64_xor(v___x_5658_, v___x_5660_);
v___x_5662_ = 16ULL;
v___x_5663_ = lean_uint64_shift_right(v_fold_5661_, v___x_5662_);
v___x_5664_ = lean_uint64_xor(v_fold_5661_, v___x_5663_);
v___x_5665_ = lean_uint64_to_usize(v___x_5664_);
v___x_5666_ = lean_usize_of_nat(v___x_5657_);
v___x_5667_ = ((size_t)1ULL);
v___x_5668_ = lean_usize_sub(v___x_5666_, v___x_5667_);
v___x_5669_ = lean_usize_land(v___x_5665_, v___x_5668_);
v___x_5670_ = lean_array_uget_borrowed(v_buckets_5656_, v___x_5669_);
v___x_5671_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_5655_, v___x_5670_);
return v___x_5671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg___boxed(lean_object* v_m_5672_, lean_object* v_a_5673_){
_start:
{
uint8_t v_a_boxed_5674_; uint8_t v_res_5675_; lean_object* v_r_5676_; 
v_a_boxed_5674_ = lean_unbox(v_a_5673_);
v_res_5675_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_m_5672_, v_a_boxed_5674_);
lean_dec_ref(v_m_5672_);
v_r_5676_ = lean_box(v_res_5675_);
return v_r_5676_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject(lean_object* v_a_5678_){
_start:
{
lean_object* v_moduleStore_5680_; lean_object* v___f_5681_; uint8_t v___x_5682_; uint8_t v___x_5683_; 
v_moduleStore_5680_ = lean_ctor_get(v_a_5678_, 17);
v___f_5681_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkProject___closed__0));
v___x_5682_ = 0;
v___x_5683_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_moduleStore_5680_, v___x_5682_);
if (v___x_5683_ == 0)
{
lean_object* v___x_5684_; 
v___x_5684_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_5678_);
if (lean_obj_tag(v___x_5684_) == 0)
{
lean_object* v___x_5685_; 
lean_dec_ref_known(v___x_5684_, 1);
v___x_5685_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v___f_5681_, v_a_5678_);
return v___x_5685_;
}
else
{
return v___x_5684_;
}
}
else
{
lean_object* v___x_5686_; 
v___x_5686_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v___f_5681_, v_a_5678_);
return v___x_5686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___boxed(lean_object* v_a_5687_, lean_object* v_a_5688_){
_start:
{
lean_object* v_res_5689_; 
v_res_5689_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v_a_5687_);
lean_dec_ref(v_a_5687_);
return v_res_5689_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0(lean_object* v_00_u03b2_5690_, lean_object* v_m_5691_, uint8_t v_a_5692_){
_start:
{
uint8_t v___x_5693_; 
v___x_5693_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_m_5691_, v_a_5692_);
return v___x_5693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___boxed(lean_object* v_00_u03b2_5694_, lean_object* v_m_5695_, lean_object* v_a_5696_){
_start:
{
uint8_t v_a_boxed_5697_; uint8_t v_res_5698_; lean_object* v_r_5699_; 
v_a_boxed_5697_ = lean_unbox(v_a_5696_);
v_res_5698_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0(v_00_u03b2_5694_, v_m_5695_, v_a_boxed_5697_);
lean_dec_ref(v_m_5695_);
v_r_5699_ = lean_box(v_res_5698_);
return v_r_5699_;
}
}
static lean_object* _init_l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_5700_; lean_object* v___x_5701_; 
v___x_5700_ = 0;
v___x_5701_ = lean_box_uint32(v___x_5700_);
return v___x_5701_;
}
}
static lean_object* _init_l_Lake_Check_runComparator___lam__0___closed__0(void){
_start:
{
lean_object* v___x_5702_; lean_object* v___x_5703_; 
v___x_5702_ = l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1;
v___x_5703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5703_, 0, v___x_5702_);
return v___x_5703_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___lam__0(lean_object* v_____r_5704_){
_start:
{
lean_object* v___x_5706_; lean_object* v___x_5707_; 
v___x_5706_ = lean_obj_once(&l_Lake_Check_runComparator___lam__0___closed__0, &l_Lake_Check_runComparator___lam__0___closed__0_once, _init_l_Lake_Check_runComparator___lam__0___closed__0);
v___x_5707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5707_, 0, v___x_5706_);
return v___x_5707_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___lam__0___boxed(lean_object* v_____r_5708_, lean_object* v___y_5709_){
_start:
{
lean_object* v_res_5710_; 
v_res_5710_ = l_Lake_Check_runComparator___lam__0(v_____r_5708_);
return v_res_5710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(size_t v_sz_5711_, size_t v_i_5712_, lean_object* v_bs_5713_){
_start:
{
uint8_t v___x_5714_; 
v___x_5714_ = lean_usize_dec_lt(v_i_5712_, v_sz_5711_);
if (v___x_5714_ == 0)
{
return v_bs_5713_;
}
else
{
lean_object* v_v_5715_; lean_object* v___x_5716_; lean_object* v_bs_x27_5717_; lean_object* v___x_5718_; size_t v___x_5719_; size_t v___x_5720_; lean_object* v___x_5721_; 
v_v_5715_ = lean_array_uget(v_bs_5713_, v_i_5712_);
v___x_5716_ = lean_unsigned_to_nat(0u);
v_bs_x27_5717_ = lean_array_uset(v_bs_5713_, v_i_5712_, v___x_5716_);
v___x_5718_ = l_String_toName(v_v_5715_);
v___x_5719_ = ((size_t)1ULL);
v___x_5720_ = lean_usize_add(v_i_5712_, v___x_5719_);
v___x_5721_ = lean_array_uset(v_bs_x27_5717_, v_i_5712_, v___x_5718_);
v_i_5712_ = v___x_5720_;
v_bs_5713_ = v___x_5721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0___boxed(lean_object* v_sz_5723_, lean_object* v_i_5724_, lean_object* v_bs_5725_){
_start:
{
size_t v_sz_boxed_5726_; size_t v_i_boxed_5727_; lean_object* v_res_5728_; 
v_sz_boxed_5726_ = lean_unbox_usize(v_sz_5723_);
lean_dec(v_sz_5723_);
v_i_boxed_5727_ = lean_unbox_usize(v_i_5724_);
lean_dec(v_i_5724_);
v_res_5728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_boxed_5726_, v_i_boxed_5727_, v_bs_5725_);
return v_res_5728_;
}
}
static lean_object* _init_l_Lake_Check_runComparator___boxed__const__1(void){
_start:
{
uint32_t v___x_5737_; lean_object* v___x_5738_; 
v___x_5737_ = 1;
v___x_5738_ = lean_box_uint32(v___x_5737_);
return v___x_5738_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator(lean_object* v_configFile_x3f_5739_, lean_object* v_challengeFromExport_x3f_5740_, lean_object* v_solutionFromExport_x3f_5741_, uint8_t v_paranoid_5742_, uint8_t v_inadvisablyNoSandbox_5743_, lean_object* v_lean_5744_, lean_object* v_lake_5745_, lean_object* v_projectDir_5746_){
_start:
{
lean_object* v_a_5749_; lean_object* v___y_5772_; lean_object* v___y_5783_; lean_object* v_a_5784_; lean_object* v___x_5791_; lean_object* v___x_5792_; uint8_t v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; uint8_t v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; 
v___x_5791_ = ((lean_object*)(l_Lake_Check_runComparator___closed__2));
v___x_5792_ = ((lean_object*)(l_Lake_Check_runComparator___closed__3));
v___x_5793_ = 2;
v___x_5794_ = lean_box(v___x_5793_);
v___x_5795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5795_, 0, v___x_5794_);
lean_ctor_set(v___x_5795_, 1, v_challengeFromExport_x3f_5740_);
v___x_5796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5796_, 0, v___x_5792_);
lean_ctor_set(v___x_5796_, 1, v___x_5795_);
v___x_5797_ = ((lean_object*)(l_Lake_Check_runComparator___closed__4));
v___x_5798_ = 1;
v___x_5799_ = lean_box(v___x_5798_);
v___x_5800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5800_, 0, v___x_5799_);
lean_ctor_set(v___x_5800_, 1, v_solutionFromExport_x3f_5741_);
v___x_5801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5801_, 0, v___x_5797_);
lean_ctor_set(v___x_5801_, 1, v___x_5800_);
v___x_5802_ = lean_unsigned_to_nat(2u);
v___x_5803_ = lean_mk_empty_array_with_capacity(v___x_5802_);
v___x_5804_ = lean_array_push(v___x_5803_, v___x_5796_);
v___x_5805_ = lean_array_push(v___x_5804_, v___x_5801_);
v___x_5806_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(v___x_5791_, v___x_5805_);
lean_dec_ref(v___x_5805_);
if (lean_obj_tag(v___x_5806_) == 0)
{
lean_object* v_a_5807_; lean_object* v___x_5809_; uint8_t v_isShared_5810_; uint8_t v_isSharedCheck_6000_; 
v_a_5807_ = lean_ctor_get(v___x_5806_, 0);
v_isSharedCheck_6000_ = !lean_is_exclusive(v___x_5806_);
if (v_isSharedCheck_6000_ == 0)
{
v___x_5809_ = v___x_5806_;
v_isShared_5810_ = v_isSharedCheck_6000_;
goto v_resetjp_5808_;
}
else
{
lean_inc(v_a_5807_);
lean_dec(v___x_5806_);
v___x_5809_ = lean_box(0);
v_isShared_5810_ = v_isSharedCheck_6000_;
goto v_resetjp_5808_;
}
v_resetjp_5808_:
{
if (lean_obj_tag(v_a_5807_) == 0)
{
lean_object* v_a_5811_; lean_object* v___x_5813_; 
lean_dec_ref(v_projectDir_5746_);
lean_dec_ref(v_lean_5744_);
v_a_5811_ = lean_ctor_get(v_a_5807_, 0);
lean_inc(v_a_5811_);
lean_dec_ref_known(v_a_5807_, 1);
if (v_isShared_5810_ == 0)
{
lean_ctor_set(v___x_5809_, 0, v_a_5811_);
v___x_5813_ = v___x_5809_;
goto v_reusejp_5812_;
}
else
{
lean_object* v_reuseFailAlloc_5814_; 
v_reuseFailAlloc_5814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5814_, 0, v_a_5811_);
v___x_5813_ = v_reuseFailAlloc_5814_;
goto v_reusejp_5812_;
}
v_reusejp_5812_:
{
return v___x_5813_;
}
}
else
{
lean_object* v_a_5815_; lean_object* v___x_5816_; 
lean_del_object(v___x_5809_);
v_a_5815_ = lean_ctor_get(v_a_5807_, 0);
lean_inc_n(v_a_5815_, 2);
lean_dec_ref_known(v_a_5807_, 1);
v___x_5816_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_5791_, v_paranoid_5742_, v_inadvisablyNoSandbox_5743_, v_lean_5744_, v_lake_5745_, v_projectDir_5746_, v_a_5815_);
if (lean_obj_tag(v___x_5816_) == 0)
{
lean_object* v_a_5817_; lean_object* v___x_5819_; uint8_t v_isShared_5820_; uint8_t v_isSharedCheck_5991_; 
v_a_5817_ = lean_ctor_get(v___x_5816_, 0);
v_isSharedCheck_5991_ = !lean_is_exclusive(v___x_5816_);
if (v_isSharedCheck_5991_ == 0)
{
v___x_5819_ = v___x_5816_;
v_isShared_5820_ = v_isSharedCheck_5991_;
goto v_resetjp_5818_;
}
else
{
lean_inc(v_a_5817_);
lean_dec(v___x_5816_);
v___x_5819_ = lean_box(0);
v_isShared_5820_ = v_isSharedCheck_5991_;
goto v_resetjp_5818_;
}
v_resetjp_5818_:
{
if (lean_obj_tag(v_a_5817_) == 0)
{
lean_object* v_a_5821_; lean_object* v___x_5823_; 
lean_dec(v_a_5815_);
v_a_5821_ = lean_ctor_get(v_a_5817_, 0);
lean_inc(v_a_5821_);
lean_dec_ref_known(v_a_5817_, 1);
if (v_isShared_5820_ == 0)
{
lean_ctor_set(v___x_5819_, 0, v_a_5821_);
v___x_5823_ = v___x_5819_;
goto v_reusejp_5822_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v_a_5821_);
v___x_5823_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5822_;
}
v_reusejp_5822_:
{
return v___x_5823_;
}
}
else
{
lean_object* v_a_5825_; size_t v___y_5827_; uint8_t v___y_5828_; lean_object* v___y_5829_; lean_object* v___y_5830_; lean_object* v___y_5831_; lean_object* v___y_5832_; lean_object* v___y_5833_; lean_object* v___y_5834_; size_t v___y_5879_; lean_object* v___y_5880_; lean_object* v___y_5881_; lean_object* v___y_5882_; lean_object* v___y_5883_; lean_object* v___y_5884_; lean_object* v___y_5885_; uint8_t v___y_5886_; size_t v___y_5907_; lean_object* v___y_5908_; lean_object* v___y_5909_; lean_object* v___y_5910_; uint8_t v___y_5911_; lean_object* v___y_5912_; lean_object* v___y_5913_; lean_object* v___y_5914_; uint8_t v___y_5915_; size_t v___y_5918_; lean_object* v___y_5919_; lean_object* v___y_5920_; lean_object* v___y_5921_; lean_object* v___y_5922_; lean_object* v___y_5923_; lean_object* v___y_5924_; uint8_t v___y_5925_; size_t v___y_5948_; lean_object* v___y_5949_; lean_object* v___y_5950_; lean_object* v___y_5951_; lean_object* v___y_5952_; lean_object* v___y_5953_; lean_object* v___y_5954_; lean_object* v___y_5965_; 
lean_del_object(v___x_5819_);
v_a_5825_ = lean_ctor_get(v_a_5817_, 0);
lean_inc(v_a_5825_);
lean_dec_ref_known(v_a_5817_, 1);
if (lean_obj_tag(v_configFile_x3f_5739_) == 0)
{
lean_object* v___x_5989_; 
v___x_5989_ = ((lean_object*)(l_Lake_Check_runComparator___closed__7));
v___y_5965_ = v___x_5989_;
goto v___jp_5964_;
}
else
{
lean_object* v_val_5990_; 
v_val_5990_ = lean_ctor_get(v_configFile_x3f_5739_, 0);
v___y_5965_ = v_val_5990_;
goto v___jp_5964_;
}
v___jp_5826_:
{
lean_object* v_projectDir_5835_; lean_object* v_leanPrefix_5836_; lean_object* v_leanPath_5837_; lean_object* v_binPath_5838_; lean_object* v_whichSandbox_5839_; lean_object* v_whichLake_5840_; lean_object* v_lakeHome_5841_; lean_object* v_whichLean4Export_5842_; lean_object* v_whichLeanChecker_5843_; lean_object* v_whichEnvBin_5844_; lean_object* v_bundledKernels_5845_; lean_object* v_moduleStore_5846_; lean_object* v___x_5848_; uint8_t v_isShared_5849_; uint8_t v_isSharedCheck_5871_; 
v_projectDir_5835_ = lean_ctor_get(v_a_5825_, 0);
v_leanPrefix_5836_ = lean_ctor_get(v_a_5825_, 6);
v_leanPath_5837_ = lean_ctor_get(v_a_5825_, 7);
v_binPath_5838_ = lean_ctor_get(v_a_5825_, 8);
v_whichSandbox_5839_ = lean_ctor_get(v_a_5825_, 9);
v_whichLake_5840_ = lean_ctor_get(v_a_5825_, 10);
v_lakeHome_5841_ = lean_ctor_get(v_a_5825_, 11);
v_whichLean4Export_5842_ = lean_ctor_get(v_a_5825_, 12);
v_whichLeanChecker_5843_ = lean_ctor_get(v_a_5825_, 13);
v_whichEnvBin_5844_ = lean_ctor_get(v_a_5825_, 14);
v_bundledKernels_5845_ = lean_ctor_get(v_a_5825_, 16);
v_moduleStore_5846_ = lean_ctor_get(v_a_5825_, 17);
v_isSharedCheck_5871_ = !lean_is_exclusive(v_a_5825_);
if (v_isSharedCheck_5871_ == 0)
{
lean_object* v_unused_5872_; lean_object* v_unused_5873_; lean_object* v_unused_5874_; lean_object* v_unused_5875_; lean_object* v_unused_5876_; lean_object* v_unused_5877_; 
v_unused_5872_ = lean_ctor_get(v_a_5825_, 15);
lean_dec(v_unused_5872_);
v_unused_5873_ = lean_ctor_get(v_a_5825_, 5);
lean_dec(v_unused_5873_);
v_unused_5874_ = lean_ctor_get(v_a_5825_, 4);
lean_dec(v_unused_5874_);
v_unused_5875_ = lean_ctor_get(v_a_5825_, 3);
lean_dec(v_unused_5875_);
v_unused_5876_ = lean_ctor_get(v_a_5825_, 2);
lean_dec(v_unused_5876_);
v_unused_5877_ = lean_ctor_get(v_a_5825_, 1);
lean_dec(v_unused_5877_);
v___x_5848_ = v_a_5825_;
v_isShared_5849_ = v_isSharedCheck_5871_;
goto v_resetjp_5847_;
}
else
{
lean_inc(v_moduleStore_5846_);
lean_inc(v_bundledKernels_5845_);
lean_inc(v_whichEnvBin_5844_);
lean_inc(v_whichLeanChecker_5843_);
lean_inc(v_whichLean4Export_5842_);
lean_inc(v_lakeHome_5841_);
lean_inc(v_whichLake_5840_);
lean_inc(v_whichSandbox_5839_);
lean_inc(v_binPath_5838_);
lean_inc(v_leanPath_5837_);
lean_inc(v_leanPrefix_5836_);
lean_inc(v_projectDir_5835_);
lean_dec(v_a_5825_);
v___x_5848_ = lean_box(0);
v_isShared_5849_ = v_isSharedCheck_5871_;
goto v_resetjp_5847_;
}
v_resetjp_5847_:
{
lean_object* v___x_5850_; lean_object* v___x_5851_; size_t v_sz_5852_; lean_object* v___x_5853_; lean_object* v___x_5855_; 
v___x_5850_ = l_String_toName(v___y_5832_);
v___x_5851_ = l_String_toName(v___y_5830_);
v_sz_5852_ = lean_array_size(v___y_5834_);
v___x_5853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_5852_, v___y_5827_, v___y_5834_);
lean_inc_ref(v_moduleStore_5846_);
lean_inc_ref(v_bundledKernels_5845_);
lean_inc(v___y_5831_);
lean_inc_ref(v_whichEnvBin_5844_);
lean_inc_ref(v_whichLeanChecker_5843_);
lean_inc_ref(v_whichLean4Export_5842_);
lean_inc_ref(v_lakeHome_5841_);
lean_inc_ref(v_whichLake_5840_);
lean_inc(v_whichSandbox_5839_);
lean_inc_ref(v_leanPrefix_5836_);
lean_inc_ref(v___x_5853_);
lean_inc_ref(v___y_5829_);
lean_inc_ref(v___y_5833_);
lean_inc(v___x_5851_);
lean_inc(v___x_5850_);
lean_inc_ref(v_projectDir_5835_);
if (v_isShared_5849_ == 0)
{
lean_ctor_set(v___x_5848_, 15, v___y_5831_);
lean_ctor_set(v___x_5848_, 5, v___x_5853_);
lean_ctor_set(v___x_5848_, 4, v___y_5829_);
lean_ctor_set(v___x_5848_, 3, v___y_5833_);
lean_ctor_set(v___x_5848_, 2, v___x_5851_);
lean_ctor_set(v___x_5848_, 1, v___x_5850_);
v___x_5855_ = v___x_5848_;
goto v_reusejp_5854_;
}
else
{
lean_object* v_reuseFailAlloc_5870_; 
v_reuseFailAlloc_5870_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_5870_, 0, v_projectDir_5835_);
lean_ctor_set(v_reuseFailAlloc_5870_, 1, v___x_5850_);
lean_ctor_set(v_reuseFailAlloc_5870_, 2, v___x_5851_);
lean_ctor_set(v_reuseFailAlloc_5870_, 3, v___y_5833_);
lean_ctor_set(v_reuseFailAlloc_5870_, 4, v___y_5829_);
lean_ctor_set(v_reuseFailAlloc_5870_, 5, v___x_5853_);
lean_ctor_set(v_reuseFailAlloc_5870_, 6, v_leanPrefix_5836_);
lean_ctor_set(v_reuseFailAlloc_5870_, 7, v_leanPath_5837_);
lean_ctor_set(v_reuseFailAlloc_5870_, 8, v_binPath_5838_);
lean_ctor_set(v_reuseFailAlloc_5870_, 9, v_whichSandbox_5839_);
lean_ctor_set(v_reuseFailAlloc_5870_, 10, v_whichLake_5840_);
lean_ctor_set(v_reuseFailAlloc_5870_, 11, v_lakeHome_5841_);
lean_ctor_set(v_reuseFailAlloc_5870_, 12, v_whichLean4Export_5842_);
lean_ctor_set(v_reuseFailAlloc_5870_, 13, v_whichLeanChecker_5843_);
lean_ctor_set(v_reuseFailAlloc_5870_, 14, v_whichEnvBin_5844_);
lean_ctor_set(v_reuseFailAlloc_5870_, 15, v___y_5831_);
lean_ctor_set(v_reuseFailAlloc_5870_, 16, v_bundledKernels_5845_);
lean_ctor_set(v_reuseFailAlloc_5870_, 17, v_moduleStore_5846_);
v___x_5855_ = v_reuseFailAlloc_5870_;
goto v_reusejp_5854_;
}
v_reusejp_5854_:
{
if (v___y_5828_ == 0)
{
lean_object* v___x_5856_; 
lean_dec_ref(v___x_5853_);
lean_dec(v___x_5851_);
lean_dec(v___x_5850_);
lean_dec_ref(v_moduleStore_5846_);
lean_dec_ref(v_bundledKernels_5845_);
lean_dec_ref(v_whichEnvBin_5844_);
lean_dec_ref(v_whichLeanChecker_5843_);
lean_dec_ref(v_whichLean4Export_5842_);
lean_dec_ref(v_lakeHome_5841_);
lean_dec_ref(v_whichLake_5840_);
lean_dec(v_whichSandbox_5839_);
lean_dec_ref(v_leanPrefix_5836_);
lean_dec_ref(v_projectDir_5835_);
lean_dec_ref(v___y_5833_);
lean_dec(v___y_5831_);
lean_dec_ref(v___y_5829_);
v___x_5856_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt(v___x_5855_);
lean_dec_ref(v___x_5855_);
if (lean_obj_tag(v___x_5856_) == 0)
{
lean_object* v_a_5857_; lean_object* v___x_5858_; 
v_a_5857_ = lean_ctor_get(v___x_5856_, 0);
lean_inc(v_a_5857_);
lean_dec_ref_known(v___x_5856_, 1);
v___x_5858_ = l_Lake_Check_runComparator___lam__0(v_a_5857_);
v___y_5772_ = v___x_5858_;
goto v___jp_5771_;
}
else
{
lean_object* v_a_5859_; 
v_a_5859_ = lean_ctor_get(v___x_5856_, 0);
lean_inc(v_a_5859_);
lean_dec_ref_known(v___x_5856_, 1);
v_a_5749_ = v_a_5859_;
goto v___jp_5748_;
}
}
else
{
lean_object* v___x_5860_; 
v___x_5860_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v___x_5855_);
lean_dec_ref(v___x_5855_);
if (lean_obj_tag(v___x_5860_) == 0)
{
lean_object* v_a_5861_; lean_object* v_fst_5862_; lean_object* v_snd_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; 
v_a_5861_ = lean_ctor_get(v___x_5860_, 0);
lean_inc(v_a_5861_);
lean_dec_ref_known(v___x_5860_, 1);
v_fst_5862_ = lean_ctor_get(v_a_5861_, 0);
lean_inc(v_fst_5862_);
v_snd_5863_ = lean_ctor_get(v_a_5861_, 1);
lean_inc(v_snd_5863_);
lean_dec(v_a_5861_);
v___x_5864_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_5864_, 0, v_projectDir_5835_);
lean_ctor_set(v___x_5864_, 1, v___x_5850_);
lean_ctor_set(v___x_5864_, 2, v___x_5851_);
lean_ctor_set(v___x_5864_, 3, v___y_5833_);
lean_ctor_set(v___x_5864_, 4, v___y_5829_);
lean_ctor_set(v___x_5864_, 5, v___x_5853_);
lean_ctor_set(v___x_5864_, 6, v_leanPrefix_5836_);
lean_ctor_set(v___x_5864_, 7, v_fst_5862_);
lean_ctor_set(v___x_5864_, 8, v_snd_5863_);
lean_ctor_set(v___x_5864_, 9, v_whichSandbox_5839_);
lean_ctor_set(v___x_5864_, 10, v_whichLake_5840_);
lean_ctor_set(v___x_5864_, 11, v_lakeHome_5841_);
lean_ctor_set(v___x_5864_, 12, v_whichLean4Export_5842_);
lean_ctor_set(v___x_5864_, 13, v_whichLeanChecker_5843_);
lean_ctor_set(v___x_5864_, 14, v_whichEnvBin_5844_);
lean_ctor_set(v___x_5864_, 15, v___y_5831_);
lean_ctor_set(v___x_5864_, 16, v_bundledKernels_5845_);
lean_ctor_set(v___x_5864_, 17, v_moduleStore_5846_);
v___x_5865_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt(v___x_5864_);
lean_dec_ref_known(v___x_5864_, 18);
if (lean_obj_tag(v___x_5865_) == 0)
{
lean_object* v_a_5866_; lean_object* v___x_5867_; 
v_a_5866_ = lean_ctor_get(v___x_5865_, 0);
lean_inc(v_a_5866_);
lean_dec_ref_known(v___x_5865_, 1);
v___x_5867_ = l_Lake_Check_runComparator___lam__0(v_a_5866_);
v___y_5772_ = v___x_5867_;
goto v___jp_5771_;
}
else
{
lean_object* v_a_5868_; 
v_a_5868_ = lean_ctor_get(v___x_5865_, 0);
lean_inc(v_a_5868_);
lean_dec_ref_known(v___x_5865_, 1);
v_a_5749_ = v_a_5868_;
goto v___jp_5748_;
}
}
else
{
lean_object* v_a_5869_; 
lean_dec_ref(v___x_5853_);
lean_dec(v___x_5851_);
lean_dec(v___x_5850_);
lean_dec_ref(v_moduleStore_5846_);
lean_dec_ref(v_bundledKernels_5845_);
lean_dec_ref(v_whichEnvBin_5844_);
lean_dec_ref(v_whichLeanChecker_5843_);
lean_dec_ref(v_whichLean4Export_5842_);
lean_dec_ref(v_lakeHome_5841_);
lean_dec_ref(v_whichLake_5840_);
lean_dec(v_whichSandbox_5839_);
lean_dec_ref(v_leanPrefix_5836_);
lean_dec_ref(v_projectDir_5835_);
lean_dec_ref(v___y_5833_);
lean_dec(v___y_5831_);
lean_dec_ref(v___y_5829_);
v_a_5869_ = lean_ctor_get(v___x_5860_, 0);
lean_inc(v_a_5869_);
lean_dec_ref_known(v___x_5860_, 1);
v_a_5749_ = v_a_5869_;
goto v___jp_5748_;
}
}
}
}
}
v___jp_5878_:
{
lean_object* v_projectDir_5887_; lean_object* v___x_5888_; 
v_projectDir_5887_ = lean_ctor_get(v_a_5825_, 0);
lean_inc_ref(v_projectDir_5887_);
v___x_5888_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_5791_, v_projectDir_5887_);
if (lean_obj_tag(v___x_5888_) == 0)
{
lean_object* v_a_5889_; lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_5897_; 
v_a_5889_ = lean_ctor_get(v___x_5888_, 0);
v_isSharedCheck_5897_ = !lean_is_exclusive(v___x_5888_);
if (v_isSharedCheck_5897_ == 0)
{
v___x_5891_ = v___x_5888_;
v_isShared_5892_ = v_isSharedCheck_5897_;
goto v_resetjp_5890_;
}
else
{
lean_inc(v_a_5889_);
lean_dec(v___x_5888_);
v___x_5891_ = lean_box(0);
v_isShared_5892_ = v_isSharedCheck_5897_;
goto v_resetjp_5890_;
}
v_resetjp_5890_:
{
if (lean_obj_tag(v_a_5889_) == 1)
{
lean_object* v_val_5893_; lean_object* v___x_5895_; 
lean_dec_ref(v___y_5885_);
lean_dec_ref(v___y_5884_);
lean_dec_ref(v___y_5883_);
lean_dec(v___y_5882_);
lean_dec_ref(v___y_5881_);
lean_dec_ref(v___y_5880_);
lean_dec(v_a_5825_);
v_val_5893_ = lean_ctor_get(v_a_5889_, 0);
lean_inc(v_val_5893_);
lean_dec_ref_known(v_a_5889_, 1);
if (v_isShared_5892_ == 0)
{
lean_ctor_set(v___x_5891_, 0, v_val_5893_);
v___x_5895_ = v___x_5891_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_5896_; 
v_reuseFailAlloc_5896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5896_, 0, v_val_5893_);
v___x_5895_ = v_reuseFailAlloc_5896_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
return v___x_5895_;
}
}
else
{
lean_del_object(v___x_5891_);
lean_dec(v_a_5889_);
v___y_5827_ = v___y_5879_;
v___y_5828_ = v___y_5886_;
v___y_5829_ = v___y_5881_;
v___y_5830_ = v___y_5880_;
v___y_5831_ = v___y_5882_;
v___y_5832_ = v___y_5883_;
v___y_5833_ = v___y_5884_;
v___y_5834_ = v___y_5885_;
goto v___jp_5826_;
}
}
}
else
{
lean_object* v_a_5898_; lean_object* v___x_5900_; uint8_t v_isShared_5901_; uint8_t v_isSharedCheck_5905_; 
lean_dec_ref(v___y_5885_);
lean_dec_ref(v___y_5884_);
lean_dec_ref(v___y_5883_);
lean_dec(v___y_5882_);
lean_dec_ref(v___y_5881_);
lean_dec_ref(v___y_5880_);
lean_dec(v_a_5825_);
v_a_5898_ = lean_ctor_get(v___x_5888_, 0);
v_isSharedCheck_5905_ = !lean_is_exclusive(v___x_5888_);
if (v_isSharedCheck_5905_ == 0)
{
v___x_5900_ = v___x_5888_;
v_isShared_5901_ = v_isSharedCheck_5905_;
goto v_resetjp_5899_;
}
else
{
lean_inc(v_a_5898_);
lean_dec(v___x_5888_);
v___x_5900_ = lean_box(0);
v_isShared_5901_ = v_isSharedCheck_5905_;
goto v_resetjp_5899_;
}
v_resetjp_5899_:
{
lean_object* v___x_5903_; 
if (v_isShared_5901_ == 0)
{
v___x_5903_ = v___x_5900_;
goto v_reusejp_5902_;
}
else
{
lean_object* v_reuseFailAlloc_5904_; 
v_reuseFailAlloc_5904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5904_, 0, v_a_5898_);
v___x_5903_ = v_reuseFailAlloc_5904_;
goto v_reusejp_5902_;
}
v_reusejp_5902_:
{
return v___x_5903_;
}
}
}
}
v___jp_5906_:
{
if (v___y_5915_ == 0)
{
uint8_t v___x_5916_; 
v___x_5916_ = 1;
v___y_5879_ = v___y_5907_;
v___y_5880_ = v___y_5909_;
v___y_5881_ = v___y_5908_;
v___y_5882_ = v___y_5910_;
v___y_5883_ = v___y_5912_;
v___y_5884_ = v___y_5913_;
v___y_5885_ = v___y_5914_;
v___y_5886_ = v___x_5916_;
goto v___jp_5878_;
}
else
{
if (v___y_5911_ == 0)
{
v___y_5827_ = v___y_5907_;
v___y_5828_ = v___y_5911_;
v___y_5829_ = v___y_5908_;
v___y_5830_ = v___y_5909_;
v___y_5831_ = v___y_5910_;
v___y_5832_ = v___y_5912_;
v___y_5833_ = v___y_5913_;
v___y_5834_ = v___y_5914_;
goto v___jp_5826_;
}
else
{
v___y_5879_ = v___y_5907_;
v___y_5880_ = v___y_5909_;
v___y_5881_ = v___y_5908_;
v___y_5882_ = v___y_5910_;
v___y_5883_ = v___y_5912_;
v___y_5884_ = v___y_5913_;
v___y_5885_ = v___y_5914_;
v___y_5886_ = v___y_5911_;
goto v___jp_5878_;
}
}
}
v___jp_5917_:
{
lean_object* v___x_5926_; 
v___x_5926_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v___y_5921_);
if (lean_obj_tag(v___x_5926_) == 0)
{
lean_object* v_a_5927_; lean_object* v___x_5929_; uint8_t v_isShared_5930_; uint8_t v_isSharedCheck_5938_; 
v_a_5927_ = lean_ctor_get(v___x_5926_, 0);
v_isSharedCheck_5938_ = !lean_is_exclusive(v___x_5926_);
if (v_isSharedCheck_5938_ == 0)
{
v___x_5929_ = v___x_5926_;
v_isShared_5930_ = v_isSharedCheck_5938_;
goto v_resetjp_5928_;
}
else
{
lean_inc(v_a_5927_);
lean_dec(v___x_5926_);
v___x_5929_ = lean_box(0);
v_isShared_5930_ = v_isSharedCheck_5938_;
goto v_resetjp_5928_;
}
v_resetjp_5928_:
{
if (lean_obj_tag(v_a_5927_) == 0)
{
lean_object* v_a_5931_; lean_object* v___x_5933_; 
lean_dec_ref(v___y_5924_);
lean_dec_ref(v___y_5923_);
lean_dec_ref(v___y_5922_);
lean_dec_ref(v___y_5920_);
lean_dec_ref(v___y_5919_);
lean_dec(v_a_5825_);
lean_dec(v_a_5815_);
v_a_5931_ = lean_ctor_get(v_a_5927_, 0);
lean_inc(v_a_5931_);
lean_dec_ref_known(v_a_5927_, 1);
if (v_isShared_5930_ == 0)
{
lean_ctor_set(v___x_5929_, 0, v_a_5931_);
v___x_5933_ = v___x_5929_;
goto v_reusejp_5932_;
}
else
{
lean_object* v_reuseFailAlloc_5934_; 
v_reuseFailAlloc_5934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5931_);
v___x_5933_ = v_reuseFailAlloc_5934_;
goto v_reusejp_5932_;
}
v_reusejp_5932_:
{
return v___x_5933_;
}
}
else
{
lean_object* v_a_5935_; uint8_t v___x_5936_; 
lean_del_object(v___x_5929_);
v_a_5935_ = lean_ctor_get(v_a_5927_, 0);
lean_inc(v_a_5935_);
lean_dec_ref_known(v_a_5927_, 1);
v___x_5936_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_a_5815_, v___x_5793_);
if (v___x_5936_ == 0)
{
lean_dec(v_a_5815_);
v___y_5907_ = v___y_5918_;
v___y_5908_ = v___y_5919_;
v___y_5909_ = v___y_5920_;
v___y_5910_ = v_a_5935_;
v___y_5911_ = v___y_5925_;
v___y_5912_ = v___y_5922_;
v___y_5913_ = v___y_5923_;
v___y_5914_ = v___y_5924_;
v___y_5915_ = v___x_5936_;
goto v___jp_5906_;
}
else
{
uint8_t v___x_5937_; 
v___x_5937_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_a_5815_, v___x_5798_);
lean_dec(v_a_5815_);
v___y_5907_ = v___y_5918_;
v___y_5908_ = v___y_5919_;
v___y_5909_ = v___y_5920_;
v___y_5910_ = v_a_5935_;
v___y_5911_ = v___y_5925_;
v___y_5912_ = v___y_5922_;
v___y_5913_ = v___y_5923_;
v___y_5914_ = v___y_5924_;
v___y_5915_ = v___x_5937_;
goto v___jp_5906_;
}
}
}
}
else
{
lean_object* v_a_5939_; lean_object* v___x_5941_; uint8_t v_isShared_5942_; uint8_t v_isSharedCheck_5946_; 
lean_dec_ref(v___y_5924_);
lean_dec_ref(v___y_5923_);
lean_dec_ref(v___y_5922_);
lean_dec_ref(v___y_5920_);
lean_dec_ref(v___y_5919_);
lean_dec(v_a_5825_);
lean_dec(v_a_5815_);
v_a_5939_ = lean_ctor_get(v___x_5926_, 0);
v_isSharedCheck_5946_ = !lean_is_exclusive(v___x_5926_);
if (v_isSharedCheck_5946_ == 0)
{
v___x_5941_ = v___x_5926_;
v_isShared_5942_ = v_isSharedCheck_5946_;
goto v_resetjp_5940_;
}
else
{
lean_inc(v_a_5939_);
lean_dec(v___x_5926_);
v___x_5941_ = lean_box(0);
v_isShared_5942_ = v_isSharedCheck_5946_;
goto v_resetjp_5940_;
}
v_resetjp_5940_:
{
lean_object* v___x_5944_; 
if (v_isShared_5942_ == 0)
{
v___x_5944_ = v___x_5941_;
goto v_reusejp_5943_;
}
else
{
lean_object* v_reuseFailAlloc_5945_; 
v_reuseFailAlloc_5945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5945_, 0, v_a_5939_);
v___x_5944_ = v_reuseFailAlloc_5945_;
goto v_reusejp_5943_;
}
v_reusejp_5943_:
{
return v___x_5944_;
}
}
}
}
v___jp_5947_:
{
size_t v_sz_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; uint8_t v___x_5959_; 
v_sz_5955_ = lean_array_size(v___y_5954_);
v___x_5956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_5955_, v___y_5948_, v___y_5954_);
v___x_5957_ = lean_array_get_size(v___y_5952_);
v___x_5958_ = lean_unsigned_to_nat(0u);
v___x_5959_ = lean_nat_dec_eq(v___x_5957_, v___x_5958_);
if (v___x_5959_ == 0)
{
v___y_5918_ = v___y_5948_;
v___y_5919_ = v___x_5956_;
v___y_5920_ = v___y_5949_;
v___y_5921_ = v___y_5950_;
v___y_5922_ = v___y_5951_;
v___y_5923_ = v___y_5952_;
v___y_5924_ = v___y_5953_;
v___y_5925_ = v___x_5959_;
goto v___jp_5917_;
}
else
{
lean_object* v___x_5960_; uint8_t v___x_5961_; 
v___x_5960_ = lean_array_get_size(v___x_5956_);
v___x_5961_ = lean_nat_dec_eq(v___x_5960_, v___x_5958_);
if (v___x_5961_ == 0)
{
v___y_5918_ = v___y_5948_;
v___y_5919_ = v___x_5956_;
v___y_5920_ = v___y_5949_;
v___y_5921_ = v___y_5950_;
v___y_5922_ = v___y_5951_;
v___y_5923_ = v___y_5952_;
v___y_5924_ = v___y_5953_;
v___y_5925_ = v___x_5961_;
goto v___jp_5917_;
}
else
{
lean_object* v___x_5962_; lean_object* v___x_5963_; 
lean_dec_ref(v___x_5956_);
lean_dec_ref(v___y_5953_);
lean_dec_ref(v___y_5952_);
lean_dec_ref(v___y_5951_);
lean_dec_ref(v___y_5950_);
lean_dec_ref(v___y_5949_);
lean_dec(v_a_5825_);
lean_dec(v_a_5815_);
v___x_5962_ = ((lean_object*)(l_Lake_Check_runComparator___closed__5));
v___x_5963_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5962_);
return v___x_5963_;
}
}
}
v___jp_5964_:
{
lean_object* v___x_5966_; 
v___x_5966_ = l_IO_FS_readFile(v___y_5965_);
if (lean_obj_tag(v___x_5966_) == 0)
{
lean_object* v_a_5967_; lean_object* v___x_5968_; 
v_a_5967_ = lean_ctor_get(v___x_5966_, 0);
lean_inc(v_a_5967_);
lean_dec_ref_known(v___x_5966_, 1);
v___x_5968_ = l_Lean_Json_parse(v_a_5967_);
if (lean_obj_tag(v___x_5968_) == 0)
{
lean_object* v_a_5969_; 
lean_dec(v_a_5825_);
lean_dec(v_a_5815_);
v_a_5969_ = lean_ctor_get(v___x_5968_, 0);
lean_inc(v_a_5969_);
lean_dec_ref_known(v___x_5968_, 1);
v___y_5783_ = v___y_5965_;
v_a_5784_ = v_a_5969_;
goto v___jp_5782_;
}
else
{
lean_object* v_a_5970_; lean_object* v___x_5971_; 
v_a_5970_ = lean_ctor_get(v___x_5968_, 0);
lean_inc(v_a_5970_);
lean_dec_ref_known(v___x_5968_, 1);
v___x_5971_ = l_Lake_Check_instFromJsonConfig_fromJson(v_a_5970_);
if (lean_obj_tag(v___x_5971_) == 0)
{
lean_object* v_a_5972_; 
lean_dec(v_a_5825_);
lean_dec(v_a_5815_);
v_a_5972_ = lean_ctor_get(v___x_5971_, 0);
lean_inc(v_a_5972_);
lean_dec_ref_known(v___x_5971_, 1);
v___y_5783_ = v___y_5965_;
v_a_5784_ = v_a_5972_;
goto v___jp_5782_;
}
else
{
lean_object* v_a_5973_; lean_object* v_challenge__module_5974_; lean_object* v_solution__module_5975_; lean_object* v_theorem__names_5976_; lean_object* v_definition__names_5977_; lean_object* v_permitted__axioms_5978_; size_t v_sz_5979_; size_t v___x_5980_; lean_object* v___x_5981_; 
v_a_5973_ = lean_ctor_get(v___x_5971_, 0);
lean_inc(v_a_5973_);
lean_dec_ref_known(v___x_5971_, 1);
v_challenge__module_5974_ = lean_ctor_get(v_a_5973_, 0);
lean_inc_ref(v_challenge__module_5974_);
v_solution__module_5975_ = lean_ctor_get(v_a_5973_, 1);
lean_inc_ref(v_solution__module_5975_);
v_theorem__names_5976_ = lean_ctor_get(v_a_5973_, 2);
v_definition__names_5977_ = lean_ctor_get(v_a_5973_, 3);
v_permitted__axioms_5978_ = lean_ctor_get(v_a_5973_, 4);
lean_inc_ref(v_permitted__axioms_5978_);
v_sz_5979_ = lean_array_size(v_theorem__names_5976_);
v___x_5980_ = ((size_t)0ULL);
lean_inc_ref(v_theorem__names_5976_);
v___x_5981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_5979_, v___x_5980_, v_theorem__names_5976_);
if (lean_obj_tag(v_definition__names_5977_) == 0)
{
lean_object* v___x_5982_; 
v___x_5982_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___y_5948_ = v___x_5980_;
v___y_5949_ = v_solution__module_5975_;
v___y_5950_ = v_a_5973_;
v___y_5951_ = v_challenge__module_5974_;
v___y_5952_ = v___x_5981_;
v___y_5953_ = v_permitted__axioms_5978_;
v___y_5954_ = v___x_5982_;
goto v___jp_5947_;
}
else
{
lean_object* v_val_5983_; 
v_val_5983_ = lean_ctor_get(v_definition__names_5977_, 0);
lean_inc(v_val_5983_);
v___y_5948_ = v___x_5980_;
v___y_5949_ = v_solution__module_5975_;
v___y_5950_ = v_a_5973_;
v___y_5951_ = v_challenge__module_5974_;
v___y_5952_ = v___x_5981_;
v___y_5953_ = v_permitted__axioms_5978_;
v___y_5954_ = v_val_5983_;
goto v___jp_5947_;
}
}
}
}
else
{
lean_object* v_a_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; 
lean_dec(v_a_5825_);
lean_dec(v_a_5815_);
v_a_5984_ = lean_ctor_get(v___x_5966_, 0);
lean_inc(v_a_5984_);
lean_dec_ref_known(v___x_5966_, 1);
v___x_5985_ = ((lean_object*)(l_Lake_Check_runComparator___closed__6));
v___x_5986_ = lean_io_error_to_string(v_a_5984_);
v___x_5987_ = lean_string_append(v___x_5985_, v___x_5986_);
lean_dec_ref(v___x_5986_);
v___x_5988_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5987_);
lean_dec_ref(v___x_5987_);
return v___x_5988_;
}
}
}
}
}
else
{
lean_object* v_a_5992_; lean_object* v___x_5994_; uint8_t v_isShared_5995_; uint8_t v_isSharedCheck_5999_; 
lean_dec(v_a_5815_);
v_a_5992_ = lean_ctor_get(v___x_5816_, 0);
v_isSharedCheck_5999_ = !lean_is_exclusive(v___x_5816_);
if (v_isSharedCheck_5999_ == 0)
{
v___x_5994_ = v___x_5816_;
v_isShared_5995_ = v_isSharedCheck_5999_;
goto v_resetjp_5993_;
}
else
{
lean_inc(v_a_5992_);
lean_dec(v___x_5816_);
v___x_5994_ = lean_box(0);
v_isShared_5995_ = v_isSharedCheck_5999_;
goto v_resetjp_5993_;
}
v_resetjp_5993_:
{
lean_object* v___x_5997_; 
if (v_isShared_5995_ == 0)
{
v___x_5997_ = v___x_5994_;
goto v_reusejp_5996_;
}
else
{
lean_object* v_reuseFailAlloc_5998_; 
v_reuseFailAlloc_5998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5998_, 0, v_a_5992_);
v___x_5997_ = v_reuseFailAlloc_5998_;
goto v_reusejp_5996_;
}
v_reusejp_5996_:
{
return v___x_5997_;
}
}
}
}
}
}
else
{
lean_object* v_a_6001_; lean_object* v___x_6003_; uint8_t v_isShared_6004_; uint8_t v_isSharedCheck_6008_; 
lean_dec_ref(v_projectDir_5746_);
lean_dec_ref(v_lean_5744_);
v_a_6001_ = lean_ctor_get(v___x_5806_, 0);
v_isSharedCheck_6008_ = !lean_is_exclusive(v___x_5806_);
if (v_isSharedCheck_6008_ == 0)
{
v___x_6003_ = v___x_5806_;
v_isShared_6004_ = v_isSharedCheck_6008_;
goto v_resetjp_6002_;
}
else
{
lean_inc(v_a_6001_);
lean_dec(v___x_5806_);
v___x_6003_ = lean_box(0);
v_isShared_6004_ = v_isSharedCheck_6008_;
goto v_resetjp_6002_;
}
v_resetjp_6002_:
{
lean_object* v___x_6006_; 
if (v_isShared_6004_ == 0)
{
v___x_6006_ = v___x_6003_;
goto v_reusejp_6005_;
}
else
{
lean_object* v_reuseFailAlloc_6007_; 
v_reuseFailAlloc_6007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6007_, 0, v_a_6001_);
v___x_6006_ = v_reuseFailAlloc_6007_;
goto v_reusejp_6005_;
}
v_reusejp_6005_:
{
return v___x_6006_;
}
}
}
v___jp_5748_:
{
lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; 
v___x_5750_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_5751_ = lean_io_error_to_string(v_a_5749_);
v___x_5752_ = lean_string_append(v___x_5750_, v___x_5751_);
lean_dec_ref(v___x_5751_);
v___x_5753_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_5752_);
if (lean_obj_tag(v___x_5753_) == 0)
{
lean_object* v___x_5755_; uint8_t v_isShared_5756_; uint8_t v_isSharedCheck_5761_; 
v_isSharedCheck_5761_ = !lean_is_exclusive(v___x_5753_);
if (v_isSharedCheck_5761_ == 0)
{
lean_object* v_unused_5762_; 
v_unused_5762_ = lean_ctor_get(v___x_5753_, 0);
lean_dec(v_unused_5762_);
v___x_5755_ = v___x_5753_;
v_isShared_5756_ = v_isSharedCheck_5761_;
goto v_resetjp_5754_;
}
else
{
lean_dec(v___x_5753_);
v___x_5755_ = lean_box(0);
v_isShared_5756_ = v_isSharedCheck_5761_;
goto v_resetjp_5754_;
}
v_resetjp_5754_:
{
lean_object* v___x_5757_; lean_object* v___x_5759_; 
v___x_5757_ = l_Lake_Check_runComparator___boxed__const__1;
if (v_isShared_5756_ == 0)
{
lean_ctor_set(v___x_5755_, 0, v___x_5757_);
v___x_5759_ = v___x_5755_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5760_; 
v_reuseFailAlloc_5760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5760_, 0, v___x_5757_);
v___x_5759_ = v_reuseFailAlloc_5760_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
return v___x_5759_;
}
}
}
else
{
lean_object* v_a_5763_; lean_object* v___x_5765_; uint8_t v_isShared_5766_; uint8_t v_isSharedCheck_5770_; 
v_a_5763_ = lean_ctor_get(v___x_5753_, 0);
v_isSharedCheck_5770_ = !lean_is_exclusive(v___x_5753_);
if (v_isSharedCheck_5770_ == 0)
{
v___x_5765_ = v___x_5753_;
v_isShared_5766_ = v_isSharedCheck_5770_;
goto v_resetjp_5764_;
}
else
{
lean_inc(v_a_5763_);
lean_dec(v___x_5753_);
v___x_5765_ = lean_box(0);
v_isShared_5766_ = v_isSharedCheck_5770_;
goto v_resetjp_5764_;
}
v_resetjp_5764_:
{
lean_object* v___x_5768_; 
if (v_isShared_5766_ == 0)
{
v___x_5768_ = v___x_5765_;
goto v_reusejp_5767_;
}
else
{
lean_object* v_reuseFailAlloc_5769_; 
v_reuseFailAlloc_5769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5769_, 0, v_a_5763_);
v___x_5768_ = v_reuseFailAlloc_5769_;
goto v_reusejp_5767_;
}
v_reusejp_5767_:
{
return v___x_5768_;
}
}
}
}
v___jp_5771_:
{
lean_object* v_a_5773_; lean_object* v___x_5775_; uint8_t v_isShared_5776_; uint8_t v_isSharedCheck_5781_; 
v_a_5773_ = lean_ctor_get(v___y_5772_, 0);
v_isSharedCheck_5781_ = !lean_is_exclusive(v___y_5772_);
if (v_isSharedCheck_5781_ == 0)
{
v___x_5775_ = v___y_5772_;
v_isShared_5776_ = v_isSharedCheck_5781_;
goto v_resetjp_5774_;
}
else
{
lean_inc(v_a_5773_);
lean_dec(v___y_5772_);
v___x_5775_ = lean_box(0);
v_isShared_5776_ = v_isSharedCheck_5781_;
goto v_resetjp_5774_;
}
v_resetjp_5774_:
{
lean_object* v_a_5777_; lean_object* v___x_5779_; 
v_a_5777_ = lean_ctor_get(v_a_5773_, 0);
lean_inc(v_a_5777_);
lean_dec(v_a_5773_);
if (v_isShared_5776_ == 0)
{
lean_ctor_set(v___x_5775_, 0, v_a_5777_);
v___x_5779_ = v___x_5775_;
goto v_reusejp_5778_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_a_5777_);
v___x_5779_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5778_;
}
v_reusejp_5778_:
{
return v___x_5779_;
}
}
}
v___jp_5782_:
{
lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; 
v___x_5785_ = ((lean_object*)(l_Lake_Check_runComparator___closed__0));
v___x_5786_ = lean_string_append(v___x_5785_, v___y_5783_);
v___x_5787_ = ((lean_object*)(l_Lake_Check_runComparator___closed__1));
v___x_5788_ = lean_string_append(v___x_5786_, v___x_5787_);
v___x_5789_ = lean_string_append(v___x_5788_, v_a_5784_);
lean_dec_ref(v_a_5784_);
v___x_5790_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5789_);
lean_dec_ref(v___x_5789_);
return v___x_5790_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___boxed(lean_object* v_configFile_x3f_6009_, lean_object* v_challengeFromExport_x3f_6010_, lean_object* v_solutionFromExport_x3f_6011_, lean_object* v_paranoid_6012_, lean_object* v_inadvisablyNoSandbox_6013_, lean_object* v_lean_6014_, lean_object* v_lake_6015_, lean_object* v_projectDir_6016_, lean_object* v_a_6017_){
_start:
{
uint8_t v_paranoid_boxed_6018_; uint8_t v_inadvisablyNoSandbox_boxed_6019_; lean_object* v_res_6020_; 
v_paranoid_boxed_6018_ = lean_unbox(v_paranoid_6012_);
v_inadvisablyNoSandbox_boxed_6019_ = lean_unbox(v_inadvisablyNoSandbox_6013_);
v_res_6020_ = l_Lake_Check_runComparator(v_configFile_x3f_6009_, v_challengeFromExport_x3f_6010_, v_solutionFromExport_x3f_6011_, v_paranoid_boxed_6018_, v_inadvisablyNoSandbox_boxed_6019_, v_lean_6014_, v_lake_6015_, v_projectDir_6016_);
lean_dec_ref(v_lake_6015_);
lean_dec(v_configFile_x3f_6009_);
return v_res_6020_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runCheck(lean_object* v_fromExport_x3f_6021_, uint8_t v_paranoid_6022_, uint8_t v_inadvisablyNoSandbox_6023_, lean_object* v_lean_6024_, lean_object* v_lake_6025_, lean_object* v_projectDir_6026_){
_start:
{
lean_object* v___x_6028_; lean_object* v___x_6029_; uint8_t v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; 
v___x_6028_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__0));
v___x_6029_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_6030_ = 0;
v___x_6031_ = lean_box(v___x_6030_);
v___x_6032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_6031_);
lean_ctor_set(v___x_6032_, 1, v_fromExport_x3f_6021_);
v___x_6033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6033_, 0, v___x_6029_);
lean_ctor_set(v___x_6033_, 1, v___x_6032_);
v___x_6034_ = lean_unsigned_to_nat(1u);
v___x_6035_ = lean_mk_empty_array_with_capacity(v___x_6034_);
v___x_6036_ = lean_array_push(v___x_6035_, v___x_6033_);
v___x_6037_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(v___x_6028_, v___x_6036_);
lean_dec_ref(v___x_6036_);
if (lean_obj_tag(v___x_6037_) == 0)
{
lean_object* v_a_6038_; lean_object* v___x_6040_; uint8_t v_isShared_6041_; uint8_t v_isSharedCheck_6147_; 
v_a_6038_ = lean_ctor_get(v___x_6037_, 0);
v_isSharedCheck_6147_ = !lean_is_exclusive(v___x_6037_);
if (v_isSharedCheck_6147_ == 0)
{
v___x_6040_ = v___x_6037_;
v_isShared_6041_ = v_isSharedCheck_6147_;
goto v_resetjp_6039_;
}
else
{
lean_inc(v_a_6038_);
lean_dec(v___x_6037_);
v___x_6040_ = lean_box(0);
v_isShared_6041_ = v_isSharedCheck_6147_;
goto v_resetjp_6039_;
}
v_resetjp_6039_:
{
if (lean_obj_tag(v_a_6038_) == 0)
{
lean_object* v_a_6042_; lean_object* v___x_6044_; 
lean_dec_ref(v_projectDir_6026_);
lean_dec_ref(v_lean_6024_);
v_a_6042_ = lean_ctor_get(v_a_6038_, 0);
lean_inc(v_a_6042_);
lean_dec_ref_known(v_a_6038_, 1);
if (v_isShared_6041_ == 0)
{
lean_ctor_set(v___x_6040_, 0, v_a_6042_);
v___x_6044_ = v___x_6040_;
goto v_reusejp_6043_;
}
else
{
lean_object* v_reuseFailAlloc_6045_; 
v_reuseFailAlloc_6045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6045_, 0, v_a_6042_);
v___x_6044_ = v_reuseFailAlloc_6045_;
goto v_reusejp_6043_;
}
v_reusejp_6043_:
{
return v___x_6044_;
}
}
else
{
lean_object* v_a_6046_; lean_object* v___x_6047_; 
lean_del_object(v___x_6040_);
v_a_6046_ = lean_ctor_get(v_a_6038_, 0);
lean_inc_n(v_a_6046_, 2);
lean_dec_ref_known(v_a_6038_, 1);
v___x_6047_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_6028_, v_paranoid_6022_, v_inadvisablyNoSandbox_6023_, v_lean_6024_, v_lake_6025_, v_projectDir_6026_, v_a_6046_);
if (lean_obj_tag(v___x_6047_) == 0)
{
lean_object* v_a_6048_; lean_object* v___x_6050_; uint8_t v_isShared_6051_; uint8_t v_isSharedCheck_6138_; 
v_a_6048_ = lean_ctor_get(v___x_6047_, 0);
v_isSharedCheck_6138_ = !lean_is_exclusive(v___x_6047_);
if (v_isSharedCheck_6138_ == 0)
{
v___x_6050_ = v___x_6047_;
v_isShared_6051_ = v_isSharedCheck_6138_;
goto v_resetjp_6049_;
}
else
{
lean_inc(v_a_6048_);
lean_dec(v___x_6047_);
v___x_6050_ = lean_box(0);
v_isShared_6051_ = v_isSharedCheck_6138_;
goto v_resetjp_6049_;
}
v_resetjp_6049_:
{
if (lean_obj_tag(v_a_6048_) == 0)
{
lean_object* v_a_6052_; lean_object* v___x_6054_; 
lean_dec(v_a_6046_);
v_a_6052_ = lean_ctor_get(v_a_6048_, 0);
lean_inc(v_a_6052_);
lean_dec_ref_known(v_a_6048_, 1);
if (v_isShared_6051_ == 0)
{
lean_ctor_set(v___x_6050_, 0, v_a_6052_);
v___x_6054_ = v___x_6050_;
goto v_reusejp_6053_;
}
else
{
lean_object* v_reuseFailAlloc_6055_; 
v_reuseFailAlloc_6055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6055_, 0, v_a_6052_);
v___x_6054_ = v_reuseFailAlloc_6055_;
goto v_reusejp_6053_;
}
v_reusejp_6053_:
{
return v___x_6054_;
}
}
else
{
lean_object* v_a_6056_; uint8_t v___x_6118_; 
lean_del_object(v___x_6050_);
v_a_6056_ = lean_ctor_get(v_a_6048_, 0);
lean_inc(v_a_6056_);
lean_dec_ref_known(v_a_6048_, 1);
v___x_6118_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_a_6046_, v___x_6030_);
lean_dec(v_a_6046_);
if (v___x_6118_ == 0)
{
lean_object* v_projectDir_6119_; lean_object* v___x_6120_; 
v_projectDir_6119_ = lean_ctor_get(v_a_6056_, 0);
lean_inc_ref(v_projectDir_6119_);
v___x_6120_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_6028_, v_projectDir_6119_);
if (lean_obj_tag(v___x_6120_) == 0)
{
lean_object* v_a_6121_; lean_object* v___x_6123_; uint8_t v_isShared_6124_; uint8_t v_isSharedCheck_6129_; 
v_a_6121_ = lean_ctor_get(v___x_6120_, 0);
v_isSharedCheck_6129_ = !lean_is_exclusive(v___x_6120_);
if (v_isSharedCheck_6129_ == 0)
{
v___x_6123_ = v___x_6120_;
v_isShared_6124_ = v_isSharedCheck_6129_;
goto v_resetjp_6122_;
}
else
{
lean_inc(v_a_6121_);
lean_dec(v___x_6120_);
v___x_6123_ = lean_box(0);
v_isShared_6124_ = v_isSharedCheck_6129_;
goto v_resetjp_6122_;
}
v_resetjp_6122_:
{
if (lean_obj_tag(v_a_6121_) == 1)
{
lean_object* v_val_6125_; lean_object* v___x_6127_; 
lean_dec(v_a_6056_);
v_val_6125_ = lean_ctor_get(v_a_6121_, 0);
lean_inc(v_val_6125_);
lean_dec_ref_known(v_a_6121_, 1);
if (v_isShared_6124_ == 0)
{
lean_ctor_set(v___x_6123_, 0, v_val_6125_);
v___x_6127_ = v___x_6123_;
goto v_reusejp_6126_;
}
else
{
lean_object* v_reuseFailAlloc_6128_; 
v_reuseFailAlloc_6128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6128_, 0, v_val_6125_);
v___x_6127_ = v_reuseFailAlloc_6128_;
goto v_reusejp_6126_;
}
v_reusejp_6126_:
{
return v___x_6127_;
}
}
else
{
lean_del_object(v___x_6123_);
lean_dec(v_a_6121_);
goto v___jp_6057_;
}
}
}
else
{
lean_object* v_a_6130_; lean_object* v___x_6132_; uint8_t v_isShared_6133_; uint8_t v_isSharedCheck_6137_; 
lean_dec(v_a_6056_);
v_a_6130_ = lean_ctor_get(v___x_6120_, 0);
v_isSharedCheck_6137_ = !lean_is_exclusive(v___x_6120_);
if (v_isSharedCheck_6137_ == 0)
{
v___x_6132_ = v___x_6120_;
v_isShared_6133_ = v_isSharedCheck_6137_;
goto v_resetjp_6131_;
}
else
{
lean_inc(v_a_6130_);
lean_dec(v___x_6120_);
v___x_6132_ = lean_box(0);
v_isShared_6133_ = v_isSharedCheck_6137_;
goto v_resetjp_6131_;
}
v_resetjp_6131_:
{
lean_object* v___x_6135_; 
if (v_isShared_6133_ == 0)
{
v___x_6135_ = v___x_6132_;
goto v_reusejp_6134_;
}
else
{
lean_object* v_reuseFailAlloc_6136_; 
v_reuseFailAlloc_6136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6136_, 0, v_a_6130_);
v___x_6135_ = v_reuseFailAlloc_6136_;
goto v_reusejp_6134_;
}
v_reusejp_6134_:
{
return v___x_6135_;
}
}
}
}
else
{
goto v___jp_6057_;
}
v___jp_6057_:
{
lean_object* v_projectDir_6058_; lean_object* v_theoremNames_6059_; lean_object* v_definitionNames_6060_; lean_object* v_leanPrefix_6061_; lean_object* v_leanPath_6062_; lean_object* v_binPath_6063_; lean_object* v_whichSandbox_6064_; lean_object* v_whichLake_6065_; lean_object* v_lakeHome_6066_; lean_object* v_whichLean4Export_6067_; lean_object* v_whichLeanChecker_6068_; lean_object* v_whichEnvBin_6069_; lean_object* v_bundledKernels_6070_; lean_object* v_moduleStore_6071_; lean_object* v___x_6073_; uint8_t v_isShared_6074_; uint8_t v_isSharedCheck_6113_; 
v_projectDir_6058_ = lean_ctor_get(v_a_6056_, 0);
v_theoremNames_6059_ = lean_ctor_get(v_a_6056_, 3);
v_definitionNames_6060_ = lean_ctor_get(v_a_6056_, 4);
v_leanPrefix_6061_ = lean_ctor_get(v_a_6056_, 6);
v_leanPath_6062_ = lean_ctor_get(v_a_6056_, 7);
v_binPath_6063_ = lean_ctor_get(v_a_6056_, 8);
v_whichSandbox_6064_ = lean_ctor_get(v_a_6056_, 9);
v_whichLake_6065_ = lean_ctor_get(v_a_6056_, 10);
v_lakeHome_6066_ = lean_ctor_get(v_a_6056_, 11);
v_whichLean4Export_6067_ = lean_ctor_get(v_a_6056_, 12);
v_whichLeanChecker_6068_ = lean_ctor_get(v_a_6056_, 13);
v_whichEnvBin_6069_ = lean_ctor_get(v_a_6056_, 14);
v_bundledKernels_6070_ = lean_ctor_get(v_a_6056_, 16);
v_moduleStore_6071_ = lean_ctor_get(v_a_6056_, 17);
v_isSharedCheck_6113_ = !lean_is_exclusive(v_a_6056_);
if (v_isSharedCheck_6113_ == 0)
{
lean_object* v_unused_6114_; lean_object* v_unused_6115_; lean_object* v_unused_6116_; lean_object* v_unused_6117_; 
v_unused_6114_ = lean_ctor_get(v_a_6056_, 15);
lean_dec(v_unused_6114_);
v_unused_6115_ = lean_ctor_get(v_a_6056_, 5);
lean_dec(v_unused_6115_);
v_unused_6116_ = lean_ctor_get(v_a_6056_, 2);
lean_dec(v_unused_6116_);
v_unused_6117_ = lean_ctor_get(v_a_6056_, 1);
lean_dec(v_unused_6117_);
v___x_6073_ = v_a_6056_;
v_isShared_6074_ = v_isSharedCheck_6113_;
goto v_resetjp_6072_;
}
else
{
lean_inc(v_moduleStore_6071_);
lean_inc(v_bundledKernels_6070_);
lean_inc(v_whichEnvBin_6069_);
lean_inc(v_whichLeanChecker_6068_);
lean_inc(v_whichLean4Export_6067_);
lean_inc(v_lakeHome_6066_);
lean_inc(v_whichLake_6065_);
lean_inc(v_whichSandbox_6064_);
lean_inc(v_binPath_6063_);
lean_inc(v_leanPath_6062_);
lean_inc(v_leanPrefix_6061_);
lean_inc(v_definitionNames_6060_);
lean_inc(v_theoremNames_6059_);
lean_inc(v_projectDir_6058_);
lean_dec(v_a_6056_);
v___x_6073_ = lean_box(0);
v_isShared_6074_ = v_isSharedCheck_6113_;
goto v_resetjp_6072_;
}
v_resetjp_6072_:
{
lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6079_; 
v___x_6075_ = lean_box(1);
v___x_6076_ = lean_box(0);
v___x_6077_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms));
if (v_isShared_6074_ == 0)
{
lean_ctor_set(v___x_6073_, 15, v___x_6075_);
lean_ctor_set(v___x_6073_, 5, v___x_6077_);
lean_ctor_set(v___x_6073_, 2, v___x_6076_);
lean_ctor_set(v___x_6073_, 1, v___x_6076_);
v___x_6079_ = v___x_6073_;
goto v_reusejp_6078_;
}
else
{
lean_object* v_reuseFailAlloc_6112_; 
v_reuseFailAlloc_6112_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_6112_, 0, v_projectDir_6058_);
lean_ctor_set(v_reuseFailAlloc_6112_, 1, v___x_6076_);
lean_ctor_set(v_reuseFailAlloc_6112_, 2, v___x_6076_);
lean_ctor_set(v_reuseFailAlloc_6112_, 3, v_theoremNames_6059_);
lean_ctor_set(v_reuseFailAlloc_6112_, 4, v_definitionNames_6060_);
lean_ctor_set(v_reuseFailAlloc_6112_, 5, v___x_6077_);
lean_ctor_set(v_reuseFailAlloc_6112_, 6, v_leanPrefix_6061_);
lean_ctor_set(v_reuseFailAlloc_6112_, 7, v_leanPath_6062_);
lean_ctor_set(v_reuseFailAlloc_6112_, 8, v_binPath_6063_);
lean_ctor_set(v_reuseFailAlloc_6112_, 9, v_whichSandbox_6064_);
lean_ctor_set(v_reuseFailAlloc_6112_, 10, v_whichLake_6065_);
lean_ctor_set(v_reuseFailAlloc_6112_, 11, v_lakeHome_6066_);
lean_ctor_set(v_reuseFailAlloc_6112_, 12, v_whichLean4Export_6067_);
lean_ctor_set(v_reuseFailAlloc_6112_, 13, v_whichLeanChecker_6068_);
lean_ctor_set(v_reuseFailAlloc_6112_, 14, v_whichEnvBin_6069_);
lean_ctor_set(v_reuseFailAlloc_6112_, 15, v___x_6075_);
lean_ctor_set(v_reuseFailAlloc_6112_, 16, v_bundledKernels_6070_);
lean_ctor_set(v_reuseFailAlloc_6112_, 17, v_moduleStore_6071_);
v___x_6079_ = v_reuseFailAlloc_6112_;
goto v_reusejp_6078_;
}
v_reusejp_6078_:
{
lean_object* v___x_6080_; 
v___x_6080_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v___x_6079_);
lean_dec_ref(v___x_6079_);
if (lean_obj_tag(v___x_6080_) == 0)
{
lean_object* v___x_6082_; uint8_t v_isShared_6083_; uint8_t v_isSharedCheck_6088_; 
v_isSharedCheck_6088_ = !lean_is_exclusive(v___x_6080_);
if (v_isSharedCheck_6088_ == 0)
{
lean_object* v_unused_6089_; 
v_unused_6089_ = lean_ctor_get(v___x_6080_, 0);
lean_dec(v_unused_6089_);
v___x_6082_ = v___x_6080_;
v_isShared_6083_ = v_isSharedCheck_6088_;
goto v_resetjp_6081_;
}
else
{
lean_dec(v___x_6080_);
v___x_6082_ = lean_box(0);
v_isShared_6083_ = v_isSharedCheck_6088_;
goto v_resetjp_6081_;
}
v_resetjp_6081_:
{
lean_object* v___x_6084_; lean_object* v___x_6086_; 
v___x_6084_ = l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1;
if (v_isShared_6083_ == 0)
{
lean_ctor_set(v___x_6082_, 0, v___x_6084_);
v___x_6086_ = v___x_6082_;
goto v_reusejp_6085_;
}
else
{
lean_object* v_reuseFailAlloc_6087_; 
v_reuseFailAlloc_6087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6087_, 0, v___x_6084_);
v___x_6086_ = v_reuseFailAlloc_6087_;
goto v_reusejp_6085_;
}
v_reusejp_6085_:
{
return v___x_6086_;
}
}
}
else
{
lean_object* v_a_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; 
v_a_6090_ = lean_ctor_get(v___x_6080_, 0);
lean_inc(v_a_6090_);
lean_dec_ref_known(v___x_6080_, 1);
v___x_6091_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_6092_ = lean_io_error_to_string(v_a_6090_);
v___x_6093_ = lean_string_append(v___x_6091_, v___x_6092_);
lean_dec_ref(v___x_6092_);
v___x_6094_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_6093_);
if (lean_obj_tag(v___x_6094_) == 0)
{
lean_object* v___x_6096_; uint8_t v_isShared_6097_; uint8_t v_isSharedCheck_6102_; 
v_isSharedCheck_6102_ = !lean_is_exclusive(v___x_6094_);
if (v_isSharedCheck_6102_ == 0)
{
lean_object* v_unused_6103_; 
v_unused_6103_ = lean_ctor_get(v___x_6094_, 0);
lean_dec(v_unused_6103_);
v___x_6096_ = v___x_6094_;
v_isShared_6097_ = v_isSharedCheck_6102_;
goto v_resetjp_6095_;
}
else
{
lean_dec(v___x_6094_);
v___x_6096_ = lean_box(0);
v_isShared_6097_ = v_isSharedCheck_6102_;
goto v_resetjp_6095_;
}
v_resetjp_6095_:
{
lean_object* v___x_6098_; lean_object* v___x_6100_; 
v___x_6098_ = l_Lake_Check_runComparator___boxed__const__1;
if (v_isShared_6097_ == 0)
{
lean_ctor_set(v___x_6096_, 0, v___x_6098_);
v___x_6100_ = v___x_6096_;
goto v_reusejp_6099_;
}
else
{
lean_object* v_reuseFailAlloc_6101_; 
v_reuseFailAlloc_6101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6101_, 0, v___x_6098_);
v___x_6100_ = v_reuseFailAlloc_6101_;
goto v_reusejp_6099_;
}
v_reusejp_6099_:
{
return v___x_6100_;
}
}
}
else
{
lean_object* v_a_6104_; lean_object* v___x_6106_; uint8_t v_isShared_6107_; uint8_t v_isSharedCheck_6111_; 
v_a_6104_ = lean_ctor_get(v___x_6094_, 0);
v_isSharedCheck_6111_ = !lean_is_exclusive(v___x_6094_);
if (v_isSharedCheck_6111_ == 0)
{
v___x_6106_ = v___x_6094_;
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
else
{
lean_inc(v_a_6104_);
lean_dec(v___x_6094_);
v___x_6106_ = lean_box(0);
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
v_resetjp_6105_:
{
lean_object* v___x_6109_; 
if (v_isShared_6107_ == 0)
{
v___x_6109_ = v___x_6106_;
goto v_reusejp_6108_;
}
else
{
lean_object* v_reuseFailAlloc_6110_; 
v_reuseFailAlloc_6110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6110_, 0, v_a_6104_);
v___x_6109_ = v_reuseFailAlloc_6110_;
goto v_reusejp_6108_;
}
v_reusejp_6108_:
{
return v___x_6109_;
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
else
{
lean_object* v_a_6139_; lean_object* v___x_6141_; uint8_t v_isShared_6142_; uint8_t v_isSharedCheck_6146_; 
lean_dec(v_a_6046_);
v_a_6139_ = lean_ctor_get(v___x_6047_, 0);
v_isSharedCheck_6146_ = !lean_is_exclusive(v___x_6047_);
if (v_isSharedCheck_6146_ == 0)
{
v___x_6141_ = v___x_6047_;
v_isShared_6142_ = v_isSharedCheck_6146_;
goto v_resetjp_6140_;
}
else
{
lean_inc(v_a_6139_);
lean_dec(v___x_6047_);
v___x_6141_ = lean_box(0);
v_isShared_6142_ = v_isSharedCheck_6146_;
goto v_resetjp_6140_;
}
v_resetjp_6140_:
{
lean_object* v___x_6144_; 
if (v_isShared_6142_ == 0)
{
v___x_6144_ = v___x_6141_;
goto v_reusejp_6143_;
}
else
{
lean_object* v_reuseFailAlloc_6145_; 
v_reuseFailAlloc_6145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6145_, 0, v_a_6139_);
v___x_6144_ = v_reuseFailAlloc_6145_;
goto v_reusejp_6143_;
}
v_reusejp_6143_:
{
return v___x_6144_;
}
}
}
}
}
}
else
{
lean_object* v_a_6148_; lean_object* v___x_6150_; uint8_t v_isShared_6151_; uint8_t v_isSharedCheck_6155_; 
lean_dec_ref(v_projectDir_6026_);
lean_dec_ref(v_lean_6024_);
v_a_6148_ = lean_ctor_get(v___x_6037_, 0);
v_isSharedCheck_6155_ = !lean_is_exclusive(v___x_6037_);
if (v_isSharedCheck_6155_ == 0)
{
v___x_6150_ = v___x_6037_;
v_isShared_6151_ = v_isSharedCheck_6155_;
goto v_resetjp_6149_;
}
else
{
lean_inc(v_a_6148_);
lean_dec(v___x_6037_);
v___x_6150_ = lean_box(0);
v_isShared_6151_ = v_isSharedCheck_6155_;
goto v_resetjp_6149_;
}
v_resetjp_6149_:
{
lean_object* v___x_6153_; 
if (v_isShared_6151_ == 0)
{
v___x_6153_ = v___x_6150_;
goto v_reusejp_6152_;
}
else
{
lean_object* v_reuseFailAlloc_6154_; 
v_reuseFailAlloc_6154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6154_, 0, v_a_6148_);
v___x_6153_ = v_reuseFailAlloc_6154_;
goto v_reusejp_6152_;
}
v_reusejp_6152_:
{
return v___x_6153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runCheck___boxed(lean_object* v_fromExport_x3f_6156_, lean_object* v_paranoid_6157_, lean_object* v_inadvisablyNoSandbox_6158_, lean_object* v_lean_6159_, lean_object* v_lake_6160_, lean_object* v_projectDir_6161_, lean_object* v_a_6162_){
_start:
{
uint8_t v_paranoid_boxed_6163_; uint8_t v_inadvisablyNoSandbox_boxed_6164_; lean_object* v_res_6165_; 
v_paranoid_boxed_6163_ = lean_unbox(v_paranoid_6157_);
v_inadvisablyNoSandbox_boxed_6164_ = lean_unbox(v_inadvisablyNoSandbox_6158_);
v_res_6165_ = l_Lake_Check_runCheck(v_fromExport_x3f_6156_, v_paranoid_boxed_6163_, v_inadvisablyNoSandbox_boxed_6164_, v_lean_6159_, v_lake_6160_, v_projectDir_6161_);
lean_dec_ref(v_lake_6160_);
return v_res_6165_;
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
lean_object* runtime_initialize_Std_Internal_UV_System(uint8_t builtin);
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
res = runtime_initialize_Std_Internal_UV_System(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1 = _init_l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1();
lean_mark_persistent(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1);
l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1 = _init_l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1();
lean_mark_persistent(l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1);
l_Lake_Check_runComparator___boxed__const__1 = _init_l_Lake_Check_runComparator___boxed__const__1();
lean_mark_persistent(l_Lake_Check_runComparator___boxed__const__1);
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
lean_object* initialize_Std_Internal_UV_System(uint8_t builtin);
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
res = initialize_Std_Internal_UV_System(builtin);
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
