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
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* lean_string_utf8_byte_size(lean_object*);
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
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATH="};
static const lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0_value;
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
static const lean_ctor_object l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1 = (const lean_object*)&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1_value;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2;
static lean_once_cell_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3;
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
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(lean_object* v_s_1125_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1126_ = lean_string_utf8_byte_size(v_s_1125_);
v___x_1127_ = lean_unsigned_to_nat(10u);
v___x_1128_ = lean_nat_dec_le(v___x_1127_, v___x_1126_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
lean_dec_ref(v_s_1125_);
v___x_1129_ = lean_box(0);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1130_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0));
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_string_memcmp(v_s_1125_, v___x_1130_, v___x_1131_, v___x_1131_, v___x_1127_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
lean_dec_ref(v_s_1125_);
v___x_1133_ = lean_box(0);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_inc_ref(v_s_1125_);
v___x_1134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1134_, 0, v_s_1125_);
lean_ctor_set(v___x_1134_, 1, v___x_1131_);
lean_ctor_set(v___x_1134_, 2, v___x_1126_);
v___x_1135_ = l_String_Slice_pos_x21(v___x_1134_, v___x_1127_);
lean_dec_ref_known(v___x_1134_, 3);
v___x_1136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1136_, 0, v_s_1125_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
lean_ctor_set(v___x_1136_, 2, v___x_1126_);
v___x_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(lean_object* v_s_1138_, lean_object* v_pat_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_s_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___boxed(lean_object* v_s_1141_, lean_object* v_pat_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(v_s_1141_, v_pat_1142_);
lean_dec_ref(v_pat_1142_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(lean_object* v_s_1145_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1146_ = lean_string_utf8_byte_size(v_s_1145_);
v___x_1147_ = lean_unsigned_to_nat(5u);
v___x_1148_ = lean_nat_dec_le(v___x_1147_, v___x_1146_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
lean_dec_ref(v_s_1145_);
v___x_1149_ = lean_box(0);
return v___x_1149_;
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0));
v___x_1151_ = lean_unsigned_to_nat(0u);
v___x_1152_ = lean_string_memcmp(v_s_1145_, v___x_1150_, v___x_1151_, v___x_1151_, v___x_1147_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; 
lean_dec_ref(v_s_1145_);
v___x_1153_ = lean_box(0);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_inc_ref(v_s_1145_);
v___x_1154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1154_, 0, v_s_1145_);
lean_ctor_set(v___x_1154_, 1, v___x_1151_);
lean_ctor_set(v___x_1154_, 2, v___x_1146_);
v___x_1155_ = l_String_Slice_pos_x21(v___x_1154_, v___x_1147_);
lean_dec_ref_known(v___x_1154_, 3);
v___x_1156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1156_, 0, v_s_1145_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
lean_ctor_set(v___x_1156_, 2, v___x_1146_);
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(lean_object* v_s_1158_, lean_object* v_pat_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_s_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___boxed(lean_object* v_s_1161_, lean_object* v_pat_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(v_s_1161_, v_pat_1162_);
lean_dec_ref(v_pat_1162_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg(){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___closed__0));
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___boxed(lean_object* v___dummy_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg();
return v_res_1169_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg();
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(lean_object* v_s_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___boxed(lean_object* v_s_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(v_s_1173_);
lean_dec_ref(v_s_1173_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(lean_object* v_a_1175_, lean_object* v___x_1176_, lean_object* v___x_1177_, lean_object* v_a_1178_, lean_object* v_b_1179_){
_start:
{
lean_object* v_it_1181_; lean_object* v_startInclusive_1182_; lean_object* v_endExclusive_1183_; 
if (lean_obj_tag(v_a_1178_) == 0)
{
lean_object* v_currPos_1188_; lean_object* v_searcher_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1212_; 
v_currPos_1188_ = lean_ctor_get(v_a_1178_, 0);
v_searcher_1189_ = lean_ctor_get(v_a_1178_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_a_1178_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1191_ = v_a_1178_;
v_isShared_1192_ = v_isSharedCheck_1212_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_searcher_1189_);
lean_inc(v_currPos_1188_);
lean_dec(v_a_1178_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1212_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
uint8_t v_decide_1193_; 
v_decide_1193_ = lean_nat_dec_eq(v_searcher_1189_, v___x_1177_);
if (v_decide_1193_ == 0)
{
uint32_t v___x_1194_; uint32_t v___x_1195_; uint8_t v___x_1196_; 
v___x_1194_ = 10;
v___x_1195_ = lean_string_utf8_get_fast(v_a_1175_, v_searcher_1189_);
v___x_1196_ = lean_uint32_dec_eq(v___x_1195_, v___x_1194_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_string_utf8_next_fast(v_a_1175_, v_searcher_1189_);
lean_dec(v_searcher_1189_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 1, v___x_1197_);
v___x_1199_ = v___x_1191_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_currPos_1188_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
v_a_1178_ = v___x_1199_;
goto _start;
}
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_slice_1205_; lean_object* v_nextIt_1207_; 
v___x_1202_ = lean_string_utf8_next_fast(v_a_1175_, v_searcher_1189_);
v___x_1203_ = lean_nat_sub(v___x_1202_, v_searcher_1189_);
v___x_1204_ = lean_nat_add(v_searcher_1189_, v___x_1203_);
lean_dec(v___x_1203_);
v_slice_1205_ = l_String_Slice_subslice_x21(v___x_1176_, v_currPos_1188_, v_searcher_1189_);
lean_inc(v___x_1204_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 1, v___x_1204_);
lean_ctor_set(v___x_1191_, 0, v___x_1204_);
v_nextIt_1207_ = v___x_1191_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1204_);
v_nextIt_1207_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v_startInclusive_1208_; lean_object* v_endExclusive_1209_; 
v_startInclusive_1208_ = lean_ctor_get(v_slice_1205_, 0);
lean_inc(v_startInclusive_1208_);
v_endExclusive_1209_ = lean_ctor_get(v_slice_1205_, 1);
lean_inc(v_endExclusive_1209_);
lean_dec_ref(v_slice_1205_);
v_it_1181_ = v_nextIt_1207_;
v_startInclusive_1182_ = v_startInclusive_1208_;
v_endExclusive_1183_ = v_endExclusive_1209_;
goto v___jp_1180_;
}
}
}
else
{
lean_object* v___x_1211_; 
lean_del_object(v___x_1191_);
lean_dec(v_searcher_1189_);
v___x_1211_ = lean_box(1);
lean_inc(v___x_1177_);
v_it_1181_ = v___x_1211_;
v_startInclusive_1182_ = v_currPos_1188_;
v_endExclusive_1183_ = v___x_1177_;
goto v___jp_1180_;
}
}
}
else
{
lean_dec(v___x_1177_);
lean_dec_ref(v_a_1175_);
return v_b_1179_;
}
v___jp_1180_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_inc_ref(v_a_1175_);
v___x_1184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1184_, 0, v_a_1175_);
lean_ctor_set(v___x_1184_, 1, v_startInclusive_1182_);
lean_ctor_set(v___x_1184_, 2, v_endExclusive_1183_);
v___x_1185_ = l_String_Slice_toString(v___x_1184_);
lean_dec_ref_known(v___x_1184_, 3);
v___x_1186_ = lean_array_push(v_b_1179_, v___x_1185_);
v_a_1178_ = v_it_1181_;
v_b_1179_ = v___x_1186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg___boxed(lean_object* v_a_1213_, lean_object* v___x_1214_, lean_object* v___x_1215_, lean_object* v_a_1216_, lean_object* v_b_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1213_, v___x_1214_, v___x_1215_, v_a_1216_, v_b_1217_);
lean_dec_ref(v___x_1214_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(lean_object* v_as_x27_1219_, lean_object* v_b_1220_){
_start:
{
if (lean_obj_tag(v_as_x27_1219_) == 0)
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v_b_1220_);
return v___x_1222_;
}
else
{
lean_object* v_head_1223_; lean_object* v_tail_1224_; lean_object* v_fst_1225_; lean_object* v_snd_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1248_; 
v_head_1223_ = lean_ctor_get(v_as_x27_1219_, 0);
v_tail_1224_ = lean_ctor_get(v_as_x27_1219_, 1);
v_fst_1225_ = lean_ctor_get(v_b_1220_, 0);
v_snd_1226_ = lean_ctor_get(v_b_1220_, 1);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_b_1220_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1228_ = v_b_1220_;
v_isShared_1229_ = v_isSharedCheck_1248_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_snd_1226_);
lean_inc(v_fst_1225_);
lean_dec(v_b_1220_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1248_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; 
lean_inc(v_head_1223_);
v___x_1230_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_head_1223_);
if (lean_obj_tag(v___x_1230_) == 1)
{
lean_object* v_val_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
lean_dec(v_fst_1225_);
v_val_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_val_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v___x_1232_ = l_String_Slice_toString(v_val_1231_);
lean_dec(v_val_1231_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1232_);
v___x_1234_ = v___x_1228_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_snd_1226_);
v___x_1234_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
v_as_x27_1219_ = v_tail_1224_;
v_b_1220_ = v___x_1234_;
goto _start;
}
}
else
{
lean_object* v___x_1237_; 
lean_dec(v___x_1230_);
lean_inc(v_head_1223_);
v___x_1237_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_head_1223_);
if (lean_obj_tag(v___x_1237_) == 1)
{
lean_object* v_val_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
lean_dec(v_snd_1226_);
v_val_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v___x_1239_ = l_String_Slice_toString(v_val_1238_);
lean_dec(v_val_1238_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___x_1239_);
v___x_1241_ = v___x_1228_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_fst_1225_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
v_as_x27_1219_ = v_tail_1224_;
v_b_1220_ = v___x_1241_;
goto _start;
}
}
else
{
lean_object* v___x_1245_; 
lean_dec(v___x_1237_);
if (v_isShared_1229_ == 0)
{
v___x_1245_ = v___x_1228_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_fst_1225_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_snd_1226_);
v___x_1245_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
v_as_x27_1219_ = v_tail_1224_;
v_b_1220_ = v___x_1245_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg___boxed(lean_object* v_as_x27_1249_, lean_object* v_b_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_1249_, v_b_1250_);
lean_dec(v_as_x27_1249_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(lean_object* v_s_1253_){
_start:
{
lean_object* v___x_1255_; lean_object* v_putStr_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_get_stdout();
v_putStr_1256_ = lean_ctor_get(v___x_1255_, 4);
lean_inc_ref(v_putStr_1256_);
lean_dec_ref(v___x_1255_);
v___x_1257_ = lean_apply_2(v_putStr_1256_, v_s_1253_, lean_box(0));
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2___boxed(lean_object* v_s_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v_s_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(lean_object* v_s_1261_){
_start:
{
uint32_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = 10;
v___x_1264_ = lean_string_push(v_s_1261_, v___x_1263_);
v___x_1265_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v___x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2___boxed(lean_object* v_s_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v_s_1266_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_1308_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1307_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_projectDir_1309_; lean_object* v_leanPrefix_1310_; lean_object* v_whichLake_1311_; lean_object* v_lakeHome_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___y_1316_; lean_object* v_leanPrefix_1317_; lean_object* v_whichLake_1318_; lean_object* v_lakeHome_1319_; uint8_t v___x_1374_; 
lean_dec_ref_known(v___x_1308_, 1);
v_projectDir_1309_ = lean_ctor_get(v_a_1302_, 0);
v_leanPrefix_1310_ = lean_ctor_get(v_a_1302_, 6);
v_whichLake_1311_ = lean_ctor_get(v_a_1302_, 10);
v_lakeHome_1312_ = lean_ctor_get(v_a_1302_, 11);
v___x_1313_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1309_);
v___x_1314_ = l_System_FilePath_join(v_projectDir_1309_, v___x_1313_);
v___x_1374_ = l_System_FilePath_pathExists(v___x_1314_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_io_create_dir(v___x_1314_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_dec_ref_known(v___x_1375_, 1);
v___y_1316_ = v_a_1302_;
v_leanPrefix_1317_ = v_leanPrefix_1310_;
v_whichLake_1318_ = v_whichLake_1311_;
v_lakeHome_1319_ = v_lakeHome_1312_;
goto v___jp_1315_;
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec_ref(v___x_1314_);
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
v___y_1316_ = v_a_1302_;
v_leanPrefix_1317_ = v_leanPrefix_1310_;
v_whichLake_1318_ = v_whichLake_1311_;
v_lakeHome_1319_ = v_lakeHome_1312_;
goto v___jp_1315_;
}
v___jp_1315_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_mk_empty_array_with_capacity(v___x_1320_);
v___x_1322_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__5));
v___x_1323_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8));
v___x_1324_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1325_ = lean_unsigned_to_nat(3u);
v___x_1326_ = lean_mk_empty_array_with_capacity(v___x_1325_);
lean_inc_ref(v_projectDir_1309_);
v___x_1327_ = lean_array_push(v___x_1326_, v_projectDir_1309_);
lean_inc_ref(v_leanPrefix_1317_);
v___x_1328_ = lean_array_push(v___x_1327_, v_leanPrefix_1317_);
lean_inc_ref(v_lakeHome_1319_);
v___x_1329_ = lean_array_push(v___x_1328_, v_lakeHome_1319_);
v___x_1330_ = lean_array_push(v___x_1321_, v___x_1314_);
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1333_ = 1;
v___x_1334_ = lean_box(0);
lean_inc_ref(v_whichLake_1318_);
v___x_1335_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1335_, 0, v_whichLake_1318_);
lean_ctor_set(v___x_1335_, 1, v___x_1322_);
lean_ctor_set(v___x_1335_, 2, v___x_1323_);
lean_ctor_set(v___x_1335_, 3, v___x_1324_);
lean_ctor_set(v___x_1335_, 4, v___x_1329_);
lean_ctor_set(v___x_1335_, 5, v___x_1330_);
lean_ctor_set(v___x_1335_, 6, v___x_1332_);
lean_ctor_set(v___x_1335_, 7, v___x_1334_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*8, v___x_1333_);
v___x_1336_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v___x_1335_, v___y_1316_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1365_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc_n(v_a_1337_, 2);
lean_dec_ref_known(v___x_1336_, 1);
v___x_1338_ = lean_string_utf8_byte_size(v_a_1337_);
v___x_1339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1339_, 0, v_a_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1331_);
lean_ctor_set(v___x_1339_, 2, v___x_1338_);
v___x_1340_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0);
v___x_1341_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1337_, v___x_1339_, v___x_1338_, v___x_1340_, v___x_1332_);
lean_dec_ref_known(v___x_1339_, 3);
v___x_1342_ = lean_array_to_list(v___x_1341_);
v___x_1343_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__15));
v___x_1344_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v___x_1342_, v___x_1343_);
lean_dec(v___x_1342_);
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1365_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1365_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v_fst_1349_; lean_object* v_snd_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1364_; 
v_fst_1349_ = lean_ctor_get(v_a_1345_, 0);
v_snd_1350_ = lean_ctor_get(v_a_1345_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_a_1345_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1352_ = v_a_1345_;
v_isShared_1353_ = v_isSharedCheck_1364_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_snd_1350_);
lean_inc(v_fst_1349_);
lean_dec(v_a_1345_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1364_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = lean_string_utf8_byte_size(v_fst_1349_);
v___x_1355_ = lean_nat_dec_eq(v___x_1354_, v___x_1331_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = lean_string_utf8_byte_size(v_snd_1350_);
v___x_1357_ = lean_nat_dec_eq(v___x_1356_, v___x_1331_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1359_; 
if (v_isShared_1353_ == 0)
{
v___x_1359_ = v___x_1352_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_fst_1349_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_snd_1350_);
v___x_1359_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1361_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1359_);
v___x_1361_ = v___x_1347_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
else
{
lean_del_object(v___x_1352_);
lean_dec(v_snd_1350_);
lean_dec(v_fst_1349_);
lean_del_object(v___x_1347_);
goto v___jp_1304_;
}
}
else
{
lean_del_object(v___x_1352_);
lean_dec(v_snd_1350_);
lean_dec(v_fst_1349_);
lean_del_object(v___x_1347_);
goto v___jp_1304_;
}
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
v_a_1366_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1336_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1336_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
v_a_1384_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1308_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1308_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
v___jp_1304_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__1));
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
return v___x_1306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___boxed(lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v_a_1392_);
lean_dec_ref(v_a_1392_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(lean_object* v_a_1395_, lean_object* v___x_1396_, lean_object* v___x_1397_, lean_object* v_inst_1398_, lean_object* v_R_1399_, lean_object* v_a_1400_, lean_object* v_b_1401_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1395_, v___x_1396_, v___x_1397_, v_a_1400_, v_b_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___boxed(lean_object* v_a_1403_, lean_object* v___x_1404_, lean_object* v___x_1405_, lean_object* v_inst_1406_, lean_object* v_R_1407_, lean_object* v_a_1408_, lean_object* v_b_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(v_a_1403_, v___x_1404_, v___x_1405_, v_inst_1406_, v_R_1407_, v_a_1408_, v_b_1409_);
lean_dec_ref(v___x_1404_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(lean_object* v_as_1411_, lean_object* v_as_x27_1412_, lean_object* v_b_1413_, lean_object* v_a_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_1412_, v_b_1413_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___boxed(lean_object* v_as_1418_, lean_object* v_as_x27_1419_, lean_object* v_b_1420_, lean_object* v_a_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(v_as_1418_, v_as_x27_1419_, v_b_1420_, v_a_1421_, v___y_1422_);
lean_dec_ref(v___y_1422_);
lean_dec(v_as_x27_1419_);
lean_dec(v_as_1418_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_1441_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1440_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_projectDir_1442_; lean_object* v_leanPrefix_1443_; lean_object* v_whichLake_1444_; lean_object* v_lakeHome_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___y_1449_; lean_object* v_leanPrefix_1450_; lean_object* v_whichLake_1451_; lean_object* v_lakeHome_1452_; uint8_t v___x_1469_; 
lean_dec_ref_known(v___x_1441_, 1);
v_projectDir_1442_ = lean_ctor_get(v_a_1438_, 0);
v_leanPrefix_1443_ = lean_ctor_get(v_a_1438_, 6);
v_whichLake_1444_ = lean_ctor_get(v_a_1438_, 10);
v_lakeHome_1445_ = lean_ctor_get(v_a_1438_, 11);
v___x_1446_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1442_);
v___x_1447_ = l_System_FilePath_join(v_projectDir_1442_, v___x_1446_);
v___x_1469_ = l_System_FilePath_pathExists(v___x_1447_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_io_create_dir(v___x_1447_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_dec_ref_known(v___x_1470_, 1);
v___y_1449_ = v_a_1438_;
v_leanPrefix_1450_ = v_leanPrefix_1443_;
v_whichLake_1451_ = v_whichLake_1444_;
v_lakeHome_1452_ = v_lakeHome_1445_;
goto v___jp_1448_;
}
else
{
lean_dec_ref(v___x_1447_);
return v___x_1470_;
}
}
else
{
v___y_1449_ = v_a_1438_;
v_leanPrefix_1450_ = v_leanPrefix_1443_;
v_whichLake_1451_ = v_whichLake_1444_;
v_lakeHome_1452_ = v_lakeHome_1445_;
goto v___jp_1448_;
}
v___jp_1448_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1453_ = lean_unsigned_to_nat(1u);
v___x_1454_ = lean_mk_empty_array_with_capacity(v___x_1453_);
v___x_1455_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__1));
v___x_1456_ = lean_unsigned_to_nat(3u);
v___x_1457_ = lean_mk_empty_array_with_capacity(v___x_1456_);
v___x_1458_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2));
v___x_1459_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
lean_inc_ref(v_projectDir_1442_);
v___x_1460_ = lean_array_push(v___x_1457_, v_projectDir_1442_);
lean_inc_ref(v_leanPrefix_1450_);
v___x_1461_ = lean_array_push(v___x_1460_, v_leanPrefix_1450_);
lean_inc_ref(v_lakeHome_1452_);
v___x_1462_ = lean_array_push(v___x_1461_, v_lakeHome_1452_);
v___x_1463_ = lean_array_push(v___x_1454_, v___x_1447_);
v___x_1464_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1465_ = 1;
v___x_1466_ = lean_box(0);
lean_inc_ref(v_whichLake_1451_);
v___x_1467_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1467_, 0, v_whichLake_1451_);
lean_ctor_set(v___x_1467_, 1, v___x_1455_);
lean_ctor_set(v___x_1467_, 2, v___x_1458_);
lean_ctor_set(v___x_1467_, 3, v___x_1459_);
lean_ctor_set(v___x_1467_, 4, v___x_1462_);
lean_ctor_set(v___x_1467_, 5, v___x_1463_);
lean_ctor_set(v___x_1467_, 6, v___x_1464_);
lean_ctor_set(v___x_1467_, 7, v___x_1466_);
lean_ctor_set_uint8(v___x_1467_, sizeof(void*)*8, v___x_1465_);
v___x_1468_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_1467_, v___y_1449_);
return v___x_1468_;
}
}
else
{
return v___x_1441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___boxed(lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_1471_);
lean_dec_ref(v_a_1471_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(lean_object* v_f_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v_fst_1488_; lean_object* v_snd_1489_; lean_object* v_r_1490_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref_known(v___x_1486_, 1);
v_fst_1488_ = lean_ctor_get(v_a_1487_, 0);
lean_inc(v_fst_1488_);
v_snd_1489_ = lean_ctor_get(v_a_1487_, 1);
lean_inc_n(v_snd_1489_, 2);
lean_dec(v_a_1487_);
lean_inc_ref(v___y_1484_);
v_r_1490_ = lean_apply_4(v_f_1483_, v_fst_1488_, v_snd_1489_, v___y_1484_, lean_box(0));
if (lean_obj_tag(v_r_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1492_; 
v_a_1491_ = lean_ctor_get(v_r_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v_r_1490_, 1);
v___x_1492_ = lean_io_remove_file(v_snd_1489_);
lean_dec(v_snd_1489_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; 
v_unused_1500_ = lean_ctor_get(v___x_1492_, 0);
lean_dec(v_unused_1500_);
v___x_1494_ = v___x_1492_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_dec(v___x_1492_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v_a_1491_);
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1491_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_a_1491_);
v_a_1501_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1492_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1492_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1510_; 
v_a_1509_ = lean_ctor_get(v_r_1490_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v_r_1490_, 1);
v___x_1510_ = lean_io_remove_file(v_snd_1489_);
lean_dec(v_snd_1489_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v___x_1510_, 0);
lean_dec(v_unused_1518_);
v___x_1512_ = v___x_1510_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_dec(v___x_1510_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
lean_ctor_set_tag(v___x_1512_, 1);
lean_ctor_set(v___x_1512_, 0, v_a_1509_);
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1509_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec(v_a_1509_);
v_a_1519_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1510_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1510_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec_ref(v_f_1483_);
v_a_1527_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1486_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1486_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg___boxed(lean_object* v_f_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v_f_1535_, v___y_1536_);
lean_dec_ref(v___y_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1(lean_object* v_00_u03b1_1539_, lean_object* v_f_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v_f_1540_, v___y_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___boxed(lean_object* v_00_u03b1_1544_, lean_object* v_f_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1(v_00_u03b1_1544_, v_f_1545_, v___y_1546_);
lean_dec_ref(v___y_1546_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0(lean_object* v_projectDir_1564_, lean_object* v_f_1565_, lean_object* v_handle_1566_, lean_object* v_path_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_leanPrefix_1570_; lean_object* v_whichLake_1571_; lean_object* v_lakeHome_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_leanPrefix_1570_ = lean_ctor_get(v___y_1568_, 6);
v_whichLake_1571_ = lean_ctor_get(v___y_1568_, 10);
v_lakeHome_1572_ = lean_ctor_get(v___y_1568_, 11);
v___x_1573_ = lean_unsigned_to_nat(1u);
v___x_1574_ = lean_mk_empty_array_with_capacity(v___x_1573_);
v___x_1575_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__1));
v___x_1576_ = lean_unsigned_to_nat(3u);
v___x_1577_ = lean_mk_empty_array_with_capacity(v___x_1576_);
v___x_1578_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2));
v___x_1579_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__4));
lean_inc_ref(v_projectDir_1564_);
v___x_1580_ = lean_array_push(v___x_1577_, v_projectDir_1564_);
lean_inc_ref(v_leanPrefix_1570_);
v___x_1581_ = lean_array_push(v___x_1580_, v_leanPrefix_1570_);
lean_inc_ref(v_lakeHome_1572_);
v___x_1582_ = lean_array_push(v___x_1581_, v_lakeHome_1572_);
v___x_1583_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
v___x_1584_ = l_System_FilePath_join(v_projectDir_1564_, v___x_1583_);
v___x_1585_ = lean_array_push(v___x_1574_, v___x_1584_);
v___x_1586_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1587_ = 0;
v___x_1588_ = lean_box(0);
lean_inc_ref(v_whichLake_1571_);
v___x_1589_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1589_, 0, v_whichLake_1571_);
lean_ctor_set(v___x_1589_, 1, v___x_1575_);
lean_ctor_set(v___x_1589_, 2, v___x_1578_);
lean_ctor_set(v___x_1589_, 3, v___x_1579_);
lean_ctor_set(v___x_1589_, 4, v___x_1582_);
lean_ctor_set(v___x_1589_, 5, v___x_1585_);
lean_ctor_set(v___x_1589_, 6, v___x_1586_);
lean_ctor_set(v___x_1589_, 7, v___x_1588_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*8, v___x_1587_);
v___x_1590_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_handle_1566_, v___x_1589_, v___y_1568_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v___x_1591_; 
lean_dec_ref_known(v___x_1590_, 1);
lean_inc_ref(v___y_1568_);
v___x_1591_ = lean_apply_3(v_f_1565_, v_path_1567_, v___y_1568_, lean_box(0));
return v___x_1591_;
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v_path_1567_);
lean_dec_ref(v_f_1565_);
v_a_1592_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1590_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1590_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___boxed(lean_object* v_projectDir_1600_, lean_object* v_f_1601_, lean_object* v_handle_1602_, lean_object* v_path_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0(v_projectDir_1600_, v_f_1601_, v_handle_1602_, v_path_1603_, v___y_1604_);
lean_dec_ref(v___y_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(uint8_t v_a_1607_, lean_object* v_x_1608_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 0)
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_box(0);
return v___x_1609_;
}
else
{
lean_object* v_key_1610_; lean_object* v_value_1611_; lean_object* v_tail_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v_key_1610_ = lean_ctor_get(v_x_1608_, 0);
v_value_1611_ = lean_ctor_get(v_x_1608_, 1);
v_tail_1612_ = lean_ctor_get(v_x_1608_, 2);
v___x_1613_ = lean_unbox(v_key_1610_);
v___x_1614_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v___x_1613_);
v___x_1615_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v_a_1607_);
v___x_1616_ = lean_nat_dec_eq(v___x_1614_, v___x_1615_);
lean_dec(v___x_1615_);
lean_dec(v___x_1614_);
if (v___x_1616_ == 0)
{
v_x_1608_ = v_tail_1612_;
goto _start;
}
else
{
lean_object* v___x_1618_; 
lean_inc(v_value_1611_);
v___x_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1618_, 0, v_value_1611_);
return v___x_1618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg___boxed(lean_object* v_a_1619_, lean_object* v_x_1620_){
_start:
{
uint8_t v_a_boxed_1621_; lean_object* v_res_1622_; 
v_a_boxed_1621_ = lean_unbox(v_a_1619_);
v_res_1622_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(v_a_boxed_1621_, v_x_1620_);
lean_dec(v_x_1620_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(lean_object* v_m_1623_, uint8_t v_a_1624_){
_start:
{
lean_object* v_buckets_1625_; lean_object* v___x_1626_; uint64_t v___x_1627_; uint64_t v___x_1628_; uint64_t v___x_1629_; uint64_t v_fold_1630_; uint64_t v___x_1631_; uint64_t v___x_1632_; uint64_t v___x_1633_; size_t v___x_1634_; size_t v___x_1635_; size_t v___x_1636_; size_t v___x_1637_; size_t v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_buckets_1625_ = lean_ctor_get(v_m_1623_, 1);
v___x_1626_ = lean_array_get_size(v_buckets_1625_);
v___x_1627_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_a_1624_);
v___x_1628_ = 32ULL;
v___x_1629_ = lean_uint64_shift_right(v___x_1627_, v___x_1628_);
v_fold_1630_ = lean_uint64_xor(v___x_1627_, v___x_1629_);
v___x_1631_ = 16ULL;
v___x_1632_ = lean_uint64_shift_right(v_fold_1630_, v___x_1631_);
v___x_1633_ = lean_uint64_xor(v_fold_1630_, v___x_1632_);
v___x_1634_ = lean_uint64_to_usize(v___x_1633_);
v___x_1635_ = lean_usize_of_nat(v___x_1626_);
v___x_1636_ = ((size_t)1ULL);
v___x_1637_ = lean_usize_sub(v___x_1635_, v___x_1636_);
v___x_1638_ = lean_usize_land(v___x_1634_, v___x_1637_);
v___x_1639_ = lean_array_uget_borrowed(v_buckets_1625_, v___x_1638_);
v___x_1640_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(v_a_1624_, v___x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg___boxed(lean_object* v_m_1641_, lean_object* v_a_1642_){
_start:
{
uint8_t v_a_boxed_1643_; lean_object* v_res_1644_; 
v_a_boxed_1643_ = lean_unbox(v_a_1642_);
v_res_1644_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_m_1641_, v_a_boxed_1643_);
lean_dec_ref(v_m_1641_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(lean_object* v_f_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_projectDir_1649_; lean_object* v_moduleStore_1650_; uint8_t v___x_1651_; lean_object* v___x_1652_; 
v_projectDir_1649_ = lean_ctor_get(v_a_1647_, 0);
v_moduleStore_1650_ = lean_ctor_get(v_a_1647_, 17);
v___x_1651_ = 0;
v___x_1652_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_moduleStore_1650_, v___x_1651_);
if (lean_obj_tag(v___x_1652_) == 1)
{
lean_object* v_val_1653_; lean_object* v___x_1654_; 
v_val_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_val_1653_);
lean_dec_ref_known(v___x_1652_, 1);
lean_inc_ref(v_a_1647_);
v___x_1654_ = lean_apply_3(v_f_1646_, v_val_1653_, v_a_1647_, lean_box(0));
return v___x_1654_;
}
else
{
lean_object* v___f_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec(v___x_1652_);
lean_inc_ref(v_projectDir_1649_);
v___f_1655_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_1655_, 0, v_projectDir_1649_);
lean_closure_set(v___f_1655_, 1, v_f_1646_);
v___x_1656_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___closed__0));
v___x_1657_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1656_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v___x_1658_; 
lean_dec_ref_known(v___x_1657_, 1);
v___x_1658_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v___f_1655_, v_a_1647_);
return v___x_1658_;
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v___f_1655_);
v_a_1659_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1657_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1657_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___boxed(lean_object* v_f_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v_f_1667_, v_a_1668_);
lean_dec_ref(v_a_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport(lean_object* v_00_u03b1_1671_, lean_object* v_f_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v_f_1672_, v_a_1673_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___boxed(lean_object* v_00_u03b1_1676_, lean_object* v_f_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport(v_00_u03b1_1676_, v_f_1677_, v_a_1678_);
lean_dec_ref(v_a_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0(lean_object* v_00_u03b2_1681_, lean_object* v_m_1682_, uint8_t v_a_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_m_1682_, v_a_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___boxed(lean_object* v_00_u03b2_1685_, lean_object* v_m_1686_, lean_object* v_a_1687_){
_start:
{
uint8_t v_a_boxed_1688_; lean_object* v_res_1689_; 
v_a_boxed_1688_ = lean_unbox(v_a_1687_);
v_res_1689_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0(v_00_u03b2_1685_, v_m_1686_, v_a_boxed_1688_);
lean_dec_ref(v_m_1686_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0(lean_object* v_00_u03b2_1690_, uint8_t v_a_1691_, lean_object* v_x_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(v_a_1691_, v_x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1694_, lean_object* v_a_1695_, lean_object* v_x_1696_){
_start:
{
uint8_t v_a_boxed_1697_; lean_object* v_res_1698_; 
v_a_boxed_1697_ = lean_unbox(v_a_1695_);
v_res_1698_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0(v_00_u03b2_1694_, v_a_boxed_1697_, v_x_1696_);
lean_dec(v_x_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(size_t v_sz_1699_, size_t v_i_1700_, lean_object* v_bs_1701_){
_start:
{
uint8_t v___x_1702_; 
v___x_1702_ = lean_usize_dec_lt(v_i_1700_, v_sz_1699_);
if (v___x_1702_ == 0)
{
return v_bs_1701_;
}
else
{
lean_object* v_v_1703_; lean_object* v___x_1704_; lean_object* v_bs_x27_1705_; lean_object* v___x_1706_; size_t v___x_1707_; size_t v___x_1708_; lean_object* v___x_1709_; 
v_v_1703_ = lean_array_uget(v_bs_1701_, v_i_1700_);
v___x_1704_ = lean_unsigned_to_nat(0u);
v_bs_x27_1705_ = lean_array_uset(v_bs_1701_, v_i_1700_, v___x_1704_);
v___x_1706_ = l_Lean_Name_toString(v_v_1703_, v___x_1702_);
v___x_1707_ = ((size_t)1ULL);
v___x_1708_ = lean_usize_add(v_i_1700_, v___x_1707_);
v___x_1709_ = lean_array_uset(v_bs_x27_1705_, v_i_1700_, v___x_1706_);
v_i_1700_ = v___x_1708_;
v_bs_1701_ = v___x_1709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0___boxed(lean_object* v_sz_1711_, lean_object* v_i_1712_, lean_object* v_bs_1713_){
_start:
{
size_t v_sz_boxed_1714_; size_t v_i_boxed_1715_; lean_object* v_res_1716_; 
v_sz_boxed_1714_ = lean_unbox_usize(v_sz_1711_);
lean_dec(v_sz_1711_);
v_i_boxed_1715_ = lean_unbox_usize(v_i_1712_);
lean_dec(v_i_1712_);
v_res_1716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_boxed_1714_, v_i_boxed_1715_, v_bs_1713_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(lean_object* v_targets_1724_, lean_object* v_a_1725_){
_start:
{
size_t v_sz_1727_; size_t v___x_1728_; lean_object* v_targetArgs_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v_targetList_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_sz_1727_ = lean_array_size(v_targets_1724_);
v___x_1728_ = ((size_t)0ULL);
v_targetArgs_1729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_1727_, v___x_1728_, v_targets_1724_);
v___x_1730_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
lean_inc_ref(v_targetArgs_1729_);
v___x_1731_ = lean_array_to_list(v_targetArgs_1729_);
v_targetList_1732_ = l_String_intercalate(v___x_1730_, v___x_1731_);
v___x_1733_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1));
v___x_1734_ = lean_string_append(v___x_1733_, v_targetList_1732_);
lean_dec_ref(v_targetList_1732_);
v___x_1735_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1734_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_projectDir_1736_; lean_object* v_leanPrefix_1737_; lean_object* v_whichLake_1738_; lean_object* v_lakeHome_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___y_1743_; lean_object* v_leanPrefix_1744_; lean_object* v_whichLake_1745_; lean_object* v_lakeHome_1746_; uint8_t v___x_1764_; 
lean_dec_ref_known(v___x_1735_, 1);
v_projectDir_1736_ = lean_ctor_get(v_a_1725_, 0);
v_leanPrefix_1737_ = lean_ctor_get(v_a_1725_, 6);
v_whichLake_1738_ = lean_ctor_get(v_a_1725_, 10);
v_lakeHome_1739_ = lean_ctor_get(v_a_1725_, 11);
v___x_1740_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1736_);
v___x_1741_ = l_System_FilePath_join(v_projectDir_1736_, v___x_1740_);
v___x_1764_ = l_System_FilePath_pathExists(v___x_1741_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_io_create_dir(v___x_1741_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_dec_ref_known(v___x_1765_, 1);
v___y_1743_ = v_a_1725_;
v_leanPrefix_1744_ = v_leanPrefix_1737_;
v_whichLake_1745_ = v_whichLake_1738_;
v_lakeHome_1746_ = v_lakeHome_1739_;
goto v___jp_1742_;
}
else
{
lean_dec_ref(v___x_1741_);
lean_dec_ref(v_targetArgs_1729_);
return v___x_1765_;
}
}
else
{
v___y_1743_ = v_a_1725_;
v_leanPrefix_1744_ = v_leanPrefix_1737_;
v_whichLake_1745_ = v_whichLake_1738_;
v_lakeHome_1746_ = v_lakeHome_1739_;
goto v___jp_1742_;
}
v___jp_1742_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = lean_mk_empty_array_with_capacity(v___x_1747_);
v___x_1749_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3));
v___x_1750_ = l_Array_append___redArg(v___x_1749_, v_targetArgs_1729_);
lean_dec_ref(v_targetArgs_1729_);
v___x_1751_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8));
v___x_1752_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1753_ = lean_unsigned_to_nat(3u);
v___x_1754_ = lean_mk_empty_array_with_capacity(v___x_1753_);
lean_inc_ref(v_projectDir_1736_);
v___x_1755_ = lean_array_push(v___x_1754_, v_projectDir_1736_);
lean_inc_ref(v_leanPrefix_1744_);
v___x_1756_ = lean_array_push(v___x_1755_, v_leanPrefix_1744_);
lean_inc_ref(v_lakeHome_1746_);
v___x_1757_ = lean_array_push(v___x_1756_, v_lakeHome_1746_);
v___x_1758_ = lean_array_push(v___x_1748_, v___x_1741_);
v___x_1759_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1760_ = 0;
v___x_1761_ = lean_box(0);
lean_inc_ref(v_whichLake_1745_);
v___x_1762_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1762_, 0, v_whichLake_1745_);
lean_ctor_set(v___x_1762_, 1, v___x_1750_);
lean_ctor_set(v___x_1762_, 2, v___x_1751_);
lean_ctor_set(v___x_1762_, 3, v___x_1752_);
lean_ctor_set(v___x_1762_, 4, v___x_1757_);
lean_ctor_set(v___x_1762_, 5, v___x_1758_);
lean_ctor_set(v___x_1762_, 6, v___x_1759_);
lean_ctor_set(v___x_1762_, 7, v___x_1761_);
lean_ctor_set_uint8(v___x_1762_, sizeof(void*)*8, v___x_1760_);
v___x_1763_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_1762_, v___y_1743_);
return v___x_1763_;
}
}
else
{
lean_dec_ref(v_targetArgs_1729_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___boxed(lean_object* v_targets_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v_targets_1766_, v_a_1767_);
lean_dec_ref(v_a_1767_);
return v_res_1769_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1779_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11));
v___x_1780_ = lean_unsigned_to_nat(3u);
v___x_1781_ = lean_mk_empty_array_with_capacity(v___x_1780_);
v___x_1782_ = lean_array_push(v___x_1781_, v___x_1779_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(lean_object* v_projectDir_1783_, lean_object* v_whichLean4Export_1784_, lean_object* v_args_1785_, lean_object* v_f_1786_, lean_object* v_exportHandle_1787_, lean_object* v_exportPath_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_leanPrefix_1791_; lean_object* v_leanPath_1792_; lean_object* v_binPath_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_leanPrefix_1791_ = lean_ctor_get(v___y_1789_, 6);
v_leanPath_1792_ = lean_ctor_get(v___y_1789_, 7);
v_binPath_1793_ = lean_ctor_get(v___y_1789_, 8);
v___x_1794_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6));
v___x_1795_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__0));
v___x_1796_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__1));
lean_inc_ref(v_leanPath_1792_);
v___x_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1797_, 0, v_leanPath_1792_);
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1795_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
lean_inc_ref(v_binPath_1793_);
v___x_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1799_, 0, v_binPath_1793_);
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1794_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2);
v___x_1802_ = lean_array_push(v___x_1801_, v___x_1798_);
v___x_1803_ = lean_array_push(v___x_1802_, v___x_1800_);
v___x_1804_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1783_);
v___x_1805_ = l_System_FilePath_join(v_projectDir_1783_, v___x_1804_);
v___x_1806_ = lean_unsigned_to_nat(4u);
v___x_1807_ = lean_mk_empty_array_with_capacity(v___x_1806_);
v___x_1808_ = lean_array_push(v___x_1807_, v_projectDir_1783_);
v___x_1809_ = lean_array_push(v___x_1808_, v___x_1805_);
lean_inc_ref(v_leanPrefix_1791_);
v___x_1810_ = lean_array_push(v___x_1809_, v_leanPrefix_1791_);
lean_inc_ref(v_whichLean4Export_1784_);
v___x_1811_ = lean_array_push(v___x_1810_, v_whichLean4Export_1784_);
v___x_1812_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1813_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1814_ = 0;
v___x_1815_ = lean_box(0);
v___x_1816_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1816_, 0, v_whichLean4Export_1784_);
lean_ctor_set(v___x_1816_, 1, v_args_1785_);
lean_ctor_set(v___x_1816_, 2, v___x_1796_);
lean_ctor_set(v___x_1816_, 3, v___x_1803_);
lean_ctor_set(v___x_1816_, 4, v___x_1811_);
lean_ctor_set(v___x_1816_, 5, v___x_1812_);
lean_ctor_set(v___x_1816_, 6, v___x_1813_);
lean_ctor_set(v___x_1816_, 7, v___x_1815_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*8, v___x_1814_);
v___x_1817_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_exportHandle_1787_, v___x_1816_, v___y_1789_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v___x_1818_; 
lean_dec_ref_known(v___x_1817_, 1);
lean_inc_ref(v___y_1789_);
v___x_1818_ = lean_apply_3(v_f_1786_, v_exportPath_1788_, v___y_1789_, lean_box(0));
return v___x_1818_;
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec_ref(v_exportPath_1788_);
lean_dec_ref(v_f_1786_);
v_a_1819_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1817_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1817_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___boxed(lean_object* v_projectDir_1827_, lean_object* v_whichLean4Export_1828_, lean_object* v_args_1829_, lean_object* v_f_1830_, lean_object* v_exportHandle_1831_, lean_object* v_exportPath_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(v_projectDir_1827_, v_whichLean4Export_1828_, v_args_1829_, v_f_1830_, v_exportHandle_1831_, v_exportPath_1832_, v___y_1833_);
lean_dec_ref(v___y_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(lean_object* v_args_1836_, lean_object* v_f_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_projectDir_1840_; lean_object* v_whichLean4Export_1841_; lean_object* v___f_1842_; lean_object* v___x_1843_; 
v_projectDir_1840_ = lean_ctor_get(v_a_1838_, 0);
v_whichLean4Export_1841_ = lean_ctor_get(v_a_1838_, 12);
lean_inc_ref(v_whichLean4Export_1841_);
lean_inc_ref(v_projectDir_1840_);
v___f_1842_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_1842_, 0, v_projectDir_1840_);
lean_closure_set(v___f_1842_, 1, v_whichLean4Export_1841_);
lean_closure_set(v___f_1842_, 2, v_args_1836_);
lean_closure_set(v___f_1842_, 3, v_f_1837_);
v___x_1843_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v___f_1842_, v_a_1838_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___boxed(lean_object* v_args_1844_, lean_object* v_f_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v_args_1844_, v_f_1845_, v_a_1846_);
lean_dec_ref(v_a_1846_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(lean_object* v_00_u03b1_1849_, lean_object* v_args_1850_, lean_object* v_f_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v_args_1850_, v_f_1851_, v_a_1852_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___boxed(lean_object* v_00_u03b1_1855_, lean_object* v_args_1856_, lean_object* v_f_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(v_00_u03b1_1855_, v_args_1856_, v_f_1857_, v_a_1858_);
lean_dec_ref(v_a_1858_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0(lean_object* v_x_1862_, lean_object* v_x_1863_){
_start:
{
if (lean_obj_tag(v_x_1863_) == 0)
{
return v_x_1862_;
}
else
{
lean_object* v_head_1864_; lean_object* v_tail_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_head_1864_ = lean_ctor_get(v_x_1863_, 0);
lean_inc(v_head_1864_);
v_tail_1865_ = lean_ctor_get(v_x_1863_, 1);
lean_inc(v_tail_1865_);
lean_dec_ref_known(v_x_1863_, 2);
v___x_1866_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0));
v___x_1867_ = lean_string_append(v_x_1862_, v___x_1866_);
v___x_1868_ = 1;
v___x_1869_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1864_, v___x_1868_);
v___x_1870_ = lean_string_append(v___x_1867_, v___x_1869_);
lean_dec_ref(v___x_1869_);
v_x_1862_ = v___x_1870_;
v_x_1863_ = v_tail_1865_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0(lean_object* v_x_1875_){
_start:
{
if (lean_obj_tag(v_x_1875_) == 0)
{
lean_object* v___x_1876_; 
v___x_1876_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__0));
return v___x_1876_;
}
else
{
lean_object* v_tail_1877_; 
v_tail_1877_ = lean_ctor_get(v_x_1875_, 1);
if (lean_obj_tag(v_tail_1877_) == 0)
{
lean_object* v_head_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_head_1878_ = lean_ctor_get(v_x_1875_, 0);
lean_inc(v_head_1878_);
lean_dec_ref_known(v_x_1875_, 2);
v___x_1879_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_1880_ = 1;
v___x_1881_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1878_, v___x_1880_);
v___x_1882_ = lean_string_append(v___x_1879_, v___x_1881_);
lean_dec_ref(v___x_1881_);
v___x_1883_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__2));
v___x_1884_ = lean_string_append(v___x_1882_, v___x_1883_);
return v___x_1884_;
}
else
{
lean_object* v_head_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; uint32_t v___x_1891_; lean_object* v___x_1892_; 
lean_inc(v_tail_1877_);
v_head_1885_ = lean_ctor_get(v_x_1875_, 0);
lean_inc(v_head_1885_);
lean_dec_ref_known(v_x_1875_, 2);
v___x_1886_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_1887_ = 1;
v___x_1888_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1885_, v___x_1887_);
v___x_1889_ = lean_string_append(v___x_1886_, v___x_1888_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0(v___x_1889_, v_tail_1877_);
v___x_1891_ = 93;
v___x_1892_ = lean_string_push(v___x_1890_, v___x_1891_);
return v___x_1892_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(size_t v_sz_1893_, size_t v_i_1894_, lean_object* v_bs_1895_){
_start:
{
uint8_t v___x_1896_; 
v___x_1896_ = lean_usize_dec_lt(v_i_1894_, v_sz_1893_);
if (v___x_1896_ == 0)
{
return v_bs_1895_;
}
else
{
lean_object* v_v_1897_; lean_object* v___x_1898_; lean_object* v_bs_x27_1899_; lean_object* v___x_1900_; size_t v___x_1901_; size_t v___x_1902_; lean_object* v___x_1903_; 
v_v_1897_ = lean_array_uget(v_bs_1895_, v_i_1894_);
v___x_1898_ = lean_unsigned_to_nat(0u);
v_bs_x27_1899_ = lean_array_uset(v_bs_1895_, v_i_1894_, v___x_1898_);
v___x_1900_ = l_Lean_Name_toString(v_v_1897_, v___x_1896_);
v___x_1901_ = ((size_t)1ULL);
v___x_1902_ = lean_usize_add(v_i_1894_, v___x_1901_);
v___x_1903_ = lean_array_uset(v_bs_x27_1899_, v_i_1894_, v___x_1900_);
v_i_1894_ = v___x_1902_;
v_bs_1895_ = v___x_1903_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1___boxed(lean_object* v_sz_1905_, lean_object* v_i_1906_, lean_object* v_bs_1907_){
_start:
{
size_t v_sz_boxed_1908_; size_t v_i_boxed_1909_; lean_object* v_res_1910_; 
v_sz_boxed_1908_ = lean_unbox_usize(v_sz_1905_);
lean_dec(v_sz_1905_);
v_i_boxed_1909_ = lean_unbox_usize(v_i_1906_);
lean_dec(v_i_1906_);
v_res_1910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(v_sz_boxed_1908_, v_i_boxed_1909_, v_bs_1907_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(lean_object* v_module_1914_, lean_object* v_decls_1915_, lean_object* v_f_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1919_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__0));
v___x_1920_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__1));
lean_inc_ref(v_decls_1915_);
v___x_1921_ = lean_array_to_list(v_decls_1915_);
v___x_1922_ = l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0(v___x_1921_);
v___x_1923_ = lean_string_append(v___x_1920_, v___x_1922_);
lean_dec_ref(v___x_1922_);
v___x_1924_ = lean_string_append(v___x_1919_, v___x_1923_);
lean_dec_ref(v___x_1923_);
v___x_1925_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__2));
v___x_1926_ = lean_string_append(v___x_1924_, v___x_1925_);
v___x_1927_ = 1;
lean_inc(v_module_1914_);
v___x_1928_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_1914_, v___x_1927_);
v___x_1929_ = lean_string_append(v___x_1926_, v___x_1928_);
lean_dec_ref(v___x_1928_);
v___x_1930_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1929_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; size_t v_sz_1937_; size_t v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec_ref_known(v___x_1930_, 1);
v___x_1931_ = l_Lean_Name_toString(v_module_1914_, v___x_1927_);
v___x_1932_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__8));
v___x_1933_ = lean_unsigned_to_nat(2u);
v___x_1934_ = lean_mk_empty_array_with_capacity(v___x_1933_);
v___x_1935_ = lean_array_push(v___x_1934_, v___x_1931_);
v___x_1936_ = lean_array_push(v___x_1935_, v___x_1932_);
v_sz_1937_ = lean_array_size(v_decls_1915_);
v___x_1938_ = ((size_t)0ULL);
v___x_1939_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(v_sz_1937_, v___x_1938_, v_decls_1915_);
v___x_1940_ = l_Array_append___redArg(v___x_1936_, v___x_1939_);
lean_dec_ref(v___x_1939_);
v___x_1941_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v___x_1940_, v_f_1916_, v_a_1917_);
return v___x_1941_;
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec_ref(v_f_1916_);
lean_dec_ref(v_decls_1915_);
lean_dec(v_module_1914_);
v_a_1942_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1930_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1930_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___boxed(lean_object* v_module_1950_, lean_object* v_decls_1951_, lean_object* v_f_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1950_, v_decls_1951_, v_f_1952_, v_a_1953_);
lean_dec_ref(v_a_1953_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(lean_object* v_00_u03b1_1956_, lean_object* v_module_1957_, lean_object* v_decls_1958_, lean_object* v_f_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1957_, v_decls_1958_, v_f_1959_, v_a_1960_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___boxed(lean_object* v_00_u03b1_1963_, lean_object* v_module_1964_, lean_object* v_decls_1965_, lean_object* v_f_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(v_00_u03b1_1963_, v_module_1964_, v_decls_1965_, v_f_1966_, v_a_1967_);
lean_dec_ref(v_a_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(uint8_t v_kind_1970_, lean_object* v_module_1971_, lean_object* v_decls_1972_, lean_object* v_f_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_moduleStore_1976_; lean_object* v___x_1977_; 
v_moduleStore_1976_ = lean_ctor_get(v_a_1974_, 17);
v___x_1977_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_moduleStore_1976_, v_kind_1970_);
if (lean_obj_tag(v___x_1977_) == 1)
{
lean_object* v_val_1978_; lean_object* v___x_1979_; 
lean_dec_ref(v_decls_1972_);
lean_dec(v_module_1971_);
v_val_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_val_1978_);
lean_dec_ref_known(v___x_1977_, 1);
lean_inc_ref(v_a_1974_);
v___x_1979_ = lean_apply_3(v_f_1973_, v_val_1978_, v_a_1974_, lean_box(0));
return v___x_1979_;
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
lean_dec(v___x_1977_);
v___x_1980_ = lean_unsigned_to_nat(1u);
v___x_1981_ = lean_mk_empty_array_with_capacity(v___x_1980_);
lean_inc(v_module_1971_);
v___x_1982_ = lean_array_push(v___x_1981_, v_module_1971_);
v___x_1983_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v___x_1982_, v_a_1974_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v___x_1984_; 
lean_dec_ref_known(v___x_1983_, 1);
v___x_1984_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1971_, v_decls_1972_, v_f_1973_, v_a_1974_);
return v___x_1984_;
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec_ref(v_f_1973_);
lean_dec_ref(v_decls_1972_);
lean_dec(v_module_1971_);
v_a_1985_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1983_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1983_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___boxed(lean_object* v_kind_1993_, lean_object* v_module_1994_, lean_object* v_decls_1995_, lean_object* v_f_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
uint8_t v_kind_boxed_1999_; lean_object* v_res_2000_; 
v_kind_boxed_1999_ = lean_unbox(v_kind_1993_);
v_res_2000_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v_kind_boxed_1999_, v_module_1994_, v_decls_1995_, v_f_1996_, v_a_1997_);
lean_dec_ref(v_a_1997_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(lean_object* v_00_u03b1_2001_, uint8_t v_kind_2002_, lean_object* v_module_2003_, lean_object* v_decls_2004_, lean_object* v_f_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v_kind_2002_, v_module_2003_, v_decls_2004_, v_f_2005_, v_a_2006_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___boxed(lean_object* v_00_u03b1_2009_, lean_object* v_kind_2010_, lean_object* v_module_2011_, lean_object* v_decls_2012_, lean_object* v_f_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
uint8_t v_kind_boxed_2016_; lean_object* v_res_2017_; 
v_kind_boxed_2016_ = lean_unbox(v_kind_2010_);
v_res_2017_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(v_00_u03b1_2009_, v_kind_boxed_2016_, v_module_2011_, v_decls_2012_, v_f_2013_, v_a_2014_);
lean_dec_ref(v_a_2014_);
return v_res_2017_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(lean_object* v_s_2018_, lean_object* v_a_2019_, uint8_t v_b_2020_){
_start:
{
uint8_t v___x_2021_; 
v___x_2021_ = 0;
switch(lean_obj_tag(v_a_2019_))
{
case 0:
{
lean_object* v_pos_2022_; lean_object* v_startInclusive_2023_; lean_object* v_endExclusive_2024_; lean_object* v___x_2025_; uint8_t v_decide_2026_; 
v_pos_2022_ = lean_ctor_get(v_a_2019_, 0);
lean_inc(v_pos_2022_);
lean_dec_ref_known(v_a_2019_, 1);
v_startInclusive_2023_ = lean_ctor_get(v_s_2018_, 1);
v_endExclusive_2024_ = lean_ctor_get(v_s_2018_, 2);
v___x_2025_ = lean_nat_sub(v_endExclusive_2024_, v_startInclusive_2023_);
v_decide_2026_ = lean_nat_dec_eq(v_pos_2022_, v___x_2025_);
lean_dec(v___x_2025_);
lean_dec(v_pos_2022_);
if (v_decide_2026_ == 0)
{
uint8_t v___x_2027_; 
v___x_2027_ = 1;
return v___x_2027_;
}
else
{
return v_decide_2026_;
}
}
case 1:
{
lean_object* v_pos_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2041_; 
v_pos_2028_ = lean_ctor_get(v_a_2019_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_a_2019_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2030_ = v_a_2019_;
v_isShared_2031_ = v_isSharedCheck_2041_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_pos_2028_);
lean_dec(v_a_2019_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2041_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_str_2032_; lean_object* v_startInclusive_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v_str_2032_ = lean_ctor_get(v_s_2018_, 0);
v_startInclusive_2033_ = lean_ctor_get(v_s_2018_, 1);
v___x_2034_ = lean_nat_add(v_startInclusive_2033_, v_pos_2028_);
lean_dec(v_pos_2028_);
v___x_2035_ = lean_string_utf8_next_fast(v_str_2032_, v___x_2034_);
lean_dec(v___x_2034_);
v___x_2036_ = lean_nat_sub(v___x_2035_, v_startInclusive_2033_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2036_);
v___x_2038_ = v___x_2030_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
v_a_2019_ = v___x_2038_;
v_b_2020_ = v___x_2021_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2042_; lean_object* v_table_2043_; lean_object* v_stackPos_2044_; lean_object* v_needlePos_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2100_; 
v_needle_2042_ = lean_ctor_get(v_a_2019_, 0);
v_table_2043_ = lean_ctor_get(v_a_2019_, 1);
v_stackPos_2044_ = lean_ctor_get(v_a_2019_, 2);
v_needlePos_2045_ = lean_ctor_get(v_a_2019_, 3);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_a_2019_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2047_ = v_a_2019_;
v_isShared_2048_ = v_isSharedCheck_2100_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_needlePos_2045_);
lean_inc(v_stackPos_2044_);
lean_inc(v_table_2043_);
lean_inc(v_needle_2042_);
lean_dec(v_a_2019_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2100_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v_str_2049_; lean_object* v_startInclusive_2050_; lean_object* v_endExclusive_2051_; lean_object* v_str_2052_; lean_object* v_startInclusive_2053_; lean_object* v_endExclusive_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v_str_2049_ = lean_ctor_get(v_needle_2042_, 0);
v_startInclusive_2050_ = lean_ctor_get(v_needle_2042_, 1);
v_endExclusive_2051_ = lean_ctor_get(v_needle_2042_, 2);
v_str_2052_ = lean_ctor_get(v_s_2018_, 0);
v_startInclusive_2053_ = lean_ctor_get(v_s_2018_, 1);
v_endExclusive_2054_ = lean_ctor_get(v_s_2018_, 2);
v___x_2055_ = lean_nat_sub(v_stackPos_2044_, v_needlePos_2045_);
v___x_2056_ = lean_nat_sub(v_endExclusive_2051_, v_startInclusive_2050_);
v___x_2057_ = lean_nat_add(v___x_2055_, v___x_2056_);
v___x_2058_ = lean_nat_sub(v_endExclusive_2054_, v_startInclusive_2053_);
v___x_2059_ = lean_nat_dec_le(v___x_2057_, v___x_2058_);
lean_dec(v___x_2057_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
lean_dec(v___x_2056_);
lean_del_object(v___x_2047_);
lean_dec(v_needlePos_2045_);
lean_dec(v_stackPos_2044_);
lean_dec_ref(v_table_2043_);
lean_dec_ref(v_needle_2042_);
v___x_2060_ = lean_unsigned_to_nat(1u);
v___x_2061_ = lean_nat_add(v___x_2055_, v___x_2060_);
lean_dec(v___x_2055_);
v___x_2062_ = lean_nat_dec_le(v___x_2061_, v___x_2058_);
lean_dec(v___x_2058_);
lean_dec(v___x_2061_);
if (v___x_2062_ == 0)
{
return v_b_2020_;
}
else
{
lean_object* v___x_2063_; 
v___x_2063_ = lean_box(3);
v_a_2019_ = v___x_2063_;
v_b_2020_ = v___x_2021_;
goto _start;
}
}
else
{
lean_object* v___x_2065_; uint8_t v_stackByte_2066_; lean_object* v___x_2067_; uint8_t v_patByte_2068_; uint8_t v___x_2069_; 
lean_dec(v___x_2058_);
lean_dec(v___x_2055_);
v___x_2065_ = lean_nat_add(v_startInclusive_2053_, v_stackPos_2044_);
v_stackByte_2066_ = lean_string_get_byte_fast(v_str_2052_, v___x_2065_);
v___x_2067_ = lean_nat_add(v_startInclusive_2050_, v_needlePos_2045_);
v_patByte_2068_ = lean_string_get_byte_fast(v_str_2049_, v___x_2067_);
v___x_2069_ = lean_uint8_dec_eq(v_stackByte_2066_, v_patByte_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; uint8_t v_decide_2071_; 
lean_dec(v___x_2056_);
v___x_2070_ = lean_unsigned_to_nat(0u);
v_decide_2071_ = lean_nat_dec_eq(v_needlePos_2045_, v___x_2070_);
if (v_decide_2071_ == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v_newNeedlePos_2074_; uint8_t v___x_2075_; 
v___x_2072_ = lean_unsigned_to_nat(1u);
v___x_2073_ = lean_nat_sub(v_needlePos_2045_, v___x_2072_);
lean_dec(v_needlePos_2045_);
v_newNeedlePos_2074_ = lean_array_fget_borrowed(v_table_2043_, v___x_2073_);
lean_dec(v___x_2073_);
v___x_2075_ = lean_nat_dec_eq(v_newNeedlePos_2074_, v___x_2070_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2077_; 
lean_inc(v_newNeedlePos_2074_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 3, v_newNeedlePos_2074_);
v___x_2077_ = v___x_2047_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_needle_2042_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_table_2043_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_stackPos_2044_);
lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_newNeedlePos_2074_);
v___x_2077_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
v_a_2019_ = v___x_2077_;
v_b_2020_ = v___x_2021_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2080_; lean_object* v___x_2082_; 
v_nextStackPos_2080_ = l_String_Slice_posGE___redArg(v_s_2018_, v_stackPos_2044_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 3, v___x_2070_);
lean_ctor_set(v___x_2047_, 2, v_nextStackPos_2080_);
v___x_2082_ = v___x_2047_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_needle_2042_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_table_2043_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_nextStackPos_2080_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v___x_2070_);
v___x_2082_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
v_a_2019_ = v___x_2082_;
v_b_2020_ = v___x_2021_;
goto _start;
}
}
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v_nextStackPos_2087_; lean_object* v___x_2089_; 
lean_dec(v_needlePos_2045_);
v___x_2085_ = lean_unsigned_to_nat(1u);
v___x_2086_ = lean_nat_add(v_stackPos_2044_, v___x_2085_);
lean_dec(v_stackPos_2044_);
v_nextStackPos_2087_ = l_String_Slice_posGE___redArg(v_s_2018_, v___x_2086_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 3, v___x_2070_);
lean_ctor_set(v___x_2047_, 2, v_nextStackPos_2087_);
v___x_2089_ = v___x_2047_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_needle_2042_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_table_2043_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_nextStackPos_2087_);
lean_ctor_set(v_reuseFailAlloc_2091_, 3, v___x_2070_);
v___x_2089_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
v_a_2019_ = v___x_2089_;
v_b_2020_ = v___x_2021_;
goto _start;
}
}
}
else
{
lean_object* v___x_2092_; lean_object* v_nextNeedlePos_2093_; uint8_t v_decide_2094_; 
v___x_2092_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2093_ = lean_nat_add(v_needlePos_2045_, v___x_2092_);
lean_dec(v_needlePos_2045_);
v_decide_2094_ = lean_nat_dec_eq(v_nextNeedlePos_2093_, v___x_2056_);
lean_dec(v___x_2056_);
if (v_decide_2094_ == 0)
{
lean_object* v_nextStackPos_2095_; lean_object* v___x_2097_; 
v_nextStackPos_2095_ = lean_nat_add(v_stackPos_2044_, v___x_2092_);
lean_dec(v_stackPos_2044_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 3, v_nextNeedlePos_2093_);
lean_ctor_set(v___x_2047_, 2, v_nextStackPos_2095_);
v___x_2097_ = v___x_2047_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_needle_2042_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_table_2043_);
lean_ctor_set(v_reuseFailAlloc_2099_, 2, v_nextStackPos_2095_);
lean_ctor_set(v_reuseFailAlloc_2099_, 3, v_nextNeedlePos_2093_);
v___x_2097_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
v_a_2019_ = v___x_2097_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2093_);
lean_del_object(v___x_2047_);
lean_dec(v_stackPos_2044_);
lean_dec_ref(v_table_2043_);
lean_dec_ref(v_needle_2042_);
return v_decide_2094_;
}
}
}
}
}
default: 
{
return v_b_2020_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg___boxed(lean_object* v_s_2101_, lean_object* v_a_2102_, lean_object* v_b_2103_){
_start:
{
uint8_t v_b_boxed_2104_; uint8_t v_res_2105_; lean_object* v_r_2106_; 
v_b_boxed_2104_ = lean_unbox(v_b_2103_);
v_res_2105_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_2101_, v_a_2102_, v_b_boxed_2104_);
lean_dec_ref(v_s_2101_);
v_r_2106_ = lean_box(v_res_2105_);
return v_r_2106_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1));
v___x_2113_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2112_);
return v___x_2113_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2115_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2);
v___x_2116_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1));
v___x_2117_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
lean_ctor_set(v___x_2117_, 1, v___x_2115_);
lean_ctor_set(v___x_2117_, 2, v___x_2114_);
lean_ctor_set(v___x_2117_, 3, v___x_2114_);
return v___x_2117_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(lean_object* v_s_2118_){
_start:
{
lean_object* v___x_2119_; uint8_t v___x_2120_; uint8_t v___x_2121_; 
v___x_2119_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3);
v___x_2120_ = 0;
v___x_2121_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_2118_, v___x_2119_, v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___boxed(lean_object* v_s_2122_){
_start:
{
uint8_t v_res_2123_; lean_object* v_r_2124_; 
v_res_2123_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v_s_2122_);
lean_dec_ref(v_s_2122_);
v_r_2124_ = lean_box(v_res_2123_);
return v_r_2124_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(lean_object* v_kernelName_2125_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = lean_string_utf8_byte_size(v_kernelName_2125_);
v___x_2128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2128_, 0, v_kernelName_2125_);
lean_ctor_set(v___x_2128_, 1, v___x_2126_);
lean_ctor_set(v___x_2128_, 2, v___x_2127_);
v___x_2129_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v___x_2128_);
lean_dec_ref_known(v___x_2128_, 3);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel___boxed(lean_object* v_kernelName_2130_){
_start:
{
uint8_t v_res_2131_; lean_object* v_r_2132_; 
v_res_2131_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_2130_);
v_r_2132_ = lean_box(v_res_2131_);
return v_r_2132_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(lean_object* v_s_2133_, lean_object* v_inst_2134_, lean_object* v_R_2135_, lean_object* v_a_2136_, uint8_t v_b_2137_, lean_object* v_c_2138_){
_start:
{
uint8_t v___x_2139_; 
v___x_2139_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_2133_, v_a_2136_, v_b_2137_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___boxed(lean_object* v_s_2140_, lean_object* v_inst_2141_, lean_object* v_R_2142_, lean_object* v_a_2143_, lean_object* v_b_2144_, lean_object* v_c_2145_){
_start:
{
uint8_t v_b_boxed_2146_; uint8_t v_res_2147_; lean_object* v_r_2148_; 
v_b_boxed_2146_ = lean_unbox(v_b_2144_);
v_res_2147_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(v_s_2140_, v_inst_2141_, v_R_2142_, v_a_2143_, v_b_boxed_2146_, v_c_2145_);
lean_dec_ref(v_s_2140_);
v_r_2148_ = lean_box(v_res_2147_);
return v_r_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(lean_object* v_a_2149_, lean_object* v_b_2150_){
_start:
{
lean_object* v_array_2151_; lean_object* v_start_2152_; lean_object* v_stop_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2166_; 
v_array_2151_ = lean_ctor_get(v_a_2149_, 0);
v_start_2152_ = lean_ctor_get(v_a_2149_, 1);
v_stop_2153_ = lean_ctor_get(v_a_2149_, 2);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_a_2149_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2155_ = v_a_2149_;
v_isShared_2156_ = v_isSharedCheck_2166_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_stop_2153_);
lean_inc(v_start_2152_);
lean_inc(v_array_2151_);
lean_dec(v_a_2149_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2166_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
uint8_t v___x_2157_; 
v___x_2157_ = lean_nat_dec_lt(v_start_2152_, v_stop_2153_);
if (v___x_2157_ == 0)
{
lean_del_object(v___x_2155_);
lean_dec(v_stop_2153_);
lean_dec(v_start_2152_);
lean_dec_ref(v_array_2151_);
return v_b_2150_;
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2158_ = lean_unsigned_to_nat(1u);
v___x_2159_ = lean_nat_add(v_start_2152_, v___x_2158_);
lean_inc_ref(v_array_2151_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v___x_2159_);
v___x_2161_ = v___x_2155_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_array_2151_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_stop_2153_);
v___x_2161_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_array_fget(v_array_2151_, v_start_2152_);
lean_dec(v_start_2152_);
lean_dec_ref(v_array_2151_);
v___x_2163_ = lean_array_push(v_b_2150_, v___x_2162_);
v_a_2149_ = v___x_2161_;
v_b_2150_ = v___x_2163_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(size_t v_sz_2167_, size_t v_i_2168_, lean_object* v_bs_2169_){
_start:
{
uint8_t v___x_2170_; 
v___x_2170_ = lean_usize_dec_lt(v_i_2168_, v_sz_2167_);
if (v___x_2170_ == 0)
{
return v_bs_2169_;
}
else
{
lean_object* v_v_2171_; lean_object* v___x_2172_; lean_object* v_bs_x27_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; size_t v___x_2176_; size_t v___x_2177_; lean_object* v___x_2178_; 
v_v_2171_ = lean_array_uget(v_bs_2169_, v_i_2168_);
v___x_2172_ = lean_unsigned_to_nat(0u);
v_bs_x27_2173_ = lean_array_uset(v_bs_2169_, v_i_2168_, v___x_2172_);
v___x_2174_ = l_Lean_Name_toString(v_v_2171_, v___x_2170_);
v___x_2175_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
v___x_2176_ = ((size_t)1ULL);
v___x_2177_ = lean_usize_add(v_i_2168_, v___x_2176_);
v___x_2178_ = lean_array_uset(v_bs_x27_2173_, v_i_2168_, v___x_2175_);
v_i_2168_ = v___x_2177_;
v_bs_2169_ = v___x_2178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0___boxed(lean_object* v_sz_2180_, lean_object* v_i_2181_, lean_object* v_bs_2182_){
_start:
{
size_t v_sz_boxed_2183_; size_t v_i_boxed_2184_; lean_object* v_res_2185_; 
v_sz_boxed_2183_ = lean_unbox_usize(v_sz_2180_);
lean_dec(v_sz_2180_);
v_i_boxed_2184_ = lean_unbox_usize(v_i_2181_);
lean_dec(v_i_2181_);
v_res_2185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_boxed_2183_, v_i_boxed_2184_, v_bs_2182_);
return v_res_2185_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = lean_unsigned_to_nat(4u);
v___x_2210_ = l_Lean_JsonNumber_fromNat(v___x_2209_);
return v___x_2210_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15);
v___x_2212_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
return v___x_2212_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16);
v___x_2214_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14));
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___x_2213_);
return v___x_2215_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24));
v___x_2233_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17);
v___x_2234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
lean_ctor_set(v___x_2234_, 1, v___x_2232_);
return v___x_2234_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25);
v___x_2236_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13));
v___x_2237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
lean_ctor_set(v___x_2237_, 1, v___x_2235_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(lean_object* v_kernelName_2238_, lean_object* v_solutionPath_2239_, lean_object* v___x_2240_, lean_object* v_kernelCommand_2241_, lean_object* v_configHandle_2242_, lean_object* v_configPath_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_a_2247_; lean_object* v_legalAxioms_2274_; uint8_t v___x_2275_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v_kernelArgs_2349_; lean_object* v___y_2350_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; size_t v_sz_2361_; size_t v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v_legalAxioms_2274_ = lean_ctor_get(v___y_2244_, 5);
v___x_2275_ = 0;
v___x_2356_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9));
v___x_2357_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10));
lean_inc_ref(v_solutionPath_2239_);
v___x_2358_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2358_, 0, v_solutionPath_2239_);
v___x_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
v_sz_2361_ = lean_array_size(v_legalAxioms_2274_);
v___x_2362_ = ((size_t)0ULL);
lean_inc_ref(v_legalAxioms_2274_);
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_2361_, v___x_2362_, v_legalAxioms_2274_);
v___x_2364_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
v___x_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2360_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26);
v___x_2367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2359_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2356_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = l_Lean_Json_mkObj(v___x_2369_);
lean_dec_ref_known(v___x_2369_, 2);
v___x_2371_ = l_Lean_Json_compress(v___x_2370_);
v___x_2372_ = lean_io_prim_handle_put_str(v_configHandle_2242_, v___x_2371_);
lean_dec_ref(v___x_2371_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v___x_2373_; 
lean_dec_ref_known(v___x_2372_, 1);
v___x_2373_ = lean_io_prim_handle_flush(v_configHandle_2242_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
lean_dec_ref_known(v___x_2373_, 1);
v___x_2374_ = lean_unsigned_to_nat(1u);
v___x_2375_ = lean_array_get_size(v_kernelCommand_2241_);
lean_inc_ref(v_kernelCommand_2241_);
v___x_2376_ = l_Array_toSubarray___redArg(v_kernelCommand_2241_, v___x_2374_, v___x_2375_);
v___x_2377_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_2378_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v___x_2376_, v___x_2377_);
lean_inc_ref(v_kernelName_2238_);
v___x_2379_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_2238_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
lean_inc_ref(v_solutionPath_2239_);
v___x_2380_ = lean_array_push(v___x_2378_, v_solutionPath_2239_);
v_kernelArgs_2349_ = v___x_2380_;
v___y_2350_ = v___y_2244_;
goto v___jp_2348_;
}
else
{
lean_object* v___x_2381_; 
lean_inc_ref(v_configPath_2243_);
v___x_2381_ = lean_array_push(v___x_2378_, v_configPath_2243_);
v_kernelArgs_2349_ = v___x_2381_;
v___y_2350_ = v___y_2244_;
goto v___jp_2348_;
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v_configPath_2243_);
lean_dec_ref(v_kernelCommand_2241_);
lean_dec_ref(v_solutionPath_2239_);
lean_dec_ref(v_kernelName_2238_);
v_a_2382_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2373_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2373_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v_configPath_2243_);
lean_dec_ref(v_kernelCommand_2241_);
lean_dec_ref(v_solutionPath_2239_);
lean_dec_ref(v_kernelName_2238_);
v_a_2390_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2372_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2372_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
v___jp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2248_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__0));
v___x_2249_ = lean_string_append(v___x_2248_, v_kernelName_2238_);
lean_dec_ref(v_kernelName_2238_);
v___x_2250_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__1));
lean_inc_ref(v___x_2249_);
v___x_2251_ = lean_string_append(v___x_2249_, v___x_2250_);
v___x_2252_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2251_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2264_; 
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; 
v_unused_2265_ = lean_ctor_get(v___x_2252_, 0);
lean_dec(v_unused_2265_);
v___x_2254_ = v___x_2252_;
v_isShared_2255_ = v_isSharedCheck_2264_;
goto v_resetjp_2253_;
}
else
{
lean_dec(v___x_2252_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2264_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2256_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__2));
v___x_2257_ = lean_string_append(v___x_2249_, v___x_2256_);
v___x_2258_ = lean_io_error_to_string(v_a_2247_);
v___x_2259_ = lean_string_append(v___x_2257_, v___x_2258_);
lean_dec_ref(v___x_2258_);
v___x_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2260_);
v___x_2262_ = v___x_2254_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec_ref(v___x_2249_);
lean_dec(v_a_2247_);
v_a_2266_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2252_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2252_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
v___jp_2276_:
{
lean_object* v_leanPrefix_2281_; lean_object* v___x_2282_; 
v_leanPrefix_2281_ = lean_ctor_get(v___y_2279_, 6);
v___x_2282_ = lean_uv_os_tmpdir();
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2284_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__4));
v___x_2285_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_2286_ = lean_unsigned_to_nat(4u);
v___x_2287_ = lean_mk_empty_array_with_capacity(v___x_2286_);
v___x_2288_ = lean_array_push(v___x_2287_, v_configPath_2243_);
v___x_2289_ = lean_array_push(v___x_2288_, v_solutionPath_2239_);
lean_inc_ref(v___y_2280_);
v___x_2290_ = lean_array_push(v___x_2289_, v___y_2280_);
lean_inc_ref(v_leanPrefix_2281_);
v___x_2291_ = lean_array_push(v___x_2290_, v_leanPrefix_2281_);
v___x_2292_ = lean_mk_empty_array_with_capacity(v___y_2278_);
v___x_2293_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2294_, 0, v_a_2283_);
v___x_2295_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_2295_, 0, v___y_2280_);
lean_ctor_set(v___x_2295_, 1, v___y_2277_);
lean_ctor_set(v___x_2295_, 2, v___x_2284_);
lean_ctor_set(v___x_2295_, 3, v___x_2285_);
lean_ctor_set(v___x_2295_, 4, v___x_2291_);
lean_ctor_set(v___x_2295_, 5, v___x_2292_);
lean_ctor_set(v___x_2295_, 6, v___x_2293_);
lean_ctor_set(v___x_2295_, 7, v___x_2294_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*8, v___x_2275_);
v___x_2296_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v___x_2295_, v___y_2279_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2338_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2338_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2338_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
uint32_t v___x_2301_; uint32_t v___x_2302_; uint8_t v___x_2303_; 
v___x_2301_ = 0;
v___x_2302_ = lean_unbox_uint32(v_a_2297_);
v___x_2303_ = lean_uint32_dec_eq(v___x_2302_, v___x_2301_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5));
lean_inc_ref(v_kernelName_2238_);
v___x_2305_ = lean_string_append(v_kernelName_2238_, v___x_2304_);
v___x_2306_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2305_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2322_; 
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v___x_2306_, 0);
lean_dec(v_unused_2323_);
v___x_2308_ = v___x_2306_;
v_isShared_2309_ = v_isSharedCheck_2322_;
goto v_resetjp_2307_;
}
else
{
lean_dec(v___x_2306_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2322_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; uint32_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2310_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6));
v___x_2311_ = lean_string_append(v_kernelName_2238_, v___x_2310_);
v___x_2312_ = lean_unbox_uint32(v_a_2297_);
lean_dec(v_a_2297_);
v___x_2313_ = lean_uint32_to_nat(v___x_2312_);
v___x_2314_ = l_Nat_reprFast(v___x_2313_);
v___x_2315_ = lean_string_append(v___x_2311_, v___x_2314_);
lean_dec_ref(v___x_2314_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set_tag(v___x_2299_, 1);
lean_ctor_set(v___x_2299_, 0, v___x_2315_);
v___x_2317_ = v___x_2299_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2319_; 
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v___x_2317_);
v___x_2319_ = v___x_2308_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_object* v_a_2324_; 
lean_del_object(v___x_2299_);
lean_dec(v_a_2297_);
v_a_2324_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2306_, 1);
v_a_2247_ = v_a_2324_;
goto v___jp_2246_;
}
}
else
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_del_object(v___x_2299_);
lean_dec(v_a_2297_);
v___x_2325_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7));
lean_inc_ref(v_kernelName_2238_);
v___x_2326_ = lean_string_append(v_kernelName_2238_, v___x_2325_);
v___x_2327_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2326_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2335_; 
lean_dec_ref(v_kernelName_2238_);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2335_ == 0)
{
lean_object* v_unused_2336_; 
v_unused_2336_ = lean_ctor_get(v___x_2327_, 0);
lean_dec(v_unused_2336_);
v___x_2329_ = v___x_2327_;
v_isShared_2330_ = v_isSharedCheck_2335_;
goto v_resetjp_2328_;
}
else
{
lean_dec(v___x_2327_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2335_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2331_ = lean_box(0);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2331_);
v___x_2333_ = v___x_2329_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
else
{
lean_object* v_a_2337_; 
v_a_2337_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2327_, 1);
v_a_2247_ = v_a_2337_;
goto v___jp_2246_;
}
}
}
}
else
{
lean_object* v_a_2339_; 
v_a_2339_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2296_, 1);
v_a_2247_ = v_a_2339_;
goto v___jp_2246_;
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v___y_2280_);
lean_dec_ref(v___y_2277_);
lean_dec_ref(v_configPath_2243_);
lean_dec_ref(v_solutionPath_2239_);
lean_dec_ref(v_kernelName_2238_);
v_a_2340_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2282_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2282_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
v___jp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v_a_2354_; 
v___x_2351_ = lean_unsigned_to_nat(0u);
v___x_2352_ = lean_array_get(v___x_2240_, v_kernelCommand_2241_, v___x_2351_);
lean_dec_ref(v_kernelCommand_2241_);
lean_inc(v___x_2352_);
v___x_2353_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_2352_);
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref(v___x_2353_);
if (lean_obj_tag(v_a_2354_) == 0)
{
v___y_2277_ = v_kernelArgs_2349_;
v___y_2278_ = v___x_2351_;
v___y_2279_ = v___y_2350_;
v___y_2280_ = v___x_2352_;
goto v___jp_2276_;
}
else
{
lean_object* v_val_2355_; 
lean_dec(v___x_2352_);
v_val_2355_ = lean_ctor_get(v_a_2354_, 0);
lean_inc(v_val_2355_);
lean_dec_ref_known(v_a_2354_, 1);
v___y_2277_ = v_kernelArgs_2349_;
v___y_2278_ = v___x_2351_;
v___y_2279_ = v___y_2350_;
v___y_2280_ = v_val_2355_;
goto v___jp_2276_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed(lean_object* v_kernelName_2398_, lean_object* v_solutionPath_2399_, lean_object* v___x_2400_, lean_object* v_kernelCommand_2401_, lean_object* v_configHandle_2402_, lean_object* v_configPath_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(v_kernelName_2398_, v_solutionPath_2399_, v___x_2400_, v_kernelCommand_2401_, v_configHandle_2402_, v_configPath_2403_, v___y_2404_);
lean_dec_ref(v___y_2404_);
lean_dec(v_configHandle_2402_);
lean_dec_ref(v___x_2400_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(lean_object* v_kernelName_2409_, lean_object* v_kernelCommand_2410_, lean_object* v_solutionPath_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v___x_2414_; lean_object* v___f_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2414_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
lean_inc_ref(v_kernelName_2409_);
v___f_2415_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed), 8, 4);
lean_closure_set(v___f_2415_, 0, v_kernelName_2409_);
lean_closure_set(v___f_2415_, 1, v_solutionPath_2411_);
lean_closure_set(v___f_2415_, 2, v___x_2414_);
lean_closure_set(v___f_2415_, 3, v_kernelCommand_2410_);
v___x_2416_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0));
v___x_2417_ = lean_string_append(v___x_2416_, v_kernelName_2409_);
lean_dec_ref(v_kernelName_2409_);
v___x_2418_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1));
v___x_2419_ = lean_string_append(v___x_2417_, v___x_2418_);
v___x_2420_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2419_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v___x_2421_; 
lean_dec_ref_known(v___x_2420_, 1);
v___x_2421_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v___f_2415_, v_a_2412_);
return v___x_2421_;
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec_ref(v___f_2415_);
v_a_2422_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2420_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2420_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___boxed(lean_object* v_kernelName_2430_, lean_object* v_kernelCommand_2431_, lean_object* v_solutionPath_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_kernelName_2430_, v_kernelCommand_2431_, v_solutionPath_2432_, v_a_2433_);
lean_dec_ref(v_a_2433_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1(lean_object* v_inst_2436_, lean_object* v_R_2437_, lean_object* v_a_2438_, lean_object* v_b_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v_a_2438_, v_b_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(lean_object* v_solutionPath_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_whichLeanChecker_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v_whichLeanChecker_2447_ = lean_ctor_get(v_a_2445_, 13);
v___x_2448_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0));
v___x_2449_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_2450_ = lean_unsigned_to_nat(3u);
v___x_2451_ = lean_mk_empty_array_with_capacity(v___x_2450_);
lean_inc_ref(v_whichLeanChecker_2447_);
v___x_2452_ = lean_array_push(v___x_2451_, v_whichLeanChecker_2447_);
v___x_2453_ = lean_array_push(v___x_2452_, v___x_2448_);
v___x_2454_ = lean_array_push(v___x_2453_, v___x_2449_);
v___x_2455_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2));
v___x_2456_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v___x_2455_, v___x_2454_, v_solutionPath_2444_, v_a_2445_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___boxed(lean_object* v_solutionPath_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_solutionPath_2457_, v_a_2458_);
lean_dec_ref(v_a_2458_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(lean_object* v_exportPath_2461_, lean_object* v_as_2462_, size_t v_sz_2463_, size_t v_i_2464_, lean_object* v_b_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_a_2469_; uint8_t v___x_2473_; 
v___x_2473_ = lean_usize_dec_lt(v_i_2464_, v_sz_2463_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; 
lean_dec_ref(v_exportPath_2461_);
v___x_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2474_, 0, v_b_2465_);
return v___x_2474_;
}
else
{
lean_object* v_a_2475_; lean_object* v_fst_2476_; lean_object* v_snd_2477_; lean_object* v___x_2478_; 
v_a_2475_ = lean_array_uget_borrowed(v_as_2462_, v_i_2464_);
v_fst_2476_ = lean_ctor_get(v_a_2475_, 0);
v_snd_2477_ = lean_ctor_get(v_a_2475_, 1);
lean_inc_ref(v_exportPath_2461_);
lean_inc(v_snd_2477_);
lean_inc(v_fst_2476_);
v___x_2478_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_fst_2476_, v_snd_2477_, v_exportPath_2461_, v___y_2466_);
if (lean_obj_tag(v___x_2478_) == 0)
{
if (lean_obj_tag(v_b_2465_) == 0)
{
lean_object* v_a_2479_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2478_, 1);
v_a_2469_ = v_a_2479_;
goto v___jp_2468_;
}
else
{
lean_dec_ref_known(v___x_2478_, 1);
v_a_2469_ = v_b_2465_;
goto v___jp_2468_;
}
}
else
{
lean_dec(v_b_2465_);
lean_dec_ref(v_exportPath_2461_);
return v___x_2478_;
}
}
v___jp_2468_:
{
size_t v___x_2470_; size_t v___x_2471_; 
v___x_2470_ = ((size_t)1ULL);
v___x_2471_ = lean_usize_add(v_i_2464_, v___x_2470_);
v_i_2464_ = v___x_2471_;
v_b_2465_ = v_a_2469_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0___boxed(lean_object* v_exportPath_2480_, lean_object* v_as_2481_, lean_object* v_sz_2482_, lean_object* v_i_2483_, lean_object* v_b_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
size_t v_sz_boxed_2487_; size_t v_i_boxed_2488_; lean_object* v_res_2489_; 
v_sz_boxed_2487_ = lean_unbox_usize(v_sz_2482_);
lean_dec(v_sz_2482_);
v_i_boxed_2488_ = lean_unbox_usize(v_i_2483_);
lean_dec(v_i_2483_);
v_res_2489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(v_exportPath_2480_, v_as_2481_, v_sz_boxed_2487_, v_i_boxed_2488_, v_b_2484_, v___y_2485_);
lean_dec_ref(v___y_2485_);
lean_dec_ref(v_as_2481_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(lean_object* v_exportPath_2490_, lean_object* v_init_2491_, lean_object* v_x_2492_, lean_object* v___y_2493_){
_start:
{
if (lean_obj_tag(v_x_2492_) == 0)
{
lean_object* v_k_2495_; lean_object* v_v_2496_; lean_object* v_l_2497_; lean_object* v_r_2498_; lean_object* v___x_2499_; 
v_k_2495_ = lean_ctor_get(v_x_2492_, 1);
lean_inc(v_k_2495_);
v_v_2496_ = lean_ctor_get(v_x_2492_, 2);
lean_inc(v_v_2496_);
v_l_2497_ = lean_ctor_get(v_x_2492_, 3);
lean_inc(v_l_2497_);
v_r_2498_ = lean_ctor_get(v_x_2492_, 4);
lean_inc(v_r_2498_);
lean_dec_ref_known(v_x_2492_, 5);
lean_inc_ref(v_exportPath_2490_);
v___x_2499_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(v_exportPath_2490_, v_init_2491_, v_l_2497_, v___y_2493_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v_a_2501_; lean_object* v___x_2502_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v_a_2501_ = lean_ctor_get(v_a_2500_, 0);
lean_inc(v_a_2501_);
lean_dec(v_a_2500_);
lean_inc_ref(v_exportPath_2490_);
v___x_2502_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_k_2495_, v_v_2496_, v_exportPath_2490_, v___y_2493_);
if (lean_obj_tag(v___x_2502_) == 0)
{
if (lean_obj_tag(v_a_2501_) == 0)
{
lean_object* v_a_2503_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2502_, 1);
v_init_2491_ = v_a_2503_;
v_x_2492_ = v_r_2498_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_2502_, 1);
v_init_2491_ = v_a_2501_;
v_x_2492_ = v_r_2498_;
goto _start;
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_a_2501_);
lean_dec(v_r_2498_);
lean_dec_ref(v_exportPath_2490_);
v_a_2506_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2502_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2502_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_dec(v_r_2498_);
lean_dec(v_v_2496_);
lean_dec(v_k_2495_);
lean_dec_ref(v_exportPath_2490_);
return v___x_2499_;
}
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec_ref(v_exportPath_2490_);
v___x_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2514_, 0, v_init_2491_);
v___x_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
return v___x_2515_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1___boxed(lean_object* v_exportPath_2516_, lean_object* v_init_2517_, lean_object* v_x_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(v_exportPath_2516_, v_init_2517_, v_x_2518_, v___y_2519_);
lean_dec_ref(v___y_2519_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runKernels(lean_object* v_exportPath_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v_val_2526_; lean_object* v_externalKernels_2529_; lean_object* v_bundledKernels_2530_; lean_object* v_a_2532_; lean_object* v_result_2565_; lean_object* v___x_2566_; 
v_externalKernels_2529_ = lean_ctor_get(v_a_2523_, 15);
v_bundledKernels_2530_ = lean_ctor_get(v_a_2523_, 16);
v_result_2565_ = lean_box(0);
lean_inc(v_externalKernels_2529_);
lean_inc_ref(v_exportPath_2522_);
v___x_2566_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(v_exportPath_2522_, v_result_2565_, v_externalKernels_2529_, v_a_2523_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v_a_2568_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2566_, 1);
v_a_2568_ = lean_ctor_get(v_a_2567_, 0);
lean_inc(v_a_2568_);
lean_dec(v_a_2567_);
v_a_2532_ = v_a_2568_;
goto v___jp_2531_;
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec_ref(v_exportPath_2522_);
v_a_2569_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2566_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2566_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
v___jp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = lean_mk_io_user_error(v_val_2526_);
v___x_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
return v___x_2528_;
}
v___jp_2531_:
{
size_t v_sz_2533_; size_t v___x_2534_; lean_object* v___x_2535_; 
v_sz_2533_ = lean_array_size(v_bundledKernels_2530_);
v___x_2534_ = ((size_t)0ULL);
lean_inc_ref(v_exportPath_2522_);
v___x_2535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(v_exportPath_2522_, v_bundledKernels_2530_, v_sz_2533_, v___x_2534_, v_a_2532_, v_a_2523_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2537_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2535_, 1);
v___x_2537_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_exportPath_2522_, v_a_2523_);
if (lean_obj_tag(v___x_2537_) == 0)
{
if (lean_obj_tag(v_a_2536_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2547_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2547_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2547_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
if (lean_obj_tag(v_a_2538_) == 1)
{
lean_object* v_val_2542_; 
lean_del_object(v___x_2540_);
v_val_2542_ = lean_ctor_get(v_a_2538_, 0);
lean_inc(v_val_2542_);
lean_dec_ref_known(v_a_2538_, 1);
v_val_2526_ = v_val_2542_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2545_; 
lean_dec(v_a_2538_);
v___x_2543_ = lean_box(0);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2543_);
v___x_2545_ = v___x_2540_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
else
{
lean_object* v_val_2548_; 
lean_dec_ref_known(v___x_2537_, 1);
v_val_2548_ = lean_ctor_get(v_a_2536_, 0);
lean_inc(v_val_2548_);
lean_dec_ref_known(v_a_2536_, 1);
v_val_2526_ = v_val_2548_;
goto v___jp_2525_;
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v_a_2536_);
v_a_2549_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2537_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2537_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec_ref(v_exportPath_2522_);
v_a_2557_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2535_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2535_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runKernels___boxed(lean_object* v_exportPath_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l___private_Lake_CLI_Check_0__Lake_Check_runKernels(v_exportPath_2577_, v_a_2578_);
lean_dec_ref(v_a_2578_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg(){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__52));
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___boxed(lean_object* v_a_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(lean_object* v_a_2735_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___boxed(lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(v_a_2738_);
lean_dec_ref(v_a_2738_);
return v_res_2740_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(lean_object* v_a_2741_, lean_object* v_as_2742_, size_t v_i_2743_, size_t v_stop_2744_){
_start:
{
uint8_t v___x_2745_; 
v___x_2745_ = lean_usize_dec_eq(v_i_2743_, v_stop_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2746_ = lean_array_uget_borrowed(v_as_2742_, v_i_2743_);
v___x_2747_ = lean_name_eq(v_a_2741_, v___x_2746_);
if (v___x_2747_ == 0)
{
size_t v___x_2748_; size_t v___x_2749_; 
v___x_2748_ = ((size_t)1ULL);
v___x_2749_ = lean_usize_add(v_i_2743_, v___x_2748_);
v_i_2743_ = v___x_2749_;
goto _start;
}
else
{
return v___x_2747_;
}
}
else
{
uint8_t v___x_2751_; 
v___x_2751_ = 0;
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0___boxed(lean_object* v_a_2752_, lean_object* v_as_2753_, lean_object* v_i_2754_, lean_object* v_stop_2755_){
_start:
{
size_t v_i_boxed_2756_; size_t v_stop_boxed_2757_; uint8_t v_res_2758_; lean_object* v_r_2759_; 
v_i_boxed_2756_ = lean_unbox_usize(v_i_2754_);
lean_dec(v_i_2754_);
v_stop_boxed_2757_ = lean_unbox_usize(v_stop_2755_);
lean_dec(v_stop_2755_);
v_res_2758_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_2752_, v_as_2753_, v_i_boxed_2756_, v_stop_boxed_2757_);
lean_dec_ref(v_as_2753_);
lean_dec(v_a_2752_);
v_r_2759_ = lean_box(v_res_2758_);
return v_r_2759_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(lean_object* v_as_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2762_ = lean_unsigned_to_nat(0u);
v___x_2763_ = lean_array_get_size(v_as_2760_);
v___x_2764_ = lean_nat_dec_lt(v___x_2762_, v___x_2763_);
if (v___x_2764_ == 0)
{
return v___x_2764_;
}
else
{
if (v___x_2764_ == 0)
{
return v___x_2764_;
}
else
{
size_t v___x_2765_; size_t v___x_2766_; uint8_t v___x_2767_; 
v___x_2765_ = ((size_t)0ULL);
v___x_2766_ = lean_usize_of_nat(v___x_2763_);
v___x_2767_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_2761_, v_as_2760_, v___x_2765_, v___x_2766_);
return v___x_2767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0___boxed(lean_object* v_as_2768_, lean_object* v_a_2769_){
_start:
{
uint8_t v_res_2770_; lean_object* v_r_2771_; 
v_res_2770_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_as_2768_, v_a_2769_);
lean_dec(v_a_2769_);
lean_dec_ref(v_as_2768_);
v_r_2771_ = lean_box(v_res_2770_);
return v_r_2771_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11(void){
_start:
{
lean_object* v___x_2802_; lean_object* v_additional_2803_; lean_object* v___x_2804_; 
v___x_2802_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__10));
v_additional_2803_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_2804_ = l_Array_append___redArg(v_additional_2803_, v___x_2802_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(lean_object* v_a_2805_){
_start:
{
lean_object* v_legalAxioms_2807_; lean_object* v_additional_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v_legalAxioms_2807_ = lean_ctor_get(v_a_2805_, 5);
v_additional_2808_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_2809_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3));
v___x_2810_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_legalAxioms_2807_, v___x_2809_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2811_, 0, v_additional_2808_);
return v___x_2811_;
}
else
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11);
v___x_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
return v___x_2813_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___boxed(lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_2814_);
lean_dec_ref(v_a_2814_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(lean_object* v_e_2817_){
_start:
{
if (lean_obj_tag(v_e_2817_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2827_; 
v_a_2819_ = lean_ctor_get(v_e_2817_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_e_2817_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2821_ = v_e_2817_;
v_isShared_2822_ = v_isSharedCheck_2827_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v_e_2817_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2827_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2823_ = lean_mk_io_user_error(v_a_2819_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set_tag(v___x_2821_, 1);
lean_ctor_set(v___x_2821_, 0, v___x_2823_);
v___x_2825_ = v___x_2821_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
v_a_2828_ = lean_ctor_get(v_e_2817_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_e_2817_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v_e_2817_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v_e_2817_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set_tag(v___x_2830_, 0);
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg___boxed(lean_object* v_e_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v_e_2836_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(lean_object* v_00_u03b1_2839_, lean_object* v_e_2840_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v_e_2840_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___boxed(lean_object* v_00_u03b1_2843_, lean_object* v_e_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(v_00_u03b1_2843_, v_e_2844_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(lean_object* v_challengeExportPath_2847_, lean_object* v_solutionExportPath_2848_, lean_object* v_a_2849_){
_start:
{
uint8_t v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = 0;
v___x_2852_ = lean_io_prim_handle_mk(v_challengeExportPath_2847_, v___x_2851_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = lean_stream_of_handle(v_a_2853_);
v___x_2855_ = l_LeanExport_parseStream(v___x_2854_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v___x_2857_ = lean_io_prim_handle_mk(v_solutionExportPath_2848_, v___x_2851_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v___x_2859_ = lean_stream_of_handle(v_a_2858_);
v___x_2860_ = l_LeanExport_parseStream(v___x_2859_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v_theoremNames_2862_; lean_object* v_definitionNames_2863_; lean_object* v_legalAxioms_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v_a_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc_n(v_a_2861_, 2);
lean_dec_ref_known(v___x_2860_, 1);
v_theoremNames_2862_ = lean_ctor_get(v_a_2849_, 3);
v_definitionNames_2863_ = lean_ctor_get(v_a_2849_, 4);
v_legalAxioms_2864_ = lean_ctor_get(v_a_2849_, 5);
lean_inc_ref(v_theoremNames_2862_);
v___x_2865_ = l_Array_append___redArg(v_theoremNames_2862_, v_legalAxioms_2864_);
v___x_2866_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2866_);
v___x_2868_ = l_Lake_Check_compareAt(v_a_2856_, v_a_2861_, v___x_2865_, v_definitionNames_2863_, v_a_2867_);
lean_dec_ref(v___x_2865_);
v___x_2869_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v___x_2868_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_dec_ref_known(v___x_2869_, 1);
v___x_2870_ = l_Lake_Check_checkAxioms(v_a_2861_, v_theoremNames_2862_, v_definitionNames_2863_, v_legalAxioms_2864_);
v___x_2871_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v___x_2870_);
return v___x_2871_;
}
else
{
lean_dec(v_a_2861_);
return v___x_2869_;
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_a_2856_);
v_a_2872_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2860_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2860_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_a_2856_);
v_a_2880_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2857_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2857_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
v_a_2888_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2855_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2855_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
v_a_2896_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2852_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2852_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare___boxed(lean_object* v_challengeExportPath_2904_, lean_object* v_solutionExportPath_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(v_challengeExportPath_2904_, v_solutionExportPath_2905_, v_a_2906_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_solutionExportPath_2905_);
lean_dec_ref(v_challengeExportPath_2904_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(lean_object* v_challengeExportPath_2909_, lean_object* v_solutionExportPath_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(v_challengeExportPath_2909_, v_solutionExportPath_2910_, v_a_2911_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v___x_2914_; 
lean_dec_ref_known(v___x_2913_, 1);
v___x_2914_ = l___private_Lake_CLI_Check_0__Lake_Check_runKernels(v_solutionExportPath_2910_, v_a_2911_);
return v___x_2914_;
}
else
{
lean_dec_ref(v_solutionExportPath_2910_);
return v___x_2913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch___boxed(lean_object* v_challengeExportPath_2915_, lean_object* v_solutionExportPath_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExportPath_2915_, v_solutionExportPath_2916_, v_a_2917_);
lean_dec_ref(v_a_2917_);
lean_dec_ref(v_challengeExportPath_2915_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0(lean_object* v_challengeExportPath_2921_, lean_object* v_solutionExportPath_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExportPath_2921_, v_solutionExportPath_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_dec_ref_known(v___x_2925_, 1);
v___x_2926_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___closed__0));
v___x_2927_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2926_);
return v___x_2927_;
}
else
{
return v___x_2925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___boxed(lean_object* v_challengeExportPath_2928_, lean_object* v_solutionExportPath_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0(v_challengeExportPath_2928_, v_solutionExportPath_2929_, v___y_2930_);
lean_dec_ref(v___y_2930_);
lean_dec_ref(v_challengeExportPath_2928_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1(lean_object* v___x_2933_, lean_object* v_challengeExportPath_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_solutionModule_2937_; lean_object* v___f_2938_; uint8_t v___x_2939_; lean_object* v___x_2940_; 
v_solutionModule_2937_ = lean_ctor_get(v___y_2935_, 2);
v___f_2938_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2938_, 0, v_challengeExportPath_2934_);
v___x_2939_ = 1;
lean_inc(v_solutionModule_2937_);
v___x_2940_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v___x_2939_, v_solutionModule_2937_, v___x_2933_, v___f_2938_, v___y_2935_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1___boxed(lean_object* v___x_2941_, lean_object* v_challengeExportPath_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1(v___x_2941_, v_challengeExportPath_2942_, v___y_2943_);
lean_dec_ref(v___y_2943_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt(lean_object* v_a_2946_){
_start:
{
lean_object* v___x_2948_; lean_object* v_a_2949_; lean_object* v_challengeModule_2950_; lean_object* v_theoremNames_2951_; lean_object* v_definitionNames_2952_; lean_object* v_legalAxioms_2953_; lean_object* v___x_2954_; lean_object* v_a_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___f_2960_; uint8_t v___x_2961_; lean_object* v___x_2962_; 
v___x_2948_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_2946_);
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref(v___x_2948_);
v_challengeModule_2950_ = lean_ctor_get(v_a_2946_, 1);
v_theoremNames_2951_ = lean_ctor_get(v_a_2946_, 3);
v_definitionNames_2952_ = lean_ctor_get(v_a_2946_, 4);
v_legalAxioms_2953_ = lean_ctor_get(v_a_2946_, 5);
v___x_2954_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref(v___x_2954_);
v___x_2956_ = l_Array_append___redArg(v_a_2949_, v_theoremNames_2951_);
v___x_2957_ = l_Array_append___redArg(v___x_2956_, v_legalAxioms_2953_);
v___x_2958_ = l_Array_append___redArg(v___x_2957_, v_a_2955_);
lean_dec(v_a_2955_);
v___x_2959_ = l_Array_append___redArg(v___x_2958_, v_definitionNames_2952_);
lean_inc_ref(v___x_2959_);
v___f_2960_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2960_, 0, v___x_2959_);
v___x_2961_ = 2;
lean_inc(v_challengeModule_2950_);
v___x_2962_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v___x_2961_, v_challengeModule_2950_, v___x_2959_, v___f_2960_, v_a_2946_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___boxed(lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt(v_a_2963_);
lean_dec_ref(v_a_2963_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(lean_object* v_j_2966_, lean_object* v_k_2967_){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = l_Lean_Json_getObjValD(v_j_2966_, v_k_2967_);
v___x_2969_ = l_Lean_Json_getStr_x3f(v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0___boxed(lean_object* v_j_2970_, lean_object* v_k_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_j_2970_, v_k_2971_);
lean_dec_ref(v_k_2971_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(size_t v_sz_2973_, size_t v_i_2974_, lean_object* v_bs_2975_){
_start:
{
uint8_t v___x_2976_; 
v___x_2976_ = lean_usize_dec_lt(v_i_2974_, v_sz_2973_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2977_, 0, v_bs_2975_);
return v___x_2977_;
}
else
{
lean_object* v_v_2978_; lean_object* v___x_2979_; 
v_v_2978_ = lean_array_uget_borrowed(v_bs_2975_, v_i_2974_);
lean_inc(v_v_2978_);
v___x_2979_ = l_Lean_Json_getStr_x3f(v_v_2978_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec_ref(v_bs_2975_);
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2979_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2979_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2989_; lean_object* v_bs_x27_2990_; size_t v___x_2991_; size_t v___x_2992_; lean_object* v___x_2993_; 
v_a_2988_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v___x_2979_, 1);
v___x_2989_ = lean_unsigned_to_nat(0u);
v_bs_x27_2990_ = lean_array_uset(v_bs_2975_, v_i_2974_, v___x_2989_);
v___x_2991_ = ((size_t)1ULL);
v___x_2992_ = lean_usize_add(v_i_2974_, v___x_2991_);
v___x_2993_ = lean_array_uset(v_bs_x27_2990_, v_i_2974_, v_a_2988_);
v_i_2974_ = v___x_2992_;
v_bs_2975_ = v___x_2993_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2995_, lean_object* v_i_2996_, lean_object* v_bs_2997_){
_start:
{
size_t v_sz_boxed_2998_; size_t v_i_boxed_2999_; lean_object* v_res_3000_; 
v_sz_boxed_2998_ = lean_unbox_usize(v_sz_2995_);
lean_dec(v_sz_2995_);
v_i_boxed_2999_ = lean_unbox_usize(v_i_2996_);
lean_dec(v_i_2996_);
v_res_3000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_2998_, v_i_boxed_2999_, v_bs_2997_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(lean_object* v_x_3003_){
_start:
{
if (lean_obj_tag(v_x_3003_) == 4)
{
lean_object* v_elems_3004_; size_t v_sz_3005_; size_t v___x_3006_; lean_object* v___x_3007_; 
v_elems_3004_ = lean_ctor_get(v_x_3003_, 0);
lean_inc_ref(v_elems_3004_);
lean_dec_ref_known(v_x_3003_, 1);
v_sz_3005_ = lean_array_size(v_elems_3004_);
v___x_3006_ = ((size_t)0ULL);
v___x_3007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_3005_, v___x_3006_, v_elems_3004_);
return v___x_3007_;
}
else
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3008_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__0));
v___x_3009_ = lean_unsigned_to_nat(80u);
v___x_3010_ = l_Lean_Json_pretty(v_x_3003_, v___x_3009_);
v___x_3011_ = lean_string_append(v___x_3008_, v___x_3010_);
lean_dec_ref(v___x_3010_);
v___x_3012_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_3013_ = lean_string_append(v___x_3011_, v___x_3012_);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
return v___x_3014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(lean_object* v_x_3017_){
_start:
{
if (lean_obj_tag(v_x_3017_) == 0)
{
lean_object* v___x_3018_; 
v___x_3018_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3___closed__0));
return v___x_3018_;
}
else
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_x_3017_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3019_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3036_; 
v_a_3028_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3030_ = v___x_3019_;
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3019_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3036_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3032_, 0, v_a_3028_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v___x_3032_);
v___x_3034_ = v___x_3030_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(lean_object* v_j_3037_, lean_object* v_k_3038_){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = l_Lean_Json_getObjValD(v_j_3037_, v_k_3038_);
v___x_3040_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(v___x_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2___boxed(lean_object* v_j_3041_, lean_object* v_k_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_j_3041_, v_k_3042_);
lean_dec_ref(v_k_3042_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(lean_object* v_x_3046_){
_start:
{
if (lean_obj_tag(v_x_3046_) == 0)
{
lean_object* v___x_3047_; 
v___x_3047_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___closed__0));
return v___x_3047_;
}
else
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_Json_getBool_x3f(v_x_3046_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3065_; 
v_a_3057_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3059_ = v___x_3048_;
v_isShared_3060_ = v_isSharedCheck_3065_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3048_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3065_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3061_, 0, v_a_3057_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3061_);
v___x_3063_ = v___x_3059_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___boxed(lean_object* v_x_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v_x_3066_);
lean_dec(v_x_3066_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(lean_object* v_j_3068_, lean_object* v_k_3069_){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = l_Lean_Json_getObjValD(v_j_3068_, v_k_3069_);
v___x_3071_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v___x_3070_);
lean_dec(v___x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3___boxed(lean_object* v_j_3072_, lean_object* v_k_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_j_3072_, v_k_3073_);
lean_dec_ref(v_k_3073_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_cmp_3075_, lean_object* v_k_3076_, lean_object* v_v_3077_, lean_object* v_t_3078_){
_start:
{
if (lean_obj_tag(v_t_3078_) == 0)
{
lean_object* v_size_3079_; lean_object* v_k_3080_; lean_object* v_v_3081_; lean_object* v_l_3082_; lean_object* v_r_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3364_; 
v_size_3079_ = lean_ctor_get(v_t_3078_, 0);
v_k_3080_ = lean_ctor_get(v_t_3078_, 1);
v_v_3081_ = lean_ctor_get(v_t_3078_, 2);
v_l_3082_ = lean_ctor_get(v_t_3078_, 3);
v_r_3083_ = lean_ctor_get(v_t_3078_, 4);
v_isSharedCheck_3364_ = !lean_is_exclusive(v_t_3078_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3085_ = v_t_3078_;
v_isShared_3086_ = v_isSharedCheck_3364_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_r_3083_);
lean_inc(v_l_3082_);
lean_inc(v_v_3081_);
lean_inc(v_k_3080_);
lean_inc(v_size_3079_);
lean_dec(v_t_3078_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3364_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; uint8_t v___x_3088_; 
lean_inc_ref(v_cmp_3075_);
lean_inc(v_k_3080_);
lean_inc_ref(v_k_3076_);
v___x_3087_ = lean_apply_2(v_cmp_3075_, v_k_3076_, v_k_3080_);
v___x_3088_ = lean_unbox(v___x_3087_);
switch(v___x_3088_)
{
case 0:
{
lean_object* v_impl_3089_; lean_object* v___x_3090_; 
lean_dec(v_size_3079_);
v_impl_3089_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3075_, v_k_3076_, v_v_3077_, v_l_3082_);
v___x_3090_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3083_) == 0)
{
lean_object* v_size_3091_; lean_object* v_size_3092_; lean_object* v_k_3093_; lean_object* v_v_3094_; lean_object* v_l_3095_; lean_object* v_r_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v_size_3091_ = lean_ctor_get(v_r_3083_, 0);
v_size_3092_ = lean_ctor_get(v_impl_3089_, 0);
v_k_3093_ = lean_ctor_get(v_impl_3089_, 1);
v_v_3094_ = lean_ctor_get(v_impl_3089_, 2);
v_l_3095_ = lean_ctor_get(v_impl_3089_, 3);
v_r_3096_ = lean_ctor_get(v_impl_3089_, 4);
lean_inc(v_r_3096_);
v___x_3097_ = lean_unsigned_to_nat(3u);
v___x_3098_ = lean_nat_mul(v___x_3097_, v_size_3091_);
v___x_3099_ = lean_nat_dec_lt(v___x_3098_, v_size_3092_);
lean_dec(v___x_3098_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3103_; 
lean_dec(v_r_3096_);
v___x_3100_ = lean_nat_add(v___x_3090_, v_size_3092_);
v___x_3101_ = lean_nat_add(v___x_3100_, v_size_3091_);
lean_dec(v___x_3100_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 3, v_impl_3089_);
lean_ctor_set(v___x_3085_, 0, v___x_3101_);
v___x_3103_ = v___x_3085_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3104_, 3, v_impl_3089_);
lean_ctor_set(v_reuseFailAlloc_3104_, 4, v_r_3083_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
else
{
lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3170_; 
lean_inc(v_l_3095_);
lean_inc(v_v_3094_);
lean_inc(v_k_3093_);
lean_inc(v_size_3092_);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_impl_3089_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; lean_object* v_unused_3172_; lean_object* v_unused_3173_; lean_object* v_unused_3174_; lean_object* v_unused_3175_; 
v_unused_3171_ = lean_ctor_get(v_impl_3089_, 4);
lean_dec(v_unused_3171_);
v_unused_3172_ = lean_ctor_get(v_impl_3089_, 3);
lean_dec(v_unused_3172_);
v_unused_3173_ = lean_ctor_get(v_impl_3089_, 2);
lean_dec(v_unused_3173_);
v_unused_3174_ = lean_ctor_get(v_impl_3089_, 1);
lean_dec(v_unused_3174_);
v_unused_3175_ = lean_ctor_get(v_impl_3089_, 0);
lean_dec(v_unused_3175_);
v___x_3106_ = v_impl_3089_;
v_isShared_3107_ = v_isSharedCheck_3170_;
goto v_resetjp_3105_;
}
else
{
lean_dec(v_impl_3089_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3170_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v_size_3108_; lean_object* v_size_3109_; lean_object* v_k_3110_; lean_object* v_v_3111_; lean_object* v_l_3112_; lean_object* v_r_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v_size_3108_ = lean_ctor_get(v_l_3095_, 0);
v_size_3109_ = lean_ctor_get(v_r_3096_, 0);
v_k_3110_ = lean_ctor_get(v_r_3096_, 1);
v_v_3111_ = lean_ctor_get(v_r_3096_, 2);
v_l_3112_ = lean_ctor_get(v_r_3096_, 3);
v_r_3113_ = lean_ctor_get(v_r_3096_, 4);
v___x_3114_ = lean_unsigned_to_nat(2u);
v___x_3115_ = lean_nat_mul(v___x_3114_, v_size_3108_);
v___x_3116_ = lean_nat_dec_lt(v_size_3109_, v___x_3115_);
lean_dec(v___x_3115_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3145_; 
lean_inc(v_r_3113_);
lean_inc(v_l_3112_);
lean_inc(v_v_3111_);
lean_inc(v_k_3110_);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_r_3096_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; lean_object* v_unused_3147_; lean_object* v_unused_3148_; lean_object* v_unused_3149_; lean_object* v_unused_3150_; 
v_unused_3146_ = lean_ctor_get(v_r_3096_, 4);
lean_dec(v_unused_3146_);
v_unused_3147_ = lean_ctor_get(v_r_3096_, 3);
lean_dec(v_unused_3147_);
v_unused_3148_ = lean_ctor_get(v_r_3096_, 2);
lean_dec(v_unused_3148_);
v_unused_3149_ = lean_ctor_get(v_r_3096_, 1);
lean_dec(v_unused_3149_);
v_unused_3150_ = lean_ctor_get(v_r_3096_, 0);
lean_dec(v_unused_3150_);
v___x_3118_ = v_r_3096_;
v_isShared_3119_ = v_isSharedCheck_3145_;
goto v_resetjp_3117_;
}
else
{
lean_dec(v_r_3096_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3145_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___x_3133_; lean_object* v___y_3135_; 
v___x_3120_ = lean_nat_add(v___x_3090_, v_size_3092_);
lean_dec(v_size_3092_);
v___x_3121_ = lean_nat_add(v___x_3120_, v_size_3091_);
lean_dec(v___x_3120_);
v___x_3133_ = lean_nat_add(v___x_3090_, v_size_3108_);
if (lean_obj_tag(v_l_3112_) == 0)
{
lean_object* v_size_3143_; 
v_size_3143_ = lean_ctor_get(v_l_3112_, 0);
lean_inc(v_size_3143_);
v___y_3135_ = v_size_3143_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3144_; 
v___x_3144_ = lean_unsigned_to_nat(0u);
v___y_3135_ = v___x_3144_;
goto v___jp_3134_;
}
v___jp_3122_:
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3126_ = lean_nat_add(v___y_3124_, v___y_3125_);
lean_dec(v___y_3125_);
lean_dec(v___y_3124_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 4, v_r_3083_);
lean_ctor_set(v___x_3118_, 3, v_r_3113_);
lean_ctor_set(v___x_3118_, 2, v_v_3081_);
lean_ctor_set(v___x_3118_, 1, v_k_3080_);
lean_ctor_set(v___x_3118_, 0, v___x_3126_);
v___x_3128_ = v___x_3118_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3126_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3132_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3132_, 3, v_r_3113_);
lean_ctor_set(v_reuseFailAlloc_3132_, 4, v_r_3083_);
v___x_3128_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3130_; 
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 4, v___x_3128_);
lean_ctor_set(v___x_3106_, 3, v___y_3123_);
lean_ctor_set(v___x_3106_, 2, v_v_3111_);
lean_ctor_set(v___x_3106_, 1, v_k_3110_);
lean_ctor_set(v___x_3106_, 0, v___x_3121_);
v___x_3130_ = v___x_3106_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3121_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_k_3110_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_v_3111_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v___y_3123_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
v___jp_3134_:
{
lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3136_ = lean_nat_add(v___x_3133_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec(v___x_3133_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 4, v_l_3112_);
lean_ctor_set(v___x_3085_, 3, v_l_3095_);
lean_ctor_set(v___x_3085_, 2, v_v_3094_);
lean_ctor_set(v___x_3085_, 1, v_k_3093_);
lean_ctor_set(v___x_3085_, 0, v___x_3136_);
v___x_3138_ = v___x_3085_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v_k_3093_);
lean_ctor_set(v_reuseFailAlloc_3142_, 2, v_v_3094_);
lean_ctor_set(v_reuseFailAlloc_3142_, 3, v_l_3095_);
lean_ctor_set(v_reuseFailAlloc_3142_, 4, v_l_3112_);
v___x_3138_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3139_; 
v___x_3139_ = lean_nat_add(v___x_3090_, v_size_3091_);
if (lean_obj_tag(v_r_3113_) == 0)
{
lean_object* v_size_3140_; 
v_size_3140_ = lean_ctor_get(v_r_3113_, 0);
lean_inc(v_size_3140_);
v___y_3123_ = v___x_3138_;
v___y_3124_ = v___x_3139_;
v___y_3125_ = v_size_3140_;
goto v___jp_3122_;
}
else
{
lean_object* v___x_3141_; 
v___x_3141_ = lean_unsigned_to_nat(0u);
v___y_3123_ = v___x_3138_;
v___y_3124_ = v___x_3139_;
v___y_3125_ = v___x_3141_;
goto v___jp_3122_;
}
}
}
}
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3156_; 
lean_del_object(v___x_3085_);
v___x_3151_ = lean_nat_add(v___x_3090_, v_size_3092_);
lean_dec(v_size_3092_);
v___x_3152_ = lean_nat_add(v___x_3151_, v_size_3091_);
lean_dec(v___x_3151_);
v___x_3153_ = lean_nat_add(v___x_3090_, v_size_3091_);
v___x_3154_ = lean_nat_add(v___x_3153_, v_size_3109_);
lean_dec(v___x_3153_);
lean_inc_ref(v_r_3083_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 4, v_r_3083_);
lean_ctor_set(v___x_3106_, 3, v_r_3096_);
lean_ctor_set(v___x_3106_, 2, v_v_3081_);
lean_ctor_set(v___x_3106_, 1, v_k_3080_);
lean_ctor_set(v___x_3106_, 0, v___x_3154_);
v___x_3156_ = v___x_3106_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3154_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3169_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3169_, 3, v_r_3096_);
lean_ctor_set(v_reuseFailAlloc_3169_, 4, v_r_3083_);
v___x_3156_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
v_isSharedCheck_3163_ = !lean_is_exclusive(v_r_3083_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; lean_object* v_unused_3165_; lean_object* v_unused_3166_; lean_object* v_unused_3167_; lean_object* v_unused_3168_; 
v_unused_3164_ = lean_ctor_get(v_r_3083_, 4);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_r_3083_, 3);
lean_dec(v_unused_3165_);
v_unused_3166_ = lean_ctor_get(v_r_3083_, 2);
lean_dec(v_unused_3166_);
v_unused_3167_ = lean_ctor_get(v_r_3083_, 1);
lean_dec(v_unused_3167_);
v_unused_3168_ = lean_ctor_get(v_r_3083_, 0);
lean_dec(v_unused_3168_);
v___x_3158_ = v_r_3083_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_dec(v_r_3083_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
lean_ctor_set(v___x_3158_, 4, v___x_3156_);
lean_ctor_set(v___x_3158_, 3, v_l_3095_);
lean_ctor_set(v___x_3158_, 2, v_v_3094_);
lean_ctor_set(v___x_3158_, 1, v_k_3093_);
lean_ctor_set(v___x_3158_, 0, v___x_3152_);
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3152_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v_k_3093_);
lean_ctor_set(v_reuseFailAlloc_3162_, 2, v_v_3094_);
lean_ctor_set(v_reuseFailAlloc_3162_, 3, v_l_3095_);
lean_ctor_set(v_reuseFailAlloc_3162_, 4, v___x_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3176_; 
v_l_3176_ = lean_ctor_get(v_impl_3089_, 3);
if (lean_obj_tag(v_l_3176_) == 0)
{
lean_object* v_r_3177_; lean_object* v_k_3178_; lean_object* v_v_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3190_; 
lean_inc_ref(v_l_3176_);
v_r_3177_ = lean_ctor_get(v_impl_3089_, 4);
v_k_3178_ = lean_ctor_get(v_impl_3089_, 1);
v_v_3179_ = lean_ctor_get(v_impl_3089_, 2);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_impl_3089_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; lean_object* v_unused_3192_; 
v_unused_3191_ = lean_ctor_get(v_impl_3089_, 3);
lean_dec(v_unused_3191_);
v_unused_3192_ = lean_ctor_get(v_impl_3089_, 0);
lean_dec(v_unused_3192_);
v___x_3181_ = v_impl_3089_;
v_isShared_3182_ = v_isSharedCheck_3190_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_r_3177_);
lean_inc(v_v_3179_);
lean_inc(v_k_3178_);
lean_dec(v_impl_3089_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3190_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3183_; lean_object* v___x_3185_; 
v___x_3183_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3177_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 3, v_r_3177_);
lean_ctor_set(v___x_3181_, 2, v_v_3081_);
lean_ctor_set(v___x_3181_, 1, v_k_3080_);
lean_ctor_set(v___x_3181_, 0, v___x_3090_);
v___x_3185_ = v___x_3181_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3189_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3189_, 3, v_r_3177_);
lean_ctor_set(v_reuseFailAlloc_3189_, 4, v_r_3177_);
v___x_3185_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3187_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 4, v___x_3185_);
lean_ctor_set(v___x_3085_, 3, v_l_3176_);
lean_ctor_set(v___x_3085_, 2, v_v_3179_);
lean_ctor_set(v___x_3085_, 1, v_k_3178_);
lean_ctor_set(v___x_3085_, 0, v___x_3183_);
v___x_3187_ = v___x_3085_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3183_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v_k_3178_);
lean_ctor_set(v_reuseFailAlloc_3188_, 2, v_v_3179_);
lean_ctor_set(v_reuseFailAlloc_3188_, 3, v_l_3176_);
lean_ctor_set(v_reuseFailAlloc_3188_, 4, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
lean_object* v_r_3193_; 
v_r_3193_ = lean_ctor_get(v_impl_3089_, 4);
lean_inc(v_r_3193_);
if (lean_obj_tag(v_r_3193_) == 0)
{
lean_object* v_k_3194_; lean_object* v_v_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3218_; 
lean_inc(v_l_3176_);
v_k_3194_ = lean_ctor_get(v_impl_3089_, 1);
v_v_3195_ = lean_ctor_get(v_impl_3089_, 2);
v_isSharedCheck_3218_ = !lean_is_exclusive(v_impl_3089_);
if (v_isSharedCheck_3218_ == 0)
{
lean_object* v_unused_3219_; lean_object* v_unused_3220_; lean_object* v_unused_3221_; 
v_unused_3219_ = lean_ctor_get(v_impl_3089_, 4);
lean_dec(v_unused_3219_);
v_unused_3220_ = lean_ctor_get(v_impl_3089_, 3);
lean_dec(v_unused_3220_);
v_unused_3221_ = lean_ctor_get(v_impl_3089_, 0);
lean_dec(v_unused_3221_);
v___x_3197_ = v_impl_3089_;
v_isShared_3198_ = v_isSharedCheck_3218_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_v_3195_);
lean_inc(v_k_3194_);
lean_dec(v_impl_3089_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3218_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v_k_3199_; lean_object* v_v_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3214_; 
v_k_3199_ = lean_ctor_get(v_r_3193_, 1);
v_v_3200_ = lean_ctor_get(v_r_3193_, 2);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_r_3193_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; lean_object* v_unused_3216_; lean_object* v_unused_3217_; 
v_unused_3215_ = lean_ctor_get(v_r_3193_, 4);
lean_dec(v_unused_3215_);
v_unused_3216_ = lean_ctor_get(v_r_3193_, 3);
lean_dec(v_unused_3216_);
v_unused_3217_ = lean_ctor_get(v_r_3193_, 0);
lean_dec(v_unused_3217_);
v___x_3202_ = v_r_3193_;
v_isShared_3203_ = v_isSharedCheck_3214_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_v_3200_);
lean_inc(v_k_3199_);
lean_dec(v_r_3193_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3214_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3206_; 
v___x_3204_ = lean_unsigned_to_nat(3u);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 4, v_l_3176_);
lean_ctor_set(v___x_3202_, 3, v_l_3176_);
lean_ctor_set(v___x_3202_, 2, v_v_3195_);
lean_ctor_set(v___x_3202_, 1, v_k_3194_);
lean_ctor_set(v___x_3202_, 0, v___x_3090_);
v___x_3206_ = v___x_3202_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v_k_3194_);
lean_ctor_set(v_reuseFailAlloc_3213_, 2, v_v_3195_);
lean_ctor_set(v_reuseFailAlloc_3213_, 3, v_l_3176_);
lean_ctor_set(v_reuseFailAlloc_3213_, 4, v_l_3176_);
v___x_3206_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3208_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 4, v_l_3176_);
lean_ctor_set(v___x_3197_, 2, v_v_3081_);
lean_ctor_set(v___x_3197_, 1, v_k_3080_);
lean_ctor_set(v___x_3197_, 0, v___x_3090_);
v___x_3208_ = v___x_3197_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3212_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3212_, 3, v_l_3176_);
lean_ctor_set(v_reuseFailAlloc_3212_, 4, v_l_3176_);
v___x_3208_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3210_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 4, v___x_3208_);
lean_ctor_set(v___x_3085_, 3, v___x_3206_);
lean_ctor_set(v___x_3085_, 2, v_v_3200_);
lean_ctor_set(v___x_3085_, 1, v_k_3199_);
lean_ctor_set(v___x_3085_, 0, v___x_3204_);
v___x_3210_ = v___x_3085_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_k_3199_);
lean_ctor_set(v_reuseFailAlloc_3211_, 2, v_v_3200_);
lean_ctor_set(v_reuseFailAlloc_3211_, 3, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3211_, 4, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
}
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3222_ = lean_unsigned_to_nat(2u);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 4, v_r_3193_);
lean_ctor_set(v___x_3085_, 3, v_impl_3089_);
lean_ctor_set(v___x_3085_, 0, v___x_3222_);
v___x_3224_ = v___x_3085_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v_impl_3089_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v_r_3193_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3227_; 
lean_dec(v_v_3081_);
lean_dec(v_k_3080_);
lean_dec_ref(v_cmp_3075_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 2, v_v_3077_);
lean_ctor_set(v___x_3085_, 1, v_k_3076_);
v___x_3227_ = v___x_3085_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_size_3079_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v_k_3076_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_v_3077_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v_l_3082_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v_r_3083_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
default: 
{
lean_object* v_impl_3229_; lean_object* v___x_3230_; 
lean_dec(v_size_3079_);
v_impl_3229_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3075_, v_k_3076_, v_v_3077_, v_r_3083_);
v___x_3230_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3082_) == 0)
{
lean_object* v_size_3231_; lean_object* v_size_3232_; lean_object* v_k_3233_; lean_object* v_v_3234_; lean_object* v_l_3235_; lean_object* v_r_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
v_size_3231_ = lean_ctor_get(v_l_3082_, 0);
v_size_3232_ = lean_ctor_get(v_impl_3229_, 0);
v_k_3233_ = lean_ctor_get(v_impl_3229_, 1);
v_v_3234_ = lean_ctor_get(v_impl_3229_, 2);
v_l_3235_ = lean_ctor_get(v_impl_3229_, 3);
lean_inc(v_l_3235_);
v_r_3236_ = lean_ctor_get(v_impl_3229_, 4);
v___x_3237_ = lean_unsigned_to_nat(3u);
v___x_3238_ = lean_nat_mul(v___x_3237_, v_size_3231_);
v___x_3239_ = lean_nat_dec_lt(v___x_3238_, v_size_3232_);
lean_dec(v___x_3238_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3243_; 
lean_dec(v_l_3235_);
v___x_3240_ = lean_nat_add(v___x_3230_, v_size_3231_);
v___x_3241_ = lean_nat_add(v___x_3240_, v_size_3232_);
lean_dec(v___x_3240_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 4, v_impl_3229_);
lean_ctor_set(v___x_3085_, 0, v___x_3241_);
v___x_3243_ = v___x_3085_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3244_, 3, v_l_3082_);
lean_ctor_set(v_reuseFailAlloc_3244_, 4, v_impl_3229_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
else
{
lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3308_; 
lean_inc(v_r_3236_);
lean_inc(v_v_3234_);
lean_inc(v_k_3233_);
lean_inc(v_size_3232_);
v_isSharedCheck_3308_ = !lean_is_exclusive(v_impl_3229_);
if (v_isSharedCheck_3308_ == 0)
{
lean_object* v_unused_3309_; lean_object* v_unused_3310_; lean_object* v_unused_3311_; lean_object* v_unused_3312_; lean_object* v_unused_3313_; 
v_unused_3309_ = lean_ctor_get(v_impl_3229_, 4);
lean_dec(v_unused_3309_);
v_unused_3310_ = lean_ctor_get(v_impl_3229_, 3);
lean_dec(v_unused_3310_);
v_unused_3311_ = lean_ctor_get(v_impl_3229_, 2);
lean_dec(v_unused_3311_);
v_unused_3312_ = lean_ctor_get(v_impl_3229_, 1);
lean_dec(v_unused_3312_);
v_unused_3313_ = lean_ctor_get(v_impl_3229_, 0);
lean_dec(v_unused_3313_);
v___x_3246_ = v_impl_3229_;
v_isShared_3247_ = v_isSharedCheck_3308_;
goto v_resetjp_3245_;
}
else
{
lean_dec(v_impl_3229_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3308_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v_size_3248_; lean_object* v_k_3249_; lean_object* v_v_3250_; lean_object* v_l_3251_; lean_object* v_r_3252_; lean_object* v_size_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
v_size_3248_ = lean_ctor_get(v_l_3235_, 0);
v_k_3249_ = lean_ctor_get(v_l_3235_, 1);
v_v_3250_ = lean_ctor_get(v_l_3235_, 2);
v_l_3251_ = lean_ctor_get(v_l_3235_, 3);
v_r_3252_ = lean_ctor_get(v_l_3235_, 4);
v_size_3253_ = lean_ctor_get(v_r_3236_, 0);
v___x_3254_ = lean_unsigned_to_nat(2u);
v___x_3255_ = lean_nat_mul(v___x_3254_, v_size_3253_);
v___x_3256_ = lean_nat_dec_lt(v_size_3248_, v___x_3255_);
lean_dec(v___x_3255_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3284_; 
lean_inc(v_r_3252_);
lean_inc(v_l_3251_);
lean_inc(v_v_3250_);
lean_inc(v_k_3249_);
v_isSharedCheck_3284_ = !lean_is_exclusive(v_l_3235_);
if (v_isSharedCheck_3284_ == 0)
{
lean_object* v_unused_3285_; lean_object* v_unused_3286_; lean_object* v_unused_3287_; lean_object* v_unused_3288_; lean_object* v_unused_3289_; 
v_unused_3285_ = lean_ctor_get(v_l_3235_, 4);
lean_dec(v_unused_3285_);
v_unused_3286_ = lean_ctor_get(v_l_3235_, 3);
lean_dec(v_unused_3286_);
v_unused_3287_ = lean_ctor_get(v_l_3235_, 2);
lean_dec(v_unused_3287_);
v_unused_3288_ = lean_ctor_get(v_l_3235_, 1);
lean_dec(v_unused_3288_);
v_unused_3289_ = lean_ctor_get(v_l_3235_, 0);
lean_dec(v_unused_3289_);
v___x_3258_ = v_l_3235_;
v_isShared_3259_ = v_isSharedCheck_3284_;
goto v_resetjp_3257_;
}
else
{
lean_dec(v_l_3235_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3284_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3274_; 
v___x_3260_ = lean_nat_add(v___x_3230_, v_size_3231_);
v___x_3261_ = lean_nat_add(v___x_3260_, v_size_3232_);
lean_dec(v_size_3232_);
if (lean_obj_tag(v_l_3251_) == 0)
{
lean_object* v_size_3282_; 
v_size_3282_ = lean_ctor_get(v_l_3251_, 0);
lean_inc(v_size_3282_);
v___y_3274_ = v_size_3282_;
goto v___jp_3273_;
}
else
{
lean_object* v___x_3283_; 
v___x_3283_ = lean_unsigned_to_nat(0u);
v___y_3274_ = v___x_3283_;
goto v___jp_3273_;
}
v___jp_3262_:
{
lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3266_ = lean_nat_add(v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
lean_dec(v___y_3264_);
if (v_isShared_3259_ == 0)
{
lean_ctor_set(v___x_3258_, 4, v_r_3236_);
lean_ctor_set(v___x_3258_, 3, v_r_3252_);
lean_ctor_set(v___x_3258_, 2, v_v_3234_);
lean_ctor_set(v___x_3258_, 1, v_k_3233_);
lean_ctor_set(v___x_3258_, 0, v___x_3266_);
v___x_3268_ = v___x_3258_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3266_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_k_3233_);
lean_ctor_set(v_reuseFailAlloc_3272_, 2, v_v_3234_);
lean_ctor_set(v_reuseFailAlloc_3272_, 3, v_r_3252_);
lean_ctor_set(v_reuseFailAlloc_3272_, 4, v_r_3236_);
v___x_3268_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3270_; 
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 4, v___x_3268_);
lean_ctor_set(v___x_3246_, 3, v___y_3263_);
lean_ctor_set(v___x_3246_, 2, v_v_3250_);
lean_ctor_set(v___x_3246_, 1, v_k_3249_);
lean_ctor_set(v___x_3246_, 0, v___x_3261_);
v___x_3270_ = v___x_3246_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3261_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_k_3249_);
lean_ctor_set(v_reuseFailAlloc_3271_, 2, v_v_3250_);
lean_ctor_set(v_reuseFailAlloc_3271_, 3, v___y_3263_);
lean_ctor_set(v_reuseFailAlloc_3271_, 4, v___x_3268_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
v___jp_3273_:
{
lean_object* v___x_3275_; lean_object* v___x_3277_; 
v___x_3275_ = lean_nat_add(v___x_3260_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec(v___x_3260_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 4, v_l_3251_);
lean_ctor_set(v___x_3085_, 0, v___x_3275_);
v___x_3277_ = v___x_3085_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3275_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3281_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3281_, 3, v_l_3082_);
lean_ctor_set(v_reuseFailAlloc_3281_, 4, v_l_3251_);
v___x_3277_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
lean_object* v___x_3278_; 
v___x_3278_ = lean_nat_add(v___x_3230_, v_size_3253_);
if (lean_obj_tag(v_r_3252_) == 0)
{
lean_object* v_size_3279_; 
v_size_3279_ = lean_ctor_get(v_r_3252_, 0);
lean_inc(v_size_3279_);
v___y_3263_ = v___x_3277_;
v___y_3264_ = v___x_3278_;
v___y_3265_ = v_size_3279_;
goto v___jp_3262_;
}
else
{
lean_object* v___x_3280_; 
v___x_3280_ = lean_unsigned_to_nat(0u);
v___y_3263_ = v___x_3277_;
v___y_3264_ = v___x_3278_;
v___y_3265_ = v___x_3280_;
goto v___jp_3262_;
}
}
}
}
}
else
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3294_; 
lean_del_object(v___x_3085_);
v___x_3290_ = lean_nat_add(v___x_3230_, v_size_3231_);
v___x_3291_ = lean_nat_add(v___x_3290_, v_size_3232_);
lean_dec(v_size_3232_);
v___x_3292_ = lean_nat_add(v___x_3290_, v_size_3248_);
lean_dec(v___x_3290_);
lean_inc_ref(v_l_3082_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 4, v_l_3235_);
lean_ctor_set(v___x_3246_, 3, v_l_3082_);
lean_ctor_set(v___x_3246_, 2, v_v_3081_);
lean_ctor_set(v___x_3246_, 1, v_k_3080_);
lean_ctor_set(v___x_3246_, 0, v___x_3292_);
v___x_3294_ = v___x_3246_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3292_);
lean_ctor_set(v_reuseFailAlloc_3307_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3307_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3307_, 3, v_l_3082_);
lean_ctor_set(v_reuseFailAlloc_3307_, 4, v_l_3235_);
v___x_3294_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
v_isSharedCheck_3301_ = !lean_is_exclusive(v_l_3082_);
if (v_isSharedCheck_3301_ == 0)
{
lean_object* v_unused_3302_; lean_object* v_unused_3303_; lean_object* v_unused_3304_; lean_object* v_unused_3305_; lean_object* v_unused_3306_; 
v_unused_3302_ = lean_ctor_get(v_l_3082_, 4);
lean_dec(v_unused_3302_);
v_unused_3303_ = lean_ctor_get(v_l_3082_, 3);
lean_dec(v_unused_3303_);
v_unused_3304_ = lean_ctor_get(v_l_3082_, 2);
lean_dec(v_unused_3304_);
v_unused_3305_ = lean_ctor_get(v_l_3082_, 1);
lean_dec(v_unused_3305_);
v_unused_3306_ = lean_ctor_get(v_l_3082_, 0);
lean_dec(v_unused_3306_);
v___x_3296_ = v_l_3082_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_dec(v_l_3082_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v_r_3236_);
lean_ctor_set(v___x_3296_, 3, v___x_3294_);
lean_ctor_set(v___x_3296_, 2, v_v_3234_);
lean_ctor_set(v___x_3296_, 1, v_k_3233_);
lean_ctor_set(v___x_3296_, 0, v___x_3291_);
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_k_3233_);
lean_ctor_set(v_reuseFailAlloc_3300_, 2, v_v_3234_);
lean_ctor_set(v_reuseFailAlloc_3300_, 3, v___x_3294_);
lean_ctor_set(v_reuseFailAlloc_3300_, 4, v_r_3236_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3314_; 
v_l_3314_ = lean_ctor_get(v_impl_3229_, 3);
lean_inc(v_l_3314_);
if (lean_obj_tag(v_l_3314_) == 0)
{
lean_object* v_r_3315_; lean_object* v_k_3316_; lean_object* v_v_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3340_; 
v_r_3315_ = lean_ctor_get(v_impl_3229_, 4);
v_k_3316_ = lean_ctor_get(v_impl_3229_, 1);
v_v_3317_ = lean_ctor_get(v_impl_3229_, 2);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_impl_3229_);
if (v_isSharedCheck_3340_ == 0)
{
lean_object* v_unused_3341_; lean_object* v_unused_3342_; 
v_unused_3341_ = lean_ctor_get(v_impl_3229_, 3);
lean_dec(v_unused_3341_);
v_unused_3342_ = lean_ctor_get(v_impl_3229_, 0);
lean_dec(v_unused_3342_);
v___x_3319_ = v_impl_3229_;
v_isShared_3320_ = v_isSharedCheck_3340_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_r_3315_);
lean_inc(v_v_3317_);
lean_inc(v_k_3316_);
lean_dec(v_impl_3229_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3340_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v_k_3321_; lean_object* v_v_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3336_; 
v_k_3321_ = lean_ctor_get(v_l_3314_, 1);
v_v_3322_ = lean_ctor_get(v_l_3314_, 2);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_l_3314_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; lean_object* v_unused_3338_; lean_object* v_unused_3339_; 
v_unused_3337_ = lean_ctor_get(v_l_3314_, 4);
lean_dec(v_unused_3337_);
v_unused_3338_ = lean_ctor_get(v_l_3314_, 3);
lean_dec(v_unused_3338_);
v_unused_3339_ = lean_ctor_get(v_l_3314_, 0);
lean_dec(v_unused_3339_);
v___x_3324_ = v_l_3314_;
v_isShared_3325_ = v_isSharedCheck_3336_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_v_3322_);
lean_inc(v_k_3321_);
lean_dec(v_l_3314_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3336_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; lean_object* v___x_3328_; 
v___x_3326_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3315_, 2);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 4, v_r_3315_);
lean_ctor_set(v___x_3324_, 3, v_r_3315_);
lean_ctor_set(v___x_3324_, 2, v_v_3081_);
lean_ctor_set(v___x_3324_, 1, v_k_3080_);
lean_ctor_set(v___x_3324_, 0, v___x_3230_);
v___x_3328_ = v___x_3324_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3335_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3335_, 3, v_r_3315_);
lean_ctor_set(v_reuseFailAlloc_3335_, 4, v_r_3315_);
v___x_3328_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
lean_object* v___x_3330_; 
lean_inc(v_r_3315_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 3, v_r_3315_);
lean_ctor_set(v___x_3319_, 0, v___x_3230_);
v___x_3330_ = v___x_3319_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v_r_3315_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_r_3315_);
v___x_3330_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 4, v___x_3330_);
lean_ctor_set(v___x_3085_, 3, v___x_3328_);
lean_ctor_set(v___x_3085_, 2, v_v_3322_);
lean_ctor_set(v___x_3085_, 1, v_k_3321_);
lean_ctor_set(v___x_3085_, 0, v___x_3326_);
v___x_3332_ = v___x_3085_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3333_, 1, v_k_3321_);
lean_ctor_set(v_reuseFailAlloc_3333_, 2, v_v_3322_);
lean_ctor_set(v_reuseFailAlloc_3333_, 3, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3333_, 4, v___x_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
}
}
else
{
lean_object* v_r_3343_; 
v_r_3343_ = lean_ctor_get(v_impl_3229_, 4);
lean_inc(v_r_3343_);
if (lean_obj_tag(v_r_3343_) == 0)
{
lean_object* v_k_3344_; lean_object* v_v_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3356_; 
v_k_3344_ = lean_ctor_get(v_impl_3229_, 1);
v_v_3345_ = lean_ctor_get(v_impl_3229_, 2);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_impl_3229_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; lean_object* v_unused_3358_; lean_object* v_unused_3359_; 
v_unused_3357_ = lean_ctor_get(v_impl_3229_, 4);
lean_dec(v_unused_3357_);
v_unused_3358_ = lean_ctor_get(v_impl_3229_, 3);
lean_dec(v_unused_3358_);
v_unused_3359_ = lean_ctor_get(v_impl_3229_, 0);
lean_dec(v_unused_3359_);
v___x_3347_ = v_impl_3229_;
v_isShared_3348_ = v_isSharedCheck_3356_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_v_3345_);
lean_inc(v_k_3344_);
lean_dec(v_impl_3229_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3356_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v___x_3351_; 
v___x_3349_ = lean_unsigned_to_nat(3u);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 4, v_l_3314_);
lean_ctor_set(v___x_3347_, 2, v_v_3081_);
lean_ctor_set(v___x_3347_, 1, v_k_3080_);
lean_ctor_set(v___x_3347_, 0, v___x_3230_);
v___x_3351_ = v___x_3347_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3355_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3355_, 3, v_l_3314_);
lean_ctor_set(v_reuseFailAlloc_3355_, 4, v_l_3314_);
v___x_3351_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3353_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 4, v_r_3343_);
lean_ctor_set(v___x_3085_, 3, v___x_3351_);
lean_ctor_set(v___x_3085_, 2, v_v_3345_);
lean_ctor_set(v___x_3085_, 1, v_k_3344_);
lean_ctor_set(v___x_3085_, 0, v___x_3349_);
v___x_3353_ = v___x_3085_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_k_3344_);
lean_ctor_set(v_reuseFailAlloc_3354_, 2, v_v_3345_);
lean_ctor_set(v_reuseFailAlloc_3354_, 3, v___x_3351_);
lean_ctor_set(v_reuseFailAlloc_3354_, 4, v_r_3343_);
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
else
{
lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3360_ = lean_unsigned_to_nat(2u);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 4, v_impl_3229_);
lean_ctor_set(v___x_3085_, 3, v_r_3343_);
lean_ctor_set(v___x_3085_, 0, v___x_3360_);
v___x_3362_ = v___x_3085_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_r_3343_);
lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_impl_3229_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
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
lean_object* v___x_3365_; lean_object* v___x_3366_; 
lean_dec_ref(v_cmp_3075_);
v___x_3365_ = lean_unsigned_to_nat(1u);
v___x_3366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
lean_ctor_set(v___x_3366_, 1, v_k_3076_);
lean_ctor_set(v___x_3366_, 2, v_v_3077_);
lean_ctor_set(v___x_3366_, 3, v_t_3078_);
lean_ctor_set(v___x_3366_, 4, v_t_3078_);
return v___x_3366_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(lean_object* v_cmp_3367_, lean_object* v_init_3368_, lean_object* v_x_3369_){
_start:
{
if (lean_obj_tag(v_x_3369_) == 0)
{
lean_object* v_k_3370_; lean_object* v_v_3371_; lean_object* v_l_3372_; lean_object* v_r_3373_; lean_object* v___x_3374_; 
v_k_3370_ = lean_ctor_get(v_x_3369_, 1);
lean_inc(v_k_3370_);
v_v_3371_ = lean_ctor_get(v_x_3369_, 2);
lean_inc(v_v_3371_);
v_l_3372_ = lean_ctor_get(v_x_3369_, 3);
lean_inc(v_l_3372_);
v_r_3373_ = lean_ctor_get(v_x_3369_, 4);
lean_inc(v_r_3373_);
lean_dec_ref_known(v_x_3369_, 5);
lean_inc_ref(v_cmp_3367_);
v___x_3374_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_3367_, v_init_3368_, v_l_3372_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_dec(v_r_3373_);
lean_dec(v_v_3371_);
lean_dec(v_k_3370_);
lean_dec_ref(v_cmp_3367_);
return v___x_3374_;
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3376_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___x_3374_, 1);
v___x_3376_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_v_3371_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec(v_a_3375_);
lean_dec(v_r_3373_);
lean_dec(v_k_3370_);
lean_dec_ref(v_cmp_3367_);
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3376_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3376_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3386_; 
v_a_3385_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3376_, 1);
lean_inc_ref(v_cmp_3367_);
v___x_3386_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3367_, v_k_3370_, v_a_3385_, v_a_3375_);
v_init_3368_ = v___x_3386_;
v_x_3369_ = v_r_3373_;
goto _start;
}
}
}
else
{
lean_object* v___x_3388_; 
lean_dec_ref(v_cmp_3367_);
v___x_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3388_, 0, v_init_3368_);
return v___x_3388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(lean_object* v_cmp_3389_, lean_object* v_j_3390_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Lean_Json_getObj_x3f(v_j_3390_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec_ref(v_cmp_3389_);
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
lean_object* v_a_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_a_3400_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3391_, 1);
v___x_3401_ = lean_box(1);
v___x_3402_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_3389_, v___x_3401_, v_a_3400_);
return v___x_3402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(lean_object* v_x_3406_){
_start:
{
if (lean_obj_tag(v_x_3406_) == 0)
{
lean_object* v___x_3407_; 
v___x_3407_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__0));
return v___x_3407_;
}
else
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__1));
v___x_3409_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(v___x_3408_, v_x_3406_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3409_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3409_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3426_; 
v_a_3418_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3420_ = v___x_3409_;
v_isShared_3421_ = v_isSharedCheck_3426_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3409_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3426_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v___x_3424_; 
v___x_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3422_, 0, v_a_3418_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3422_);
v___x_3424_ = v___x_3420_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(lean_object* v_j_3427_, lean_object* v_k_3428_){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = l_Lean_Json_getObjValD(v_j_3427_, v_k_3428_);
v___x_3430_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(v___x_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4___boxed(lean_object* v_j_3431_, lean_object* v_k_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_j_3431_, v_k_3432_);
lean_dec_ref(v_k_3432_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(lean_object* v_j_3434_, lean_object* v_k_3435_){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = l_Lean_Json_getObjValD(v_j_3434_, v_k_3435_);
v___x_3437_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v___x_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1___boxed(lean_object* v_j_3438_, lean_object* v_k_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_j_3438_, v_k_3439_);
lean_dec_ref(v_k_3439_);
return v_res_3440_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3449_ = 1;
v___x_3450_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__4));
v___x_3451_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3450_, v___x_3449_);
return v___x_3451_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3453_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__6));
v___x_3454_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__5, &l_Lake_Check_instFromJsonConfig_fromJson___closed__5_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5);
v___x_3455_ = lean_string_append(v___x_3454_, v___x_3453_);
return v___x_3455_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = 1;
v___x_3459_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__8));
v___x_3460_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3459_, v___x_3458_);
return v___x_3460_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3461_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__9, &l_Lake_Check_instFromJsonConfig_fromJson___closed__9_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9);
v___x_3462_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3463_ = lean_string_append(v___x_3462_, v___x_3461_);
return v___x_3463_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3465_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3466_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__10, &l_Lake_Check_instFromJsonConfig_fromJson___closed__10_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10);
v___x_3467_ = lean_string_append(v___x_3466_, v___x_3465_);
return v___x_3467_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15(void){
_start:
{
uint8_t v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = 1;
v___x_3472_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__14));
v___x_3473_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3472_, v___x_3471_);
return v___x_3473_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16(void){
_start:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3474_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__15, &l_Lake_Check_instFromJsonConfig_fromJson___closed__15_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15);
v___x_3475_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3476_ = lean_string_append(v___x_3475_, v___x_3474_);
return v___x_3476_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3477_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3478_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__16, &l_Lake_Check_instFromJsonConfig_fromJson___closed__16_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16);
v___x_3479_ = lean_string_append(v___x_3478_, v___x_3477_);
return v___x_3479_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20(void){
_start:
{
uint8_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3483_ = 1;
v___x_3484_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__19));
v___x_3485_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3484_, v___x_3483_);
return v___x_3485_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__20, &l_Lake_Check_instFromJsonConfig_fromJson___closed__20_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20);
v___x_3487_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3488_ = lean_string_append(v___x_3487_, v___x_3486_);
return v___x_3488_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3490_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__21, &l_Lake_Check_instFromJsonConfig_fromJson___closed__21_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21);
v___x_3491_ = lean_string_append(v___x_3490_, v___x_3489_);
return v___x_3491_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25(void){
_start:
{
uint8_t v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3495_ = 1;
v___x_3496_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__24));
v___x_3497_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3496_, v___x_3495_);
return v___x_3497_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__25, &l_Lake_Check_instFromJsonConfig_fromJson___closed__25_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25);
v___x_3499_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3500_ = lean_string_append(v___x_3499_, v___x_3498_);
return v___x_3500_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3502_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__26, &l_Lake_Check_instFromJsonConfig_fromJson___closed__26_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26);
v___x_3503_ = lean_string_append(v___x_3502_, v___x_3501_);
return v___x_3503_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29(void){
_start:
{
uint8_t v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3506_ = 1;
v___x_3507_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__28));
v___x_3508_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3507_, v___x_3506_);
return v___x_3508_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__29, &l_Lake_Check_instFromJsonConfig_fromJson___closed__29_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29);
v___x_3510_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3511_ = lean_string_append(v___x_3510_, v___x_3509_);
return v___x_3511_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3513_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__30, &l_Lake_Check_instFromJsonConfig_fromJson___closed__30_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30);
v___x_3514_ = lean_string_append(v___x_3513_, v___x_3512_);
return v___x_3514_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35(void){
_start:
{
uint8_t v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3519_ = 1;
v___x_3520_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__34));
v___x_3521_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3520_, v___x_3519_);
return v___x_3521_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3522_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__35, &l_Lake_Check_instFromJsonConfig_fromJson___closed__35_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35);
v___x_3523_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3524_ = lean_string_append(v___x_3523_, v___x_3522_);
return v___x_3524_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3525_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3526_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__36, &l_Lake_Check_instFromJsonConfig_fromJson___closed__36_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36);
v___x_3527_ = lean_string_append(v___x_3526_, v___x_3525_);
return v___x_3527_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41(void){
_start:
{
uint8_t v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3532_ = 1;
v___x_3533_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__40));
v___x_3534_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3533_, v___x_3532_);
return v___x_3534_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3535_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__41, &l_Lake_Check_instFromJsonConfig_fromJson___closed__41_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41);
v___x_3536_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3537_ = lean_string_append(v___x_3536_, v___x_3535_);
return v___x_3537_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3539_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__42, &l_Lake_Check_instFromJsonConfig_fromJson___closed__42_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42);
v___x_3540_ = lean_string_append(v___x_3539_, v___x_3538_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instFromJsonConfig_fromJson(lean_object* v_json_3541_){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
lean_inc(v_json_3541_);
v___x_3543_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_3541_, v___x_3542_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3553_; 
lean_dec(v_json_3541_);
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3546_ = v___x_3543_;
v_isShared_3547_ = v_isSharedCheck_3553_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3543_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3553_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3551_; 
v___x_3548_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__12, &l_Lake_Check_instFromJsonConfig_fromJson___closed__12_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12);
v___x_3549_ = lean_string_append(v___x_3548_, v_a_3544_);
lean_dec(v_a_3544_);
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 0, v___x_3549_);
v___x_3551_ = v___x_3546_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3549_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
else
{
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec(v_json_3541_);
v_a_3554_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3543_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3543_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
lean_ctor_set_tag(v___x_3556_, 0);
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
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
lean_object* v_a_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v_a_3562_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v___x_3543_, 1);
v___x_3563_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
lean_inc(v_json_3541_);
v___x_3564_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_3541_, v___x_3563_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v_a_3562_);
lean_dec(v_json_3541_);
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3567_ = v___x_3564_;
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3564_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3569_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__17, &l_Lake_Check_instFromJsonConfig_fromJson___closed__17_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17);
v___x_3570_ = lean_string_append(v___x_3569_, v_a_3565_);
lean_dec(v_a_3565_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v___x_3570_);
v___x_3572_ = v___x_3567_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
else
{
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec(v_a_3562_);
lean_dec(v_json_3541_);
v_a_3575_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3564_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3564_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
lean_ctor_set_tag(v___x_3577_, 0);
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v_a_3583_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3564_, 1);
v___x_3584_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
lean_inc(v_json_3541_);
v___x_3585_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_3541_, v___x_3584_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3595_; 
lean_dec(v_a_3583_);
lean_dec(v_a_3562_);
lean_dec(v_json_3541_);
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3588_ = v___x_3585_;
v_isShared_3589_ = v_isSharedCheck_3595_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3585_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3595_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3590_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__22, &l_Lake_Check_instFromJsonConfig_fromJson___closed__22_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22);
v___x_3591_ = lean_string_append(v___x_3590_, v_a_3586_);
lean_dec(v_a_3586_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 0, v___x_3591_);
v___x_3593_ = v___x_3588_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
else
{
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v_a_3583_);
lean_dec(v_a_3562_);
lean_dec(v_json_3541_);
v_a_3596_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3585_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3585_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
lean_ctor_set_tag(v___x_3598_, 0);
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v_a_3604_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3585_, 1);
v___x_3605_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
lean_inc(v_json_3541_);
v___x_3606_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_json_3541_, v___x_3605_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3616_; 
lean_dec(v_a_3604_);
lean_dec(v_a_3583_);
lean_dec(v_a_3562_);
lean_dec(v_json_3541_);
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3616_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3616_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3614_; 
v___x_3611_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__27, &l_Lake_Check_instFromJsonConfig_fromJson___closed__27_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27);
v___x_3612_ = lean_string_append(v___x_3611_, v_a_3607_);
lean_dec(v_a_3607_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3612_);
v___x_3614_ = v___x_3609_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
else
{
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec(v_a_3604_);
lean_dec(v_a_3583_);
lean_dec(v_a_3562_);
lean_dec(v_json_3541_);
v_a_3617_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3606_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3606_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set_tag(v___x_3619_, 0);
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v_a_3625_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3606_, 1);
v___x_3626_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
lean_inc(v_json_3541_);
v___x_3627_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_3541_, v___x_3626_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3637_; 
lean_dec(v_a_3625_);
lean_dec(v_a_3604_);
lean_dec(v_a_3583_);
lean_dec(v_a_3562_);
lean_dec(v_json_3541_);
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3630_ = v___x_3627_;
v_isShared_3631_ = v_isSharedCheck_3637_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3637_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3635_; 
v___x_3632_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__31, &l_Lake_Check_instFromJsonConfig_fromJson___closed__31_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31);
v___x_3633_ = lean_string_append(v___x_3632_, v_a_3628_);
lean_dec(v_a_3628_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3633_);
v___x_3635_ = v___x_3630_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
else
{
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec(v_a_3625_);
lean_dec(v_a_3604_);
lean_dec(v_a_3583_);
lean_dec(v_a_3562_);
lean_dec(v_json_3541_);
v_a_3638_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3627_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3627_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
lean_ctor_set_tag(v___x_3640_, 0);
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v_a_3646_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_a_3646_);
lean_dec_ref_known(v___x_3627_, 1);
v___x_3647_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
lean_inc(v_json_3541_);
v___x_3648_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_json_3541_, v___x_3647_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3658_; 
lean_dec(v_a_3646_);
lean_dec(v_a_3625_);
lean_dec(v_a_3604_);
lean_dec(v_a_3583_);
lean_dec(v_a_3562_);
lean_dec(v_json_3541_);
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3651_ = v___x_3648_;
v_isShared_3652_ = v_isSharedCheck_3658_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3648_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3658_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3653_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__37, &l_Lake_Check_instFromJsonConfig_fromJson___closed__37_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37);
v___x_3654_ = lean_string_append(v___x_3653_, v_a_3649_);
lean_dec(v_a_3649_);
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
else
{
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec(v_a_3646_);
lean_dec(v_a_3625_);
lean_dec(v_a_3604_);
lean_dec(v_a_3583_);
lean_dec(v_a_3562_);
lean_dec(v_json_3541_);
v_a_3659_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3648_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3648_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
lean_ctor_set_tag(v___x_3661_, 0);
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v_a_3667_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3648_, 1);
v___x_3668_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_3669_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_json_3541_, v___x_3668_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3679_; 
lean_dec(v_a_3667_);
lean_dec(v_a_3646_);
lean_dec(v_a_3625_);
lean_dec(v_a_3604_);
lean_dec(v_a_3583_);
lean_dec(v_a_3562_);
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3679_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3679_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3677_; 
v___x_3674_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__43, &l_Lake_Check_instFromJsonConfig_fromJson___closed__43_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43);
v___x_3675_ = lean_string_append(v___x_3674_, v_a_3670_);
lean_dec(v_a_3670_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v___x_3675_);
v___x_3677_ = v___x_3672_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
else
{
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_dec(v_a_3667_);
lean_dec(v_a_3646_);
lean_dec(v_a_3625_);
lean_dec(v_a_3604_);
lean_dec(v_a_3583_);
lean_dec(v_a_3562_);
v_a_3680_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3669_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3669_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
lean_ctor_set_tag(v___x_3682_, 0);
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3696_; 
v_a_3688_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3690_ = v___x_3669_;
v_isShared_3691_ = v_isSharedCheck_3696_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3669_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3696_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3692_; lean_object* v___x_3694_; 
v___x_3692_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3692_, 0, v_a_3562_);
lean_ctor_set(v___x_3692_, 1, v_a_3583_);
lean_ctor_set(v___x_3692_, 2, v_a_3604_);
lean_ctor_set(v___x_3692_, 3, v_a_3625_);
lean_ctor_set(v___x_3692_, 4, v_a_3646_);
lean_ctor_set(v___x_3692_, 5, v_a_3667_);
lean_ctor_set(v___x_3692_, 6, v_a_3688_);
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 0, v___x_3692_);
v___x_3694_ = v___x_3690_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10(lean_object* v_cmp_3697_, lean_object* v_00_u03b2_3698_, lean_object* v_k_3699_, lean_object* v_v_3700_, lean_object* v_t_3701_, lean_object* v_hl_3702_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3697_, v_k_3699_, v_v_3700_, v_t_3701_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(lean_object* v_k_3706_, lean_object* v_x_3707_){
_start:
{
if (lean_obj_tag(v_x_3707_) == 0)
{
lean_object* v___x_3708_; 
lean_dec_ref(v_k_3706_);
v___x_3708_ = lean_box(0);
return v___x_3708_;
}
else
{
lean_object* v_val_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v_val_3709_ = lean_ctor_get(v_x_3707_, 0);
v___x_3710_ = lean_alloc_ctor(1, 0, 1);
v___x_3711_ = lean_unbox(v_val_3709_);
lean_ctor_set_uint8(v___x_3710_, 0, v___x_3711_);
v___x_3712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3712_, 0, v_k_3706_);
lean_ctor_set(v___x_3712_, 1, v___x_3710_);
v___x_3713_ = lean_box(0);
v___x_3714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
return v___x_3714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2___boxed(lean_object* v_k_3715_, lean_object* v_x_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v_k_3715_, v_x_3716_);
lean_dec(v_x_3716_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(size_t v_sz_3718_, size_t v_i_3719_, lean_object* v_bs_3720_){
_start:
{
uint8_t v___x_3721_; 
v___x_3721_ = lean_usize_dec_lt(v_i_3719_, v_sz_3718_);
if (v___x_3721_ == 0)
{
return v_bs_3720_;
}
else
{
lean_object* v_v_3722_; lean_object* v___x_3723_; lean_object* v_bs_x27_3724_; lean_object* v___x_3725_; size_t v___x_3726_; size_t v___x_3727_; lean_object* v___x_3728_; 
v_v_3722_ = lean_array_uget(v_bs_3720_, v_i_3719_);
v___x_3723_ = lean_unsigned_to_nat(0u);
v_bs_x27_3724_ = lean_array_uset(v_bs_3720_, v_i_3719_, v___x_3723_);
v___x_3725_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3725_, 0, v_v_3722_);
v___x_3726_ = ((size_t)1ULL);
v___x_3727_ = lean_usize_add(v_i_3719_, v___x_3726_);
v___x_3728_ = lean_array_uset(v_bs_x27_3724_, v_i_3719_, v___x_3725_);
v_i_3719_ = v___x_3727_;
v_bs_3720_ = v___x_3728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3730_, lean_object* v_i_3731_, lean_object* v_bs_3732_){
_start:
{
size_t v_sz_boxed_3733_; size_t v_i_boxed_3734_; lean_object* v_res_3735_; 
v_sz_boxed_3733_ = lean_unbox_usize(v_sz_3730_);
lean_dec(v_sz_3730_);
v_i_boxed_3734_ = lean_unbox_usize(v_i_3731_);
lean_dec(v_i_3731_);
v_res_3735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_boxed_3733_, v_i_boxed_3734_, v_bs_3732_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(lean_object* v_a_3736_){
_start:
{
size_t v_sz_3737_; size_t v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v_sz_3737_ = lean_array_size(v_a_3736_);
v___x_3738_ = ((size_t)0ULL);
v___x_3739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_3737_, v___x_3738_, v_a_3736_);
v___x_3740_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(lean_object* v_x_3741_){
_start:
{
if (lean_obj_tag(v_x_3741_) == 0)
{
lean_object* v___x_3742_; 
v___x_3742_ = lean_box(0);
return v___x_3742_;
}
else
{
lean_object* v_val_3743_; lean_object* v___x_3744_; 
v_val_3743_ = lean_ctor_get(v_x_3741_, 0);
lean_inc(v_val_3743_);
lean_dec_ref_known(v_x_3741_, 1);
v___x_3744_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_val_3743_);
return v___x_3744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(lean_object* v_a_3745_, lean_object* v_a_3746_){
_start:
{
if (lean_obj_tag(v_a_3745_) == 0)
{
lean_object* v___x_3747_; 
v___x_3747_ = lean_array_to_list(v_a_3746_);
return v___x_3747_;
}
else
{
lean_object* v_head_3748_; lean_object* v_tail_3749_; lean_object* v___x_3750_; 
v_head_3748_ = lean_ctor_get(v_a_3745_, 0);
lean_inc(v_head_3748_);
v_tail_3749_ = lean_ctor_get(v_a_3745_, 1);
lean_inc(v_tail_3749_);
lean_dec_ref_known(v_a_3745_, 2);
v___x_3750_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_3746_, v_head_3748_);
v_a_3745_ = v_tail_3749_;
v_a_3746_ = v___x_3750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(lean_object* v_t_3752_){
_start:
{
if (lean_obj_tag(v_t_3752_) == 0)
{
lean_object* v_size_3753_; lean_object* v_k_3754_; lean_object* v_v_3755_; lean_object* v_l_3756_; lean_object* v_r_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3767_; 
v_size_3753_ = lean_ctor_get(v_t_3752_, 0);
v_k_3754_ = lean_ctor_get(v_t_3752_, 1);
v_v_3755_ = lean_ctor_get(v_t_3752_, 2);
v_l_3756_ = lean_ctor_get(v_t_3752_, 3);
v_r_3757_ = lean_ctor_get(v_t_3752_, 4);
v_isSharedCheck_3767_ = !lean_is_exclusive(v_t_3752_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3759_ = v_t_3752_;
v_isShared_3760_ = v_isSharedCheck_3767_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_r_3757_);
lean_inc(v_l_3756_);
lean_inc(v_v_3755_);
lean_inc(v_k_3754_);
lean_inc(v_size_3753_);
lean_dec(v_t_3752_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3767_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3765_; 
v___x_3761_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_v_3755_);
v___x_3762_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_l_3756_);
v___x_3763_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_r_3757_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 4, v___x_3763_);
lean_ctor_set(v___x_3759_, 3, v___x_3762_);
lean_ctor_set(v___x_3759_, 2, v___x_3761_);
v___x_3765_ = v___x_3759_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_size_3753_);
lean_ctor_set(v_reuseFailAlloc_3766_, 1, v_k_3754_);
lean_ctor_set(v_reuseFailAlloc_3766_, 2, v___x_3761_);
lean_ctor_set(v_reuseFailAlloc_3766_, 3, v___x_3762_);
lean_ctor_set(v_reuseFailAlloc_3766_, 4, v___x_3763_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
else
{
lean_object* v___x_3768_; 
v___x_3768_ = lean_box(1);
return v___x_3768_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(lean_object* v_map_3769_){
_start:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_map_3769_);
v___x_3771_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(lean_object* v_k_3772_, lean_object* v_x_3773_){
_start:
{
if (lean_obj_tag(v_x_3773_) == 0)
{
lean_object* v___x_3774_; 
lean_dec_ref(v_k_3772_);
v___x_3774_ = lean_box(0);
return v___x_3774_;
}
else
{
lean_object* v_val_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v_val_3775_ = lean_ctor_get(v_x_3773_, 0);
lean_inc(v_val_3775_);
lean_dec_ref_known(v_x_3773_, 1);
v___x_3776_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(v_val_3775_);
v___x_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3777_, 0, v_k_3772_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = lean_box(0);
v___x_3779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3777_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
return v___x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instToJsonConfig_toJson(lean_object* v_x_3782_){
_start:
{
lean_object* v_challenge__module_3783_; lean_object* v_solution__module_3784_; lean_object* v_theorem__names_3785_; lean_object* v_definition__names_3786_; lean_object* v_permitted__axioms_3787_; lean_object* v_enable__nanoda_x3f_3788_; lean_object* v_external__kernels_x3f_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v_challenge__module_3783_ = lean_ctor_get(v_x_3782_, 0);
lean_inc_ref(v_challenge__module_3783_);
v_solution__module_3784_ = lean_ctor_get(v_x_3782_, 1);
lean_inc_ref(v_solution__module_3784_);
v_theorem__names_3785_ = lean_ctor_get(v_x_3782_, 2);
lean_inc_ref(v_theorem__names_3785_);
v_definition__names_3786_ = lean_ctor_get(v_x_3782_, 3);
lean_inc(v_definition__names_3786_);
v_permitted__axioms_3787_ = lean_ctor_get(v_x_3782_, 4);
lean_inc_ref(v_permitted__axioms_3787_);
v_enable__nanoda_x3f_3788_ = lean_ctor_get(v_x_3782_, 5);
lean_inc(v_enable__nanoda_x3f_3788_);
v_external__kernels_x3f_3789_ = lean_ctor_get(v_x_3782_, 6);
lean_inc(v_external__kernels_x3f_3789_);
lean_dec_ref(v_x_3782_);
v___x_3790_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
v___x_3791_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3791_, 0, v_challenge__module_3783_);
v___x_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3790_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = lean_box(0);
v___x_3794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3792_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
v___x_3795_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
v___x_3796_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3796_, 0, v_solution__module_3784_);
v___x_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3795_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
lean_ctor_set(v___x_3798_, 1, v___x_3793_);
v___x_3799_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
v___x_3800_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_theorem__names_3785_);
v___x_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3799_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
lean_ctor_set(v___x_3802_, 1, v___x_3793_);
v___x_3803_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
v___x_3804_ = l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(v_definition__names_3786_);
v___x_3805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3803_);
lean_ctor_set(v___x_3805_, 1, v___x_3804_);
v___x_3806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
lean_ctor_set(v___x_3806_, 1, v___x_3793_);
v___x_3807_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
v___x_3808_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_permitted__axioms_3787_);
v___x_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
lean_ctor_set(v___x_3810_, 1, v___x_3793_);
v___x_3811_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
v___x_3812_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v___x_3811_, v_enable__nanoda_x3f_3788_);
lean_dec(v_enable__nanoda_x3f_3788_);
v___x_3813_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_3814_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(v___x_3813_, v_external__kernels_x3f_3789_);
v___x_3815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
lean_ctor_set(v___x_3815_, 1, v___x_3793_);
v___x_3816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3812_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
v___x_3817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3810_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3806_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
v___x_3819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3802_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
v___x_3820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3798_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3794_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = ((lean_object*)(l_Lake_Check_instToJsonConfig_toJson___closed__0));
v___x_3823_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(v___x_3821_, v___x_3822_);
v___x_3824_ = l_Lean_Json_mkObj(v___x_3823_);
lean_dec(v___x_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(lean_object* v_x_3833_, lean_object* v_x_3834_){
_start:
{
if (lean_obj_tag(v_x_3833_) == 0)
{
lean_object* v___x_3835_; 
v___x_3835_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3835_;
}
else
{
lean_object* v_val_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v_val_3836_ = lean_ctor_get(v_x_3833_, 0);
v___x_3837_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3838_ = lean_unbox(v_val_3836_);
v___x_3839_ = l_Bool_repr___redArg(v___x_3838_);
v___x_3840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3837_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
v___x_3841_ = l_Repr_addAppParen(v___x_3840_, v_x_3834_);
return v___x_3841_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___boxed(lean_object* v_x_3842_, lean_object* v_x_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_x_3842_, v_x_3843_);
lean_dec(v_x_3843_);
lean_dec(v_x_3842_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_Check_instReprConfig_repr_spec__4(lean_object* v_a_3845_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = lean_nat_to_int(v_a_3845_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(lean_object* v_x_3847_, lean_object* v_x_3848_, lean_object* v_x_3849_){
_start:
{
if (lean_obj_tag(v_x_3849_) == 0)
{
lean_dec(v_x_3847_);
return v_x_3848_;
}
else
{
lean_object* v_head_3850_; lean_object* v_tail_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3862_; 
v_head_3850_ = lean_ctor_get(v_x_3849_, 0);
v_tail_3851_ = lean_ctor_get(v_x_3849_, 1);
v_isSharedCheck_3862_ = !lean_is_exclusive(v_x_3849_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3853_ = v_x_3849_;
v_isShared_3854_ = v_isSharedCheck_3862_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_tail_3851_);
lean_inc(v_head_3850_);
lean_dec(v_x_3849_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3862_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
lean_inc(v_x_3847_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set_tag(v___x_3853_, 5);
lean_ctor_set(v___x_3853_, 1, v_x_3847_);
lean_ctor_set(v___x_3853_, 0, v_x_3848_);
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_x_3848_);
lean_ctor_set(v_reuseFailAlloc_3861_, 1, v_x_3847_);
v___x_3856_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3857_ = l_String_quote(v_head_3850_);
v___x_3858_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3857_);
v___x_3859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3856_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
v_x_3848_ = v___x_3859_;
v_x_3849_ = v_tail_3851_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_3863_, lean_object* v_x_3864_, lean_object* v_x_3865_){
_start:
{
if (lean_obj_tag(v_x_3865_) == 0)
{
lean_dec(v_x_3863_);
return v_x_3864_;
}
else
{
lean_object* v_head_3866_; lean_object* v_tail_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3878_; 
v_head_3866_ = lean_ctor_get(v_x_3865_, 0);
v_tail_3867_ = lean_ctor_get(v_x_3865_, 1);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_x_3865_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3869_ = v_x_3865_;
v_isShared_3870_ = v_isSharedCheck_3878_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_tail_3867_);
lean_inc(v_head_3866_);
lean_dec(v_x_3865_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3878_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
lean_inc(v_x_3863_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set_tag(v___x_3869_, 5);
lean_ctor_set(v___x_3869_, 1, v_x_3863_);
lean_ctor_set(v___x_3869_, 0, v_x_3864_);
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_x_3864_);
lean_ctor_set(v_reuseFailAlloc_3877_, 1, v_x_3863_);
v___x_3872_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3873_ = l_String_quote(v_head_3866_);
v___x_3874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
v___x_3875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3872_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
v___x_3876_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(v_x_3863_, v___x_3875_, v_tail_3867_);
return v___x_3876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(lean_object* v___y_3879_){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = l_String_quote(v___y_3879_);
v___x_3881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(lean_object* v_x_3882_, lean_object* v_x_3883_){
_start:
{
if (lean_obj_tag(v_x_3882_) == 0)
{
lean_object* v___x_3884_; 
lean_dec(v_x_3883_);
v___x_3884_ = lean_box(0);
return v___x_3884_;
}
else
{
lean_object* v_tail_3885_; 
v_tail_3885_ = lean_ctor_get(v_x_3882_, 1);
if (lean_obj_tag(v_tail_3885_) == 0)
{
lean_object* v_head_3886_; lean_object* v___x_3887_; 
lean_dec(v_x_3883_);
v_head_3886_ = lean_ctor_get(v_x_3882_, 0);
lean_inc(v_head_3886_);
lean_dec_ref_known(v_x_3882_, 2);
v___x_3887_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3886_);
return v___x_3887_;
}
else
{
lean_object* v_head_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
lean_inc(v_tail_3885_);
v_head_3888_ = lean_ctor_get(v_x_3882_, 0);
lean_inc(v_head_3888_);
lean_dec_ref_known(v_x_3882_, 2);
v___x_3889_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3888_);
v___x_3890_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(v_x_3883_, v___x_3889_, v_tail_3885_);
return v___x_3890_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__0));
v___x_3899_ = lean_string_length(v___x_3898_);
return v___x_3899_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4);
v___x_3901_ = lean_nat_to_int(v___x_3900_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(lean_object* v_xs_3909_){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; uint8_t v___x_3912_; 
v___x_3910_ = lean_array_get_size(v_xs_3909_);
v___x_3911_ = lean_unsigned_to_nat(0u);
v___x_3912_ = lean_nat_dec_eq(v___x_3910_, v___x_3911_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3913_ = lean_array_to_list(v_xs_3909_);
v___x_3914_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3915_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(v___x_3913_, v___x_3914_);
v___x_3916_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5);
v___x_3917_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__6));
v___x_3918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
lean_ctor_set(v___x_3918_, 1, v___x_3915_);
v___x_3919_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_3920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3918_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3916_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = l_Std_Format_fill(v___x_3921_);
return v___x_3922_;
}
else
{
lean_object* v___x_3923_; 
lean_dec_ref(v_xs_3909_);
v___x_3923_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__9));
return v___x_3923_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(lean_object* v_x_3924_, lean_object* v_x_3925_){
_start:
{
if (lean_obj_tag(v_x_3924_) == 0)
{
lean_object* v___x_3926_; 
v___x_3926_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3926_;
}
else
{
lean_object* v_val_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v_val_3927_ = lean_ctor_get(v_x_3924_, 0);
lean_inc(v_val_3927_);
lean_dec_ref_known(v_x_3924_, 1);
v___x_3928_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3929_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_val_3927_);
v___x_3930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3928_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = l_Repr_addAppParen(v___x_3930_, v_x_3925_);
return v___x_3931_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1___boxed(lean_object* v_x_3932_, lean_object* v_x_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_x_3932_, v_x_3933_);
lean_dec(v_x_3933_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(lean_object* v_init_3935_, lean_object* v_x_3936_){
_start:
{
if (lean_obj_tag(v_x_3936_) == 0)
{
lean_object* v_k_3937_; lean_object* v_v_3938_; lean_object* v_l_3939_; lean_object* v_r_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v_k_3937_ = lean_ctor_get(v_x_3936_, 1);
v_v_3938_ = lean_ctor_get(v_x_3936_, 2);
v_l_3939_ = lean_ctor_get(v_x_3936_, 3);
v_r_3940_ = lean_ctor_get(v_x_3936_, 4);
v___x_3941_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_3935_, v_r_3940_);
lean_inc(v_v_3938_);
lean_inc(v_k_3937_);
v___x_3942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3942_, 0, v_k_3937_);
lean_ctor_set(v___x_3942_, 1, v_v_3938_);
v___x_3943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
lean_ctor_set(v___x_3943_, 1, v___x_3941_);
v_init_3935_ = v___x_3943_;
v_x_3936_ = v_l_3939_;
goto _start;
}
else
{
return v_init_3935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4___boxed(lean_object* v_init_3945_, lean_object* v_x_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_3945_, v_x_3946_);
lean_dec(v_x_3946_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(lean_object* v_x_3948_, lean_object* v_x_3949_, lean_object* v_x_3950_){
_start:
{
if (lean_obj_tag(v_x_3950_) == 0)
{
lean_dec(v_x_3948_);
return v_x_3949_;
}
else
{
lean_object* v_head_3951_; lean_object* v_tail_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3961_; 
v_head_3951_ = lean_ctor_get(v_x_3950_, 0);
v_tail_3952_ = lean_ctor_get(v_x_3950_, 1);
v_isSharedCheck_3961_ = !lean_is_exclusive(v_x_3950_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3954_ = v_x_3950_;
v_isShared_3955_ = v_isSharedCheck_3961_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_tail_3952_);
lean_inc(v_head_3951_);
lean_dec(v_x_3950_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3961_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3957_; 
lean_inc(v_x_3948_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set_tag(v___x_3954_, 5);
lean_ctor_set(v___x_3954_, 1, v_x_3948_);
lean_ctor_set(v___x_3954_, 0, v_x_3949_);
v___x_3957_ = v___x_3954_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_x_3949_);
lean_ctor_set(v_reuseFailAlloc_3960_, 1, v_x_3948_);
v___x_3957_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
lean_object* v___x_3958_; 
v___x_3958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
lean_ctor_set(v___x_3958_, 1, v_head_3951_);
v_x_3949_ = v___x_3958_;
v_x_3950_ = v_tail_3952_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(lean_object* v_x_3962_, lean_object* v_x_3963_){
_start:
{
if (lean_obj_tag(v_x_3962_) == 0)
{
lean_object* v___x_3964_; 
lean_dec(v_x_3963_);
v___x_3964_ = lean_box(0);
return v___x_3964_;
}
else
{
lean_object* v_tail_3965_; 
v_tail_3965_ = lean_ctor_get(v_x_3962_, 1);
if (lean_obj_tag(v_tail_3965_) == 0)
{
lean_object* v_head_3966_; 
lean_dec(v_x_3963_);
v_head_3966_ = lean_ctor_get(v_x_3962_, 0);
lean_inc(v_head_3966_);
lean_dec_ref_known(v_x_3962_, 2);
return v_head_3966_;
}
else
{
lean_object* v_head_3967_; lean_object* v___x_3968_; 
lean_inc(v_tail_3965_);
v_head_3967_ = lean_ctor_get(v_x_3962_, 0);
lean_inc(v_head_3967_);
lean_dec_ref_known(v_x_3962_, 2);
v___x_3968_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(v_x_3963_, v_head_3967_, v_tail_3965_);
return v___x_3968_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__0));
v___x_3972_ = lean_string_length(v___x_3971_);
return v___x_3972_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2);
v___x_3974_ = lean_nat_to_int(v___x_3973_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(lean_object* v_x_3979_){
_start:
{
lean_object* v_fst_3980_; lean_object* v_snd_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_4004_; 
v_fst_3980_ = lean_ctor_get(v_x_3979_, 0);
v_snd_3981_ = lean_ctor_get(v_x_3979_, 1);
v_isSharedCheck_4004_ = !lean_is_exclusive(v_x_3979_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3983_ = v_x_3979_;
v_isShared_3984_ = v_isSharedCheck_4004_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_snd_3981_);
lean_inc(v_fst_3980_);
lean_dec(v_x_3979_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_4004_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3989_; 
v___x_3985_ = l_String_quote(v_fst_3980_);
v___x_3986_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
v___x_3987_ = lean_box(0);
if (v_isShared_3984_ == 0)
{
lean_ctor_set_tag(v___x_3983_, 1);
lean_ctor_set(v___x_3983_, 1, v___x_3987_);
lean_ctor_set(v___x_3983_, 0, v___x_3986_);
v___x_3989_ = v___x_3983_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_3986_);
lean_ctor_set(v_reuseFailAlloc_4003_, 1, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_4003_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; uint8_t v___x_4001_; lean_object* v___x_4002_; 
v___x_3990_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_snd_3981_);
v___x_3991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
lean_ctor_set(v___x_3991_, 1, v___x_3989_);
v___x_3992_ = l_List_reverse___redArg(v___x_3991_);
v___x_3993_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3994_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(v___x_3992_, v___x_3993_);
v___x_3995_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3);
v___x_3996_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__4));
v___x_3997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
lean_ctor_set(v___x_3997_, 1, v___x_3994_);
v___x_3998_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__5));
v___x_3999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3997_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3995_);
lean_ctor_set(v___x_4000_, 1, v___x_3999_);
v___x_4001_ = 0;
v___x_4002_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4002_, 0, v___x_4000_);
lean_ctor_set_uint8(v___x_4002_, sizeof(void*)*1, v___x_4001_);
return v___x_4002_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(lean_object* v_x_4005_, lean_object* v_x_4006_, lean_object* v_x_4007_){
_start:
{
if (lean_obj_tag(v_x_4007_) == 0)
{
lean_dec(v_x_4005_);
return v_x_4006_;
}
else
{
lean_object* v_head_4008_; lean_object* v_tail_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4019_; 
v_head_4008_ = lean_ctor_get(v_x_4007_, 0);
v_tail_4009_ = lean_ctor_get(v_x_4007_, 1);
v_isSharedCheck_4019_ = !lean_is_exclusive(v_x_4007_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4011_ = v_x_4007_;
v_isShared_4012_ = v_isSharedCheck_4019_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_tail_4009_);
lean_inc(v_head_4008_);
lean_dec(v_x_4007_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4019_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
lean_inc(v_x_4005_);
if (v_isShared_4012_ == 0)
{
lean_ctor_set_tag(v___x_4011_, 5);
lean_ctor_set(v___x_4011_, 1, v_x_4005_);
lean_ctor_set(v___x_4011_, 0, v_x_4006_);
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_x_4006_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v_x_4005_);
v___x_4014_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4015_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_4008_);
v___x_4016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4014_);
lean_ctor_set(v___x_4016_, 1, v___x_4015_);
v_x_4006_ = v___x_4016_;
v_x_4007_ = v_tail_4009_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(lean_object* v_x_4020_, lean_object* v_x_4021_, lean_object* v_x_4022_){
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
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4030_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_4023_);
v___x_4031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4029_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
v___x_4032_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(v_x_4020_, v___x_4031_, v_tail_4024_);
return v___x_4032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(lean_object* v_x_4035_, lean_object* v_x_4036_){
_start:
{
if (lean_obj_tag(v_x_4035_) == 0)
{
lean_object* v___x_4037_; 
lean_dec(v_x_4036_);
v___x_4037_ = lean_box(0);
return v___x_4037_;
}
else
{
lean_object* v_tail_4038_; 
v_tail_4038_ = lean_ctor_get(v_x_4035_, 1);
if (lean_obj_tag(v_tail_4038_) == 0)
{
lean_object* v_head_4039_; lean_object* v___x_4040_; 
lean_dec(v_x_4036_);
v_head_4039_ = lean_ctor_get(v_x_4035_, 0);
lean_inc(v_head_4039_);
lean_dec_ref_known(v_x_4035_, 2);
v___x_4040_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_4039_);
return v___x_4040_;
}
else
{
lean_object* v_head_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
lean_inc(v_tail_4038_);
v_head_4041_ = lean_ctor_get(v_x_4035_, 0);
lean_inc(v_head_4041_);
lean_dec_ref_known(v_x_4035_, 2);
v___x_4042_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_4041_);
v___x_4043_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(v_x_4036_, v___x_4042_, v_tail_4038_);
return v___x_4043_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_4047_ = lean_string_length(v___x_4046_);
return v___x_4047_;
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1);
v___x_4049_ = lean_nat_to_int(v___x_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(lean_object* v_a_4052_){
_start:
{
if (lean_obj_tag(v_a_4052_) == 0)
{
lean_object* v___x_4053_; 
v___x_4053_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0));
return v___x_4053_;
}
else
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; uint8_t v___x_4062_; lean_object* v___x_4063_; 
v___x_4054_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_4055_ = l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(v_a_4052_, v___x_4054_);
v___x_4056_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2);
v___x_4057_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__3));
v___x_4058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
lean_ctor_set(v___x_4058_, 1, v___x_4055_);
v___x_4059_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_4060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4058_);
lean_ctor_set(v___x_4060_, 1, v___x_4059_);
v___x_4061_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4056_);
lean_ctor_set(v___x_4061_, 1, v___x_4060_);
v___x_4062_ = 0;
v___x_4063_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4063_, 0, v___x_4061_);
lean_ctor_set_uint8(v___x_4063_, sizeof(void*)*1, v___x_4062_);
return v___x_4063_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(lean_object* v_x_4067_, lean_object* v_x_4068_){
_start:
{
if (lean_obj_tag(v_x_4067_) == 0)
{
lean_object* v___x_4069_; 
v___x_4069_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_4069_;
}
else
{
lean_object* v_val_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v_val_4070_ = lean_ctor_get(v_x_4067_, 0);
v___x_4071_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_4072_ = lean_unsigned_to_nat(1024u);
v___x_4073_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__1));
v___x_4074_ = lean_box(0);
v___x_4075_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v___x_4074_, v_val_4070_);
v___x_4076_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v___x_4075_);
v___x_4077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4073_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
v___x_4078_ = l_Repr_addAppParen(v___x_4077_, v___x_4072_);
v___x_4079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4071_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
v___x_4080_ = l_Repr_addAppParen(v___x_4079_, v_x_4068_);
return v___x_4080_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___boxed(lean_object* v_x_4081_, lean_object* v_x_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_x_4081_, v_x_4082_);
lean_dec(v_x_4082_);
lean_dec(v_x_4081_);
return v_res_4083_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4096_ = lean_unsigned_to_nat(20u);
v___x_4097_ = lean_nat_to_int(v___x_4096_);
return v___x_4097_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4100_ = lean_unsigned_to_nat(19u);
v___x_4101_ = lean_nat_to_int(v___x_4100_);
return v___x_4101_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = lean_unsigned_to_nat(17u);
v___x_4105_ = lean_nat_to_int(v___x_4104_);
return v___x_4105_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = lean_unsigned_to_nat(18u);
v___x_4113_ = lean_nat_to_int(v___x_4112_);
return v___x_4113_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4116_ = lean_unsigned_to_nat(21u);
v___x_4117_ = lean_nat_to_int(v___x_4116_);
return v___x_4117_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4119_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__0));
v___x_4120_ = lean_string_length(v___x_4119_);
return v___x_4120_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4121_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__18, &l_Lake_Check_instReprConfig_repr___redArg___closed__18_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18);
v___x_4122_ = lean_nat_to_int(v___x_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___redArg(lean_object* v_x_4127_){
_start:
{
lean_object* v_challenge__module_4128_; lean_object* v_solution__module_4129_; lean_object* v_theorem__names_4130_; lean_object* v_definition__names_4131_; lean_object* v_permitted__axioms_4132_; lean_object* v_enable__nanoda_x3f_4133_; lean_object* v_external__kernels_x3f_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; uint8_t v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v_challenge__module_4128_ = lean_ctor_get(v_x_4127_, 0);
lean_inc_ref(v_challenge__module_4128_);
v_solution__module_4129_ = lean_ctor_get(v_x_4127_, 1);
lean_inc_ref(v_solution__module_4129_);
v_theorem__names_4130_ = lean_ctor_get(v_x_4127_, 2);
lean_inc_ref(v_theorem__names_4130_);
v_definition__names_4131_ = lean_ctor_get(v_x_4127_, 3);
lean_inc(v_definition__names_4131_);
v_permitted__axioms_4132_ = lean_ctor_get(v_x_4127_, 4);
lean_inc_ref(v_permitted__axioms_4132_);
v_enable__nanoda_x3f_4133_ = lean_ctor_get(v_x_4127_, 5);
lean_inc(v_enable__nanoda_x3f_4133_);
v_external__kernels_x3f_4134_ = lean_ctor_get(v_x_4127_, 6);
lean_inc(v_external__kernels_x3f_4134_);
lean_dec_ref(v_x_4127_);
v___x_4135_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__4));
v___x_4136_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__5));
v___x_4137_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__6, &l_Lake_Check_instReprConfig_repr___redArg___closed__6_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6);
v___x_4138_ = l_String_quote(v_challenge__module_4128_);
v___x_4139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4138_);
v___x_4140_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4137_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = 0;
v___x_4142_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4142_, 0, v___x_4140_);
lean_ctor_set_uint8(v___x_4142_, sizeof(void*)*1, v___x_4141_);
v___x_4143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4136_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
v___x_4144_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__2));
v___x_4145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4143_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
v___x_4146_ = lean_box(1);
v___x_4147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4145_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
v___x_4148_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__7));
v___x_4149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4147_);
lean_ctor_set(v___x_4149_, 1, v___x_4148_);
v___x_4150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
lean_ctor_set(v___x_4150_, 1, v___x_4135_);
v___x_4151_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__8, &l_Lake_Check_instReprConfig_repr___redArg___closed__8_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8);
v___x_4152_ = l_String_quote(v_solution__module_4129_);
v___x_4153_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
v___x_4154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4151_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
v___x_4155_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
lean_ctor_set_uint8(v___x_4155_, sizeof(void*)*1, v___x_4141_);
v___x_4156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4150_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4156_);
lean_ctor_set(v___x_4157_, 1, v___x_4144_);
v___x_4158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
lean_ctor_set(v___x_4158_, 1, v___x_4146_);
v___x_4159_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__9));
v___x_4160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4158_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
v___x_4161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
lean_ctor_set(v___x_4161_, 1, v___x_4135_);
v___x_4162_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__10, &l_Lake_Check_instReprConfig_repr___redArg___closed__10_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10);
v___x_4163_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_theorem__names_4130_);
v___x_4164_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4162_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
lean_ctor_set_uint8(v___x_4165_, sizeof(void*)*1, v___x_4141_);
v___x_4166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4161_);
lean_ctor_set(v___x_4166_, 1, v___x_4165_);
v___x_4167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
lean_ctor_set(v___x_4167_, 1, v___x_4144_);
v___x_4168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
lean_ctor_set(v___x_4168_, 1, v___x_4146_);
v___x_4169_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__11));
v___x_4170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4168_);
lean_ctor_set(v___x_4170_, 1, v___x_4169_);
v___x_4171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
lean_ctor_set(v___x_4171_, 1, v___x_4135_);
v___x_4172_ = lean_unsigned_to_nat(0u);
v___x_4173_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_definition__names_4131_, v___x_4172_);
v___x_4174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4137_);
lean_ctor_set(v___x_4174_, 1, v___x_4173_);
v___x_4175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
lean_ctor_set_uint8(v___x_4175_, sizeof(void*)*1, v___x_4141_);
v___x_4176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4171_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4176_);
lean_ctor_set(v___x_4177_, 1, v___x_4144_);
v___x_4178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
lean_ctor_set(v___x_4178_, 1, v___x_4146_);
v___x_4179_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__12));
v___x_4180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4178_);
lean_ctor_set(v___x_4180_, 1, v___x_4179_);
v___x_4181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4180_);
lean_ctor_set(v___x_4181_, 1, v___x_4135_);
v___x_4182_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_permitted__axioms_4132_);
v___x_4183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4137_);
lean_ctor_set(v___x_4183_, 1, v___x_4182_);
v___x_4184_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
lean_ctor_set_uint8(v___x_4184_, sizeof(void*)*1, v___x_4141_);
v___x_4185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4181_);
lean_ctor_set(v___x_4185_, 1, v___x_4184_);
v___x_4186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
lean_ctor_set(v___x_4186_, 1, v___x_4144_);
v___x_4187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
lean_ctor_set(v___x_4187_, 1, v___x_4146_);
v___x_4188_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__13));
v___x_4189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4187_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
lean_ctor_set(v___x_4190_, 1, v___x_4135_);
v___x_4191_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__14, &l_Lake_Check_instReprConfig_repr___redArg___closed__14_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14);
v___x_4192_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_enable__nanoda_x3f_4133_, v___x_4172_);
lean_dec(v_enable__nanoda_x3f_4133_);
v___x_4193_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4191_);
lean_ctor_set(v___x_4193_, 1, v___x_4192_);
v___x_4194_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
lean_ctor_set_uint8(v___x_4194_, sizeof(void*)*1, v___x_4141_);
v___x_4195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4190_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
v___x_4196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
lean_ctor_set(v___x_4196_, 1, v___x_4144_);
v___x_4197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
lean_ctor_set(v___x_4197_, 1, v___x_4146_);
v___x_4198_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__15));
v___x_4199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4197_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
v___x_4200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4199_);
lean_ctor_set(v___x_4200_, 1, v___x_4135_);
v___x_4201_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__16, &l_Lake_Check_instReprConfig_repr___redArg___closed__16_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16);
v___x_4202_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_external__kernels_x3f_4134_, v___x_4172_);
lean_dec(v_external__kernels_x3f_4134_);
v___x_4203_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4201_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___x_4204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
lean_ctor_set_uint8(v___x_4204_, sizeof(void*)*1, v___x_4141_);
v___x_4205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4200_);
lean_ctor_set(v___x_4205_, 1, v___x_4204_);
v___x_4206_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__19, &l_Lake_Check_instReprConfig_repr___redArg___closed__19_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19);
v___x_4207_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__20));
v___x_4208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
lean_ctor_set(v___x_4208_, 1, v___x_4205_);
v___x_4209_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__21));
v___x_4210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4208_);
lean_ctor_set(v___x_4210_, 1, v___x_4209_);
v___x_4211_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4206_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
v___x_4212_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4212_, 0, v___x_4211_);
lean_ctor_set_uint8(v___x_4212_, sizeof(void*)*1, v___x_4141_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr(lean_object* v_x_4213_, lean_object* v_prec_4214_){
_start:
{
lean_object* v___x_4215_; 
v___x_4215_ = l_Lake_Check_instReprConfig_repr___redArg(v_x_4213_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___boxed(lean_object* v_x_4216_, lean_object* v_prec_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_Lake_Check_instReprConfig_repr(v_x_4216_, v_prec_4217_);
lean_dec(v_prec_4217_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(lean_object* v_a_4219_, lean_object* v_n_4220_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v_a_4219_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___boxed(lean_object* v_a_4222_, lean_object* v_n_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(v_a_4222_, v_n_4223_);
lean_dec(v_n_4223_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(lean_object* v_x_4225_, lean_object* v_x_4226_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_x_4225_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___boxed(lean_object* v_x_4228_, lean_object* v_x_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(v_x_4228_, v_x_4229_);
lean_dec(v_x_4229_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(lean_object* v_s_4233_){
_start:
{
uint32_t v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4235_ = 10;
v___x_4236_ = lean_string_push(v_s_4233_, v___x_4235_);
v___x_4237_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v___x_4236_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0___boxed(lean_object* v_s_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v_s_4238_);
return v_res_4240_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1(void){
_start:
{
uint32_t v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = 2;
v___x_4243_ = lean_box_uint32(v___x_4242_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(lean_object* v_msg_4244_){
_start:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4246_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_4247_ = lean_string_append(v___x_4246_, v_msg_4244_);
v___x_4248_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_4247_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4256_; 
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4256_ == 0)
{
lean_object* v_unused_4257_; 
v_unused_4257_ = lean_ctor_get(v___x_4248_, 0);
lean_dec(v_unused_4257_);
v___x_4250_ = v___x_4248_;
v_isShared_4251_ = v_isSharedCheck_4256_;
goto v_resetjp_4249_;
}
else
{
lean_dec(v___x_4248_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4256_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4252_; lean_object* v___x_4254_; 
v___x_4252_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1;
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 0, v___x_4252_);
v___x_4254_ = v___x_4250_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4252_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
else
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
v_a_4258_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4260_ = v___x_4248_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4248_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed(lean_object* v_msg_4266_, lean_object* v_a_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v_msg_4266_);
lean_dec_ref(v_msg_4266_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(lean_object* v_cmd_4272_, lean_object* v_projectDir_4273_){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; uint8_t v___x_4277_; 
v___x_4275_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__0));
lean_inc_ref(v_projectDir_4273_);
v___x_4276_ = l_System_FilePath_join(v_projectDir_4273_, v___x_4275_);
v___x_4277_ = l_System_FilePath_pathExists(v___x_4276_);
lean_dec_ref(v___x_4276_);
if (v___x_4277_ == 0)
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4278_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_4279_ = lean_string_append(v___x_4278_, v_projectDir_4273_);
lean_dec_ref(v_projectDir_4273_);
v___x_4280_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__1));
v___x_4281_ = lean_string_append(v___x_4279_, v___x_4280_);
v___x_4282_ = lean_string_append(v___x_4281_, v_cmd_4272_);
v___x_4283_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__2));
v___x_4284_ = lean_string_append(v___x_4282_, v___x_4283_);
v___x_4285_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4284_);
lean_dec_ref(v___x_4284_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4294_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4288_ = v___x_4285_;
v_isShared_4289_ = v_isSharedCheck_4294_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4285_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4294_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4290_; lean_object* v___x_4292_; 
v___x_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4290_, 0, v_a_4286_);
if (v_isShared_4289_ == 0)
{
lean_ctor_set(v___x_4288_, 0, v___x_4290_);
v___x_4292_ = v___x_4288_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4290_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
v_a_4295_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4285_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4285_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
else
{
lean_object* v___x_4303_; lean_object* v___x_4304_; 
lean_dec_ref(v_projectDir_4273_);
v___x_4303_ = lean_box(0);
v___x_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4303_);
return v___x_4304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___boxed(lean_object* v_cmd_4305_, lean_object* v_projectDir_4306_, lean_object* v_a_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v_cmd_4305_, v_projectDir_4306_);
lean_dec_ref(v_cmd_4305_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(lean_object* v_lean_4309_, lean_object* v_name_4310_){
_start:
{
lean_object* v_binDir_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v_binDir_4311_ = lean_ctor_get(v_lean_4309_, 6);
lean_inc_ref(v_binDir_4311_);
lean_dec_ref(v_lean_4309_);
v___x_4312_ = l_System_FilePath_join(v_binDir_4311_, v_name_4310_);
v___x_4313_ = l_System_FilePath_exeExtension;
v___x_4314_ = l_System_FilePath_addExtension(v___x_4312_, v___x_4313_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels(lean_object* v_lean_4323_){
_start:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4324_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__0));
v___x_4325_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__1));
lean_inc_ref_n(v_lean_4323_, 4);
v___x_4326_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4323_, v___x_4325_);
v___x_4327_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0));
v___x_4328_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_4329_ = lean_unsigned_to_nat(3u);
v___x_4330_ = lean_mk_empty_array_with_capacity(v___x_4329_);
v___x_4331_ = lean_array_push(v___x_4330_, v___x_4326_);
v___x_4332_ = lean_array_push(v___x_4331_, v___x_4327_);
v___x_4333_ = lean_array_push(v___x_4332_, v___x_4328_);
v___x_4334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4324_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
v___x_4335_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__2));
v___x_4336_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4323_, v___x_4335_);
v___x_4337_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__3));
v___x_4338_ = lean_unsigned_to_nat(2u);
v___x_4339_ = lean_mk_empty_array_with_capacity(v___x_4338_);
v___x_4340_ = lean_array_push(v___x_4339_, v___x_4336_);
v___x_4341_ = lean_array_push(v___x_4340_, v___x_4337_);
v___x_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4342_, 0, v___x_4335_);
lean_ctor_set(v___x_4342_, 1, v___x_4341_);
v___x_4343_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__4));
v___x_4344_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__5));
v___x_4345_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4323_, v___x_4344_);
v___x_4346_ = lean_unsigned_to_nat(1u);
v___x_4347_ = lean_mk_empty_array_with_capacity(v___x_4346_);
lean_inc_ref_n(v___x_4347_, 2);
v___x_4348_ = lean_array_push(v___x_4347_, v___x_4345_);
v___x_4349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4343_);
lean_ctor_set(v___x_4349_, 1, v___x_4348_);
v___x_4350_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__6));
v___x_4351_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4323_, v___x_4350_);
v___x_4352_ = lean_array_push(v___x_4347_, v___x_4351_);
v___x_4353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4350_);
lean_ctor_set(v___x_4353_, 1, v___x_4352_);
v___x_4354_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__7));
v___x_4355_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4323_, v___x_4354_);
v___x_4356_ = lean_array_push(v___x_4347_, v___x_4355_);
v___x_4357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4354_);
lean_ctor_set(v___x_4357_, 1, v___x_4356_);
v___x_4358_ = lean_unsigned_to_nat(5u);
v___x_4359_ = lean_mk_empty_array_with_capacity(v___x_4358_);
v___x_4360_ = lean_array_push(v___x_4359_, v___x_4334_);
v___x_4361_ = lean_array_push(v___x_4360_, v___x_4342_);
v___x_4362_ = lean_array_push(v___x_4361_, v___x_4349_);
v___x_4363_ = lean_array_push(v___x_4362_, v___x_4353_);
v___x_4364_ = lean_array_push(v___x_4363_, v___x_4357_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(uint8_t v_a_4365_, lean_object* v_b_4366_, lean_object* v_x_4367_){
_start:
{
if (lean_obj_tag(v_x_4367_) == 0)
{
lean_dec(v_b_4366_);
return v_x_4367_;
}
else
{
lean_object* v_key_4368_; lean_object* v_value_4369_; lean_object* v_tail_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4386_; 
v_key_4368_ = lean_ctor_get(v_x_4367_, 0);
v_value_4369_ = lean_ctor_get(v_x_4367_, 1);
v_tail_4370_ = lean_ctor_get(v_x_4367_, 2);
v_isSharedCheck_4386_ = !lean_is_exclusive(v_x_4367_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4372_ = v_x_4367_;
v_isShared_4373_ = v_isSharedCheck_4386_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_tail_4370_);
lean_inc(v_value_4369_);
lean_inc(v_key_4368_);
lean_dec(v_x_4367_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4386_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
uint8_t v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; uint8_t v___x_4377_; 
v___x_4374_ = lean_unbox(v_key_4368_);
v___x_4375_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v___x_4374_);
v___x_4376_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v_a_4365_);
v___x_4377_ = lean_nat_dec_eq(v___x_4375_, v___x_4376_);
lean_dec(v___x_4376_);
lean_dec(v___x_4375_);
if (v___x_4377_ == 0)
{
lean_object* v___x_4378_; lean_object* v___x_4380_; 
v___x_4378_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_4365_, v_b_4366_, v_tail_4370_);
if (v_isShared_4373_ == 0)
{
lean_ctor_set(v___x_4372_, 2, v___x_4378_);
v___x_4380_ = v___x_4372_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_key_4368_);
lean_ctor_set(v_reuseFailAlloc_4381_, 1, v_value_4369_);
lean_ctor_set(v_reuseFailAlloc_4381_, 2, v___x_4378_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
else
{
lean_object* v___x_4382_; lean_object* v___x_4384_; 
lean_dec(v_value_4369_);
lean_dec(v_key_4368_);
v___x_4382_ = lean_box(v_a_4365_);
if (v_isShared_4373_ == 0)
{
lean_ctor_set(v___x_4372_, 1, v_b_4366_);
lean_ctor_set(v___x_4372_, 0, v___x_4382_);
v___x_4384_ = v___x_4372_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4382_);
lean_ctor_set(v_reuseFailAlloc_4385_, 1, v_b_4366_);
lean_ctor_set(v_reuseFailAlloc_4385_, 2, v_tail_4370_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg___boxed(lean_object* v_a_4387_, lean_object* v_b_4388_, lean_object* v_x_4389_){
_start:
{
uint8_t v_a_boxed_4390_; lean_object* v_res_4391_; 
v_a_boxed_4390_ = lean_unbox(v_a_4387_);
v_res_4391_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_boxed_4390_, v_b_4388_, v_x_4389_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_4392_, lean_object* v_x_4393_){
_start:
{
if (lean_obj_tag(v_x_4393_) == 0)
{
return v_x_4392_;
}
else
{
lean_object* v_key_4394_; lean_object* v_value_4395_; lean_object* v_tail_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4420_; 
v_key_4394_ = lean_ctor_get(v_x_4393_, 0);
v_value_4395_ = lean_ctor_get(v_x_4393_, 1);
v_tail_4396_ = lean_ctor_get(v_x_4393_, 2);
v_isSharedCheck_4420_ = !lean_is_exclusive(v_x_4393_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4398_ = v_x_4393_;
v_isShared_4399_ = v_isSharedCheck_4420_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_tail_4396_);
lean_inc(v_value_4395_);
lean_inc(v_key_4394_);
lean_dec(v_x_4393_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4420_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4400_; uint8_t v___x_4401_; uint64_t v___x_4402_; uint64_t v___x_4403_; uint64_t v___x_4404_; uint64_t v_fold_4405_; uint64_t v___x_4406_; uint64_t v___x_4407_; uint64_t v___x_4408_; size_t v___x_4409_; size_t v___x_4410_; size_t v___x_4411_; size_t v___x_4412_; size_t v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4416_; 
v___x_4400_ = lean_array_get_size(v_x_4392_);
v___x_4401_ = lean_unbox(v_key_4394_);
v___x_4402_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v___x_4401_);
v___x_4403_ = 32ULL;
v___x_4404_ = lean_uint64_shift_right(v___x_4402_, v___x_4403_);
v_fold_4405_ = lean_uint64_xor(v___x_4402_, v___x_4404_);
v___x_4406_ = 16ULL;
v___x_4407_ = lean_uint64_shift_right(v_fold_4405_, v___x_4406_);
v___x_4408_ = lean_uint64_xor(v_fold_4405_, v___x_4407_);
v___x_4409_ = lean_uint64_to_usize(v___x_4408_);
v___x_4410_ = lean_usize_of_nat(v___x_4400_);
v___x_4411_ = ((size_t)1ULL);
v___x_4412_ = lean_usize_sub(v___x_4410_, v___x_4411_);
v___x_4413_ = lean_usize_land(v___x_4409_, v___x_4412_);
v___x_4414_ = lean_array_uget_borrowed(v_x_4392_, v___x_4413_);
lean_inc(v___x_4414_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 2, v___x_4414_);
v___x_4416_ = v___x_4398_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_key_4394_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v_value_4395_);
lean_ctor_set(v_reuseFailAlloc_4419_, 2, v___x_4414_);
v___x_4416_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4417_; 
v___x_4417_ = lean_array_uset(v_x_4392_, v___x_4413_, v___x_4416_);
v_x_4392_ = v___x_4417_;
v_x_4393_ = v_tail_4396_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2___redArg(lean_object* v_i_4421_, lean_object* v_source_4422_, lean_object* v_target_4423_){
_start:
{
lean_object* v___x_4424_; uint8_t v___x_4425_; 
v___x_4424_ = lean_array_get_size(v_source_4422_);
v___x_4425_ = lean_nat_dec_lt(v_i_4421_, v___x_4424_);
if (v___x_4425_ == 0)
{
lean_dec_ref(v_source_4422_);
lean_dec(v_i_4421_);
return v_target_4423_;
}
else
{
lean_object* v_es_4426_; lean_object* v___x_4427_; lean_object* v_source_4428_; lean_object* v_target_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v_es_4426_ = lean_array_fget(v_source_4422_, v_i_4421_);
v___x_4427_ = lean_box(0);
v_source_4428_ = lean_array_fset(v_source_4422_, v_i_4421_, v___x_4427_);
v_target_4429_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4___redArg(v_target_4423_, v_es_4426_);
v___x_4430_ = lean_unsigned_to_nat(1u);
v___x_4431_ = lean_nat_add(v_i_4421_, v___x_4430_);
lean_dec(v_i_4421_);
v_i_4421_ = v___x_4431_;
v_source_4422_ = v_source_4428_;
v_target_4423_ = v_target_4429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1___redArg(lean_object* v_data_4433_){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v_nbuckets_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4434_ = lean_array_get_size(v_data_4433_);
v___x_4435_ = lean_unsigned_to_nat(2u);
v_nbuckets_4436_ = lean_nat_mul(v___x_4434_, v___x_4435_);
v___x_4437_ = lean_unsigned_to_nat(0u);
v___x_4438_ = lean_box(0);
v___x_4439_ = lean_mk_array(v_nbuckets_4436_, v___x_4438_);
v___x_4440_ = lean_array_propagate_mark(v_data_4433_, v___x_4439_);
v___x_4441_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2___redArg(v___x_4437_, v_data_4433_, v___x_4440_);
return v___x_4441_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(uint8_t v_a_4442_, lean_object* v_x_4443_){
_start:
{
if (lean_obj_tag(v_x_4443_) == 0)
{
uint8_t v___x_4444_; 
v___x_4444_ = 0;
return v___x_4444_;
}
else
{
lean_object* v_key_4445_; lean_object* v_tail_4446_; uint8_t v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; uint8_t v___x_4450_; 
v_key_4445_ = lean_ctor_get(v_x_4443_, 0);
v_tail_4446_ = lean_ctor_get(v_x_4443_, 2);
v___x_4447_ = lean_unbox(v_key_4445_);
v___x_4448_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v___x_4447_);
v___x_4449_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx(v_a_4442_);
v___x_4450_ = lean_nat_dec_eq(v___x_4448_, v___x_4449_);
lean_dec(v___x_4449_);
lean_dec(v___x_4448_);
if (v___x_4450_ == 0)
{
v_x_4443_ = v_tail_4446_;
goto _start;
}
else
{
return v___x_4450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg___boxed(lean_object* v_a_4452_, lean_object* v_x_4453_){
_start:
{
uint8_t v_a_boxed_4454_; uint8_t v_res_4455_; lean_object* v_r_4456_; 
v_a_boxed_4454_ = lean_unbox(v_a_4452_);
v_res_4455_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_boxed_4454_, v_x_4453_);
lean_dec(v_x_4453_);
v_r_4456_ = lean_box(v_res_4455_);
return v_r_4456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(lean_object* v_m_4457_, uint8_t v_a_4458_, lean_object* v_b_4459_){
_start:
{
lean_object* v_size_4460_; lean_object* v_buckets_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4505_; 
v_size_4460_ = lean_ctor_get(v_m_4457_, 0);
v_buckets_4461_ = lean_ctor_get(v_m_4457_, 1);
v_isSharedCheck_4505_ = !lean_is_exclusive(v_m_4457_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4463_ = v_m_4457_;
v_isShared_4464_ = v_isSharedCheck_4505_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_buckets_4461_);
lean_inc(v_size_4460_);
lean_dec(v_m_4457_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4505_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; uint64_t v___x_4466_; uint64_t v___x_4467_; uint64_t v___x_4468_; uint64_t v_fold_4469_; uint64_t v___x_4470_; uint64_t v___x_4471_; uint64_t v___x_4472_; size_t v___x_4473_; size_t v___x_4474_; size_t v___x_4475_; size_t v___x_4476_; size_t v___x_4477_; lean_object* v_bkt_4478_; uint8_t v___x_4479_; 
v___x_4465_ = lean_array_get_size(v_buckets_4461_);
v___x_4466_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_a_4458_);
v___x_4467_ = 32ULL;
v___x_4468_ = lean_uint64_shift_right(v___x_4466_, v___x_4467_);
v_fold_4469_ = lean_uint64_xor(v___x_4466_, v___x_4468_);
v___x_4470_ = 16ULL;
v___x_4471_ = lean_uint64_shift_right(v_fold_4469_, v___x_4470_);
v___x_4472_ = lean_uint64_xor(v_fold_4469_, v___x_4471_);
v___x_4473_ = lean_uint64_to_usize(v___x_4472_);
v___x_4474_ = lean_usize_of_nat(v___x_4465_);
v___x_4475_ = ((size_t)1ULL);
v___x_4476_ = lean_usize_sub(v___x_4474_, v___x_4475_);
v___x_4477_ = lean_usize_land(v___x_4473_, v___x_4476_);
v_bkt_4478_ = lean_array_uget_borrowed(v_buckets_4461_, v___x_4477_);
v___x_4479_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_4458_, v_bkt_4478_);
if (v___x_4479_ == 0)
{
lean_object* v___x_4480_; lean_object* v_size_x27_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v_buckets_x27_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; uint8_t v___x_4490_; 
v___x_4480_ = lean_unsigned_to_nat(1u);
v_size_x27_4481_ = lean_nat_add(v_size_4460_, v___x_4480_);
lean_dec(v_size_4460_);
v___x_4482_ = lean_box(v_a_4458_);
lean_inc(v_bkt_4478_);
v___x_4483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4482_);
lean_ctor_set(v___x_4483_, 1, v_b_4459_);
lean_ctor_set(v___x_4483_, 2, v_bkt_4478_);
v_buckets_x27_4484_ = lean_array_uset(v_buckets_4461_, v___x_4477_, v___x_4483_);
v___x_4485_ = lean_unsigned_to_nat(4u);
v___x_4486_ = lean_nat_mul(v_size_x27_4481_, v___x_4485_);
v___x_4487_ = lean_unsigned_to_nat(3u);
v___x_4488_ = lean_nat_div(v___x_4486_, v___x_4487_);
lean_dec(v___x_4486_);
v___x_4489_ = lean_array_get_size(v_buckets_x27_4484_);
v___x_4490_ = lean_nat_dec_le(v___x_4488_, v___x_4489_);
lean_dec(v___x_4488_);
if (v___x_4490_ == 0)
{
lean_object* v_val_4491_; lean_object* v___x_4493_; 
v_val_4491_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1___redArg(v_buckets_x27_4484_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 1, v_val_4491_);
lean_ctor_set(v___x_4463_, 0, v_size_x27_4481_);
v___x_4493_ = v___x_4463_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_size_x27_4481_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v_val_4491_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
else
{
lean_object* v___x_4496_; 
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 1, v_buckets_x27_4484_);
lean_ctor_set(v___x_4463_, 0, v_size_x27_4481_);
v___x_4496_ = v___x_4463_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_size_x27_4481_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v_buckets_x27_4484_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
else
{
lean_object* v___x_4498_; lean_object* v_buckets_x27_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4503_; 
lean_inc(v_bkt_4478_);
v___x_4498_ = lean_box(0);
v_buckets_x27_4499_ = lean_array_uset(v_buckets_4461_, v___x_4477_, v___x_4498_);
v___x_4500_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_4458_, v_b_4459_, v_bkt_4478_);
v___x_4501_ = lean_array_uset(v_buckets_x27_4499_, v___x_4477_, v___x_4500_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 1, v___x_4501_);
v___x_4503_ = v___x_4463_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_size_4460_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v___x_4501_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg___boxed(lean_object* v_m_4506_, lean_object* v_a_4507_, lean_object* v_b_4508_){
_start:
{
uint8_t v_a_boxed_4509_; lean_object* v_res_4510_; 
v_a_boxed_4509_ = lean_unbox(v_a_4507_);
v_res_4510_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(v_m_4506_, v_a_boxed_4509_, v_b_4508_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(lean_object* v_cmd_4514_, lean_object* v_as_4515_, size_t v_sz_4516_, size_t v_i_4517_, lean_object* v_b_4518_){
_start:
{
lean_object* v_a_4521_; uint8_t v___x_4525_; 
v___x_4525_ = lean_usize_dec_lt(v_i_4517_, v_sz_4516_);
if (v___x_4525_ == 0)
{
lean_object* v___x_4526_; 
v___x_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4526_, 0, v_b_4518_);
return v___x_4526_;
}
else
{
lean_object* v_a_4527_; lean_object* v_snd_4528_; lean_object* v_fst_4529_; lean_object* v_fst_4530_; lean_object* v_snd_4531_; lean_object* v_snd_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4630_; 
v_a_4527_ = lean_array_uget_borrowed(v_as_4515_, v_i_4517_);
v_snd_4528_ = lean_ctor_get(v_a_4527_, 1);
v_fst_4529_ = lean_ctor_get(v_a_4527_, 0);
v_fst_4530_ = lean_ctor_get(v_snd_4528_, 0);
v_snd_4531_ = lean_ctor_get(v_snd_4528_, 1);
lean_inc(v_snd_4531_);
v_snd_4532_ = lean_ctor_get(v_b_4518_, 1);
v_isSharedCheck_4630_ = !lean_is_exclusive(v_b_4518_);
if (v_isSharedCheck_4630_ == 0)
{
lean_object* v_unused_4631_; 
v_unused_4631_ = lean_ctor_get(v_b_4518_, 0);
lean_dec(v_unused_4631_);
v___x_4534_ = v_b_4518_;
v_isShared_4535_ = v_isSharedCheck_4630_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_snd_4532_);
lean_dec(v_b_4518_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4630_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4536_; 
v___x_4536_ = lean_box(0);
if (lean_obj_tag(v_snd_4531_) == 1)
{
lean_object* v_val_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4626_; 
v_val_4537_ = lean_ctor_get(v_snd_4531_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v_snd_4531_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4539_ = v_snd_4531_;
v_isShared_4540_ = v_isSharedCheck_4626_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_val_4537_);
lean_dec(v_snd_4531_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4626_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
uint8_t v___x_4541_; 
v___x_4541_ = l_System_FilePath_pathExists(v_val_4537_);
if (v___x_4541_ == 0)
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4542_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4543_ = lean_string_append(v___x_4542_, v_cmd_4514_);
v___x_4544_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
v___x_4545_ = lean_string_append(v___x_4543_, v___x_4544_);
v___x_4546_ = lean_string_append(v___x_4545_, v_fst_4529_);
v___x_4547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__0));
v___x_4548_ = lean_string_append(v___x_4546_, v___x_4547_);
v___x_4549_ = lean_string_append(v___x_4548_, v_val_4537_);
lean_dec(v_val_4537_);
v___x_4550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__1));
v___x_4551_ = lean_string_append(v___x_4549_, v___x_4550_);
v___x_4552_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4551_);
lean_dec_ref(v___x_4551_);
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4567_; 
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4567_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4555_ = v___x_4552_;
v_isShared_4556_ = v_isSharedCheck_4567_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4552_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4567_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4557_; lean_object* v___x_4559_; 
v___x_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4557_, 0, v_a_4553_);
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 0, v___x_4557_);
v___x_4559_ = v___x_4539_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v___x_4557_);
v___x_4559_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
lean_object* v___x_4561_; 
if (v_isShared_4535_ == 0)
{
lean_ctor_set(v___x_4534_, 0, v___x_4559_);
v___x_4561_ = v___x_4534_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4559_);
lean_ctor_set(v_reuseFailAlloc_4565_, 1, v_snd_4532_);
v___x_4561_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
lean_object* v___x_4563_; 
if (v_isShared_4556_ == 0)
{
lean_ctor_set(v___x_4555_, 0, v___x_4561_);
v___x_4563_ = v___x_4555_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4561_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
}
else
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
lean_del_object(v___x_4539_);
lean_del_object(v___x_4534_);
lean_dec(v_snd_4532_);
v_a_4568_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___x_4552_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4552_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4571_ == 0)
{
v___x_4573_ = v___x_4570_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
}
else
{
uint8_t v___x_4576_; 
v___x_4576_ = l_System_FilePath_isDir(v_val_4537_);
if (v___x_4576_ == 0)
{
lean_object* v___x_4577_; 
lean_del_object(v___x_4539_);
v___x_4577_ = lean_io_realpath(v_val_4537_);
if (lean_obj_tag(v___x_4577_) == 0)
{
lean_object* v_a_4578_; uint8_t v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4582_; 
v_a_4578_ = lean_ctor_get(v___x_4577_, 0);
lean_inc(v_a_4578_);
lean_dec_ref_known(v___x_4577_, 1);
v___x_4579_ = lean_unbox(v_fst_4530_);
v___x_4580_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(v_snd_4532_, v___x_4579_, v_a_4578_);
if (v_isShared_4535_ == 0)
{
lean_ctor_set(v___x_4534_, 1, v___x_4580_);
lean_ctor_set(v___x_4534_, 0, v___x_4536_);
v___x_4582_ = v___x_4534_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___x_4536_);
lean_ctor_set(v_reuseFailAlloc_4583_, 1, v___x_4580_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
v_a_4521_ = v___x_4582_;
goto v___jp_4520_;
}
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
lean_del_object(v___x_4534_);
lean_dec(v_snd_4532_);
v_a_4584_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4577_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4577_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
}
else
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v___x_4592_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4593_ = lean_string_append(v___x_4592_, v_cmd_4514_);
v___x_4594_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
v___x_4595_ = lean_string_append(v___x_4593_, v___x_4594_);
v___x_4596_ = lean_string_append(v___x_4595_, v_fst_4529_);
v___x_4597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__0));
v___x_4598_ = lean_string_append(v___x_4596_, v___x_4597_);
v___x_4599_ = lean_string_append(v___x_4598_, v_val_4537_);
lean_dec(v_val_4537_);
v___x_4600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__2));
v___x_4601_ = lean_string_append(v___x_4599_, v___x_4600_);
v___x_4602_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4601_);
lean_dec_ref(v___x_4601_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4617_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4605_ = v___x_4602_;
v_isShared_4606_ = v_isSharedCheck_4617_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4602_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4617_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4607_; lean_object* v___x_4609_; 
v___x_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4607_, 0, v_a_4603_);
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 0, v___x_4607_);
v___x_4609_ = v___x_4539_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4607_);
v___x_4609_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v___x_4611_; 
if (v_isShared_4535_ == 0)
{
lean_ctor_set(v___x_4534_, 0, v___x_4609_);
v___x_4611_ = v___x_4534_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4609_);
lean_ctor_set(v_reuseFailAlloc_4615_, 1, v_snd_4532_);
v___x_4611_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
lean_object* v___x_4613_; 
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 0, v___x_4611_);
v___x_4613_ = v___x_4605_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v___x_4611_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
}
}
else
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4625_; 
lean_del_object(v___x_4539_);
lean_del_object(v___x_4534_);
lean_dec(v_snd_4532_);
v_a_4618_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4620_ = v___x_4602_;
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4602_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4618_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4628_; 
lean_dec(v_snd_4531_);
if (v_isShared_4535_ == 0)
{
lean_ctor_set(v___x_4534_, 0, v___x_4536_);
v___x_4628_ = v___x_4534_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4536_);
lean_ctor_set(v_reuseFailAlloc_4629_, 1, v_snd_4532_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
v_a_4521_ = v___x_4628_;
goto v___jp_4520_;
}
}
}
}
v___jp_4520_:
{
size_t v___x_4522_; size_t v___x_4523_; 
v___x_4522_ = ((size_t)1ULL);
v___x_4523_ = lean_usize_add(v_i_4517_, v___x_4522_);
v_i_4517_ = v___x_4523_;
v_b_4518_ = v_a_4521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___boxed(lean_object* v_cmd_4632_, lean_object* v_as_4633_, lean_object* v_sz_4634_, lean_object* v_i_4635_, lean_object* v_b_4636_, lean_object* v___y_4637_){
_start:
{
size_t v_sz_boxed_4638_; size_t v_i_boxed_4639_; lean_object* v_res_4640_; 
v_sz_boxed_4638_ = lean_unbox_usize(v_sz_4634_);
lean_dec(v_sz_4634_);
v_i_boxed_4639_ = lean_unbox_usize(v_i_4635_);
lean_dec(v_i_4635_);
v_res_4640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(v_cmd_4632_, v_as_4633_, v_sz_boxed_4638_, v_i_boxed_4639_, v_b_4636_);
lean_dec_ref(v_as_4633_);
lean_dec_ref(v_cmd_4632_);
return v_res_4640_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4641_ = lean_box(0);
v___x_4642_ = lean_unsigned_to_nat(16u);
v___x_4643_ = lean_mk_array(v___x_4642_, v___x_4641_);
return v___x_4643_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1(void){
_start:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v_store_4646_; 
v___x_4644_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0, &l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0);
v___x_4645_ = lean_unsigned_to_nat(0u);
v_store_4646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_store_4646_, 0, v___x_4645_);
lean_ctor_set(v_store_4646_, 1, v___x_4644_);
return v_store_4646_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2(void){
_start:
{
lean_object* v_store_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v_store_4647_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1, &l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1);
v___x_4648_ = lean_box(0);
v___x_4649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4648_);
lean_ctor_set(v___x_4649_, 1, v_store_4647_);
return v___x_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(lean_object* v_cmd_4650_, lean_object* v_entries_4651_){
_start:
{
lean_object* v___x_4653_; size_t v_sz_4654_; size_t v___x_4655_; lean_object* v___x_4656_; 
v___x_4653_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2);
v_sz_4654_ = lean_array_size(v_entries_4651_);
v___x_4655_ = ((size_t)0ULL);
v___x_4656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(v_cmd_4650_, v_entries_4651_, v_sz_4654_, v___x_4655_, v___x_4653_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4671_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4659_ = v___x_4656_;
v_isShared_4660_ = v_isSharedCheck_4671_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v___x_4656_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4671_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v_fst_4661_; 
v_fst_4661_ = lean_ctor_get(v_a_4657_, 0);
if (lean_obj_tag(v_fst_4661_) == 0)
{
lean_object* v_snd_4662_; lean_object* v___x_4663_; lean_object* v___x_4665_; 
v_snd_4662_ = lean_ctor_get(v_a_4657_, 1);
lean_inc(v_snd_4662_);
lean_dec(v_a_4657_);
v___x_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4663_, 0, v_snd_4662_);
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 0, v___x_4663_);
v___x_4665_ = v___x_4659_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4663_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
else
{
lean_object* v_val_4667_; lean_object* v___x_4669_; 
lean_inc_ref(v_fst_4661_);
lean_dec(v_a_4657_);
v_val_4667_ = lean_ctor_get(v_fst_4661_, 0);
lean_inc(v_val_4667_);
lean_dec_ref_known(v_fst_4661_, 1);
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 0, v_val_4667_);
v___x_4669_ = v___x_4659_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_val_4667_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
v_a_4672_ = lean_ctor_get(v___x_4656_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4656_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4656_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___boxed(lean_object* v_cmd_4680_, lean_object* v_entries_4681_, lean_object* v_a_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(v_cmd_4680_, v_entries_4681_);
lean_dec_ref(v_entries_4681_);
lean_dec_ref(v_cmd_4680_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0(lean_object* v_00_u03b2_4684_, lean_object* v_m_4685_, uint8_t v_a_4686_, lean_object* v_b_4687_){
_start:
{
lean_object* v___x_4688_; 
v___x_4688_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(v_m_4685_, v_a_4686_, v_b_4687_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___boxed(lean_object* v_00_u03b2_4689_, lean_object* v_m_4690_, lean_object* v_a_4691_, lean_object* v_b_4692_){
_start:
{
uint8_t v_a_boxed_4693_; lean_object* v_res_4694_; 
v_a_boxed_4693_ = lean_unbox(v_a_4691_);
v_res_4694_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0(v_00_u03b2_4689_, v_m_4690_, v_a_boxed_4693_, v_b_4692_);
return v_res_4694_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0(lean_object* v_00_u03b2_4695_, uint8_t v_a_4696_, lean_object* v_x_4697_){
_start:
{
uint8_t v___x_4698_; 
v___x_4698_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_4696_, v_x_4697_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4699_, lean_object* v_a_4700_, lean_object* v_x_4701_){
_start:
{
uint8_t v_a_boxed_4702_; uint8_t v_res_4703_; lean_object* v_r_4704_; 
v_a_boxed_4702_ = lean_unbox(v_a_4700_);
v_res_4703_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0(v_00_u03b2_4699_, v_a_boxed_4702_, v_x_4701_);
lean_dec(v_x_4701_);
v_r_4704_ = lean_box(v_res_4703_);
return v_r_4704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1(lean_object* v_00_u03b2_4705_, lean_object* v_data_4706_){
_start:
{
lean_object* v___x_4707_; 
v___x_4707_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1___redArg(v_data_4706_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2(lean_object* v_00_u03b2_4708_, uint8_t v_a_4709_, lean_object* v_b_4710_, lean_object* v_x_4711_){
_start:
{
lean_object* v___x_4712_; 
v___x_4712_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_4709_, v_b_4710_, v_x_4711_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4713_, lean_object* v_a_4714_, lean_object* v_b_4715_, lean_object* v_x_4716_){
_start:
{
uint8_t v_a_boxed_4717_; lean_object* v_res_4718_; 
v_a_boxed_4717_ = lean_unbox(v_a_4714_);
v_res_4718_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2(v_00_u03b2_4713_, v_a_boxed_4717_, v_b_4715_, v_x_4716_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4719_, lean_object* v_i_4720_, lean_object* v_source_4721_, lean_object* v_target_4722_){
_start:
{
lean_object* v___x_4723_; 
v___x_4723_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2___redArg(v_i_4720_, v_source_4721_, v_target_4722_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4724_, lean_object* v_x_4725_, lean_object* v_x_4726_){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4___redArg(v_x_4725_, v_x_4726_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext(lean_object* v_cmd_4739_, uint8_t v_paranoid_4740_, uint8_t v_inadvisablyNoSandbox_4741_, lean_object* v_lean_4742_, lean_object* v_lake_4743_, lean_object* v_projectDir_4744_, lean_object* v_moduleStore_4745_){
_start:
{
lean_object* v___y_4748_; lean_object* v___y_4749_; lean_object* v___y_4750_; lean_object* v___y_4751_; lean_object* v___y_4752_; lean_object* v___y_4753_; lean_object* v_whichSandbox_4780_; 
if (v_inadvisablyNoSandbox_4741_ == 0)
{
uint8_t v___x_4856_; 
v___x_4856_ = l_System_Platform_isLinux;
if (v___x_4856_ == 0)
{
lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
lean_dec_ref(v_moduleStore_4745_);
lean_dec_ref(v_projectDir_4744_);
lean_dec_ref(v_lean_4742_);
v___x_4857_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4858_ = lean_string_append(v___x_4857_, v_cmd_4739_);
v___x_4859_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6));
v___x_4860_ = lean_string_append(v___x_4858_, v___x_4859_);
v___x_4861_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4860_);
lean_dec_ref(v___x_4860_);
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4870_; 
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4861_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4864_ = v___x_4861_;
v_isShared_4865_ = v_isSharedCheck_4870_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v___x_4861_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4870_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4866_; lean_object* v___x_4868_; 
v___x_4866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4866_, 0, v_a_4862_);
if (v_isShared_4865_ == 0)
{
lean_ctor_set(v___x_4864_, 0, v___x_4866_);
v___x_4868_ = v___x_4864_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4866_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
else
{
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4878_; 
v_a_4871_ = lean_ctor_get(v___x_4861_, 0);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4861_);
if (v_isSharedCheck_4878_ == 0)
{
v___x_4873_ = v___x_4861_;
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4861_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4876_; 
if (v_isShared_4874_ == 0)
{
v___x_4876_ = v___x_4873_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4871_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
}
else
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___y_4882_; 
v___x_4879_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7));
v___x_4880_ = lean_io_getenv(v___x_4879_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v___x_4918_; 
v___x_4918_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__8));
v___y_4882_ = v___x_4918_;
goto v___jp_4881_;
}
else
{
lean_object* v_val_4919_; 
v_val_4919_ = lean_ctor_get(v___x_4880_, 0);
lean_inc(v_val_4919_);
lean_dec_ref_known(v___x_4880_, 1);
v___y_4882_ = v_val_4919_;
goto v___jp_4881_;
}
v___jp_4881_:
{
lean_object* v___x_4883_; lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4917_; 
lean_inc_ref(v___y_4882_);
v___x_4883_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___y_4882_);
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4886_ = v___x_4883_;
v_isShared_4887_ = v_isSharedCheck_4917_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4883_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4917_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
if (lean_obj_tag(v_a_4884_) == 1)
{
lean_object* v_val_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4895_; 
lean_del_object(v___x_4886_);
lean_dec_ref(v___y_4882_);
v_val_4888_ = lean_ctor_get(v_a_4884_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v_a_4884_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4890_ = v_a_4884_;
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_val_4888_);
lean_dec(v_a_4884_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4893_; 
if (v_isShared_4891_ == 0)
{
v___x_4893_ = v___x_4890_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_val_4888_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
v_whichSandbox_4780_ = v___x_4893_;
goto v___jp_4779_;
}
}
}
else
{
lean_object* v___x_4896_; lean_object* v___x_4897_; 
lean_dec(v_a_4884_);
lean_dec_ref(v_moduleStore_4745_);
lean_dec_ref(v_projectDir_4744_);
lean_dec_ref(v_lean_4742_);
v___x_4896_ = l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError(v_cmd_4739_, v___y_4882_);
lean_dec_ref(v___y_4882_);
v___x_4897_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4896_);
lean_dec_ref(v___x_4896_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4908_; 
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4900_ = v___x_4897_;
v_isShared_4901_ = v_isSharedCheck_4908_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4897_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4908_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4903_; 
if (v_isShared_4887_ == 0)
{
lean_ctor_set(v___x_4886_, 0, v_a_4898_);
v___x_4903_ = v___x_4886_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_a_4898_);
v___x_4903_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
lean_object* v___x_4905_; 
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 0, v___x_4903_);
v___x_4905_ = v___x_4900_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v___x_4903_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
}
else
{
lean_object* v_a_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4916_; 
lean_del_object(v___x_4886_);
v_a_4909_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4916_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4911_ = v___x_4897_;
v_isShared_4912_ = v_isSharedCheck_4916_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_a_4909_);
lean_dec(v___x_4897_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4916_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v___x_4914_; 
if (v_isShared_4912_ == 0)
{
v___x_4914_ = v___x_4911_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4909_);
v___x_4914_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
return v___x_4914_;
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
lean_object* v___x_4920_; lean_object* v___x_4921_; 
v___x_4920_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__9));
v___x_4921_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_4920_);
if (lean_obj_tag(v___x_4921_) == 0)
{
lean_object* v___x_4922_; 
lean_dec_ref_known(v___x_4921_, 1);
v___x_4922_ = lean_box(0);
v_whichSandbox_4780_ = v___x_4922_;
goto v___jp_4779_;
}
else
{
lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4930_; 
lean_dec_ref(v_moduleStore_4745_);
lean_dec_ref(v_projectDir_4744_);
lean_dec_ref(v_lean_4742_);
v_a_4923_ = lean_ctor_get(v___x_4921_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4925_ = v___x_4921_;
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4921_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4928_; 
if (v_isShared_4926_ == 0)
{
v___x_4928_ = v___x_4925_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4923_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
}
v___jp_4747_:
{
lean_object* v___x_4754_; 
v___x_4754_ = lean_io_realpath(v_projectDir_4744_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4770_; 
v_a_4755_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4757_ = v___x_4754_;
v_isShared_4758_ = v_isSharedCheck_4770_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4754_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4770_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v_home_4759_; lean_object* v_lake_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4768_; 
v_home_4759_ = lean_ctor_get(v_lake_4743_, 0);
v_lake_4760_ = lean_ctor_get(v_lake_4743_, 5);
v___x_4761_ = lean_box(0);
v___x_4762_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_4763_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
v___x_4764_ = lean_box(1);
lean_inc_ref(v_home_4759_);
lean_inc_ref(v_lake_4760_);
v___x_4765_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_4765_, 0, v_a_4755_);
lean_ctor_set(v___x_4765_, 1, v___x_4761_);
lean_ctor_set(v___x_4765_, 2, v___x_4761_);
lean_ctor_set(v___x_4765_, 3, v___x_4762_);
lean_ctor_set(v___x_4765_, 4, v___x_4762_);
lean_ctor_set(v___x_4765_, 5, v___x_4762_);
lean_ctor_set(v___x_4765_, 6, v___y_4752_);
lean_ctor_set(v___x_4765_, 7, v___x_4763_);
lean_ctor_set(v___x_4765_, 8, v___x_4763_);
lean_ctor_set(v___x_4765_, 9, v___y_4749_);
lean_ctor_set(v___x_4765_, 10, v_lake_4760_);
lean_ctor_set(v___x_4765_, 11, v_home_4759_);
lean_ctor_set(v___x_4765_, 12, v___y_4748_);
lean_ctor_set(v___x_4765_, 13, v___y_4750_);
lean_ctor_set(v___x_4765_, 14, v___y_4751_);
lean_ctor_set(v___x_4765_, 15, v___x_4764_);
lean_ctor_set(v___x_4765_, 16, v___y_4753_);
lean_ctor_set(v___x_4765_, 17, v_moduleStore_4745_);
v___x_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4765_);
if (v_isShared_4758_ == 0)
{
lean_ctor_set(v___x_4757_, 0, v___x_4766_);
v___x_4768_ = v___x_4757_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v___x_4766_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4778_; 
lean_dec_ref(v___y_4753_);
lean_dec_ref(v___y_4752_);
lean_dec_ref(v___y_4751_);
lean_dec_ref(v___y_4750_);
lean_dec(v___y_4749_);
lean_dec_ref(v___y_4748_);
lean_dec_ref(v_moduleStore_4745_);
v_a_4771_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4773_ = v___x_4754_;
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4754_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4776_; 
if (v_isShared_4774_ == 0)
{
v___x_4776_ = v___x_4773_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
v___jp_4779_:
{
lean_object* v_sysroot_4781_; lean_object* v_binDir_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v_whichLean4Export_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v_whichLeanChecker_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4855_; 
v_sysroot_4781_ = lean_ctor_get(v_lean_4742_, 0);
lean_inc_ref(v_sysroot_4781_);
v_binDir_4782_ = lean_ctor_get(v_lean_4742_, 6);
v___x_4783_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0));
lean_inc_ref_n(v_binDir_4782_, 2);
v___x_4784_ = l_System_FilePath_join(v_binDir_4782_, v___x_4783_);
v___x_4785_ = l_System_FilePath_exeExtension;
v_whichLean4Export_4786_ = l_System_FilePath_addExtension(v___x_4784_, v___x_4785_);
v___x_4787_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1));
v___x_4788_ = l_System_FilePath_join(v_binDir_4782_, v___x_4787_);
v_whichLeanChecker_4789_ = l_System_FilePath_addExtension(v___x_4788_, v___x_4785_);
v___x_4790_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2));
v___x_4791_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4790_);
v_a_4792_ = lean_ctor_get(v___x_4791_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4794_ = v___x_4791_;
v_isShared_4795_ = v_isSharedCheck_4855_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4791_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4855_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
if (lean_obj_tag(v_a_4792_) == 1)
{
lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4830_; 
lean_dec_ref_known(v_a_4792_, 1);
lean_del_object(v___x_4794_);
v___x_4796_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__4));
v___x_4797_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4796_);
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4800_ = v___x_4797_;
v_isShared_4801_ = v_isSharedCheck_4830_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4797_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4830_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
if (lean_obj_tag(v_a_4798_) == 1)
{
lean_del_object(v___x_4800_);
if (v_paranoid_4740_ == 0)
{
lean_object* v_val_4802_; lean_object* v___x_4803_; 
lean_dec_ref(v_lean_4742_);
v_val_4802_ = lean_ctor_get(v_a_4798_, 0);
lean_inc(v_val_4802_);
lean_dec_ref_known(v_a_4798_, 1);
v___x_4803_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3));
v___y_4748_ = v_whichLean4Export_4786_;
v___y_4749_ = v_whichSandbox_4780_;
v___y_4750_ = v_whichLeanChecker_4789_;
v___y_4751_ = v_val_4802_;
v___y_4752_ = v_sysroot_4781_;
v___y_4753_ = v___x_4803_;
goto v___jp_4747_;
}
else
{
lean_object* v_val_4804_; lean_object* v___x_4805_; 
v_val_4804_ = lean_ctor_get(v_a_4798_, 0);
lean_inc(v_val_4804_);
lean_dec_ref_known(v_a_4798_, 1);
v___x_4805_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels(v_lean_4742_);
v___y_4748_ = v_whichLean4Export_4786_;
v___y_4749_ = v_whichSandbox_4780_;
v___y_4750_ = v_whichLeanChecker_4789_;
v___y_4751_ = v_val_4804_;
v___y_4752_ = v_sysroot_4781_;
v___y_4753_ = v___x_4805_;
goto v___jp_4747_;
}
}
else
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
lean_dec(v_a_4798_);
lean_dec_ref(v_whichLeanChecker_4789_);
lean_dec_ref(v_whichLean4Export_4786_);
lean_dec_ref(v_sysroot_4781_);
lean_dec(v_whichSandbox_4780_);
lean_dec_ref(v_moduleStore_4745_);
lean_dec_ref(v_projectDir_4744_);
lean_dec_ref(v_lean_4742_);
v___x_4806_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4807_ = lean_string_append(v___x_4806_, v_cmd_4739_);
v___x_4808_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4));
v___x_4809_ = lean_string_append(v___x_4807_, v___x_4808_);
v___x_4810_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4809_);
lean_dec_ref(v___x_4809_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4821_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4813_ = v___x_4810_;
v_isShared_4814_ = v_isSharedCheck_4821_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4810_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4821_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 0, v_a_4811_);
v___x_4816_ = v___x_4800_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_a_4811_);
v___x_4816_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
lean_object* v___x_4818_; 
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 0, v___x_4816_);
v___x_4818_ = v___x_4813_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v___x_4816_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
lean_del_object(v___x_4800_);
v_a_4822_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4810_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4810_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
}
}
else
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
lean_dec(v_a_4792_);
lean_dec_ref(v_whichLeanChecker_4789_);
lean_dec_ref(v_whichLean4Export_4786_);
lean_dec_ref(v_sysroot_4781_);
lean_dec(v_whichSandbox_4780_);
lean_dec_ref(v_moduleStore_4745_);
lean_dec_ref(v_projectDir_4744_);
lean_dec_ref(v_lean_4742_);
v___x_4831_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4832_ = lean_string_append(v___x_4831_, v_cmd_4739_);
v___x_4833_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5));
v___x_4834_ = lean_string_append(v___x_4832_, v___x_4833_);
v___x_4835_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4834_);
lean_dec_ref(v___x_4834_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4846_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4838_ = v___x_4835_;
v_isShared_4839_ = v_isSharedCheck_4846_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_a_4836_);
lean_dec(v___x_4835_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4846_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v___x_4841_; 
if (v_isShared_4795_ == 0)
{
lean_ctor_set(v___x_4794_, 0, v_a_4836_);
v___x_4841_ = v___x_4794_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4836_);
v___x_4841_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
lean_object* v___x_4843_; 
if (v_isShared_4839_ == 0)
{
lean_ctor_set(v___x_4838_, 0, v___x_4841_);
v___x_4843_ = v___x_4838_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v___x_4841_);
v___x_4843_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
return v___x_4843_;
}
}
}
}
else
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
lean_del_object(v___x_4794_);
v_a_4847_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4835_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4835_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4847_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___boxed(lean_object* v_cmd_4931_, lean_object* v_paranoid_4932_, lean_object* v_inadvisablyNoSandbox_4933_, lean_object* v_lean_4934_, lean_object* v_lake_4935_, lean_object* v_projectDir_4936_, lean_object* v_moduleStore_4937_, lean_object* v_a_4938_){
_start:
{
uint8_t v_paranoid_boxed_4939_; uint8_t v_inadvisablyNoSandbox_boxed_4940_; lean_object* v_res_4941_; 
v_paranoid_boxed_4939_ = lean_unbox(v_paranoid_4932_);
v_inadvisablyNoSandbox_boxed_4940_ = lean_unbox(v_inadvisablyNoSandbox_4933_);
v_res_4941_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v_cmd_4931_, v_paranoid_boxed_4939_, v_inadvisablyNoSandbox_boxed_4940_, v_lean_4934_, v_lake_4935_, v_projectDir_4936_, v_moduleStore_4937_);
lean_dec_ref(v_lake_4935_);
lean_dec_ref(v_cmd_4931_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(lean_object* v_init_4948_, lean_object* v_x_4949_){
_start:
{
lean_object* v_d_4952_; 
if (lean_obj_tag(v_x_4949_) == 0)
{
lean_object* v_k_4955_; lean_object* v_v_4956_; lean_object* v_l_4957_; lean_object* v_r_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v_k_4955_ = lean_ctor_get(v_x_4949_, 1);
v_v_4956_ = lean_ctor_get(v_x_4949_, 2);
v_l_4957_ = lean_ctor_get(v_x_4949_, 3);
v_r_4958_ = lean_ctor_get(v_x_4949_, 4);
v___x_4959_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
v___x_4960_ = lean_box(0);
v___x_4961_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_4962_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_4948_, v_l_4957_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_a_4963_);
lean_dec_ref_known(v___x_4962_, 1);
if (lean_obj_tag(v_a_4963_) == 0)
{
lean_object* v_a_4964_; 
v_a_4964_ = lean_ctor_get(v_a_4963_, 0);
lean_inc(v_a_4964_);
lean_dec_ref_known(v_a_4963_, 1);
v_d_4952_ = v_a_4964_;
goto v___jp_4951_;
}
else
{
lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_5001_; 
v_isSharedCheck_5001_ = !lean_is_exclusive(v_a_4963_);
if (v_isSharedCheck_5001_ == 0)
{
lean_object* v_unused_5002_; 
v_unused_5002_ = lean_ctor_get(v_a_4963_, 0);
lean_dec(v_unused_5002_);
v___x_4966_ = v_a_4963_;
v_isShared_4967_ = v_isSharedCheck_5001_;
goto v_resetjp_4965_;
}
else
{
lean_dec(v_a_4963_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_5001_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v_a_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_5000_; 
v___x_4968_ = lean_unsigned_to_nat(0u);
v___x_4969_ = lean_array_get_borrowed(v___x_4959_, v_v_4956_, v___x_4968_);
lean_inc(v___x_4969_);
v___x_4970_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4969_);
v_a_4971_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4973_ = v___x_4970_;
v_isShared_4974_ = v_isSharedCheck_5000_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_a_4971_);
lean_dec(v___x_4970_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_5000_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
if (lean_obj_tag(v_a_4971_) == 0)
{
lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4975_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1));
v___x_4976_ = lean_string_append(v___x_4975_, v_k_4955_);
v___x_4977_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2));
v___x_4978_ = lean_string_append(v___x_4976_, v___x_4977_);
v___x_4979_ = lean_string_append(v___x_4978_, v___x_4969_);
v___x_4980_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v___x_4981_ = lean_string_append(v___x_4979_, v___x_4980_);
v___x_4982_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4981_);
lean_dec_ref(v___x_4981_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4985_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
lean_inc(v_a_4983_);
lean_dec_ref_known(v___x_4982_, 1);
if (v_isShared_4974_ == 0)
{
lean_ctor_set(v___x_4973_, 0, v_a_4983_);
v___x_4985_ = v___x_4973_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_a_4983_);
v___x_4985_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
lean_object* v___x_4987_; 
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 0, v___x_4985_);
v___x_4987_ = v___x_4966_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4985_);
v___x_4987_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
lean_object* v___x_4988_; 
v___x_4988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4987_);
lean_ctor_set(v___x_4988_, 1, v___x_4960_);
v_d_4952_ = v___x_4988_;
goto v___jp_4951_;
}
}
}
else
{
lean_object* v_a_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_4998_; 
lean_del_object(v___x_4973_);
lean_del_object(v___x_4966_);
v_a_4991_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4993_ = v___x_4982_;
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_a_4991_);
lean_dec(v___x_4982_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v___x_4996_; 
if (v_isShared_4994_ == 0)
{
v___x_4996_ = v___x_4993_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_a_4991_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
return v___x_4996_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_4971_, 1);
lean_del_object(v___x_4973_);
lean_del_object(v___x_4966_);
v_init_4948_ = v___x_4961_;
v_x_4949_ = v_r_4958_;
goto _start;
}
}
}
}
}
else
{
return v___x_4962_;
}
}
else
{
lean_object* v___x_5003_; lean_object* v___x_5004_; 
v___x_5003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5003_, 0, v_init_4948_);
v___x_5004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5004_, 0, v___x_5003_);
return v___x_5004_;
}
v___jp_4951_:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4953_, 0, v_d_4952_);
v___x_4954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4954_, 0, v___x_4953_);
return v___x_4954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___boxed(lean_object* v_init_5005_, lean_object* v_x_5006_, lean_object* v___y_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_5005_, v_x_5006_);
lean_dec(v_x_5006_);
return v_res_5008_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(lean_object* v_k_5009_, lean_object* v_v_5010_, lean_object* v_t_5011_){
_start:
{
if (lean_obj_tag(v_t_5011_) == 0)
{
lean_object* v_size_5012_; lean_object* v_k_5013_; lean_object* v_v_5014_; lean_object* v_l_5015_; lean_object* v_r_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5296_; 
v_size_5012_ = lean_ctor_get(v_t_5011_, 0);
v_k_5013_ = lean_ctor_get(v_t_5011_, 1);
v_v_5014_ = lean_ctor_get(v_t_5011_, 2);
v_l_5015_ = lean_ctor_get(v_t_5011_, 3);
v_r_5016_ = lean_ctor_get(v_t_5011_, 4);
v_isSharedCheck_5296_ = !lean_is_exclusive(v_t_5011_);
if (v_isSharedCheck_5296_ == 0)
{
v___x_5018_ = v_t_5011_;
v_isShared_5019_ = v_isSharedCheck_5296_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_r_5016_);
lean_inc(v_l_5015_);
lean_inc(v_v_5014_);
lean_inc(v_k_5013_);
lean_inc(v_size_5012_);
lean_dec(v_t_5011_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5296_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
uint8_t v___x_5020_; 
v___x_5020_ = lean_string_compare(v_k_5009_, v_k_5013_);
switch(v___x_5020_)
{
case 0:
{
lean_object* v_impl_5021_; lean_object* v___x_5022_; 
lean_dec(v_size_5012_);
v_impl_5021_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_5009_, v_v_5010_, v_l_5015_);
v___x_5022_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5016_) == 0)
{
lean_object* v_size_5023_; lean_object* v_size_5024_; lean_object* v_k_5025_; lean_object* v_v_5026_; lean_object* v_l_5027_; lean_object* v_r_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; uint8_t v___x_5031_; 
v_size_5023_ = lean_ctor_get(v_r_5016_, 0);
v_size_5024_ = lean_ctor_get(v_impl_5021_, 0);
v_k_5025_ = lean_ctor_get(v_impl_5021_, 1);
v_v_5026_ = lean_ctor_get(v_impl_5021_, 2);
v_l_5027_ = lean_ctor_get(v_impl_5021_, 3);
v_r_5028_ = lean_ctor_get(v_impl_5021_, 4);
lean_inc(v_r_5028_);
v___x_5029_ = lean_unsigned_to_nat(3u);
v___x_5030_ = lean_nat_mul(v___x_5029_, v_size_5023_);
v___x_5031_ = lean_nat_dec_lt(v___x_5030_, v_size_5024_);
lean_dec(v___x_5030_);
if (v___x_5031_ == 0)
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5035_; 
lean_dec(v_r_5028_);
v___x_5032_ = lean_nat_add(v___x_5022_, v_size_5024_);
v___x_5033_ = lean_nat_add(v___x_5032_, v_size_5023_);
lean_dec(v___x_5032_);
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 3, v_impl_5021_);
lean_ctor_set(v___x_5018_, 0, v___x_5033_);
v___x_5035_ = v___x_5018_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v___x_5033_);
lean_ctor_set(v_reuseFailAlloc_5036_, 1, v_k_5013_);
lean_ctor_set(v_reuseFailAlloc_5036_, 2, v_v_5014_);
lean_ctor_set(v_reuseFailAlloc_5036_, 3, v_impl_5021_);
lean_ctor_set(v_reuseFailAlloc_5036_, 4, v_r_5016_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
return v___x_5035_;
}
}
else
{
lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5102_; 
lean_inc(v_l_5027_);
lean_inc(v_v_5026_);
lean_inc(v_k_5025_);
lean_inc(v_size_5024_);
v_isSharedCheck_5102_ = !lean_is_exclusive(v_impl_5021_);
if (v_isSharedCheck_5102_ == 0)
{
lean_object* v_unused_5103_; lean_object* v_unused_5104_; lean_object* v_unused_5105_; lean_object* v_unused_5106_; lean_object* v_unused_5107_; 
v_unused_5103_ = lean_ctor_get(v_impl_5021_, 4);
lean_dec(v_unused_5103_);
v_unused_5104_ = lean_ctor_get(v_impl_5021_, 3);
lean_dec(v_unused_5104_);
v_unused_5105_ = lean_ctor_get(v_impl_5021_, 2);
lean_dec(v_unused_5105_);
v_unused_5106_ = lean_ctor_get(v_impl_5021_, 1);
lean_dec(v_unused_5106_);
v_unused_5107_ = lean_ctor_get(v_impl_5021_, 0);
lean_dec(v_unused_5107_);
v___x_5038_ = v_impl_5021_;
v_isShared_5039_ = v_isSharedCheck_5102_;
goto v_resetjp_5037_;
}
else
{
lean_dec(v_impl_5021_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5102_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v_size_5040_; lean_object* v_size_5041_; lean_object* v_k_5042_; lean_object* v_v_5043_; lean_object* v_l_5044_; lean_object* v_r_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; uint8_t v___x_5048_; 
v_size_5040_ = lean_ctor_get(v_l_5027_, 0);
v_size_5041_ = lean_ctor_get(v_r_5028_, 0);
v_k_5042_ = lean_ctor_get(v_r_5028_, 1);
v_v_5043_ = lean_ctor_get(v_r_5028_, 2);
v_l_5044_ = lean_ctor_get(v_r_5028_, 3);
v_r_5045_ = lean_ctor_get(v_r_5028_, 4);
v___x_5046_ = lean_unsigned_to_nat(2u);
v___x_5047_ = lean_nat_mul(v___x_5046_, v_size_5040_);
v___x_5048_ = lean_nat_dec_lt(v_size_5041_, v___x_5047_);
lean_dec(v___x_5047_);
if (v___x_5048_ == 0)
{
lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5077_; 
lean_inc(v_r_5045_);
lean_inc(v_l_5044_);
lean_inc(v_v_5043_);
lean_inc(v_k_5042_);
v_isSharedCheck_5077_ = !lean_is_exclusive(v_r_5028_);
if (v_isSharedCheck_5077_ == 0)
{
lean_object* v_unused_5078_; lean_object* v_unused_5079_; lean_object* v_unused_5080_; lean_object* v_unused_5081_; lean_object* v_unused_5082_; 
v_unused_5078_ = lean_ctor_get(v_r_5028_, 4);
lean_dec(v_unused_5078_);
v_unused_5079_ = lean_ctor_get(v_r_5028_, 3);
lean_dec(v_unused_5079_);
v_unused_5080_ = lean_ctor_get(v_r_5028_, 2);
lean_dec(v_unused_5080_);
v_unused_5081_ = lean_ctor_get(v_r_5028_, 1);
lean_dec(v_unused_5081_);
v_unused_5082_ = lean_ctor_get(v_r_5028_, 0);
lean_dec(v_unused_5082_);
v___x_5050_ = v_r_5028_;
v_isShared_5051_ = v_isSharedCheck_5077_;
goto v_resetjp_5049_;
}
else
{
lean_dec(v_r_5028_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5077_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___y_5055_; lean_object* v___y_5056_; lean_object* v___y_5057_; lean_object* v___x_5065_; lean_object* v___y_5067_; 
v___x_5052_ = lean_nat_add(v___x_5022_, v_size_5024_);
lean_dec(v_size_5024_);
v___x_5053_ = lean_nat_add(v___x_5052_, v_size_5023_);
lean_dec(v___x_5052_);
v___x_5065_ = lean_nat_add(v___x_5022_, v_size_5040_);
if (lean_obj_tag(v_l_5044_) == 0)
{
lean_object* v_size_5075_; 
v_size_5075_ = lean_ctor_get(v_l_5044_, 0);
lean_inc(v_size_5075_);
v___y_5067_ = v_size_5075_;
goto v___jp_5066_;
}
else
{
lean_object* v___x_5076_; 
v___x_5076_ = lean_unsigned_to_nat(0u);
v___y_5067_ = v___x_5076_;
goto v___jp_5066_;
}
v___jp_5054_:
{
lean_object* v___x_5058_; lean_object* v___x_5060_; 
v___x_5058_ = lean_nat_add(v___y_5056_, v___y_5057_);
lean_dec(v___y_5057_);
lean_dec(v___y_5056_);
if (v_isShared_5051_ == 0)
{
lean_ctor_set(v___x_5050_, 4, v_r_5016_);
lean_ctor_set(v___x_5050_, 3, v_r_5045_);
lean_ctor_set(v___x_5050_, 2, v_v_5014_);
lean_ctor_set(v___x_5050_, 1, v_k_5013_);
lean_ctor_set(v___x_5050_, 0, v___x_5058_);
v___x_5060_ = v___x_5050_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v___x_5058_);
lean_ctor_set(v_reuseFailAlloc_5064_, 1, v_k_5013_);
lean_ctor_set(v_reuseFailAlloc_5064_, 2, v_v_5014_);
lean_ctor_set(v_reuseFailAlloc_5064_, 3, v_r_5045_);
lean_ctor_set(v_reuseFailAlloc_5064_, 4, v_r_5016_);
v___x_5060_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
lean_object* v___x_5062_; 
if (v_isShared_5039_ == 0)
{
lean_ctor_set(v___x_5038_, 4, v___x_5060_);
lean_ctor_set(v___x_5038_, 3, v___y_5055_);
lean_ctor_set(v___x_5038_, 2, v_v_5043_);
lean_ctor_set(v___x_5038_, 1, v_k_5042_);
lean_ctor_set(v___x_5038_, 0, v___x_5053_);
v___x_5062_ = v___x_5038_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5053_);
lean_ctor_set(v_reuseFailAlloc_5063_, 1, v_k_5042_);
lean_ctor_set(v_reuseFailAlloc_5063_, 2, v_v_5043_);
lean_ctor_set(v_reuseFailAlloc_5063_, 3, v___y_5055_);
lean_ctor_set(v_reuseFailAlloc_5063_, 4, v___x_5060_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
return v___x_5062_;
}
}
}
v___jp_5066_:
{
lean_object* v___x_5068_; lean_object* v___x_5070_; 
v___x_5068_ = lean_nat_add(v___x_5065_, v___y_5067_);
lean_dec(v___y_5067_);
lean_dec(v___x_5065_);
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 4, v_l_5044_);
lean_ctor_set(v___x_5018_, 3, v_l_5027_);
lean_ctor_set(v___x_5018_, 2, v_v_5026_);
lean_ctor_set(v___x_5018_, 1, v_k_5025_);
lean_ctor_set(v___x_5018_, 0, v___x_5068_);
v___x_5070_ = v___x_5018_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v___x_5068_);
lean_ctor_set(v_reuseFailAlloc_5074_, 1, v_k_5025_);
lean_ctor_set(v_reuseFailAlloc_5074_, 2, v_v_5026_);
lean_ctor_set(v_reuseFailAlloc_5074_, 3, v_l_5027_);
lean_ctor_set(v_reuseFailAlloc_5074_, 4, v_l_5044_);
v___x_5070_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
lean_object* v___x_5071_; 
v___x_5071_ = lean_nat_add(v___x_5022_, v_size_5023_);
if (lean_obj_tag(v_r_5045_) == 0)
{
lean_object* v_size_5072_; 
v_size_5072_ = lean_ctor_get(v_r_5045_, 0);
lean_inc(v_size_5072_);
v___y_5055_ = v___x_5070_;
v___y_5056_ = v___x_5071_;
v___y_5057_ = v_size_5072_;
goto v___jp_5054_;
}
else
{
lean_object* v___x_5073_; 
v___x_5073_ = lean_unsigned_to_nat(0u);
v___y_5055_ = v___x_5070_;
v___y_5056_ = v___x_5071_;
v___y_5057_ = v___x_5073_;
goto v___jp_5054_;
}
}
}
}
}
else
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5088_; 
lean_del_object(v___x_5018_);
v___x_5083_ = lean_nat_add(v___x_5022_, v_size_5024_);
lean_dec(v_size_5024_);
v___x_5084_ = lean_nat_add(v___x_5083_, v_size_5023_);
lean_dec(v___x_5083_);
v___x_5085_ = lean_nat_add(v___x_5022_, v_size_5023_);
v___x_5086_ = lean_nat_add(v___x_5085_, v_size_5041_);
lean_dec(v___x_5085_);
lean_inc_ref(v_r_5016_);
if (v_isShared_5039_ == 0)
{
lean_ctor_set(v___x_5038_, 4, v_r_5016_);
lean_ctor_set(v___x_5038_, 3, v_r_5028_);
lean_ctor_set(v___x_5038_, 2, v_v_5014_);
lean_ctor_set(v___x_5038_, 1, v_k_5013_);
lean_ctor_set(v___x_5038_, 0, v___x_5086_);
v___x_5088_ = v___x_5038_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v___x_5086_);
lean_ctor_set(v_reuseFailAlloc_5101_, 1, v_k_5013_);
lean_ctor_set(v_reuseFailAlloc_5101_, 2, v_v_5014_);
lean_ctor_set(v_reuseFailAlloc_5101_, 3, v_r_5028_);
lean_ctor_set(v_reuseFailAlloc_5101_, 4, v_r_5016_);
v___x_5088_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5095_; 
v_isSharedCheck_5095_ = !lean_is_exclusive(v_r_5016_);
if (v_isSharedCheck_5095_ == 0)
{
lean_object* v_unused_5096_; lean_object* v_unused_5097_; lean_object* v_unused_5098_; lean_object* v_unused_5099_; lean_object* v_unused_5100_; 
v_unused_5096_ = lean_ctor_get(v_r_5016_, 4);
lean_dec(v_unused_5096_);
v_unused_5097_ = lean_ctor_get(v_r_5016_, 3);
lean_dec(v_unused_5097_);
v_unused_5098_ = lean_ctor_get(v_r_5016_, 2);
lean_dec(v_unused_5098_);
v_unused_5099_ = lean_ctor_get(v_r_5016_, 1);
lean_dec(v_unused_5099_);
v_unused_5100_ = lean_ctor_get(v_r_5016_, 0);
lean_dec(v_unused_5100_);
v___x_5090_ = v_r_5016_;
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
else
{
lean_dec(v_r_5016_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5093_; 
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 4, v___x_5088_);
lean_ctor_set(v___x_5090_, 3, v_l_5027_);
lean_ctor_set(v___x_5090_, 2, v_v_5026_);
lean_ctor_set(v___x_5090_, 1, v_k_5025_);
lean_ctor_set(v___x_5090_, 0, v___x_5084_);
v___x_5093_ = v___x_5090_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v___x_5084_);
lean_ctor_set(v_reuseFailAlloc_5094_, 1, v_k_5025_);
lean_ctor_set(v_reuseFailAlloc_5094_, 2, v_v_5026_);
lean_ctor_set(v_reuseFailAlloc_5094_, 3, v_l_5027_);
lean_ctor_set(v_reuseFailAlloc_5094_, 4, v___x_5088_);
v___x_5093_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
return v___x_5093_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5108_; 
v_l_5108_ = lean_ctor_get(v_impl_5021_, 3);
if (lean_obj_tag(v_l_5108_) == 0)
{
lean_object* v_r_5109_; lean_object* v_k_5110_; lean_object* v_v_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5122_; 
lean_inc_ref(v_l_5108_);
v_r_5109_ = lean_ctor_get(v_impl_5021_, 4);
v_k_5110_ = lean_ctor_get(v_impl_5021_, 1);
v_v_5111_ = lean_ctor_get(v_impl_5021_, 2);
v_isSharedCheck_5122_ = !lean_is_exclusive(v_impl_5021_);
if (v_isSharedCheck_5122_ == 0)
{
lean_object* v_unused_5123_; lean_object* v_unused_5124_; 
v_unused_5123_ = lean_ctor_get(v_impl_5021_, 3);
lean_dec(v_unused_5123_);
v_unused_5124_ = lean_ctor_get(v_impl_5021_, 0);
lean_dec(v_unused_5124_);
v___x_5113_ = v_impl_5021_;
v_isShared_5114_ = v_isSharedCheck_5122_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_r_5109_);
lean_inc(v_v_5111_);
lean_inc(v_k_5110_);
lean_dec(v_impl_5021_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5122_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5115_; lean_object* v___x_5117_; 
v___x_5115_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5109_);
if (v_isShared_5114_ == 0)
{
lean_ctor_set(v___x_5113_, 3, v_r_5109_);
lean_ctor_set(v___x_5113_, 2, v_v_5014_);
lean_ctor_set(v___x_5113_, 1, v_k_5013_);
lean_ctor_set(v___x_5113_, 0, v___x_5022_);
v___x_5117_ = v___x_5113_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v___x_5022_);
lean_ctor_set(v_reuseFailAlloc_5121_, 1, v_k_5013_);
lean_ctor_set(v_reuseFailAlloc_5121_, 2, v_v_5014_);
lean_ctor_set(v_reuseFailAlloc_5121_, 3, v_r_5109_);
lean_ctor_set(v_reuseFailAlloc_5121_, 4, v_r_5109_);
v___x_5117_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
lean_object* v___x_5119_; 
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 4, v___x_5117_);
lean_ctor_set(v___x_5018_, 3, v_l_5108_);
lean_ctor_set(v___x_5018_, 2, v_v_5111_);
lean_ctor_set(v___x_5018_, 1, v_k_5110_);
lean_ctor_set(v___x_5018_, 0, v___x_5115_);
v___x_5119_ = v___x_5018_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v___x_5115_);
lean_ctor_set(v_reuseFailAlloc_5120_, 1, v_k_5110_);
lean_ctor_set(v_reuseFailAlloc_5120_, 2, v_v_5111_);
lean_ctor_set(v_reuseFailAlloc_5120_, 3, v_l_5108_);
lean_ctor_set(v_reuseFailAlloc_5120_, 4, v___x_5117_);
v___x_5119_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
return v___x_5119_;
}
}
}
}
else
{
lean_object* v_r_5125_; 
v_r_5125_ = lean_ctor_get(v_impl_5021_, 4);
lean_inc(v_r_5125_);
if (lean_obj_tag(v_r_5125_) == 0)
{
lean_object* v_k_5126_; lean_object* v_v_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5150_; 
lean_inc(v_l_5108_);
v_k_5126_ = lean_ctor_get(v_impl_5021_, 1);
v_v_5127_ = lean_ctor_get(v_impl_5021_, 2);
v_isSharedCheck_5150_ = !lean_is_exclusive(v_impl_5021_);
if (v_isSharedCheck_5150_ == 0)
{
lean_object* v_unused_5151_; lean_object* v_unused_5152_; lean_object* v_unused_5153_; 
v_unused_5151_ = lean_ctor_get(v_impl_5021_, 4);
lean_dec(v_unused_5151_);
v_unused_5152_ = lean_ctor_get(v_impl_5021_, 3);
lean_dec(v_unused_5152_);
v_unused_5153_ = lean_ctor_get(v_impl_5021_, 0);
lean_dec(v_unused_5153_);
v___x_5129_ = v_impl_5021_;
v_isShared_5130_ = v_isSharedCheck_5150_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_v_5127_);
lean_inc(v_k_5126_);
lean_dec(v_impl_5021_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5150_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v_k_5131_; lean_object* v_v_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5146_; 
v_k_5131_ = lean_ctor_get(v_r_5125_, 1);
v_v_5132_ = lean_ctor_get(v_r_5125_, 2);
v_isSharedCheck_5146_ = !lean_is_exclusive(v_r_5125_);
if (v_isSharedCheck_5146_ == 0)
{
lean_object* v_unused_5147_; lean_object* v_unused_5148_; lean_object* v_unused_5149_; 
v_unused_5147_ = lean_ctor_get(v_r_5125_, 4);
lean_dec(v_unused_5147_);
v_unused_5148_ = lean_ctor_get(v_r_5125_, 3);
lean_dec(v_unused_5148_);
v_unused_5149_ = lean_ctor_get(v_r_5125_, 0);
lean_dec(v_unused_5149_);
v___x_5134_ = v_r_5125_;
v_isShared_5135_ = v_isSharedCheck_5146_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_v_5132_);
lean_inc(v_k_5131_);
lean_dec(v_r_5125_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5146_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5136_; lean_object* v___x_5138_; 
v___x_5136_ = lean_unsigned_to_nat(3u);
if (v_isShared_5135_ == 0)
{
lean_ctor_set(v___x_5134_, 4, v_l_5108_);
lean_ctor_set(v___x_5134_, 3, v_l_5108_);
lean_ctor_set(v___x_5134_, 2, v_v_5127_);
lean_ctor_set(v___x_5134_, 1, v_k_5126_);
lean_ctor_set(v___x_5134_, 0, v___x_5022_);
v___x_5138_ = v___x_5134_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5145_; 
v_reuseFailAlloc_5145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5145_, 0, v___x_5022_);
lean_ctor_set(v_reuseFailAlloc_5145_, 1, v_k_5126_);
lean_ctor_set(v_reuseFailAlloc_5145_, 2, v_v_5127_);
lean_ctor_set(v_reuseFailAlloc_5145_, 3, v_l_5108_);
lean_ctor_set(v_reuseFailAlloc_5145_, 4, v_l_5108_);
v___x_5138_ = v_reuseFailAlloc_5145_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
lean_object* v___x_5140_; 
if (v_isShared_5130_ == 0)
{
lean_ctor_set(v___x_5129_, 4, v_l_5108_);
lean_ctor_set(v___x_5129_, 2, v_v_5014_);
lean_ctor_set(v___x_5129_, 1, v_k_5013_);
lean_ctor_set(v___x_5129_, 0, v___x_5022_);
v___x_5140_ = v___x_5129_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v___x_5022_);
lean_ctor_set(v_reuseFailAlloc_5144_, 1, v_k_5013_);
lean_ctor_set(v_reuseFailAlloc_5144_, 2, v_v_5014_);
lean_ctor_set(v_reuseFailAlloc_5144_, 3, v_l_5108_);
lean_ctor_set(v_reuseFailAlloc_5144_, 4, v_l_5108_);
v___x_5140_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
lean_object* v___x_5142_; 
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 4, v___x_5140_);
lean_ctor_set(v___x_5018_, 3, v___x_5138_);
lean_ctor_set(v___x_5018_, 2, v_v_5132_);
lean_ctor_set(v___x_5018_, 1, v_k_5131_);
lean_ctor_set(v___x_5018_, 0, v___x_5136_);
v___x_5142_ = v___x_5018_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v___x_5136_);
lean_ctor_set(v_reuseFailAlloc_5143_, 1, v_k_5131_);
lean_ctor_set(v_reuseFailAlloc_5143_, 2, v_v_5132_);
lean_ctor_set(v_reuseFailAlloc_5143_, 3, v___x_5138_);
lean_ctor_set(v_reuseFailAlloc_5143_, 4, v___x_5140_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
}
}
else
{
lean_object* v___x_5154_; lean_object* v___x_5156_; 
v___x_5154_ = lean_unsigned_to_nat(2u);
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 4, v_r_5125_);
lean_ctor_set(v___x_5018_, 3, v_impl_5021_);
lean_ctor_set(v___x_5018_, 0, v___x_5154_);
v___x_5156_ = v___x_5018_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v___x_5154_);
lean_ctor_set(v_reuseFailAlloc_5157_, 1, v_k_5013_);
lean_ctor_set(v_reuseFailAlloc_5157_, 2, v_v_5014_);
lean_ctor_set(v_reuseFailAlloc_5157_, 3, v_impl_5021_);
lean_ctor_set(v_reuseFailAlloc_5157_, 4, v_r_5125_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
}
}
case 1:
{
lean_object* v___x_5159_; 
lean_dec(v_v_5014_);
lean_dec(v_k_5013_);
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 2, v_v_5010_);
lean_ctor_set(v___x_5018_, 1, v_k_5009_);
v___x_5159_ = v___x_5018_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v_size_5012_);
lean_ctor_set(v_reuseFailAlloc_5160_, 1, v_k_5009_);
lean_ctor_set(v_reuseFailAlloc_5160_, 2, v_v_5010_);
lean_ctor_set(v_reuseFailAlloc_5160_, 3, v_l_5015_);
lean_ctor_set(v_reuseFailAlloc_5160_, 4, v_r_5016_);
v___x_5159_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
return v___x_5159_;
}
}
default: 
{
lean_object* v_impl_5161_; lean_object* v___x_5162_; 
lean_dec(v_size_5012_);
v_impl_5161_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_5009_, v_v_5010_, v_r_5016_);
v___x_5162_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5015_) == 0)
{
lean_object* v_size_5163_; lean_object* v_size_5164_; lean_object* v_k_5165_; lean_object* v_v_5166_; lean_object* v_l_5167_; lean_object* v_r_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; uint8_t v___x_5171_; 
v_size_5163_ = lean_ctor_get(v_l_5015_, 0);
v_size_5164_ = lean_ctor_get(v_impl_5161_, 0);
v_k_5165_ = lean_ctor_get(v_impl_5161_, 1);
v_v_5166_ = lean_ctor_get(v_impl_5161_, 2);
v_l_5167_ = lean_ctor_get(v_impl_5161_, 3);
lean_inc(v_l_5167_);
v_r_5168_ = lean_ctor_get(v_impl_5161_, 4);
v___x_5169_ = lean_unsigned_to_nat(3u);
v___x_5170_ = lean_nat_mul(v___x_5169_, v_size_5163_);
v___x_5171_ = lean_nat_dec_lt(v___x_5170_, v_size_5164_);
lean_dec(v___x_5170_);
if (v___x_5171_ == 0)
{
lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5175_; 
lean_dec(v_l_5167_);
v___x_5172_ = lean_nat_add(v___x_5162_, v_size_5163_);
v___x_5173_ = lean_nat_add(v___x_5172_, v_size_5164_);
lean_dec(v___x_5172_);
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 4, v_impl_5161_);
lean_ctor_set(v___x_5018_, 0, v___x_5173_);
v___x_5175_ = v___x_5018_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v___x_5173_);
lean_ctor_set(v_reuseFailAlloc_5176_, 1, v_k_5013_);
lean_ctor_set(v_reuseFailAlloc_5176_, 2, v_v_5014_);
lean_ctor_set(v_reuseFailAlloc_5176_, 3, v_l_5015_);
lean_ctor_set(v_reuseFailAlloc_5176_, 4, v_impl_5161_);
v___x_5175_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5174_;
}
v_reusejp_5174_:
{
return v___x_5175_;
}
}
else
{
lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5240_; 
lean_inc(v_r_5168_);
lean_inc(v_v_5166_);
lean_inc(v_k_5165_);
lean_inc(v_size_5164_);
v_isSharedCheck_5240_ = !lean_is_exclusive(v_impl_5161_);
if (v_isSharedCheck_5240_ == 0)
{
lean_object* v_unused_5241_; lean_object* v_unused_5242_; lean_object* v_unused_5243_; lean_object* v_unused_5244_; lean_object* v_unused_5245_; 
v_unused_5241_ = lean_ctor_get(v_impl_5161_, 4);
lean_dec(v_unused_5241_);
v_unused_5242_ = lean_ctor_get(v_impl_5161_, 3);
lean_dec(v_unused_5242_);
v_unused_5243_ = lean_ctor_get(v_impl_5161_, 2);
lean_dec(v_unused_5243_);
v_unused_5244_ = lean_ctor_get(v_impl_5161_, 1);
lean_dec(v_unused_5244_);
v_unused_5245_ = lean_ctor_get(v_impl_5161_, 0);
lean_dec(v_unused_5245_);
v___x_5178_ = v_impl_5161_;
v_isShared_5179_ = v_isSharedCheck_5240_;
goto v_resetjp_5177_;
}
else
{
lean_dec(v_impl_5161_);
v___x_5178_ = lean_box(0);
v_isShared_5179_ = v_isSharedCheck_5240_;
goto v_resetjp_5177_;
}
v_resetjp_5177_:
{
lean_object* v_size_5180_; lean_object* v_k_5181_; lean_object* v_v_5182_; lean_object* v_l_5183_; lean_object* v_r_5184_; lean_object* v_size_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; uint8_t v___x_5188_; 
v_size_5180_ = lean_ctor_get(v_l_5167_, 0);
v_k_5181_ = lean_ctor_get(v_l_5167_, 1);
v_v_5182_ = lean_ctor_get(v_l_5167_, 2);
v_l_5183_ = lean_ctor_get(v_l_5167_, 3);
v_r_5184_ = lean_ctor_get(v_l_5167_, 4);
v_size_5185_ = lean_ctor_get(v_r_5168_, 0);
v___x_5186_ = lean_unsigned_to_nat(2u);
v___x_5187_ = lean_nat_mul(v___x_5186_, v_size_5185_);
v___x_5188_ = lean_nat_dec_lt(v_size_5180_, v___x_5187_);
lean_dec(v___x_5187_);
if (v___x_5188_ == 0)
{
lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5216_; 
lean_inc(v_r_5184_);
lean_inc(v_l_5183_);
lean_inc(v_v_5182_);
lean_inc(v_k_5181_);
v_isSharedCheck_5216_ = !lean_is_exclusive(v_l_5167_);
if (v_isSharedCheck_5216_ == 0)
{
lean_object* v_unused_5217_; lean_object* v_unused_5218_; lean_object* v_unused_5219_; lean_object* v_unused_5220_; lean_object* v_unused_5221_; 
v_unused_5217_ = lean_ctor_get(v_l_5167_, 4);
lean_dec(v_unused_5217_);
v_unused_5218_ = lean_ctor_get(v_l_5167_, 3);
lean_dec(v_unused_5218_);
v_unused_5219_ = lean_ctor_get(v_l_5167_, 2);
lean_dec(v_unused_5219_);
v_unused_5220_ = lean_ctor_get(v_l_5167_, 1);
lean_dec(v_unused_5220_);
v_unused_5221_ = lean_ctor_get(v_l_5167_, 0);
lean_dec(v_unused_5221_);
v___x_5190_ = v_l_5167_;
v_isShared_5191_ = v_isSharedCheck_5216_;
goto v_resetjp_5189_;
}
else
{
lean_dec(v_l_5167_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5216_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___y_5195_; lean_object* v___y_5196_; lean_object* v___y_5197_; lean_object* v___y_5206_; 
v___x_5192_ = lean_nat_add(v___x_5162_, v_size_5163_);
v___x_5193_ = lean_nat_add(v___x_5192_, v_size_5164_);
lean_dec(v_size_5164_);
if (lean_obj_tag(v_l_5183_) == 0)
{
lean_object* v_size_5214_; 
v_size_5214_ = lean_ctor_get(v_l_5183_, 0);
lean_inc(v_size_5214_);
v___y_5206_ = v_size_5214_;
goto v___jp_5205_;
}
else
{
lean_object* v___x_5215_; 
v___x_5215_ = lean_unsigned_to_nat(0u);
v___y_5206_ = v___x_5215_;
goto v___jp_5205_;
}
v___jp_5194_:
{
lean_object* v___x_5198_; lean_object* v___x_5200_; 
v___x_5198_ = lean_nat_add(v___y_5196_, v___y_5197_);
lean_dec(v___y_5197_);
lean_dec(v___y_5196_);
if (v_isShared_5191_ == 0)
{
lean_ctor_set(v___x_5190_, 4, v_r_5168_);
lean_ctor_set(v___x_5190_, 3, v_r_5184_);
lean_ctor_set(v___x_5190_, 2, v_v_5166_);
lean_ctor_set(v___x_5190_, 1, v_k_5165_);
lean_ctor_set(v___x_5190_, 0, v___x_5198_);
v___x_5200_ = v___x_5190_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v___x_5198_);
lean_ctor_set(v_reuseFailAlloc_5204_, 1, v_k_5165_);
lean_ctor_set(v_reuseFailAlloc_5204_, 2, v_v_5166_);
lean_ctor_set(v_reuseFailAlloc_5204_, 3, v_r_5184_);
lean_ctor_set(v_reuseFailAlloc_5204_, 4, v_r_5168_);
v___x_5200_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
lean_object* v___x_5202_; 
if (v_isShared_5179_ == 0)
{
lean_ctor_set(v___x_5178_, 4, v___x_5200_);
lean_ctor_set(v___x_5178_, 3, v___y_5195_);
lean_ctor_set(v___x_5178_, 2, v_v_5182_);
lean_ctor_set(v___x_5178_, 1, v_k_5181_);
lean_ctor_set(v___x_5178_, 0, v___x_5193_);
v___x_5202_ = v___x_5178_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v___x_5193_);
lean_ctor_set(v_reuseFailAlloc_5203_, 1, v_k_5181_);
lean_ctor_set(v_reuseFailAlloc_5203_, 2, v_v_5182_);
lean_ctor_set(v_reuseFailAlloc_5203_, 3, v___y_5195_);
lean_ctor_set(v_reuseFailAlloc_5203_, 4, v___x_5200_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
return v___x_5202_;
}
}
}
v___jp_5205_:
{
lean_object* v___x_5207_; lean_object* v___x_5209_; 
v___x_5207_ = lean_nat_add(v___x_5192_, v___y_5206_);
lean_dec(v___y_5206_);
lean_dec(v___x_5192_);
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 4, v_l_5183_);
lean_ctor_set(v___x_5018_, 0, v___x_5207_);
v___x_5209_ = v___x_5018_;
goto v_reusejp_5208_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5207_);
lean_ctor_set(v_reuseFailAlloc_5213_, 1, v_k_5013_);
lean_ctor_set(v_reuseFailAlloc_5213_, 2, v_v_5014_);
lean_ctor_set(v_reuseFailAlloc_5213_, 3, v_l_5015_);
lean_ctor_set(v_reuseFailAlloc_5213_, 4, v_l_5183_);
v___x_5209_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5208_;
}
v_reusejp_5208_:
{
lean_object* v___x_5210_; 
v___x_5210_ = lean_nat_add(v___x_5162_, v_size_5185_);
if (lean_obj_tag(v_r_5184_) == 0)
{
lean_object* v_size_5211_; 
v_size_5211_ = lean_ctor_get(v_r_5184_, 0);
lean_inc(v_size_5211_);
v___y_5195_ = v___x_5209_;
v___y_5196_ = v___x_5210_;
v___y_5197_ = v_size_5211_;
goto v___jp_5194_;
}
else
{
lean_object* v___x_5212_; 
v___x_5212_ = lean_unsigned_to_nat(0u);
v___y_5195_ = v___x_5209_;
v___y_5196_ = v___x_5210_;
v___y_5197_ = v___x_5212_;
goto v___jp_5194_;
}
}
}
}
}
else
{
lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5226_; 
lean_del_object(v___x_5018_);
v___x_5222_ = lean_nat_add(v___x_5162_, v_size_5163_);
v___x_5223_ = lean_nat_add(v___x_5222_, v_size_5164_);
lean_dec(v_size_5164_);
v___x_5224_ = lean_nat_add(v___x_5222_, v_size_5180_);
lean_dec(v___x_5222_);
lean_inc_ref(v_l_5015_);
if (v_isShared_5179_ == 0)
{
lean_ctor_set(v___x_5178_, 4, v_l_5167_);
lean_ctor_set(v___x_5178_, 3, v_l_5015_);
lean_ctor_set(v___x_5178_, 2, v_v_5014_);
lean_ctor_set(v___x_5178_, 1, v_k_5013_);
lean_ctor_set(v___x_5178_, 0, v___x_5224_);
v___x_5226_ = v___x_5178_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5224_);
lean_ctor_set(v_reuseFailAlloc_5239_, 1, v_k_5013_);
lean_ctor_set(v_reuseFailAlloc_5239_, 2, v_v_5014_);
lean_ctor_set(v_reuseFailAlloc_5239_, 3, v_l_5015_);
lean_ctor_set(v_reuseFailAlloc_5239_, 4, v_l_5167_);
v___x_5226_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5233_; 
v_isSharedCheck_5233_ = !lean_is_exclusive(v_l_5015_);
if (v_isSharedCheck_5233_ == 0)
{
lean_object* v_unused_5234_; lean_object* v_unused_5235_; lean_object* v_unused_5236_; lean_object* v_unused_5237_; lean_object* v_unused_5238_; 
v_unused_5234_ = lean_ctor_get(v_l_5015_, 4);
lean_dec(v_unused_5234_);
v_unused_5235_ = lean_ctor_get(v_l_5015_, 3);
lean_dec(v_unused_5235_);
v_unused_5236_ = lean_ctor_get(v_l_5015_, 2);
lean_dec(v_unused_5236_);
v_unused_5237_ = lean_ctor_get(v_l_5015_, 1);
lean_dec(v_unused_5237_);
v_unused_5238_ = lean_ctor_get(v_l_5015_, 0);
lean_dec(v_unused_5238_);
v___x_5228_ = v_l_5015_;
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
else
{
lean_dec(v_l_5015_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5231_; 
if (v_isShared_5229_ == 0)
{
lean_ctor_set(v___x_5228_, 4, v_r_5168_);
lean_ctor_set(v___x_5228_, 3, v___x_5226_);
lean_ctor_set(v___x_5228_, 2, v_v_5166_);
lean_ctor_set(v___x_5228_, 1, v_k_5165_);
lean_ctor_set(v___x_5228_, 0, v___x_5223_);
v___x_5231_ = v___x_5228_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v___x_5223_);
lean_ctor_set(v_reuseFailAlloc_5232_, 1, v_k_5165_);
lean_ctor_set(v_reuseFailAlloc_5232_, 2, v_v_5166_);
lean_ctor_set(v_reuseFailAlloc_5232_, 3, v___x_5226_);
lean_ctor_set(v_reuseFailAlloc_5232_, 4, v_r_5168_);
v___x_5231_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
return v___x_5231_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5246_; 
v_l_5246_ = lean_ctor_get(v_impl_5161_, 3);
lean_inc(v_l_5246_);
if (lean_obj_tag(v_l_5246_) == 0)
{
lean_object* v_r_5247_; lean_object* v_k_5248_; lean_object* v_v_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5272_; 
v_r_5247_ = lean_ctor_get(v_impl_5161_, 4);
v_k_5248_ = lean_ctor_get(v_impl_5161_, 1);
v_v_5249_ = lean_ctor_get(v_impl_5161_, 2);
v_isSharedCheck_5272_ = !lean_is_exclusive(v_impl_5161_);
if (v_isSharedCheck_5272_ == 0)
{
lean_object* v_unused_5273_; lean_object* v_unused_5274_; 
v_unused_5273_ = lean_ctor_get(v_impl_5161_, 3);
lean_dec(v_unused_5273_);
v_unused_5274_ = lean_ctor_get(v_impl_5161_, 0);
lean_dec(v_unused_5274_);
v___x_5251_ = v_impl_5161_;
v_isShared_5252_ = v_isSharedCheck_5272_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_r_5247_);
lean_inc(v_v_5249_);
lean_inc(v_k_5248_);
lean_dec(v_impl_5161_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5272_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v_k_5253_; lean_object* v_v_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5268_; 
v_k_5253_ = lean_ctor_get(v_l_5246_, 1);
v_v_5254_ = lean_ctor_get(v_l_5246_, 2);
v_isSharedCheck_5268_ = !lean_is_exclusive(v_l_5246_);
if (v_isSharedCheck_5268_ == 0)
{
lean_object* v_unused_5269_; lean_object* v_unused_5270_; lean_object* v_unused_5271_; 
v_unused_5269_ = lean_ctor_get(v_l_5246_, 4);
lean_dec(v_unused_5269_);
v_unused_5270_ = lean_ctor_get(v_l_5246_, 3);
lean_dec(v_unused_5270_);
v_unused_5271_ = lean_ctor_get(v_l_5246_, 0);
lean_dec(v_unused_5271_);
v___x_5256_ = v_l_5246_;
v_isShared_5257_ = v_isSharedCheck_5268_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_v_5254_);
lean_inc(v_k_5253_);
lean_dec(v_l_5246_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5268_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5258_; lean_object* v___x_5260_; 
v___x_5258_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5247_, 2);
if (v_isShared_5257_ == 0)
{
lean_ctor_set(v___x_5256_, 4, v_r_5247_);
lean_ctor_set(v___x_5256_, 3, v_r_5247_);
lean_ctor_set(v___x_5256_, 2, v_v_5014_);
lean_ctor_set(v___x_5256_, 1, v_k_5013_);
lean_ctor_set(v___x_5256_, 0, v___x_5162_);
v___x_5260_ = v___x_5256_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v___x_5162_);
lean_ctor_set(v_reuseFailAlloc_5267_, 1, v_k_5013_);
lean_ctor_set(v_reuseFailAlloc_5267_, 2, v_v_5014_);
lean_ctor_set(v_reuseFailAlloc_5267_, 3, v_r_5247_);
lean_ctor_set(v_reuseFailAlloc_5267_, 4, v_r_5247_);
v___x_5260_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
lean_object* v___x_5262_; 
lean_inc(v_r_5247_);
if (v_isShared_5252_ == 0)
{
lean_ctor_set(v___x_5251_, 3, v_r_5247_);
lean_ctor_set(v___x_5251_, 0, v___x_5162_);
v___x_5262_ = v___x_5251_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v___x_5162_);
lean_ctor_set(v_reuseFailAlloc_5266_, 1, v_k_5248_);
lean_ctor_set(v_reuseFailAlloc_5266_, 2, v_v_5249_);
lean_ctor_set(v_reuseFailAlloc_5266_, 3, v_r_5247_);
lean_ctor_set(v_reuseFailAlloc_5266_, 4, v_r_5247_);
v___x_5262_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
lean_object* v___x_5264_; 
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 4, v___x_5262_);
lean_ctor_set(v___x_5018_, 3, v___x_5260_);
lean_ctor_set(v___x_5018_, 2, v_v_5254_);
lean_ctor_set(v___x_5018_, 1, v_k_5253_);
lean_ctor_set(v___x_5018_, 0, v___x_5258_);
v___x_5264_ = v___x_5018_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v___x_5258_);
lean_ctor_set(v_reuseFailAlloc_5265_, 1, v_k_5253_);
lean_ctor_set(v_reuseFailAlloc_5265_, 2, v_v_5254_);
lean_ctor_set(v_reuseFailAlloc_5265_, 3, v___x_5260_);
lean_ctor_set(v_reuseFailAlloc_5265_, 4, v___x_5262_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
}
}
}
}
else
{
lean_object* v_r_5275_; 
v_r_5275_ = lean_ctor_get(v_impl_5161_, 4);
lean_inc(v_r_5275_);
if (lean_obj_tag(v_r_5275_) == 0)
{
lean_object* v_k_5276_; lean_object* v_v_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5288_; 
v_k_5276_ = lean_ctor_get(v_impl_5161_, 1);
v_v_5277_ = lean_ctor_get(v_impl_5161_, 2);
v_isSharedCheck_5288_ = !lean_is_exclusive(v_impl_5161_);
if (v_isSharedCheck_5288_ == 0)
{
lean_object* v_unused_5289_; lean_object* v_unused_5290_; lean_object* v_unused_5291_; 
v_unused_5289_ = lean_ctor_get(v_impl_5161_, 4);
lean_dec(v_unused_5289_);
v_unused_5290_ = lean_ctor_get(v_impl_5161_, 3);
lean_dec(v_unused_5290_);
v_unused_5291_ = lean_ctor_get(v_impl_5161_, 0);
lean_dec(v_unused_5291_);
v___x_5279_ = v_impl_5161_;
v_isShared_5280_ = v_isSharedCheck_5288_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_v_5277_);
lean_inc(v_k_5276_);
lean_dec(v_impl_5161_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5288_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v___x_5281_; lean_object* v___x_5283_; 
v___x_5281_ = lean_unsigned_to_nat(3u);
if (v_isShared_5280_ == 0)
{
lean_ctor_set(v___x_5279_, 4, v_l_5246_);
lean_ctor_set(v___x_5279_, 2, v_v_5014_);
lean_ctor_set(v___x_5279_, 1, v_k_5013_);
lean_ctor_set(v___x_5279_, 0, v___x_5162_);
v___x_5283_ = v___x_5279_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v___x_5162_);
lean_ctor_set(v_reuseFailAlloc_5287_, 1, v_k_5013_);
lean_ctor_set(v_reuseFailAlloc_5287_, 2, v_v_5014_);
lean_ctor_set(v_reuseFailAlloc_5287_, 3, v_l_5246_);
lean_ctor_set(v_reuseFailAlloc_5287_, 4, v_l_5246_);
v___x_5283_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
lean_object* v___x_5285_; 
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 4, v_r_5275_);
lean_ctor_set(v___x_5018_, 3, v___x_5283_);
lean_ctor_set(v___x_5018_, 2, v_v_5277_);
lean_ctor_set(v___x_5018_, 1, v_k_5276_);
lean_ctor_set(v___x_5018_, 0, v___x_5281_);
v___x_5285_ = v___x_5018_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v___x_5281_);
lean_ctor_set(v_reuseFailAlloc_5286_, 1, v_k_5276_);
lean_ctor_set(v_reuseFailAlloc_5286_, 2, v_v_5277_);
lean_ctor_set(v_reuseFailAlloc_5286_, 3, v___x_5283_);
lean_ctor_set(v_reuseFailAlloc_5286_, 4, v_r_5275_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
}
}
else
{
lean_object* v___x_5292_; lean_object* v___x_5294_; 
v___x_5292_ = lean_unsigned_to_nat(2u);
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 4, v_impl_5161_);
lean_ctor_set(v___x_5018_, 3, v_r_5275_);
lean_ctor_set(v___x_5018_, 0, v___x_5292_);
v___x_5294_ = v___x_5018_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v___x_5292_);
lean_ctor_set(v_reuseFailAlloc_5295_, 1, v_k_5013_);
lean_ctor_set(v_reuseFailAlloc_5295_, 2, v_v_5014_);
lean_ctor_set(v_reuseFailAlloc_5295_, 3, v_r_5275_);
lean_ctor_set(v_reuseFailAlloc_5295_, 4, v_impl_5161_);
v___x_5294_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
return v___x_5294_;
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
lean_object* v___x_5297_; lean_object* v___x_5298_; 
v___x_5297_ = lean_unsigned_to_nat(1u);
v___x_5298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5298_, 0, v___x_5297_);
lean_ctor_set(v___x_5298_, 1, v_k_5009_);
lean_ctor_set(v___x_5298_, 2, v_v_5010_);
lean_ctor_set(v___x_5298_, 3, v_t_5011_);
lean_ctor_set(v___x_5298_, 4, v_t_5011_);
return v___x_5298_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(lean_object* v_init_5300_, lean_object* v_x_5301_){
_start:
{
lean_object* v_d_5304_; 
if (lean_obj_tag(v_x_5301_) == 0)
{
lean_object* v_k_5307_; lean_object* v_v_5308_; lean_object* v_l_5309_; lean_object* v_r_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; 
v_k_5307_ = lean_ctor_get(v_x_5301_, 1);
v_v_5308_ = lean_ctor_get(v_x_5301_, 2);
v_l_5309_ = lean_ctor_get(v_x_5301_, 3);
v_r_5310_ = lean_ctor_get(v_x_5301_, 4);
v___x_5311_ = lean_box(0);
v___x_5312_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_5313_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v_init_5300_, v_l_5309_);
if (lean_obj_tag(v___x_5313_) == 0)
{
lean_object* v_a_5314_; lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5349_; 
v_a_5314_ = lean_ctor_get(v___x_5313_, 0);
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5313_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5316_ = v___x_5313_;
v_isShared_5317_ = v_isSharedCheck_5349_;
goto v_resetjp_5315_;
}
else
{
lean_inc(v_a_5314_);
lean_dec(v___x_5313_);
v___x_5316_ = lean_box(0);
v_isShared_5317_ = v_isSharedCheck_5349_;
goto v_resetjp_5315_;
}
v_resetjp_5315_:
{
if (lean_obj_tag(v_a_5314_) == 0)
{
lean_object* v_a_5318_; 
lean_del_object(v___x_5316_);
v_a_5318_ = lean_ctor_get(v_a_5314_, 0);
lean_inc(v_a_5318_);
lean_dec_ref_known(v_a_5314_, 1);
v_d_5304_ = v_a_5318_;
goto v___jp_5303_;
}
else
{
lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5347_; 
v_isSharedCheck_5347_ = !lean_is_exclusive(v_a_5314_);
if (v_isSharedCheck_5347_ == 0)
{
lean_object* v_unused_5348_; 
v_unused_5348_ = lean_ctor_get(v_a_5314_, 0);
lean_dec(v_unused_5348_);
v___x_5320_ = v_a_5314_;
v_isShared_5321_ = v_isSharedCheck_5347_;
goto v_resetjp_5319_;
}
else
{
lean_dec(v_a_5314_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5347_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5322_; lean_object* v___x_5323_; uint8_t v___x_5324_; 
v___x_5322_ = lean_array_get_size(v_v_5308_);
v___x_5323_ = lean_unsigned_to_nat(0u);
v___x_5324_ = lean_nat_dec_eq(v___x_5322_, v___x_5323_);
if (v___x_5324_ == 0)
{
lean_del_object(v___x_5320_);
lean_del_object(v___x_5316_);
v_init_5300_ = v___x_5312_;
v_x_5301_ = v_r_5310_;
goto _start;
}
else
{
lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; 
v___x_5326_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1));
v___x_5327_ = lean_string_append(v___x_5326_, v_k_5307_);
v___x_5328_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___closed__0));
v___x_5329_ = lean_string_append(v___x_5327_, v___x_5328_);
v___x_5330_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5329_);
lean_dec_ref(v___x_5329_);
if (lean_obj_tag(v___x_5330_) == 0)
{
lean_object* v_a_5331_; lean_object* v___x_5333_; 
v_a_5331_ = lean_ctor_get(v___x_5330_, 0);
lean_inc(v_a_5331_);
lean_dec_ref_known(v___x_5330_, 1);
if (v_isShared_5321_ == 0)
{
lean_ctor_set_tag(v___x_5320_, 0);
lean_ctor_set(v___x_5320_, 0, v_a_5331_);
v___x_5333_ = v___x_5320_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5338_; 
v_reuseFailAlloc_5338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5338_, 0, v_a_5331_);
v___x_5333_ = v_reuseFailAlloc_5338_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
lean_object* v___x_5335_; 
if (v_isShared_5317_ == 0)
{
lean_ctor_set_tag(v___x_5316_, 1);
lean_ctor_set(v___x_5316_, 0, v___x_5333_);
v___x_5335_ = v___x_5316_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5337_; 
v_reuseFailAlloc_5337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5337_, 0, v___x_5333_);
v___x_5335_ = v_reuseFailAlloc_5337_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
lean_object* v___x_5336_; 
v___x_5336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5336_, 0, v___x_5335_);
lean_ctor_set(v___x_5336_, 1, v___x_5311_);
v_d_5304_ = v___x_5336_;
goto v___jp_5303_;
}
}
}
else
{
lean_object* v_a_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5346_; 
lean_del_object(v___x_5320_);
lean_del_object(v___x_5316_);
v_a_5339_ = lean_ctor_get(v___x_5330_, 0);
v_isSharedCheck_5346_ = !lean_is_exclusive(v___x_5330_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5341_ = v___x_5330_;
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_a_5339_);
lean_dec(v___x_5330_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5344_; 
if (v_isShared_5342_ == 0)
{
v___x_5344_ = v___x_5341_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_a_5339_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
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
return v___x_5313_;
}
}
else
{
lean_object* v___x_5350_; lean_object* v___x_5351_; 
v___x_5350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5350_, 0, v_init_5300_);
v___x_5351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5351_, 0, v___x_5350_);
return v___x_5351_;
}
v___jp_5303_:
{
lean_object* v___x_5305_; lean_object* v___x_5306_; 
v___x_5305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5305_, 0, v_d_5304_);
v___x_5306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5305_);
return v___x_5306_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___boxed(lean_object* v_init_5352_, lean_object* v_x_5353_, lean_object* v___y_5354_){
_start:
{
lean_object* v_res_5355_; 
v_res_5355_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v_init_5352_, v_x_5353_);
lean_dec(v_x_5353_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(lean_object* v_cfg_5361_){
_start:
{
lean_object* v___y_5364_; lean_object* v_a_5365_; lean_object* v___y_5378_; lean_object* v_externalKernels_5379_; lean_object* v___y_5392_; lean_object* v___y_5393_; uint8_t v___y_5394_; lean_object* v_a_5395_; lean_object* v___y_5409_; uint8_t v___y_5410_; lean_object* v_enable__nanoda_x3f_5423_; lean_object* v_external__kernels_x3f_5424_; lean_object* v___y_5426_; 
v_enable__nanoda_x3f_5423_ = lean_ctor_get(v_cfg_5361_, 5);
lean_inc(v_enable__nanoda_x3f_5423_);
v_external__kernels_x3f_5424_ = lean_ctor_get(v_cfg_5361_, 6);
lean_inc(v_external__kernels_x3f_5424_);
lean_dec_ref(v_cfg_5361_);
if (lean_obj_tag(v_external__kernels_x3f_5424_) == 0)
{
lean_object* v___x_5457_; 
v___x_5457_ = lean_box(1);
v___y_5426_ = v___x_5457_;
goto v___jp_5425_;
}
else
{
lean_object* v_val_5458_; 
v_val_5458_ = lean_ctor_get(v_external__kernels_x3f_5424_, 0);
lean_inc(v_val_5458_);
lean_dec_ref_known(v_external__kernels_x3f_5424_, 1);
v___y_5426_ = v_val_5458_;
goto v___jp_5425_;
}
v___jp_5363_:
{
lean_object* v_fst_5366_; 
v_fst_5366_ = lean_ctor_get(v_a_5365_, 0);
lean_inc(v_fst_5366_);
lean_dec_ref(v_a_5365_);
if (lean_obj_tag(v_fst_5366_) == 0)
{
lean_object* v___x_5367_; lean_object* v___x_5368_; 
v___x_5367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5367_, 0, v___y_5364_);
v___x_5368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5368_, 0, v___x_5367_);
return v___x_5368_;
}
else
{
lean_object* v_val_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5376_; 
lean_dec(v___y_5364_);
v_val_5369_ = lean_ctor_get(v_fst_5366_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v_fst_5366_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5371_ = v_fst_5366_;
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_val_5369_);
lean_dec(v_fst_5366_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
lean_object* v___x_5374_; 
if (v_isShared_5372_ == 0)
{
lean_ctor_set_tag(v___x_5371_, 0);
v___x_5374_ = v___x_5371_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_val_5369_);
v___x_5374_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
return v___x_5374_;
}
}
}
}
v___jp_5377_:
{
lean_object* v___x_5380_; 
v___x_5380_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v___y_5378_, v_externalKernels_5379_);
if (lean_obj_tag(v___x_5380_) == 0)
{
lean_object* v_a_5381_; lean_object* v_a_5382_; 
v_a_5381_ = lean_ctor_get(v___x_5380_, 0);
lean_inc(v_a_5381_);
lean_dec_ref_known(v___x_5380_, 1);
v_a_5382_ = lean_ctor_get(v_a_5381_, 0);
lean_inc(v_a_5382_);
lean_dec(v_a_5381_);
v___y_5364_ = v_externalKernels_5379_;
v_a_5365_ = v_a_5382_;
goto v___jp_5363_;
}
else
{
lean_object* v_a_5383_; lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5390_; 
lean_dec(v_externalKernels_5379_);
v_a_5383_ = lean_ctor_get(v___x_5380_, 0);
v_isSharedCheck_5390_ = !lean_is_exclusive(v___x_5380_);
if (v_isSharedCheck_5390_ == 0)
{
v___x_5385_ = v___x_5380_;
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
else
{
lean_inc(v_a_5383_);
lean_dec(v___x_5380_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
lean_object* v___x_5388_; 
if (v_isShared_5386_ == 0)
{
v___x_5388_ = v___x_5385_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5389_; 
v_reuseFailAlloc_5389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5389_, 0, v_a_5383_);
v___x_5388_ = v_reuseFailAlloc_5389_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
return v___x_5388_;
}
}
}
}
v___jp_5391_:
{
lean_object* v_fst_5396_; 
v_fst_5396_ = lean_ctor_get(v_a_5395_, 0);
lean_inc(v_fst_5396_);
lean_dec_ref(v_a_5395_);
if (lean_obj_tag(v_fst_5396_) == 0)
{
if (v___y_5394_ == 0)
{
v___y_5378_ = v___y_5392_;
v_externalKernels_5379_ = v___y_5393_;
goto v___jp_5377_;
}
else
{
lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; 
v___x_5397_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__4));
v___x_5398_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0));
v___x_5399_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v___x_5397_, v___x_5398_, v___y_5393_);
v___y_5378_ = v___y_5392_;
v_externalKernels_5379_ = v___x_5399_;
goto v___jp_5377_;
}
}
else
{
lean_object* v_val_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5407_; 
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
v_val_5400_ = lean_ctor_get(v_fst_5396_, 0);
v_isSharedCheck_5407_ = !lean_is_exclusive(v_fst_5396_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5402_ = v_fst_5396_;
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_val_5400_);
lean_dec(v_fst_5396_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v___x_5405_; 
if (v_isShared_5403_ == 0)
{
lean_ctor_set_tag(v___x_5402_, 0);
v___x_5405_ = v___x_5402_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_val_5400_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
}
v___jp_5408_:
{
lean_object* v___x_5411_; lean_object* v___x_5412_; 
v___x_5411_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_5412_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v___x_5411_, v___y_5409_);
if (lean_obj_tag(v___x_5412_) == 0)
{
lean_object* v_a_5413_; lean_object* v_a_5414_; 
v_a_5413_ = lean_ctor_get(v___x_5412_, 0);
lean_inc(v_a_5413_);
lean_dec_ref_known(v___x_5412_, 1);
v_a_5414_ = lean_ctor_get(v_a_5413_, 0);
lean_inc(v_a_5414_);
lean_dec(v_a_5413_);
v___y_5392_ = v___x_5411_;
v___y_5393_ = v___y_5409_;
v___y_5394_ = v___y_5410_;
v_a_5395_ = v_a_5414_;
goto v___jp_5391_;
}
else
{
lean_object* v_a_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5422_; 
lean_dec(v___y_5409_);
v_a_5415_ = lean_ctor_get(v___x_5412_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v___x_5412_);
if (v_isSharedCheck_5422_ == 0)
{
v___x_5417_ = v___x_5412_;
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_a_5415_);
lean_dec(v___x_5412_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5420_; 
if (v_isShared_5418_ == 0)
{
v___x_5420_ = v___x_5417_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v_a_5415_);
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
v___jp_5425_:
{
if (lean_obj_tag(v_enable__nanoda_x3f_5423_) == 0)
{
uint8_t v___x_5427_; 
v___x_5427_ = 0;
v___y_5409_ = v___y_5426_;
v___y_5410_ = v___x_5427_;
goto v___jp_5408_;
}
else
{
lean_object* v_val_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5456_; 
v_val_5428_ = lean_ctor_get(v_enable__nanoda_x3f_5423_, 0);
v_isSharedCheck_5456_ = !lean_is_exclusive(v_enable__nanoda_x3f_5423_);
if (v_isSharedCheck_5456_ == 0)
{
v___x_5430_ = v_enable__nanoda_x3f_5423_;
v_isShared_5431_ = v_isSharedCheck_5456_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_val_5428_);
lean_dec(v_enable__nanoda_x3f_5423_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5456_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
uint8_t v___x_5432_; 
v___x_5432_ = lean_unbox(v_val_5428_);
if (v___x_5432_ == 0)
{
uint8_t v___x_5433_; 
lean_del_object(v___x_5430_);
v___x_5433_ = lean_unbox(v_val_5428_);
lean_dec(v_val_5428_);
v___y_5409_ = v___y_5426_;
v___y_5410_ = v___x_5433_;
goto v___jp_5408_;
}
else
{
if (lean_obj_tag(v___y_5426_) == 0)
{
lean_object* v___x_5434_; lean_object* v___x_5435_; 
lean_dec_ref_known(v___y_5426_, 5);
lean_dec(v_val_5428_);
v___x_5434_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__1));
v___x_5435_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5434_);
if (lean_obj_tag(v___x_5435_) == 0)
{
lean_object* v_a_5436_; lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5446_; 
v_a_5436_ = lean_ctor_get(v___x_5435_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5435_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5438_ = v___x_5435_;
v_isShared_5439_ = v_isSharedCheck_5446_;
goto v_resetjp_5437_;
}
else
{
lean_inc(v_a_5436_);
lean_dec(v___x_5435_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5446_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
lean_object* v___x_5441_; 
if (v_isShared_5431_ == 0)
{
lean_ctor_set_tag(v___x_5430_, 0);
lean_ctor_set(v___x_5430_, 0, v_a_5436_);
v___x_5441_ = v___x_5430_;
goto v_reusejp_5440_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5436_);
v___x_5441_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5440_;
}
v_reusejp_5440_:
{
lean_object* v___x_5443_; 
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 0, v___x_5441_);
v___x_5443_ = v___x_5438_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v___x_5441_);
v___x_5443_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
return v___x_5443_;
}
}
}
}
else
{
lean_object* v_a_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5454_; 
lean_del_object(v___x_5430_);
v_a_5447_ = lean_ctor_get(v___x_5435_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v___x_5435_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5449_ = v___x_5435_;
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_a_5447_);
lean_dec(v___x_5435_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v___x_5452_; 
if (v_isShared_5450_ == 0)
{
v___x_5452_ = v___x_5449_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
return v___x_5452_;
}
}
}
}
else
{
uint8_t v___x_5455_; 
lean_del_object(v___x_5430_);
v___x_5455_ = lean_unbox(v_val_5428_);
lean_dec(v_val_5428_);
v___y_5409_ = v___y_5426_;
v___y_5410_ = v___x_5455_;
goto v___jp_5408_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___boxed(lean_object* v_cfg_5459_, lean_object* v_a_5460_){
_start:
{
lean_object* v_res_5461_; 
v_res_5461_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v_cfg_5459_);
return v_res_5461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(lean_object* v_00_u03b2_5462_, lean_object* v_k_5463_, lean_object* v_v_5464_, lean_object* v_t_5465_, lean_object* v_hl_5466_){
_start:
{
lean_object* v___x_5467_; 
v___x_5467_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_5463_, v_v_5464_, v_t_5465_);
return v___x_5467_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(lean_object* v_a_5485_, lean_object* v_a_5486_){
_start:
{
if (lean_obj_tag(v_a_5485_) == 0)
{
lean_object* v___x_5487_; 
v___x_5487_ = l_List_reverse___redArg(v_a_5486_);
return v___x_5487_;
}
else
{
lean_object* v_head_5488_; lean_object* v_tail_5489_; lean_object* v___x_5491_; uint8_t v_isShared_5492_; uint8_t v_isSharedCheck_5500_; 
v_head_5488_ = lean_ctor_get(v_a_5485_, 0);
v_tail_5489_ = lean_ctor_get(v_a_5485_, 1);
v_isSharedCheck_5500_ = !lean_is_exclusive(v_a_5485_);
if (v_isSharedCheck_5500_ == 0)
{
v___x_5491_ = v_a_5485_;
v_isShared_5492_ = v_isSharedCheck_5500_;
goto v_resetjp_5490_;
}
else
{
lean_inc(v_tail_5489_);
lean_inc(v_head_5488_);
lean_dec(v_a_5485_);
v___x_5491_ = lean_box(0);
v_isShared_5492_ = v_isSharedCheck_5500_;
goto v_resetjp_5490_;
}
v_resetjp_5490_:
{
lean_object* v_fst_5493_; uint8_t v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5497_; 
v_fst_5493_ = lean_ctor_get(v_head_5488_, 0);
lean_inc(v_fst_5493_);
lean_dec(v_head_5488_);
v___x_5494_ = 1;
v___x_5495_ = l_Lean_Name_toString(v_fst_5493_, v___x_5494_);
if (v_isShared_5492_ == 0)
{
lean_ctor_set(v___x_5491_, 1, v_a_5486_);
lean_ctor_set(v___x_5491_, 0, v___x_5495_);
v___x_5497_ = v___x_5491_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v___x_5495_);
lean_ctor_set(v_reuseFailAlloc_5499_, 1, v_a_5486_);
v___x_5497_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
v_a_5485_ = v_tail_5489_;
v_a_5486_ = v___x_5497_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(lean_object* v_as_5501_, size_t v_i_5502_, size_t v_stop_5503_, lean_object* v_b_5504_){
_start:
{
lean_object* v___y_5506_; uint8_t v___x_5510_; 
v___x_5510_ = lean_usize_dec_eq(v_i_5502_, v_stop_5503_);
if (v___x_5510_ == 0)
{
lean_object* v___x_5511_; lean_object* v_fst_5512_; lean_object* v___x_5513_; uint8_t v___x_5514_; 
v___x_5511_ = lean_array_uget_borrowed(v_as_5501_, v_i_5502_);
v_fst_5512_ = lean_ctor_get(v___x_5511_, 0);
v___x_5513_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms));
v___x_5514_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v___x_5513_, v_fst_5512_);
if (v___x_5514_ == 0)
{
lean_object* v___x_5515_; 
lean_inc(v___x_5511_);
v___x_5515_ = lean_array_push(v_b_5504_, v___x_5511_);
v___y_5506_ = v___x_5515_;
goto v___jp_5505_;
}
else
{
v___y_5506_ = v_b_5504_;
goto v___jp_5505_;
}
}
else
{
return v_b_5504_;
}
v___jp_5505_:
{
size_t v___x_5507_; size_t v___x_5508_; 
v___x_5507_ = ((size_t)1ULL);
v___x_5508_ = lean_usize_add(v_i_5502_, v___x_5507_);
v_i_5502_ = v___x_5508_;
v_b_5504_ = v___y_5506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1___boxed(lean_object* v_as_5516_, lean_object* v_i_5517_, lean_object* v_stop_5518_, lean_object* v_b_5519_){
_start:
{
size_t v_i_boxed_5520_; size_t v_stop_boxed_5521_; lean_object* v_res_5522_; 
v_i_boxed_5520_ = lean_unbox_usize(v_i_5517_);
lean_dec(v_i_5517_);
v_stop_boxed_5521_ = lean_unbox_usize(v_stop_5518_);
lean_dec(v_stop_5518_);
v_res_5522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_as_5516_, v_i_boxed_5520_, v_stop_boxed_5521_, v_b_5519_);
lean_dec_ref(v_as_5516_);
return v_res_5522_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(lean_object* v_a_5525_, lean_object* v_a_5526_){
_start:
{
if (lean_obj_tag(v_a_5525_) == 0)
{
lean_object* v___x_5527_; 
v___x_5527_ = l_List_reverse___redArg(v_a_5526_);
return v___x_5527_;
}
else
{
lean_object* v_head_5528_; lean_object* v_tail_5529_; lean_object* v___x_5531_; uint8_t v_isShared_5532_; uint8_t v_isSharedCheck_5549_; 
v_head_5528_ = lean_ctor_get(v_a_5525_, 0);
v_tail_5529_ = lean_ctor_get(v_a_5525_, 1);
v_isSharedCheck_5549_ = !lean_is_exclusive(v_a_5525_);
if (v_isSharedCheck_5549_ == 0)
{
v___x_5531_ = v_a_5525_;
v_isShared_5532_ = v_isSharedCheck_5549_;
goto v_resetjp_5530_;
}
else
{
lean_inc(v_tail_5529_);
lean_inc(v_head_5528_);
lean_dec(v_a_5525_);
v___x_5531_ = lean_box(0);
v_isShared_5532_ = v_isSharedCheck_5549_;
goto v_resetjp_5530_;
}
v_resetjp_5530_:
{
lean_object* v_fst_5533_; lean_object* v_snd_5534_; lean_object* v___x_5535_; uint8_t v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5546_; 
v_fst_5533_ = lean_ctor_get(v_head_5528_, 0);
lean_inc(v_fst_5533_);
v_snd_5534_ = lean_ctor_get(v_head_5528_, 1);
lean_inc(v_snd_5534_);
lean_dec(v_head_5528_);
v___x_5535_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__0));
v___x_5536_ = 1;
v___x_5537_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_5533_, v___x_5536_);
v___x_5538_ = lean_string_append(v___x_5535_, v___x_5537_);
lean_dec_ref(v___x_5537_);
v___x_5539_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__1));
v___x_5540_ = lean_string_append(v___x_5538_, v___x_5539_);
v___x_5541_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_snd_5534_, v___x_5536_);
v___x_5542_ = lean_string_append(v___x_5540_, v___x_5541_);
lean_dec_ref(v___x_5541_);
v___x_5543_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_5544_ = lean_string_append(v___x_5542_, v___x_5543_);
if (v_isShared_5532_ == 0)
{
lean_ctor_set(v___x_5531_, 1, v_a_5526_);
lean_ctor_set(v___x_5531_, 0, v___x_5544_);
v___x_5546_ = v___x_5531_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v___x_5544_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v_a_5526_);
v___x_5546_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
v_a_5525_ = v_tail_5529_;
v_a_5526_ = v___x_5546_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(lean_object* v_exported_5555_){
_start:
{
lean_object* v___y_5558_; lean_object* v_used_5571_; lean_object* v___x_5584_; lean_object* v___x_5585_; uint8_t v___x_5586_; 
v_used_5571_ = l_Lake_Check_usedAxioms(v_exported_5555_);
v___x_5584_ = lean_array_get_size(v_used_5571_);
v___x_5585_ = lean_unsigned_to_nat(0u);
v___x_5586_ = lean_nat_dec_eq(v___x_5584_, v___x_5585_);
if (v___x_5586_ == 0)
{
lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; 
v___x_5587_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__2));
v___x_5588_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0));
lean_inc_ref(v_used_5571_);
v___x_5589_ = lean_array_to_list(v_used_5571_);
v___x_5590_ = lean_box(0);
v___x_5591_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(v___x_5589_, v___x_5590_);
v___x_5592_ = l_String_intercalate(v___x_5588_, v___x_5591_);
v___x_5593_ = lean_string_append(v___x_5587_, v___x_5592_);
lean_dec_ref(v___x_5592_);
v___x_5594_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_5593_);
if (lean_obj_tag(v___x_5594_) == 0)
{
lean_dec_ref_known(v___x_5594_, 1);
goto v___jp_5572_;
}
else
{
lean_dec_ref(v_used_5571_);
return v___x_5594_;
}
}
else
{
lean_object* v___x_5595_; lean_object* v___x_5596_; 
v___x_5595_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__3));
v___x_5596_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_5595_);
if (lean_obj_tag(v___x_5596_) == 0)
{
lean_dec_ref_known(v___x_5596_, 1);
goto v___jp_5572_;
}
else
{
lean_dec_ref(v_used_5571_);
return v___x_5596_;
}
}
v___jp_5557_:
{
lean_object* v___x_5559_; lean_object* v___x_5560_; uint8_t v___x_5561_; 
v___x_5559_ = lean_array_get_size(v___y_5558_);
v___x_5560_ = lean_unsigned_to_nat(0u);
v___x_5561_ = lean_nat_dec_eq(v___x_5559_, v___x_5560_);
if (v___x_5561_ == 0)
{
lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; 
v___x_5562_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__0));
v___x_5563_ = lean_array_to_list(v___y_5558_);
v___x_5564_ = lean_box(0);
v___x_5565_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(v___x_5563_, v___x_5564_);
v___x_5566_ = l_String_intercalate(v___x_5562_, v___x_5565_);
v___x_5567_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_5567_, 0, v___x_5566_);
v___x_5568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5568_, 0, v___x_5567_);
return v___x_5568_;
}
else
{
lean_object* v___x_5569_; lean_object* v___x_5570_; 
lean_dec_ref(v___y_5558_);
v___x_5569_ = lean_box(0);
v___x_5570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5570_, 0, v___x_5569_);
return v___x_5570_;
}
}
v___jp_5572_:
{
lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; uint8_t v___x_5576_; 
v___x_5573_ = lean_unsigned_to_nat(0u);
v___x_5574_ = lean_array_get_size(v_used_5571_);
v___x_5575_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__1));
v___x_5576_ = lean_nat_dec_lt(v___x_5573_, v___x_5574_);
if (v___x_5576_ == 0)
{
lean_dec_ref(v_used_5571_);
v___y_5558_ = v___x_5575_;
goto v___jp_5557_;
}
else
{
uint8_t v___x_5577_; 
v___x_5577_ = lean_nat_dec_le(v___x_5574_, v___x_5574_);
if (v___x_5577_ == 0)
{
if (v___x_5576_ == 0)
{
lean_dec_ref(v_used_5571_);
v___y_5558_ = v___x_5575_;
goto v___jp_5557_;
}
else
{
size_t v___x_5578_; size_t v___x_5579_; lean_object* v___x_5580_; 
v___x_5578_ = ((size_t)0ULL);
v___x_5579_ = lean_usize_of_nat(v___x_5574_);
v___x_5580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_used_5571_, v___x_5578_, v___x_5579_, v___x_5575_);
lean_dec_ref(v_used_5571_);
v___y_5558_ = v___x_5580_;
goto v___jp_5557_;
}
}
else
{
size_t v___x_5581_; size_t v___x_5582_; lean_object* v___x_5583_; 
v___x_5581_ = ((size_t)0ULL);
v___x_5582_ = lean_usize_of_nat(v___x_5574_);
v___x_5583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_used_5571_, v___x_5581_, v___x_5582_, v___x_5575_);
lean_dec_ref(v_used_5571_);
v___y_5558_ = v___x_5583_;
goto v___jp_5557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___boxed(lean_object* v_exported_5597_, lean_object* v_a_5598_){
_start:
{
lean_object* v_res_5599_; 
v_res_5599_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_5597_);
return v_res_5599_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(lean_object* v_exported_5600_, lean_object* v_a_5601_){
_start:
{
lean_object* v___x_5603_; 
v___x_5603_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_5600_);
return v___x_5603_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___boxed(lean_object* v_exported_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_){
_start:
{
lean_object* v_res_5607_; 
v_res_5607_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(v_exported_5604_, v_a_5605_);
lean_dec_ref(v_a_5605_);
return v_res_5607_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(lean_object* v_exportPath_5608_, lean_object* v___y_5609_){
_start:
{
lean_object* v___x_5611_; 
lean_inc_ref(v_exportPath_5608_);
v___x_5611_ = l___private_Lake_CLI_Check_0__Lake_Check_runKernels(v_exportPath_5608_, v___y_5609_);
if (lean_obj_tag(v___x_5611_) == 0)
{
uint8_t v___x_5612_; lean_object* v___x_5613_; 
lean_dec_ref_known(v___x_5611_, 1);
v___x_5612_ = 0;
v___x_5613_ = lean_io_prim_handle_mk(v_exportPath_5608_, v___x_5612_);
lean_dec_ref(v_exportPath_5608_);
if (lean_obj_tag(v___x_5613_) == 0)
{
lean_object* v_a_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; 
v_a_5614_ = lean_ctor_get(v___x_5613_, 0);
lean_inc(v_a_5614_);
lean_dec_ref_known(v___x_5613_, 1);
v___x_5615_ = lean_stream_of_handle(v_a_5614_);
v___x_5616_ = l_LeanExport_parseStream(v___x_5615_);
if (lean_obj_tag(v___x_5616_) == 0)
{
lean_object* v_a_5617_; lean_object* v___x_5618_; 
v_a_5617_ = lean_ctor_get(v___x_5616_, 0);
lean_inc(v_a_5617_);
lean_dec_ref_known(v___x_5616_, 1);
v___x_5618_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_a_5617_);
return v___x_5618_;
}
else
{
lean_object* v_a_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5626_; 
v_a_5619_ = lean_ctor_get(v___x_5616_, 0);
v_isSharedCheck_5626_ = !lean_is_exclusive(v___x_5616_);
if (v_isSharedCheck_5626_ == 0)
{
v___x_5621_ = v___x_5616_;
v_isShared_5622_ = v_isSharedCheck_5626_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_a_5619_);
lean_dec(v___x_5616_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5626_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
lean_object* v___x_5624_; 
if (v_isShared_5622_ == 0)
{
v___x_5624_ = v___x_5621_;
goto v_reusejp_5623_;
}
else
{
lean_object* v_reuseFailAlloc_5625_; 
v_reuseFailAlloc_5625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5625_, 0, v_a_5619_);
v___x_5624_ = v_reuseFailAlloc_5625_;
goto v_reusejp_5623_;
}
v_reusejp_5623_:
{
return v___x_5624_;
}
}
}
}
else
{
lean_object* v_a_5627_; lean_object* v___x_5629_; uint8_t v_isShared_5630_; uint8_t v_isSharedCheck_5634_; 
v_a_5627_ = lean_ctor_get(v___x_5613_, 0);
v_isSharedCheck_5634_ = !lean_is_exclusive(v___x_5613_);
if (v_isSharedCheck_5634_ == 0)
{
v___x_5629_ = v___x_5613_;
v_isShared_5630_ = v_isSharedCheck_5634_;
goto v_resetjp_5628_;
}
else
{
lean_inc(v_a_5627_);
lean_dec(v___x_5613_);
v___x_5629_ = lean_box(0);
v_isShared_5630_ = v_isSharedCheck_5634_;
goto v_resetjp_5628_;
}
v_resetjp_5628_:
{
lean_object* v___x_5632_; 
if (v_isShared_5630_ == 0)
{
v___x_5632_ = v___x_5629_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_a_5627_);
v___x_5632_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
return v___x_5632_;
}
}
}
}
else
{
lean_dec_ref(v_exportPath_5608_);
return v___x_5611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0___boxed(lean_object* v_exportPath_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_){
_start:
{
lean_object* v_res_5638_; 
v_res_5638_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(v_exportPath_5635_, v___y_5636_);
lean_dec_ref(v___y_5636_);
return v_res_5638_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(lean_object* v_m_5639_, uint8_t v_a_5640_){
_start:
{
lean_object* v_buckets_5641_; lean_object* v___x_5642_; uint64_t v___x_5643_; uint64_t v___x_5644_; uint64_t v___x_5645_; uint64_t v_fold_5646_; uint64_t v___x_5647_; uint64_t v___x_5648_; uint64_t v___x_5649_; size_t v___x_5650_; size_t v___x_5651_; size_t v___x_5652_; size_t v___x_5653_; size_t v___x_5654_; lean_object* v___x_5655_; uint8_t v___x_5656_; 
v_buckets_5641_ = lean_ctor_get(v_m_5639_, 1);
v___x_5642_ = lean_array_get_size(v_buckets_5641_);
v___x_5643_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_a_5640_);
v___x_5644_ = 32ULL;
v___x_5645_ = lean_uint64_shift_right(v___x_5643_, v___x_5644_);
v_fold_5646_ = lean_uint64_xor(v___x_5643_, v___x_5645_);
v___x_5647_ = 16ULL;
v___x_5648_ = lean_uint64_shift_right(v_fold_5646_, v___x_5647_);
v___x_5649_ = lean_uint64_xor(v_fold_5646_, v___x_5648_);
v___x_5650_ = lean_uint64_to_usize(v___x_5649_);
v___x_5651_ = lean_usize_of_nat(v___x_5642_);
v___x_5652_ = ((size_t)1ULL);
v___x_5653_ = lean_usize_sub(v___x_5651_, v___x_5652_);
v___x_5654_ = lean_usize_land(v___x_5650_, v___x_5653_);
v___x_5655_ = lean_array_uget_borrowed(v_buckets_5641_, v___x_5654_);
v___x_5656_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_5640_, v___x_5655_);
return v___x_5656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg___boxed(lean_object* v_m_5657_, lean_object* v_a_5658_){
_start:
{
uint8_t v_a_boxed_5659_; uint8_t v_res_5660_; lean_object* v_r_5661_; 
v_a_boxed_5659_ = lean_unbox(v_a_5658_);
v_res_5660_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_m_5657_, v_a_boxed_5659_);
lean_dec_ref(v_m_5657_);
v_r_5661_ = lean_box(v_res_5660_);
return v_r_5661_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject(lean_object* v_a_5663_){
_start:
{
lean_object* v_moduleStore_5665_; lean_object* v___f_5666_; uint8_t v___x_5667_; uint8_t v___x_5668_; 
v_moduleStore_5665_ = lean_ctor_get(v_a_5663_, 17);
v___f_5666_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkProject___closed__0));
v___x_5667_ = 0;
v___x_5668_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_moduleStore_5665_, v___x_5667_);
if (v___x_5668_ == 0)
{
lean_object* v___x_5669_; 
v___x_5669_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_5663_);
if (lean_obj_tag(v___x_5669_) == 0)
{
lean_object* v___x_5670_; 
lean_dec_ref_known(v___x_5669_, 1);
v___x_5670_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v___f_5666_, v_a_5663_);
return v___x_5670_;
}
else
{
return v___x_5669_;
}
}
else
{
lean_object* v___x_5671_; 
v___x_5671_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v___f_5666_, v_a_5663_);
return v___x_5671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___boxed(lean_object* v_a_5672_, lean_object* v_a_5673_){
_start:
{
lean_object* v_res_5674_; 
v_res_5674_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v_a_5672_);
lean_dec_ref(v_a_5672_);
return v_res_5674_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0(lean_object* v_00_u03b2_5675_, lean_object* v_m_5676_, uint8_t v_a_5677_){
_start:
{
uint8_t v___x_5678_; 
v___x_5678_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_m_5676_, v_a_5677_);
return v___x_5678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___boxed(lean_object* v_00_u03b2_5679_, lean_object* v_m_5680_, lean_object* v_a_5681_){
_start:
{
uint8_t v_a_boxed_5682_; uint8_t v_res_5683_; lean_object* v_r_5684_; 
v_a_boxed_5682_ = lean_unbox(v_a_5681_);
v_res_5683_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0(v_00_u03b2_5679_, v_m_5680_, v_a_boxed_5682_);
lean_dec_ref(v_m_5680_);
v_r_5684_ = lean_box(v_res_5683_);
return v_r_5684_;
}
}
static lean_object* _init_l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_5685_; lean_object* v___x_5686_; 
v___x_5685_ = 0;
v___x_5686_ = lean_box_uint32(v___x_5685_);
return v___x_5686_;
}
}
static lean_object* _init_l_Lake_Check_runComparator___lam__0___closed__0(void){
_start:
{
lean_object* v___x_5687_; lean_object* v___x_5688_; 
v___x_5687_ = l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1;
v___x_5688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5687_);
return v___x_5688_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___lam__0(lean_object* v_____r_5689_){
_start:
{
lean_object* v___x_5691_; lean_object* v___x_5692_; 
v___x_5691_ = lean_obj_once(&l_Lake_Check_runComparator___lam__0___closed__0, &l_Lake_Check_runComparator___lam__0___closed__0_once, _init_l_Lake_Check_runComparator___lam__0___closed__0);
v___x_5692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5692_, 0, v___x_5691_);
return v___x_5692_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___lam__0___boxed(lean_object* v_____r_5693_, lean_object* v___y_5694_){
_start:
{
lean_object* v_res_5695_; 
v_res_5695_ = l_Lake_Check_runComparator___lam__0(v_____r_5693_);
return v_res_5695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(size_t v_sz_5696_, size_t v_i_5697_, lean_object* v_bs_5698_){
_start:
{
uint8_t v___x_5699_; 
v___x_5699_ = lean_usize_dec_lt(v_i_5697_, v_sz_5696_);
if (v___x_5699_ == 0)
{
return v_bs_5698_;
}
else
{
lean_object* v_v_5700_; lean_object* v___x_5701_; lean_object* v_bs_x27_5702_; lean_object* v___x_5703_; size_t v___x_5704_; size_t v___x_5705_; lean_object* v___x_5706_; 
v_v_5700_ = lean_array_uget(v_bs_5698_, v_i_5697_);
v___x_5701_ = lean_unsigned_to_nat(0u);
v_bs_x27_5702_ = lean_array_uset(v_bs_5698_, v_i_5697_, v___x_5701_);
v___x_5703_ = l_String_toName(v_v_5700_);
v___x_5704_ = ((size_t)1ULL);
v___x_5705_ = lean_usize_add(v_i_5697_, v___x_5704_);
v___x_5706_ = lean_array_uset(v_bs_x27_5702_, v_i_5697_, v___x_5703_);
v_i_5697_ = v___x_5705_;
v_bs_5698_ = v___x_5706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0___boxed(lean_object* v_sz_5708_, lean_object* v_i_5709_, lean_object* v_bs_5710_){
_start:
{
size_t v_sz_boxed_5711_; size_t v_i_boxed_5712_; lean_object* v_res_5713_; 
v_sz_boxed_5711_ = lean_unbox_usize(v_sz_5708_);
lean_dec(v_sz_5708_);
v_i_boxed_5712_ = lean_unbox_usize(v_i_5709_);
lean_dec(v_i_5709_);
v_res_5713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_boxed_5711_, v_i_boxed_5712_, v_bs_5710_);
return v_res_5713_;
}
}
static lean_object* _init_l_Lake_Check_runComparator___boxed__const__1(void){
_start:
{
uint32_t v___x_5722_; lean_object* v___x_5723_; 
v___x_5722_ = 1;
v___x_5723_ = lean_box_uint32(v___x_5722_);
return v___x_5723_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator(lean_object* v_configFile_x3f_5724_, lean_object* v_challengeFromExport_x3f_5725_, lean_object* v_solutionFromExport_x3f_5726_, uint8_t v_paranoid_5727_, uint8_t v_inadvisablyNoSandbox_5728_, lean_object* v_lean_5729_, lean_object* v_lake_5730_, lean_object* v_projectDir_5731_){
_start:
{
lean_object* v_a_5734_; lean_object* v___y_5757_; lean_object* v___y_5768_; lean_object* v_a_5769_; lean_object* v___x_5776_; lean_object* v___x_5777_; uint8_t v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; uint8_t v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; 
v___x_5776_ = ((lean_object*)(l_Lake_Check_runComparator___closed__2));
v___x_5777_ = ((lean_object*)(l_Lake_Check_runComparator___closed__3));
v___x_5778_ = 2;
v___x_5779_ = lean_box(v___x_5778_);
v___x_5780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5780_, 0, v___x_5779_);
lean_ctor_set(v___x_5780_, 1, v_challengeFromExport_x3f_5725_);
v___x_5781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5781_, 0, v___x_5777_);
lean_ctor_set(v___x_5781_, 1, v___x_5780_);
v___x_5782_ = ((lean_object*)(l_Lake_Check_runComparator___closed__4));
v___x_5783_ = 1;
v___x_5784_ = lean_box(v___x_5783_);
v___x_5785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5785_, 0, v___x_5784_);
lean_ctor_set(v___x_5785_, 1, v_solutionFromExport_x3f_5726_);
v___x_5786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5786_, 0, v___x_5782_);
lean_ctor_set(v___x_5786_, 1, v___x_5785_);
v___x_5787_ = lean_unsigned_to_nat(2u);
v___x_5788_ = lean_mk_empty_array_with_capacity(v___x_5787_);
v___x_5789_ = lean_array_push(v___x_5788_, v___x_5781_);
v___x_5790_ = lean_array_push(v___x_5789_, v___x_5786_);
v___x_5791_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(v___x_5776_, v___x_5790_);
lean_dec_ref(v___x_5790_);
if (lean_obj_tag(v___x_5791_) == 0)
{
lean_object* v_a_5792_; lean_object* v___x_5794_; uint8_t v_isShared_5795_; uint8_t v_isSharedCheck_5985_; 
v_a_5792_ = lean_ctor_get(v___x_5791_, 0);
v_isSharedCheck_5985_ = !lean_is_exclusive(v___x_5791_);
if (v_isSharedCheck_5985_ == 0)
{
v___x_5794_ = v___x_5791_;
v_isShared_5795_ = v_isSharedCheck_5985_;
goto v_resetjp_5793_;
}
else
{
lean_inc(v_a_5792_);
lean_dec(v___x_5791_);
v___x_5794_ = lean_box(0);
v_isShared_5795_ = v_isSharedCheck_5985_;
goto v_resetjp_5793_;
}
v_resetjp_5793_:
{
if (lean_obj_tag(v_a_5792_) == 0)
{
lean_object* v_a_5796_; lean_object* v___x_5798_; 
lean_dec_ref(v_projectDir_5731_);
lean_dec_ref(v_lean_5729_);
v_a_5796_ = lean_ctor_get(v_a_5792_, 0);
lean_inc(v_a_5796_);
lean_dec_ref_known(v_a_5792_, 1);
if (v_isShared_5795_ == 0)
{
lean_ctor_set(v___x_5794_, 0, v_a_5796_);
v___x_5798_ = v___x_5794_;
goto v_reusejp_5797_;
}
else
{
lean_object* v_reuseFailAlloc_5799_; 
v_reuseFailAlloc_5799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5799_, 0, v_a_5796_);
v___x_5798_ = v_reuseFailAlloc_5799_;
goto v_reusejp_5797_;
}
v_reusejp_5797_:
{
return v___x_5798_;
}
}
else
{
lean_object* v_a_5800_; lean_object* v___x_5801_; 
lean_del_object(v___x_5794_);
v_a_5800_ = lean_ctor_get(v_a_5792_, 0);
lean_inc_n(v_a_5800_, 2);
lean_dec_ref_known(v_a_5792_, 1);
v___x_5801_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_5776_, v_paranoid_5727_, v_inadvisablyNoSandbox_5728_, v_lean_5729_, v_lake_5730_, v_projectDir_5731_, v_a_5800_);
if (lean_obj_tag(v___x_5801_) == 0)
{
lean_object* v_a_5802_; lean_object* v___x_5804_; uint8_t v_isShared_5805_; uint8_t v_isSharedCheck_5976_; 
v_a_5802_ = lean_ctor_get(v___x_5801_, 0);
v_isSharedCheck_5976_ = !lean_is_exclusive(v___x_5801_);
if (v_isSharedCheck_5976_ == 0)
{
v___x_5804_ = v___x_5801_;
v_isShared_5805_ = v_isSharedCheck_5976_;
goto v_resetjp_5803_;
}
else
{
lean_inc(v_a_5802_);
lean_dec(v___x_5801_);
v___x_5804_ = lean_box(0);
v_isShared_5805_ = v_isSharedCheck_5976_;
goto v_resetjp_5803_;
}
v_resetjp_5803_:
{
if (lean_obj_tag(v_a_5802_) == 0)
{
lean_object* v_a_5806_; lean_object* v___x_5808_; 
lean_dec(v_a_5800_);
v_a_5806_ = lean_ctor_get(v_a_5802_, 0);
lean_inc(v_a_5806_);
lean_dec_ref_known(v_a_5802_, 1);
if (v_isShared_5805_ == 0)
{
lean_ctor_set(v___x_5804_, 0, v_a_5806_);
v___x_5808_ = v___x_5804_;
goto v_reusejp_5807_;
}
else
{
lean_object* v_reuseFailAlloc_5809_; 
v_reuseFailAlloc_5809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5809_, 0, v_a_5806_);
v___x_5808_ = v_reuseFailAlloc_5809_;
goto v_reusejp_5807_;
}
v_reusejp_5807_:
{
return v___x_5808_;
}
}
else
{
lean_object* v_a_5810_; size_t v___y_5812_; lean_object* v___y_5813_; lean_object* v___y_5814_; uint8_t v___y_5815_; lean_object* v___y_5816_; lean_object* v___y_5817_; lean_object* v___y_5818_; lean_object* v___y_5819_; size_t v___y_5864_; lean_object* v___y_5865_; lean_object* v___y_5866_; lean_object* v___y_5867_; lean_object* v___y_5868_; lean_object* v___y_5869_; lean_object* v___y_5870_; uint8_t v___y_5871_; uint8_t v___y_5892_; size_t v___y_5893_; lean_object* v___y_5894_; lean_object* v___y_5895_; lean_object* v___y_5896_; lean_object* v___y_5897_; lean_object* v___y_5898_; lean_object* v___y_5899_; uint8_t v___y_5900_; size_t v___y_5903_; lean_object* v___y_5904_; lean_object* v___y_5905_; lean_object* v___y_5906_; lean_object* v___y_5907_; lean_object* v___y_5908_; lean_object* v___y_5909_; uint8_t v___y_5910_; size_t v___y_5933_; lean_object* v___y_5934_; lean_object* v___y_5935_; lean_object* v___y_5936_; lean_object* v___y_5937_; lean_object* v___y_5938_; lean_object* v___y_5939_; lean_object* v___y_5950_; 
lean_del_object(v___x_5804_);
v_a_5810_ = lean_ctor_get(v_a_5802_, 0);
lean_inc(v_a_5810_);
lean_dec_ref_known(v_a_5802_, 1);
if (lean_obj_tag(v_configFile_x3f_5724_) == 0)
{
lean_object* v___x_5974_; 
v___x_5974_ = ((lean_object*)(l_Lake_Check_runComparator___closed__7));
v___y_5950_ = v___x_5974_;
goto v___jp_5949_;
}
else
{
lean_object* v_val_5975_; 
v_val_5975_ = lean_ctor_get(v_configFile_x3f_5724_, 0);
v___y_5950_ = v_val_5975_;
goto v___jp_5949_;
}
v___jp_5811_:
{
lean_object* v_projectDir_5820_; lean_object* v_leanPrefix_5821_; lean_object* v_leanPath_5822_; lean_object* v_binPath_5823_; lean_object* v_whichSandbox_5824_; lean_object* v_whichLake_5825_; lean_object* v_lakeHome_5826_; lean_object* v_whichLean4Export_5827_; lean_object* v_whichLeanChecker_5828_; lean_object* v_whichEnvBin_5829_; lean_object* v_bundledKernels_5830_; lean_object* v_moduleStore_5831_; lean_object* v___x_5833_; uint8_t v_isShared_5834_; uint8_t v_isSharedCheck_5856_; 
v_projectDir_5820_ = lean_ctor_get(v_a_5810_, 0);
v_leanPrefix_5821_ = lean_ctor_get(v_a_5810_, 6);
v_leanPath_5822_ = lean_ctor_get(v_a_5810_, 7);
v_binPath_5823_ = lean_ctor_get(v_a_5810_, 8);
v_whichSandbox_5824_ = lean_ctor_get(v_a_5810_, 9);
v_whichLake_5825_ = lean_ctor_get(v_a_5810_, 10);
v_lakeHome_5826_ = lean_ctor_get(v_a_5810_, 11);
v_whichLean4Export_5827_ = lean_ctor_get(v_a_5810_, 12);
v_whichLeanChecker_5828_ = lean_ctor_get(v_a_5810_, 13);
v_whichEnvBin_5829_ = lean_ctor_get(v_a_5810_, 14);
v_bundledKernels_5830_ = lean_ctor_get(v_a_5810_, 16);
v_moduleStore_5831_ = lean_ctor_get(v_a_5810_, 17);
v_isSharedCheck_5856_ = !lean_is_exclusive(v_a_5810_);
if (v_isSharedCheck_5856_ == 0)
{
lean_object* v_unused_5857_; lean_object* v_unused_5858_; lean_object* v_unused_5859_; lean_object* v_unused_5860_; lean_object* v_unused_5861_; lean_object* v_unused_5862_; 
v_unused_5857_ = lean_ctor_get(v_a_5810_, 15);
lean_dec(v_unused_5857_);
v_unused_5858_ = lean_ctor_get(v_a_5810_, 5);
lean_dec(v_unused_5858_);
v_unused_5859_ = lean_ctor_get(v_a_5810_, 4);
lean_dec(v_unused_5859_);
v_unused_5860_ = lean_ctor_get(v_a_5810_, 3);
lean_dec(v_unused_5860_);
v_unused_5861_ = lean_ctor_get(v_a_5810_, 2);
lean_dec(v_unused_5861_);
v_unused_5862_ = lean_ctor_get(v_a_5810_, 1);
lean_dec(v_unused_5862_);
v___x_5833_ = v_a_5810_;
v_isShared_5834_ = v_isSharedCheck_5856_;
goto v_resetjp_5832_;
}
else
{
lean_inc(v_moduleStore_5831_);
lean_inc(v_bundledKernels_5830_);
lean_inc(v_whichEnvBin_5829_);
lean_inc(v_whichLeanChecker_5828_);
lean_inc(v_whichLean4Export_5827_);
lean_inc(v_lakeHome_5826_);
lean_inc(v_whichLake_5825_);
lean_inc(v_whichSandbox_5824_);
lean_inc(v_binPath_5823_);
lean_inc(v_leanPath_5822_);
lean_inc(v_leanPrefix_5821_);
lean_inc(v_projectDir_5820_);
lean_dec(v_a_5810_);
v___x_5833_ = lean_box(0);
v_isShared_5834_ = v_isSharedCheck_5856_;
goto v_resetjp_5832_;
}
v_resetjp_5832_:
{
lean_object* v___x_5835_; lean_object* v___x_5836_; size_t v_sz_5837_; lean_object* v___x_5838_; lean_object* v___x_5840_; 
v___x_5835_ = l_String_toName(v___y_5816_);
v___x_5836_ = l_String_toName(v___y_5819_);
v_sz_5837_ = lean_array_size(v___y_5814_);
v___x_5838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_5837_, v___y_5812_, v___y_5814_);
lean_inc_ref(v_moduleStore_5831_);
lean_inc_ref(v_bundledKernels_5830_);
lean_inc(v___y_5813_);
lean_inc_ref(v_whichEnvBin_5829_);
lean_inc_ref(v_whichLeanChecker_5828_);
lean_inc_ref(v_whichLean4Export_5827_);
lean_inc_ref(v_lakeHome_5826_);
lean_inc_ref(v_whichLake_5825_);
lean_inc(v_whichSandbox_5824_);
lean_inc_ref(v_leanPrefix_5821_);
lean_inc_ref(v___x_5838_);
lean_inc_ref(v___y_5818_);
lean_inc_ref(v___y_5817_);
lean_inc(v___x_5836_);
lean_inc(v___x_5835_);
lean_inc_ref(v_projectDir_5820_);
if (v_isShared_5834_ == 0)
{
lean_ctor_set(v___x_5833_, 15, v___y_5813_);
lean_ctor_set(v___x_5833_, 5, v___x_5838_);
lean_ctor_set(v___x_5833_, 4, v___y_5818_);
lean_ctor_set(v___x_5833_, 3, v___y_5817_);
lean_ctor_set(v___x_5833_, 2, v___x_5836_);
lean_ctor_set(v___x_5833_, 1, v___x_5835_);
v___x_5840_ = v___x_5833_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5855_; 
v_reuseFailAlloc_5855_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_5855_, 0, v_projectDir_5820_);
lean_ctor_set(v_reuseFailAlloc_5855_, 1, v___x_5835_);
lean_ctor_set(v_reuseFailAlloc_5855_, 2, v___x_5836_);
lean_ctor_set(v_reuseFailAlloc_5855_, 3, v___y_5817_);
lean_ctor_set(v_reuseFailAlloc_5855_, 4, v___y_5818_);
lean_ctor_set(v_reuseFailAlloc_5855_, 5, v___x_5838_);
lean_ctor_set(v_reuseFailAlloc_5855_, 6, v_leanPrefix_5821_);
lean_ctor_set(v_reuseFailAlloc_5855_, 7, v_leanPath_5822_);
lean_ctor_set(v_reuseFailAlloc_5855_, 8, v_binPath_5823_);
lean_ctor_set(v_reuseFailAlloc_5855_, 9, v_whichSandbox_5824_);
lean_ctor_set(v_reuseFailAlloc_5855_, 10, v_whichLake_5825_);
lean_ctor_set(v_reuseFailAlloc_5855_, 11, v_lakeHome_5826_);
lean_ctor_set(v_reuseFailAlloc_5855_, 12, v_whichLean4Export_5827_);
lean_ctor_set(v_reuseFailAlloc_5855_, 13, v_whichLeanChecker_5828_);
lean_ctor_set(v_reuseFailAlloc_5855_, 14, v_whichEnvBin_5829_);
lean_ctor_set(v_reuseFailAlloc_5855_, 15, v___y_5813_);
lean_ctor_set(v_reuseFailAlloc_5855_, 16, v_bundledKernels_5830_);
lean_ctor_set(v_reuseFailAlloc_5855_, 17, v_moduleStore_5831_);
v___x_5840_ = v_reuseFailAlloc_5855_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
if (v___y_5815_ == 0)
{
lean_object* v___x_5841_; 
lean_dec_ref(v___x_5838_);
lean_dec(v___x_5836_);
lean_dec(v___x_5835_);
lean_dec_ref(v_moduleStore_5831_);
lean_dec_ref(v_bundledKernels_5830_);
lean_dec_ref(v_whichEnvBin_5829_);
lean_dec_ref(v_whichLeanChecker_5828_);
lean_dec_ref(v_whichLean4Export_5827_);
lean_dec_ref(v_lakeHome_5826_);
lean_dec_ref(v_whichLake_5825_);
lean_dec(v_whichSandbox_5824_);
lean_dec_ref(v_leanPrefix_5821_);
lean_dec_ref(v_projectDir_5820_);
lean_dec_ref(v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v___y_5813_);
v___x_5841_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt(v___x_5840_);
lean_dec_ref(v___x_5840_);
if (lean_obj_tag(v___x_5841_) == 0)
{
lean_object* v_a_5842_; lean_object* v___x_5843_; 
v_a_5842_ = lean_ctor_get(v___x_5841_, 0);
lean_inc(v_a_5842_);
lean_dec_ref_known(v___x_5841_, 1);
v___x_5843_ = l_Lake_Check_runComparator___lam__0(v_a_5842_);
v___y_5757_ = v___x_5843_;
goto v___jp_5756_;
}
else
{
lean_object* v_a_5844_; 
v_a_5844_ = lean_ctor_get(v___x_5841_, 0);
lean_inc(v_a_5844_);
lean_dec_ref_known(v___x_5841_, 1);
v_a_5734_ = v_a_5844_;
goto v___jp_5733_;
}
}
else
{
lean_object* v___x_5845_; 
v___x_5845_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v___x_5840_);
lean_dec_ref(v___x_5840_);
if (lean_obj_tag(v___x_5845_) == 0)
{
lean_object* v_a_5846_; lean_object* v_fst_5847_; lean_object* v_snd_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; 
v_a_5846_ = lean_ctor_get(v___x_5845_, 0);
lean_inc(v_a_5846_);
lean_dec_ref_known(v___x_5845_, 1);
v_fst_5847_ = lean_ctor_get(v_a_5846_, 0);
lean_inc(v_fst_5847_);
v_snd_5848_ = lean_ctor_get(v_a_5846_, 1);
lean_inc(v_snd_5848_);
lean_dec(v_a_5846_);
v___x_5849_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_5849_, 0, v_projectDir_5820_);
lean_ctor_set(v___x_5849_, 1, v___x_5835_);
lean_ctor_set(v___x_5849_, 2, v___x_5836_);
lean_ctor_set(v___x_5849_, 3, v___y_5817_);
lean_ctor_set(v___x_5849_, 4, v___y_5818_);
lean_ctor_set(v___x_5849_, 5, v___x_5838_);
lean_ctor_set(v___x_5849_, 6, v_leanPrefix_5821_);
lean_ctor_set(v___x_5849_, 7, v_fst_5847_);
lean_ctor_set(v___x_5849_, 8, v_snd_5848_);
lean_ctor_set(v___x_5849_, 9, v_whichSandbox_5824_);
lean_ctor_set(v___x_5849_, 10, v_whichLake_5825_);
lean_ctor_set(v___x_5849_, 11, v_lakeHome_5826_);
lean_ctor_set(v___x_5849_, 12, v_whichLean4Export_5827_);
lean_ctor_set(v___x_5849_, 13, v_whichLeanChecker_5828_);
lean_ctor_set(v___x_5849_, 14, v_whichEnvBin_5829_);
lean_ctor_set(v___x_5849_, 15, v___y_5813_);
lean_ctor_set(v___x_5849_, 16, v_bundledKernels_5830_);
lean_ctor_set(v___x_5849_, 17, v_moduleStore_5831_);
v___x_5850_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt(v___x_5849_);
lean_dec_ref_known(v___x_5849_, 18);
if (lean_obj_tag(v___x_5850_) == 0)
{
lean_object* v_a_5851_; lean_object* v___x_5852_; 
v_a_5851_ = lean_ctor_get(v___x_5850_, 0);
lean_inc(v_a_5851_);
lean_dec_ref_known(v___x_5850_, 1);
v___x_5852_ = l_Lake_Check_runComparator___lam__0(v_a_5851_);
v___y_5757_ = v___x_5852_;
goto v___jp_5756_;
}
else
{
lean_object* v_a_5853_; 
v_a_5853_ = lean_ctor_get(v___x_5850_, 0);
lean_inc(v_a_5853_);
lean_dec_ref_known(v___x_5850_, 1);
v_a_5734_ = v_a_5853_;
goto v___jp_5733_;
}
}
else
{
lean_object* v_a_5854_; 
lean_dec_ref(v___x_5838_);
lean_dec(v___x_5836_);
lean_dec(v___x_5835_);
lean_dec_ref(v_moduleStore_5831_);
lean_dec_ref(v_bundledKernels_5830_);
lean_dec_ref(v_whichEnvBin_5829_);
lean_dec_ref(v_whichLeanChecker_5828_);
lean_dec_ref(v_whichLean4Export_5827_);
lean_dec_ref(v_lakeHome_5826_);
lean_dec_ref(v_whichLake_5825_);
lean_dec(v_whichSandbox_5824_);
lean_dec_ref(v_leanPrefix_5821_);
lean_dec_ref(v_projectDir_5820_);
lean_dec_ref(v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v___y_5813_);
v_a_5854_ = lean_ctor_get(v___x_5845_, 0);
lean_inc(v_a_5854_);
lean_dec_ref_known(v___x_5845_, 1);
v_a_5734_ = v_a_5854_;
goto v___jp_5733_;
}
}
}
}
}
v___jp_5863_:
{
lean_object* v_projectDir_5872_; lean_object* v___x_5873_; 
v_projectDir_5872_ = lean_ctor_get(v_a_5810_, 0);
lean_inc_ref(v_projectDir_5872_);
v___x_5873_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_5776_, v_projectDir_5872_);
if (lean_obj_tag(v___x_5873_) == 0)
{
lean_object* v_a_5874_; lean_object* v___x_5876_; uint8_t v_isShared_5877_; uint8_t v_isSharedCheck_5882_; 
v_a_5874_ = lean_ctor_get(v___x_5873_, 0);
v_isSharedCheck_5882_ = !lean_is_exclusive(v___x_5873_);
if (v_isSharedCheck_5882_ == 0)
{
v___x_5876_ = v___x_5873_;
v_isShared_5877_ = v_isSharedCheck_5882_;
goto v_resetjp_5875_;
}
else
{
lean_inc(v_a_5874_);
lean_dec(v___x_5873_);
v___x_5876_ = lean_box(0);
v_isShared_5877_ = v_isSharedCheck_5882_;
goto v_resetjp_5875_;
}
v_resetjp_5875_:
{
if (lean_obj_tag(v_a_5874_) == 1)
{
lean_object* v_val_5878_; lean_object* v___x_5880_; 
lean_dec_ref(v___y_5870_);
lean_dec_ref(v___y_5869_);
lean_dec_ref(v___y_5868_);
lean_dec_ref(v___y_5867_);
lean_dec(v___y_5866_);
lean_dec_ref(v___y_5865_);
lean_dec(v_a_5810_);
v_val_5878_ = lean_ctor_get(v_a_5874_, 0);
lean_inc(v_val_5878_);
lean_dec_ref_known(v_a_5874_, 1);
if (v_isShared_5877_ == 0)
{
lean_ctor_set(v___x_5876_, 0, v_val_5878_);
v___x_5880_ = v___x_5876_;
goto v_reusejp_5879_;
}
else
{
lean_object* v_reuseFailAlloc_5881_; 
v_reuseFailAlloc_5881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5881_, 0, v_val_5878_);
v___x_5880_ = v_reuseFailAlloc_5881_;
goto v_reusejp_5879_;
}
v_reusejp_5879_:
{
return v___x_5880_;
}
}
else
{
lean_del_object(v___x_5876_);
lean_dec(v_a_5874_);
v___y_5812_ = v___y_5864_;
v___y_5813_ = v___y_5866_;
v___y_5814_ = v___y_5865_;
v___y_5815_ = v___y_5871_;
v___y_5816_ = v___y_5867_;
v___y_5817_ = v___y_5868_;
v___y_5818_ = v___y_5870_;
v___y_5819_ = v___y_5869_;
goto v___jp_5811_;
}
}
}
else
{
lean_object* v_a_5883_; lean_object* v___x_5885_; uint8_t v_isShared_5886_; uint8_t v_isSharedCheck_5890_; 
lean_dec_ref(v___y_5870_);
lean_dec_ref(v___y_5869_);
lean_dec_ref(v___y_5868_);
lean_dec_ref(v___y_5867_);
lean_dec(v___y_5866_);
lean_dec_ref(v___y_5865_);
lean_dec(v_a_5810_);
v_a_5883_ = lean_ctor_get(v___x_5873_, 0);
v_isSharedCheck_5890_ = !lean_is_exclusive(v___x_5873_);
if (v_isSharedCheck_5890_ == 0)
{
v___x_5885_ = v___x_5873_;
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
else
{
lean_inc(v_a_5883_);
lean_dec(v___x_5873_);
v___x_5885_ = lean_box(0);
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
v_resetjp_5884_:
{
lean_object* v___x_5888_; 
if (v_isShared_5886_ == 0)
{
v___x_5888_ = v___x_5885_;
goto v_reusejp_5887_;
}
else
{
lean_object* v_reuseFailAlloc_5889_; 
v_reuseFailAlloc_5889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5889_, 0, v_a_5883_);
v___x_5888_ = v_reuseFailAlloc_5889_;
goto v_reusejp_5887_;
}
v_reusejp_5887_:
{
return v___x_5888_;
}
}
}
}
v___jp_5891_:
{
if (v___y_5900_ == 0)
{
uint8_t v___x_5901_; 
v___x_5901_ = 1;
v___y_5864_ = v___y_5893_;
v___y_5865_ = v___y_5895_;
v___y_5866_ = v___y_5894_;
v___y_5867_ = v___y_5896_;
v___y_5868_ = v___y_5897_;
v___y_5869_ = v___y_5899_;
v___y_5870_ = v___y_5898_;
v___y_5871_ = v___x_5901_;
goto v___jp_5863_;
}
else
{
if (v___y_5892_ == 0)
{
v___y_5812_ = v___y_5893_;
v___y_5813_ = v___y_5894_;
v___y_5814_ = v___y_5895_;
v___y_5815_ = v___y_5892_;
v___y_5816_ = v___y_5896_;
v___y_5817_ = v___y_5897_;
v___y_5818_ = v___y_5898_;
v___y_5819_ = v___y_5899_;
goto v___jp_5811_;
}
else
{
v___y_5864_ = v___y_5893_;
v___y_5865_ = v___y_5895_;
v___y_5866_ = v___y_5894_;
v___y_5867_ = v___y_5896_;
v___y_5868_ = v___y_5897_;
v___y_5869_ = v___y_5899_;
v___y_5870_ = v___y_5898_;
v___y_5871_ = v___y_5892_;
goto v___jp_5863_;
}
}
}
v___jp_5902_:
{
lean_object* v___x_5911_; 
v___x_5911_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v___y_5905_);
if (lean_obj_tag(v___x_5911_) == 0)
{
lean_object* v_a_5912_; lean_object* v___x_5914_; uint8_t v_isShared_5915_; uint8_t v_isSharedCheck_5923_; 
v_a_5912_ = lean_ctor_get(v___x_5911_, 0);
v_isSharedCheck_5923_ = !lean_is_exclusive(v___x_5911_);
if (v_isSharedCheck_5923_ == 0)
{
v___x_5914_ = v___x_5911_;
v_isShared_5915_ = v_isSharedCheck_5923_;
goto v_resetjp_5913_;
}
else
{
lean_inc(v_a_5912_);
lean_dec(v___x_5911_);
v___x_5914_ = lean_box(0);
v_isShared_5915_ = v_isSharedCheck_5923_;
goto v_resetjp_5913_;
}
v_resetjp_5913_:
{
if (lean_obj_tag(v_a_5912_) == 0)
{
lean_object* v_a_5916_; lean_object* v___x_5918_; 
lean_dec_ref(v___y_5909_);
lean_dec_ref(v___y_5908_);
lean_dec_ref(v___y_5907_);
lean_dec_ref(v___y_5906_);
lean_dec_ref(v___y_5904_);
lean_dec(v_a_5810_);
lean_dec(v_a_5800_);
v_a_5916_ = lean_ctor_get(v_a_5912_, 0);
lean_inc(v_a_5916_);
lean_dec_ref_known(v_a_5912_, 1);
if (v_isShared_5915_ == 0)
{
lean_ctor_set(v___x_5914_, 0, v_a_5916_);
v___x_5918_ = v___x_5914_;
goto v_reusejp_5917_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_a_5916_);
v___x_5918_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5917_;
}
v_reusejp_5917_:
{
return v___x_5918_;
}
}
else
{
lean_object* v_a_5920_; uint8_t v___x_5921_; 
lean_del_object(v___x_5914_);
v_a_5920_ = lean_ctor_get(v_a_5912_, 0);
lean_inc(v_a_5920_);
lean_dec_ref_known(v_a_5912_, 1);
v___x_5921_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_a_5800_, v___x_5778_);
if (v___x_5921_ == 0)
{
lean_dec(v_a_5800_);
v___y_5892_ = v___y_5910_;
v___y_5893_ = v___y_5903_;
v___y_5894_ = v_a_5920_;
v___y_5895_ = v___y_5904_;
v___y_5896_ = v___y_5906_;
v___y_5897_ = v___y_5907_;
v___y_5898_ = v___y_5908_;
v___y_5899_ = v___y_5909_;
v___y_5900_ = v___x_5921_;
goto v___jp_5891_;
}
else
{
uint8_t v___x_5922_; 
v___x_5922_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_a_5800_, v___x_5783_);
lean_dec(v_a_5800_);
v___y_5892_ = v___y_5910_;
v___y_5893_ = v___y_5903_;
v___y_5894_ = v_a_5920_;
v___y_5895_ = v___y_5904_;
v___y_5896_ = v___y_5906_;
v___y_5897_ = v___y_5907_;
v___y_5898_ = v___y_5908_;
v___y_5899_ = v___y_5909_;
v___y_5900_ = v___x_5922_;
goto v___jp_5891_;
}
}
}
}
else
{
lean_object* v_a_5924_; lean_object* v___x_5926_; uint8_t v_isShared_5927_; uint8_t v_isSharedCheck_5931_; 
lean_dec_ref(v___y_5909_);
lean_dec_ref(v___y_5908_);
lean_dec_ref(v___y_5907_);
lean_dec_ref(v___y_5906_);
lean_dec_ref(v___y_5904_);
lean_dec(v_a_5810_);
lean_dec(v_a_5800_);
v_a_5924_ = lean_ctor_get(v___x_5911_, 0);
v_isSharedCheck_5931_ = !lean_is_exclusive(v___x_5911_);
if (v_isSharedCheck_5931_ == 0)
{
v___x_5926_ = v___x_5911_;
v_isShared_5927_ = v_isSharedCheck_5931_;
goto v_resetjp_5925_;
}
else
{
lean_inc(v_a_5924_);
lean_dec(v___x_5911_);
v___x_5926_ = lean_box(0);
v_isShared_5927_ = v_isSharedCheck_5931_;
goto v_resetjp_5925_;
}
v_resetjp_5925_:
{
lean_object* v___x_5929_; 
if (v_isShared_5927_ == 0)
{
v___x_5929_ = v___x_5926_;
goto v_reusejp_5928_;
}
else
{
lean_object* v_reuseFailAlloc_5930_; 
v_reuseFailAlloc_5930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5930_, 0, v_a_5924_);
v___x_5929_ = v_reuseFailAlloc_5930_;
goto v_reusejp_5928_;
}
v_reusejp_5928_:
{
return v___x_5929_;
}
}
}
}
v___jp_5932_:
{
size_t v_sz_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; uint8_t v___x_5944_; 
v_sz_5940_ = lean_array_size(v___y_5939_);
v___x_5941_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_5940_, v___y_5933_, v___y_5939_);
v___x_5942_ = lean_array_get_size(v___y_5937_);
v___x_5943_ = lean_unsigned_to_nat(0u);
v___x_5944_ = lean_nat_dec_eq(v___x_5942_, v___x_5943_);
if (v___x_5944_ == 0)
{
v___y_5903_ = v___y_5933_;
v___y_5904_ = v___y_5934_;
v___y_5905_ = v___y_5935_;
v___y_5906_ = v___y_5936_;
v___y_5907_ = v___y_5937_;
v___y_5908_ = v___x_5941_;
v___y_5909_ = v___y_5938_;
v___y_5910_ = v___x_5944_;
goto v___jp_5902_;
}
else
{
lean_object* v___x_5945_; uint8_t v___x_5946_; 
v___x_5945_ = lean_array_get_size(v___x_5941_);
v___x_5946_ = lean_nat_dec_eq(v___x_5945_, v___x_5943_);
if (v___x_5946_ == 0)
{
v___y_5903_ = v___y_5933_;
v___y_5904_ = v___y_5934_;
v___y_5905_ = v___y_5935_;
v___y_5906_ = v___y_5936_;
v___y_5907_ = v___y_5937_;
v___y_5908_ = v___x_5941_;
v___y_5909_ = v___y_5938_;
v___y_5910_ = v___x_5946_;
goto v___jp_5902_;
}
else
{
lean_object* v___x_5947_; lean_object* v___x_5948_; 
lean_dec_ref(v___x_5941_);
lean_dec_ref(v___y_5938_);
lean_dec_ref(v___y_5937_);
lean_dec_ref(v___y_5936_);
lean_dec_ref(v___y_5935_);
lean_dec_ref(v___y_5934_);
lean_dec(v_a_5810_);
lean_dec(v_a_5800_);
v___x_5947_ = ((lean_object*)(l_Lake_Check_runComparator___closed__5));
v___x_5948_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5947_);
return v___x_5948_;
}
}
}
v___jp_5949_:
{
lean_object* v___x_5951_; 
v___x_5951_ = l_IO_FS_readFile(v___y_5950_);
if (lean_obj_tag(v___x_5951_) == 0)
{
lean_object* v_a_5952_; lean_object* v___x_5953_; 
v_a_5952_ = lean_ctor_get(v___x_5951_, 0);
lean_inc(v_a_5952_);
lean_dec_ref_known(v___x_5951_, 1);
v___x_5953_ = l_Lean_Json_parse(v_a_5952_);
if (lean_obj_tag(v___x_5953_) == 0)
{
lean_object* v_a_5954_; 
lean_dec(v_a_5810_);
lean_dec(v_a_5800_);
v_a_5954_ = lean_ctor_get(v___x_5953_, 0);
lean_inc(v_a_5954_);
lean_dec_ref_known(v___x_5953_, 1);
v___y_5768_ = v___y_5950_;
v_a_5769_ = v_a_5954_;
goto v___jp_5767_;
}
else
{
lean_object* v_a_5955_; lean_object* v___x_5956_; 
v_a_5955_ = lean_ctor_get(v___x_5953_, 0);
lean_inc(v_a_5955_);
lean_dec_ref_known(v___x_5953_, 1);
v___x_5956_ = l_Lake_Check_instFromJsonConfig_fromJson(v_a_5955_);
if (lean_obj_tag(v___x_5956_) == 0)
{
lean_object* v_a_5957_; 
lean_dec(v_a_5810_);
lean_dec(v_a_5800_);
v_a_5957_ = lean_ctor_get(v___x_5956_, 0);
lean_inc(v_a_5957_);
lean_dec_ref_known(v___x_5956_, 1);
v___y_5768_ = v___y_5950_;
v_a_5769_ = v_a_5957_;
goto v___jp_5767_;
}
else
{
lean_object* v_a_5958_; lean_object* v_challenge__module_5959_; lean_object* v_solution__module_5960_; lean_object* v_theorem__names_5961_; lean_object* v_definition__names_5962_; lean_object* v_permitted__axioms_5963_; size_t v_sz_5964_; size_t v___x_5965_; lean_object* v___x_5966_; 
v_a_5958_ = lean_ctor_get(v___x_5956_, 0);
lean_inc(v_a_5958_);
lean_dec_ref_known(v___x_5956_, 1);
v_challenge__module_5959_ = lean_ctor_get(v_a_5958_, 0);
lean_inc_ref(v_challenge__module_5959_);
v_solution__module_5960_ = lean_ctor_get(v_a_5958_, 1);
lean_inc_ref(v_solution__module_5960_);
v_theorem__names_5961_ = lean_ctor_get(v_a_5958_, 2);
v_definition__names_5962_ = lean_ctor_get(v_a_5958_, 3);
v_permitted__axioms_5963_ = lean_ctor_get(v_a_5958_, 4);
lean_inc_ref(v_permitted__axioms_5963_);
v_sz_5964_ = lean_array_size(v_theorem__names_5961_);
v___x_5965_ = ((size_t)0ULL);
lean_inc_ref(v_theorem__names_5961_);
v___x_5966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_5964_, v___x_5965_, v_theorem__names_5961_);
if (lean_obj_tag(v_definition__names_5962_) == 0)
{
lean_object* v___x_5967_; 
v___x_5967_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___y_5933_ = v___x_5965_;
v___y_5934_ = v_permitted__axioms_5963_;
v___y_5935_ = v_a_5958_;
v___y_5936_ = v_challenge__module_5959_;
v___y_5937_ = v___x_5966_;
v___y_5938_ = v_solution__module_5960_;
v___y_5939_ = v___x_5967_;
goto v___jp_5932_;
}
else
{
lean_object* v_val_5968_; 
v_val_5968_ = lean_ctor_get(v_definition__names_5962_, 0);
lean_inc(v_val_5968_);
v___y_5933_ = v___x_5965_;
v___y_5934_ = v_permitted__axioms_5963_;
v___y_5935_ = v_a_5958_;
v___y_5936_ = v_challenge__module_5959_;
v___y_5937_ = v___x_5966_;
v___y_5938_ = v_solution__module_5960_;
v___y_5939_ = v_val_5968_;
goto v___jp_5932_;
}
}
}
}
else
{
lean_object* v_a_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; 
lean_dec(v_a_5810_);
lean_dec(v_a_5800_);
v_a_5969_ = lean_ctor_get(v___x_5951_, 0);
lean_inc(v_a_5969_);
lean_dec_ref_known(v___x_5951_, 1);
v___x_5970_ = ((lean_object*)(l_Lake_Check_runComparator___closed__6));
v___x_5971_ = lean_io_error_to_string(v_a_5969_);
v___x_5972_ = lean_string_append(v___x_5970_, v___x_5971_);
lean_dec_ref(v___x_5971_);
v___x_5973_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5972_);
lean_dec_ref(v___x_5972_);
return v___x_5973_;
}
}
}
}
}
else
{
lean_object* v_a_5977_; lean_object* v___x_5979_; uint8_t v_isShared_5980_; uint8_t v_isSharedCheck_5984_; 
lean_dec(v_a_5800_);
v_a_5977_ = lean_ctor_get(v___x_5801_, 0);
v_isSharedCheck_5984_ = !lean_is_exclusive(v___x_5801_);
if (v_isSharedCheck_5984_ == 0)
{
v___x_5979_ = v___x_5801_;
v_isShared_5980_ = v_isSharedCheck_5984_;
goto v_resetjp_5978_;
}
else
{
lean_inc(v_a_5977_);
lean_dec(v___x_5801_);
v___x_5979_ = lean_box(0);
v_isShared_5980_ = v_isSharedCheck_5984_;
goto v_resetjp_5978_;
}
v_resetjp_5978_:
{
lean_object* v___x_5982_; 
if (v_isShared_5980_ == 0)
{
v___x_5982_ = v___x_5979_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_5983_; 
v_reuseFailAlloc_5983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5983_, 0, v_a_5977_);
v___x_5982_ = v_reuseFailAlloc_5983_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
return v___x_5982_;
}
}
}
}
}
}
else
{
lean_object* v_a_5986_; lean_object* v___x_5988_; uint8_t v_isShared_5989_; uint8_t v_isSharedCheck_5993_; 
lean_dec_ref(v_projectDir_5731_);
lean_dec_ref(v_lean_5729_);
v_a_5986_ = lean_ctor_get(v___x_5791_, 0);
v_isSharedCheck_5993_ = !lean_is_exclusive(v___x_5791_);
if (v_isSharedCheck_5993_ == 0)
{
v___x_5988_ = v___x_5791_;
v_isShared_5989_ = v_isSharedCheck_5993_;
goto v_resetjp_5987_;
}
else
{
lean_inc(v_a_5986_);
lean_dec(v___x_5791_);
v___x_5988_ = lean_box(0);
v_isShared_5989_ = v_isSharedCheck_5993_;
goto v_resetjp_5987_;
}
v_resetjp_5987_:
{
lean_object* v___x_5991_; 
if (v_isShared_5989_ == 0)
{
v___x_5991_ = v___x_5988_;
goto v_reusejp_5990_;
}
else
{
lean_object* v_reuseFailAlloc_5992_; 
v_reuseFailAlloc_5992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5992_, 0, v_a_5986_);
v___x_5991_ = v_reuseFailAlloc_5992_;
goto v_reusejp_5990_;
}
v_reusejp_5990_:
{
return v___x_5991_;
}
}
}
v___jp_5733_:
{
lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; 
v___x_5735_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_5736_ = lean_io_error_to_string(v_a_5734_);
v___x_5737_ = lean_string_append(v___x_5735_, v___x_5736_);
lean_dec_ref(v___x_5736_);
v___x_5738_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_5737_);
if (lean_obj_tag(v___x_5738_) == 0)
{
lean_object* v___x_5740_; uint8_t v_isShared_5741_; uint8_t v_isSharedCheck_5746_; 
v_isSharedCheck_5746_ = !lean_is_exclusive(v___x_5738_);
if (v_isSharedCheck_5746_ == 0)
{
lean_object* v_unused_5747_; 
v_unused_5747_ = lean_ctor_get(v___x_5738_, 0);
lean_dec(v_unused_5747_);
v___x_5740_ = v___x_5738_;
v_isShared_5741_ = v_isSharedCheck_5746_;
goto v_resetjp_5739_;
}
else
{
lean_dec(v___x_5738_);
v___x_5740_ = lean_box(0);
v_isShared_5741_ = v_isSharedCheck_5746_;
goto v_resetjp_5739_;
}
v_resetjp_5739_:
{
lean_object* v___x_5742_; lean_object* v___x_5744_; 
v___x_5742_ = l_Lake_Check_runComparator___boxed__const__1;
if (v_isShared_5741_ == 0)
{
lean_ctor_set(v___x_5740_, 0, v___x_5742_);
v___x_5744_ = v___x_5740_;
goto v_reusejp_5743_;
}
else
{
lean_object* v_reuseFailAlloc_5745_; 
v_reuseFailAlloc_5745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5745_, 0, v___x_5742_);
v___x_5744_ = v_reuseFailAlloc_5745_;
goto v_reusejp_5743_;
}
v_reusejp_5743_:
{
return v___x_5744_;
}
}
}
else
{
lean_object* v_a_5748_; lean_object* v___x_5750_; uint8_t v_isShared_5751_; uint8_t v_isSharedCheck_5755_; 
v_a_5748_ = lean_ctor_get(v___x_5738_, 0);
v_isSharedCheck_5755_ = !lean_is_exclusive(v___x_5738_);
if (v_isSharedCheck_5755_ == 0)
{
v___x_5750_ = v___x_5738_;
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
else
{
lean_inc(v_a_5748_);
lean_dec(v___x_5738_);
v___x_5750_ = lean_box(0);
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
v_resetjp_5749_:
{
lean_object* v___x_5753_; 
if (v_isShared_5751_ == 0)
{
v___x_5753_ = v___x_5750_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_a_5748_);
v___x_5753_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
return v___x_5753_;
}
}
}
}
v___jp_5756_:
{
lean_object* v_a_5758_; lean_object* v___x_5760_; uint8_t v_isShared_5761_; uint8_t v_isSharedCheck_5766_; 
v_a_5758_ = lean_ctor_get(v___y_5757_, 0);
v_isSharedCheck_5766_ = !lean_is_exclusive(v___y_5757_);
if (v_isSharedCheck_5766_ == 0)
{
v___x_5760_ = v___y_5757_;
v_isShared_5761_ = v_isSharedCheck_5766_;
goto v_resetjp_5759_;
}
else
{
lean_inc(v_a_5758_);
lean_dec(v___y_5757_);
v___x_5760_ = lean_box(0);
v_isShared_5761_ = v_isSharedCheck_5766_;
goto v_resetjp_5759_;
}
v_resetjp_5759_:
{
lean_object* v_a_5762_; lean_object* v___x_5764_; 
v_a_5762_ = lean_ctor_get(v_a_5758_, 0);
lean_inc(v_a_5762_);
lean_dec(v_a_5758_);
if (v_isShared_5761_ == 0)
{
lean_ctor_set(v___x_5760_, 0, v_a_5762_);
v___x_5764_ = v___x_5760_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5765_; 
v_reuseFailAlloc_5765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_a_5762_);
v___x_5764_ = v_reuseFailAlloc_5765_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
return v___x_5764_;
}
}
}
v___jp_5767_:
{
lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; 
v___x_5770_ = ((lean_object*)(l_Lake_Check_runComparator___closed__0));
v___x_5771_ = lean_string_append(v___x_5770_, v___y_5768_);
v___x_5772_ = ((lean_object*)(l_Lake_Check_runComparator___closed__1));
v___x_5773_ = lean_string_append(v___x_5771_, v___x_5772_);
v___x_5774_ = lean_string_append(v___x_5773_, v_a_5769_);
lean_dec_ref(v_a_5769_);
v___x_5775_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5774_);
lean_dec_ref(v___x_5774_);
return v___x_5775_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___boxed(lean_object* v_configFile_x3f_5994_, lean_object* v_challengeFromExport_x3f_5995_, lean_object* v_solutionFromExport_x3f_5996_, lean_object* v_paranoid_5997_, lean_object* v_inadvisablyNoSandbox_5998_, lean_object* v_lean_5999_, lean_object* v_lake_6000_, lean_object* v_projectDir_6001_, lean_object* v_a_6002_){
_start:
{
uint8_t v_paranoid_boxed_6003_; uint8_t v_inadvisablyNoSandbox_boxed_6004_; lean_object* v_res_6005_; 
v_paranoid_boxed_6003_ = lean_unbox(v_paranoid_5997_);
v_inadvisablyNoSandbox_boxed_6004_ = lean_unbox(v_inadvisablyNoSandbox_5998_);
v_res_6005_ = l_Lake_Check_runComparator(v_configFile_x3f_5994_, v_challengeFromExport_x3f_5995_, v_solutionFromExport_x3f_5996_, v_paranoid_boxed_6003_, v_inadvisablyNoSandbox_boxed_6004_, v_lean_5999_, v_lake_6000_, v_projectDir_6001_);
lean_dec_ref(v_lake_6000_);
lean_dec(v_configFile_x3f_5994_);
return v_res_6005_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runCheck(lean_object* v_fromExport_x3f_6006_, uint8_t v_paranoid_6007_, uint8_t v_inadvisablyNoSandbox_6008_, lean_object* v_lean_6009_, lean_object* v_lake_6010_, lean_object* v_projectDir_6011_){
_start:
{
lean_object* v___x_6013_; lean_object* v___x_6014_; uint8_t v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; 
v___x_6013_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__0));
v___x_6014_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_6015_ = 0;
v___x_6016_ = lean_box(v___x_6015_);
v___x_6017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
lean_ctor_set(v___x_6017_, 1, v_fromExport_x3f_6006_);
v___x_6018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6018_, 0, v___x_6014_);
lean_ctor_set(v___x_6018_, 1, v___x_6017_);
v___x_6019_ = lean_unsigned_to_nat(1u);
v___x_6020_ = lean_mk_empty_array_with_capacity(v___x_6019_);
v___x_6021_ = lean_array_push(v___x_6020_, v___x_6018_);
v___x_6022_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(v___x_6013_, v___x_6021_);
lean_dec_ref(v___x_6021_);
if (lean_obj_tag(v___x_6022_) == 0)
{
lean_object* v_a_6023_; lean_object* v___x_6025_; uint8_t v_isShared_6026_; uint8_t v_isSharedCheck_6132_; 
v_a_6023_ = lean_ctor_get(v___x_6022_, 0);
v_isSharedCheck_6132_ = !lean_is_exclusive(v___x_6022_);
if (v_isSharedCheck_6132_ == 0)
{
v___x_6025_ = v___x_6022_;
v_isShared_6026_ = v_isSharedCheck_6132_;
goto v_resetjp_6024_;
}
else
{
lean_inc(v_a_6023_);
lean_dec(v___x_6022_);
v___x_6025_ = lean_box(0);
v_isShared_6026_ = v_isSharedCheck_6132_;
goto v_resetjp_6024_;
}
v_resetjp_6024_:
{
if (lean_obj_tag(v_a_6023_) == 0)
{
lean_object* v_a_6027_; lean_object* v___x_6029_; 
lean_dec_ref(v_projectDir_6011_);
lean_dec_ref(v_lean_6009_);
v_a_6027_ = lean_ctor_get(v_a_6023_, 0);
lean_inc(v_a_6027_);
lean_dec_ref_known(v_a_6023_, 1);
if (v_isShared_6026_ == 0)
{
lean_ctor_set(v___x_6025_, 0, v_a_6027_);
v___x_6029_ = v___x_6025_;
goto v_reusejp_6028_;
}
else
{
lean_object* v_reuseFailAlloc_6030_; 
v_reuseFailAlloc_6030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6030_, 0, v_a_6027_);
v___x_6029_ = v_reuseFailAlloc_6030_;
goto v_reusejp_6028_;
}
v_reusejp_6028_:
{
return v___x_6029_;
}
}
else
{
lean_object* v_a_6031_; lean_object* v___x_6032_; 
lean_del_object(v___x_6025_);
v_a_6031_ = lean_ctor_get(v_a_6023_, 0);
lean_inc_n(v_a_6031_, 2);
lean_dec_ref_known(v_a_6023_, 1);
v___x_6032_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_6013_, v_paranoid_6007_, v_inadvisablyNoSandbox_6008_, v_lean_6009_, v_lake_6010_, v_projectDir_6011_, v_a_6031_);
if (lean_obj_tag(v___x_6032_) == 0)
{
lean_object* v_a_6033_; lean_object* v___x_6035_; uint8_t v_isShared_6036_; uint8_t v_isSharedCheck_6123_; 
v_a_6033_ = lean_ctor_get(v___x_6032_, 0);
v_isSharedCheck_6123_ = !lean_is_exclusive(v___x_6032_);
if (v_isSharedCheck_6123_ == 0)
{
v___x_6035_ = v___x_6032_;
v_isShared_6036_ = v_isSharedCheck_6123_;
goto v_resetjp_6034_;
}
else
{
lean_inc(v_a_6033_);
lean_dec(v___x_6032_);
v___x_6035_ = lean_box(0);
v_isShared_6036_ = v_isSharedCheck_6123_;
goto v_resetjp_6034_;
}
v_resetjp_6034_:
{
if (lean_obj_tag(v_a_6033_) == 0)
{
lean_object* v_a_6037_; lean_object* v___x_6039_; 
lean_dec(v_a_6031_);
v_a_6037_ = lean_ctor_get(v_a_6033_, 0);
lean_inc(v_a_6037_);
lean_dec_ref_known(v_a_6033_, 1);
if (v_isShared_6036_ == 0)
{
lean_ctor_set(v___x_6035_, 0, v_a_6037_);
v___x_6039_ = v___x_6035_;
goto v_reusejp_6038_;
}
else
{
lean_object* v_reuseFailAlloc_6040_; 
v_reuseFailAlloc_6040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6040_, 0, v_a_6037_);
v___x_6039_ = v_reuseFailAlloc_6040_;
goto v_reusejp_6038_;
}
v_reusejp_6038_:
{
return v___x_6039_;
}
}
else
{
lean_object* v_a_6041_; uint8_t v___x_6103_; 
lean_del_object(v___x_6035_);
v_a_6041_ = lean_ctor_get(v_a_6033_, 0);
lean_inc(v_a_6041_);
lean_dec_ref_known(v_a_6033_, 1);
v___x_6103_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_a_6031_, v___x_6015_);
lean_dec(v_a_6031_);
if (v___x_6103_ == 0)
{
lean_object* v_projectDir_6104_; lean_object* v___x_6105_; 
v_projectDir_6104_ = lean_ctor_get(v_a_6041_, 0);
lean_inc_ref(v_projectDir_6104_);
v___x_6105_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_6013_, v_projectDir_6104_);
if (lean_obj_tag(v___x_6105_) == 0)
{
lean_object* v_a_6106_; lean_object* v___x_6108_; uint8_t v_isShared_6109_; uint8_t v_isSharedCheck_6114_; 
v_a_6106_ = lean_ctor_get(v___x_6105_, 0);
v_isSharedCheck_6114_ = !lean_is_exclusive(v___x_6105_);
if (v_isSharedCheck_6114_ == 0)
{
v___x_6108_ = v___x_6105_;
v_isShared_6109_ = v_isSharedCheck_6114_;
goto v_resetjp_6107_;
}
else
{
lean_inc(v_a_6106_);
lean_dec(v___x_6105_);
v___x_6108_ = lean_box(0);
v_isShared_6109_ = v_isSharedCheck_6114_;
goto v_resetjp_6107_;
}
v_resetjp_6107_:
{
if (lean_obj_tag(v_a_6106_) == 1)
{
lean_object* v_val_6110_; lean_object* v___x_6112_; 
lean_dec(v_a_6041_);
v_val_6110_ = lean_ctor_get(v_a_6106_, 0);
lean_inc(v_val_6110_);
lean_dec_ref_known(v_a_6106_, 1);
if (v_isShared_6109_ == 0)
{
lean_ctor_set(v___x_6108_, 0, v_val_6110_);
v___x_6112_ = v___x_6108_;
goto v_reusejp_6111_;
}
else
{
lean_object* v_reuseFailAlloc_6113_; 
v_reuseFailAlloc_6113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6113_, 0, v_val_6110_);
v___x_6112_ = v_reuseFailAlloc_6113_;
goto v_reusejp_6111_;
}
v_reusejp_6111_:
{
return v___x_6112_;
}
}
else
{
lean_del_object(v___x_6108_);
lean_dec(v_a_6106_);
goto v___jp_6042_;
}
}
}
else
{
lean_object* v_a_6115_; lean_object* v___x_6117_; uint8_t v_isShared_6118_; uint8_t v_isSharedCheck_6122_; 
lean_dec(v_a_6041_);
v_a_6115_ = lean_ctor_get(v___x_6105_, 0);
v_isSharedCheck_6122_ = !lean_is_exclusive(v___x_6105_);
if (v_isSharedCheck_6122_ == 0)
{
v___x_6117_ = v___x_6105_;
v_isShared_6118_ = v_isSharedCheck_6122_;
goto v_resetjp_6116_;
}
else
{
lean_inc(v_a_6115_);
lean_dec(v___x_6105_);
v___x_6117_ = lean_box(0);
v_isShared_6118_ = v_isSharedCheck_6122_;
goto v_resetjp_6116_;
}
v_resetjp_6116_:
{
lean_object* v___x_6120_; 
if (v_isShared_6118_ == 0)
{
v___x_6120_ = v___x_6117_;
goto v_reusejp_6119_;
}
else
{
lean_object* v_reuseFailAlloc_6121_; 
v_reuseFailAlloc_6121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6121_, 0, v_a_6115_);
v___x_6120_ = v_reuseFailAlloc_6121_;
goto v_reusejp_6119_;
}
v_reusejp_6119_:
{
return v___x_6120_;
}
}
}
}
else
{
goto v___jp_6042_;
}
v___jp_6042_:
{
lean_object* v_projectDir_6043_; lean_object* v_theoremNames_6044_; lean_object* v_definitionNames_6045_; lean_object* v_leanPrefix_6046_; lean_object* v_leanPath_6047_; lean_object* v_binPath_6048_; lean_object* v_whichSandbox_6049_; lean_object* v_whichLake_6050_; lean_object* v_lakeHome_6051_; lean_object* v_whichLean4Export_6052_; lean_object* v_whichLeanChecker_6053_; lean_object* v_whichEnvBin_6054_; lean_object* v_bundledKernels_6055_; lean_object* v_moduleStore_6056_; lean_object* v___x_6058_; uint8_t v_isShared_6059_; uint8_t v_isSharedCheck_6098_; 
v_projectDir_6043_ = lean_ctor_get(v_a_6041_, 0);
v_theoremNames_6044_ = lean_ctor_get(v_a_6041_, 3);
v_definitionNames_6045_ = lean_ctor_get(v_a_6041_, 4);
v_leanPrefix_6046_ = lean_ctor_get(v_a_6041_, 6);
v_leanPath_6047_ = lean_ctor_get(v_a_6041_, 7);
v_binPath_6048_ = lean_ctor_get(v_a_6041_, 8);
v_whichSandbox_6049_ = lean_ctor_get(v_a_6041_, 9);
v_whichLake_6050_ = lean_ctor_get(v_a_6041_, 10);
v_lakeHome_6051_ = lean_ctor_get(v_a_6041_, 11);
v_whichLean4Export_6052_ = lean_ctor_get(v_a_6041_, 12);
v_whichLeanChecker_6053_ = lean_ctor_get(v_a_6041_, 13);
v_whichEnvBin_6054_ = lean_ctor_get(v_a_6041_, 14);
v_bundledKernels_6055_ = lean_ctor_get(v_a_6041_, 16);
v_moduleStore_6056_ = lean_ctor_get(v_a_6041_, 17);
v_isSharedCheck_6098_ = !lean_is_exclusive(v_a_6041_);
if (v_isSharedCheck_6098_ == 0)
{
lean_object* v_unused_6099_; lean_object* v_unused_6100_; lean_object* v_unused_6101_; lean_object* v_unused_6102_; 
v_unused_6099_ = lean_ctor_get(v_a_6041_, 15);
lean_dec(v_unused_6099_);
v_unused_6100_ = lean_ctor_get(v_a_6041_, 5);
lean_dec(v_unused_6100_);
v_unused_6101_ = lean_ctor_get(v_a_6041_, 2);
lean_dec(v_unused_6101_);
v_unused_6102_ = lean_ctor_get(v_a_6041_, 1);
lean_dec(v_unused_6102_);
v___x_6058_ = v_a_6041_;
v_isShared_6059_ = v_isSharedCheck_6098_;
goto v_resetjp_6057_;
}
else
{
lean_inc(v_moduleStore_6056_);
lean_inc(v_bundledKernels_6055_);
lean_inc(v_whichEnvBin_6054_);
lean_inc(v_whichLeanChecker_6053_);
lean_inc(v_whichLean4Export_6052_);
lean_inc(v_lakeHome_6051_);
lean_inc(v_whichLake_6050_);
lean_inc(v_whichSandbox_6049_);
lean_inc(v_binPath_6048_);
lean_inc(v_leanPath_6047_);
lean_inc(v_leanPrefix_6046_);
lean_inc(v_definitionNames_6045_);
lean_inc(v_theoremNames_6044_);
lean_inc(v_projectDir_6043_);
lean_dec(v_a_6041_);
v___x_6058_ = lean_box(0);
v_isShared_6059_ = v_isSharedCheck_6098_;
goto v_resetjp_6057_;
}
v_resetjp_6057_:
{
lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6064_; 
v___x_6060_ = lean_box(1);
v___x_6061_ = lean_box(0);
v___x_6062_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms));
if (v_isShared_6059_ == 0)
{
lean_ctor_set(v___x_6058_, 15, v___x_6060_);
lean_ctor_set(v___x_6058_, 5, v___x_6062_);
lean_ctor_set(v___x_6058_, 2, v___x_6061_);
lean_ctor_set(v___x_6058_, 1, v___x_6061_);
v___x_6064_ = v___x_6058_;
goto v_reusejp_6063_;
}
else
{
lean_object* v_reuseFailAlloc_6097_; 
v_reuseFailAlloc_6097_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_6097_, 0, v_projectDir_6043_);
lean_ctor_set(v_reuseFailAlloc_6097_, 1, v___x_6061_);
lean_ctor_set(v_reuseFailAlloc_6097_, 2, v___x_6061_);
lean_ctor_set(v_reuseFailAlloc_6097_, 3, v_theoremNames_6044_);
lean_ctor_set(v_reuseFailAlloc_6097_, 4, v_definitionNames_6045_);
lean_ctor_set(v_reuseFailAlloc_6097_, 5, v___x_6062_);
lean_ctor_set(v_reuseFailAlloc_6097_, 6, v_leanPrefix_6046_);
lean_ctor_set(v_reuseFailAlloc_6097_, 7, v_leanPath_6047_);
lean_ctor_set(v_reuseFailAlloc_6097_, 8, v_binPath_6048_);
lean_ctor_set(v_reuseFailAlloc_6097_, 9, v_whichSandbox_6049_);
lean_ctor_set(v_reuseFailAlloc_6097_, 10, v_whichLake_6050_);
lean_ctor_set(v_reuseFailAlloc_6097_, 11, v_lakeHome_6051_);
lean_ctor_set(v_reuseFailAlloc_6097_, 12, v_whichLean4Export_6052_);
lean_ctor_set(v_reuseFailAlloc_6097_, 13, v_whichLeanChecker_6053_);
lean_ctor_set(v_reuseFailAlloc_6097_, 14, v_whichEnvBin_6054_);
lean_ctor_set(v_reuseFailAlloc_6097_, 15, v___x_6060_);
lean_ctor_set(v_reuseFailAlloc_6097_, 16, v_bundledKernels_6055_);
lean_ctor_set(v_reuseFailAlloc_6097_, 17, v_moduleStore_6056_);
v___x_6064_ = v_reuseFailAlloc_6097_;
goto v_reusejp_6063_;
}
v_reusejp_6063_:
{
lean_object* v___x_6065_; 
v___x_6065_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v___x_6064_);
lean_dec_ref(v___x_6064_);
if (lean_obj_tag(v___x_6065_) == 0)
{
lean_object* v___x_6067_; uint8_t v_isShared_6068_; uint8_t v_isSharedCheck_6073_; 
v_isSharedCheck_6073_ = !lean_is_exclusive(v___x_6065_);
if (v_isSharedCheck_6073_ == 0)
{
lean_object* v_unused_6074_; 
v_unused_6074_ = lean_ctor_get(v___x_6065_, 0);
lean_dec(v_unused_6074_);
v___x_6067_ = v___x_6065_;
v_isShared_6068_ = v_isSharedCheck_6073_;
goto v_resetjp_6066_;
}
else
{
lean_dec(v___x_6065_);
v___x_6067_ = lean_box(0);
v_isShared_6068_ = v_isSharedCheck_6073_;
goto v_resetjp_6066_;
}
v_resetjp_6066_:
{
lean_object* v___x_6069_; lean_object* v___x_6071_; 
v___x_6069_ = l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1;
if (v_isShared_6068_ == 0)
{
lean_ctor_set(v___x_6067_, 0, v___x_6069_);
v___x_6071_ = v___x_6067_;
goto v_reusejp_6070_;
}
else
{
lean_object* v_reuseFailAlloc_6072_; 
v_reuseFailAlloc_6072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6072_, 0, v___x_6069_);
v___x_6071_ = v_reuseFailAlloc_6072_;
goto v_reusejp_6070_;
}
v_reusejp_6070_:
{
return v___x_6071_;
}
}
}
else
{
lean_object* v_a_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; 
v_a_6075_ = lean_ctor_get(v___x_6065_, 0);
lean_inc(v_a_6075_);
lean_dec_ref_known(v___x_6065_, 1);
v___x_6076_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_6077_ = lean_io_error_to_string(v_a_6075_);
v___x_6078_ = lean_string_append(v___x_6076_, v___x_6077_);
lean_dec_ref(v___x_6077_);
v___x_6079_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_6078_);
if (lean_obj_tag(v___x_6079_) == 0)
{
lean_object* v___x_6081_; uint8_t v_isShared_6082_; uint8_t v_isSharedCheck_6087_; 
v_isSharedCheck_6087_ = !lean_is_exclusive(v___x_6079_);
if (v_isSharedCheck_6087_ == 0)
{
lean_object* v_unused_6088_; 
v_unused_6088_ = lean_ctor_get(v___x_6079_, 0);
lean_dec(v_unused_6088_);
v___x_6081_ = v___x_6079_;
v_isShared_6082_ = v_isSharedCheck_6087_;
goto v_resetjp_6080_;
}
else
{
lean_dec(v___x_6079_);
v___x_6081_ = lean_box(0);
v_isShared_6082_ = v_isSharedCheck_6087_;
goto v_resetjp_6080_;
}
v_resetjp_6080_:
{
lean_object* v___x_6083_; lean_object* v___x_6085_; 
v___x_6083_ = l_Lake_Check_runComparator___boxed__const__1;
if (v_isShared_6082_ == 0)
{
lean_ctor_set(v___x_6081_, 0, v___x_6083_);
v___x_6085_ = v___x_6081_;
goto v_reusejp_6084_;
}
else
{
lean_object* v_reuseFailAlloc_6086_; 
v_reuseFailAlloc_6086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6086_, 0, v___x_6083_);
v___x_6085_ = v_reuseFailAlloc_6086_;
goto v_reusejp_6084_;
}
v_reusejp_6084_:
{
return v___x_6085_;
}
}
}
else
{
lean_object* v_a_6089_; lean_object* v___x_6091_; uint8_t v_isShared_6092_; uint8_t v_isSharedCheck_6096_; 
v_a_6089_ = lean_ctor_get(v___x_6079_, 0);
v_isSharedCheck_6096_ = !lean_is_exclusive(v___x_6079_);
if (v_isSharedCheck_6096_ == 0)
{
v___x_6091_ = v___x_6079_;
v_isShared_6092_ = v_isSharedCheck_6096_;
goto v_resetjp_6090_;
}
else
{
lean_inc(v_a_6089_);
lean_dec(v___x_6079_);
v___x_6091_ = lean_box(0);
v_isShared_6092_ = v_isSharedCheck_6096_;
goto v_resetjp_6090_;
}
v_resetjp_6090_:
{
lean_object* v___x_6094_; 
if (v_isShared_6092_ == 0)
{
v___x_6094_ = v___x_6091_;
goto v_reusejp_6093_;
}
else
{
lean_object* v_reuseFailAlloc_6095_; 
v_reuseFailAlloc_6095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6095_, 0, v_a_6089_);
v___x_6094_ = v_reuseFailAlloc_6095_;
goto v_reusejp_6093_;
}
v_reusejp_6093_:
{
return v___x_6094_;
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
lean_object* v_a_6124_; lean_object* v___x_6126_; uint8_t v_isShared_6127_; uint8_t v_isSharedCheck_6131_; 
lean_dec(v_a_6031_);
v_a_6124_ = lean_ctor_get(v___x_6032_, 0);
v_isSharedCheck_6131_ = !lean_is_exclusive(v___x_6032_);
if (v_isSharedCheck_6131_ == 0)
{
v___x_6126_ = v___x_6032_;
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
else
{
lean_inc(v_a_6124_);
lean_dec(v___x_6032_);
v___x_6126_ = lean_box(0);
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
v_resetjp_6125_:
{
lean_object* v___x_6129_; 
if (v_isShared_6127_ == 0)
{
v___x_6129_ = v___x_6126_;
goto v_reusejp_6128_;
}
else
{
lean_object* v_reuseFailAlloc_6130_; 
v_reuseFailAlloc_6130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6130_, 0, v_a_6124_);
v___x_6129_ = v_reuseFailAlloc_6130_;
goto v_reusejp_6128_;
}
v_reusejp_6128_:
{
return v___x_6129_;
}
}
}
}
}
}
else
{
lean_object* v_a_6133_; lean_object* v___x_6135_; uint8_t v_isShared_6136_; uint8_t v_isSharedCheck_6140_; 
lean_dec_ref(v_projectDir_6011_);
lean_dec_ref(v_lean_6009_);
v_a_6133_ = lean_ctor_get(v___x_6022_, 0);
v_isSharedCheck_6140_ = !lean_is_exclusive(v___x_6022_);
if (v_isSharedCheck_6140_ == 0)
{
v___x_6135_ = v___x_6022_;
v_isShared_6136_ = v_isSharedCheck_6140_;
goto v_resetjp_6134_;
}
else
{
lean_inc(v_a_6133_);
lean_dec(v___x_6022_);
v___x_6135_ = lean_box(0);
v_isShared_6136_ = v_isSharedCheck_6140_;
goto v_resetjp_6134_;
}
v_resetjp_6134_:
{
lean_object* v___x_6138_; 
if (v_isShared_6136_ == 0)
{
v___x_6138_ = v___x_6135_;
goto v_reusejp_6137_;
}
else
{
lean_object* v_reuseFailAlloc_6139_; 
v_reuseFailAlloc_6139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6139_, 0, v_a_6133_);
v___x_6138_ = v_reuseFailAlloc_6139_;
goto v_reusejp_6137_;
}
v_reusejp_6137_:
{
return v___x_6138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runCheck___boxed(lean_object* v_fromExport_x3f_6141_, lean_object* v_paranoid_6142_, lean_object* v_inadvisablyNoSandbox_6143_, lean_object* v_lean_6144_, lean_object* v_lake_6145_, lean_object* v_projectDir_6146_, lean_object* v_a_6147_){
_start:
{
uint8_t v_paranoid_boxed_6148_; uint8_t v_inadvisablyNoSandbox_boxed_6149_; lean_object* v_res_6150_; 
v_paranoid_boxed_6148_ = lean_unbox(v_paranoid_6142_);
v_inadvisablyNoSandbox_boxed_6149_ = lean_unbox(v_inadvisablyNoSandbox_6143_);
v_res_6150_ = l_Lake_Check_runCheck(v_fromExport_x3f_6141_, v_paranoid_boxed_6148_, v_inadvisablyNoSandbox_boxed_6149_, v_lean_6144_, v_lake_6145_, v_projectDir_6146_);
lean_dec_ref(v_lake_6145_);
return v_res_6150_;
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
