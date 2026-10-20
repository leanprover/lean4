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
lean_object* lean_obj_tag_nat(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_noSandbox_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_noSandbox_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_path_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_path_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
return v_k_6_;
}
else
{
lean_object* v_path_7_; lean_object* v___x_8_; 
v_path_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_path_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_path_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_noSandbox_elim___redArg(lean_object* v_t_21_, lean_object* v_noSandbox_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(v_t_21_, v_noSandbox_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_noSandbox_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_noSandbox_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(v_t_25_, v_noSandbox_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_path_elim___redArg(lean_object* v_t_29_, lean_object* v_path_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(v_t_29_, v_path_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_path_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_path_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l___private_Lake_CLI_Check_0__Lake_Check_SandboxLocation_ctorElim___redArg(v_t_33_, v_path_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx___impl(uint8_t v_x_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_box(v_x_37_);
v___x_39_ = lean_obj_tag_nat(v___x_38_);
lean_dec(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx___impl___boxed(lean_object* v_x_40_){
_start:
{
uint8_t v_x_4__boxed_41_; lean_object* v_res_42_; 
v_x_4__boxed_41_ = lean_unbox(v_x_40_);
v_res_42_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx___impl(v_x_4__boxed_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___redArg(lean_object* v_k_43_){
_start:
{
lean_inc(v_k_43_);
return v_k_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___redArg___boxed(lean_object* v_k_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___redArg(v_k_44_);
lean_dec(v_k_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim(lean_object* v_motive_46_, lean_object* v_ctorIdx_47_, uint8_t v_t_48_, lean_object* v_h_49_, lean_object* v_k_50_){
_start:
{
lean_inc(v_k_50_);
return v_k_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___boxed(lean_object* v_motive_51_, lean_object* v_ctorIdx_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_k_55_){
_start:
{
uint8_t v_t_boxed_56_; lean_object* v_res_57_; 
v_t_boxed_56_ = lean_unbox(v_t_53_);
v_res_57_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim(v_motive_51_, v_ctorIdx_52_, v_t_boxed_56_, v_h_54_, v_k_55_);
lean_dec(v_k_55_);
lean_dec(v_ctorIdx_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim___redArg(lean_object* v_check_58_){
_start:
{
lean_inc(v_check_58_);
return v_check_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim___redArg___boxed(lean_object* v_check_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim___redArg(v_check_59_);
lean_dec(v_check_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim(lean_object* v_motive_61_, uint8_t v_t_62_, lean_object* v_h_63_, lean_object* v_check_64_){
_start:
{
lean_inc(v_check_64_);
return v_check_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim___boxed(lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_check_68_){
_start:
{
uint8_t v_t_boxed_69_; lean_object* v_res_70_; 
v_t_boxed_69_ = lean_unbox(v_t_66_);
v_res_70_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim(v_motive_65_, v_t_boxed_69_, v_h_67_, v_check_68_);
lean_dec(v_check_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___redArg(lean_object* v_solution_71_){
_start:
{
lean_inc(v_solution_71_);
return v_solution_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___redArg___boxed(lean_object* v_solution_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___redArg(v_solution_72_);
lean_dec(v_solution_72_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim(lean_object* v_motive_74_, uint8_t v_t_75_, lean_object* v_h_76_, lean_object* v_solution_77_){
_start:
{
lean_inc(v_solution_77_);
return v_solution_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___boxed(lean_object* v_motive_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_solution_81_){
_start:
{
uint8_t v_t_boxed_82_; lean_object* v_res_83_; 
v_t_boxed_82_ = lean_unbox(v_t_79_);
v_res_83_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim(v_motive_78_, v_t_boxed_82_, v_h_80_, v_solution_81_);
lean_dec(v_solution_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___redArg(lean_object* v_challenge_84_){
_start:
{
lean_inc(v_challenge_84_);
return v_challenge_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___redArg___boxed(lean_object* v_challenge_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___redArg(v_challenge_85_);
lean_dec(v_challenge_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim(lean_object* v_motive_87_, uint8_t v_t_88_, lean_object* v_h_89_, lean_object* v_challenge_90_){
_start:
{
lean_inc(v_challenge_90_);
return v_challenge_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___boxed(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_challenge_94_){
_start:
{
uint8_t v_t_boxed_95_; lean_object* v_res_96_; 
v_t_boxed_95_ = lean_unbox(v_t_92_);
v_res_96_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim(v_motive_91_, v_t_boxed_95_, v_h_93_, v_challenge_94_);
lean_dec(v_challenge_94_);
return v_res_96_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ofNat(lean_object* v_n_97_){
_start:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_nat_dec_le(v_n_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_dec_le(v_n_97_, v___x_100_);
if (v___x_101_ == 0)
{
uint8_t v___x_102_; 
v___x_102_ = 2;
return v___x_102_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = 1;
return v___x_103_;
}
}
else
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ofNat___boxed(lean_object* v_n_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ofNat(v_n_105_);
lean_dec(v_n_105_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_instDecidableEqModuleKind(uint8_t v_x_108_, uint8_t v_y_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_110_ = lean_box(v_x_108_);
v___x_111_ = lean_obj_tag_nat(v___x_110_);
lean_dec(v___x_110_);
v___x_112_ = lean_box(v_y_109_);
v___x_113_ = lean_obj_tag_nat(v___x_112_);
lean_dec(v___x_112_);
v___x_114_ = lean_nat_dec_eq(v___x_111_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instDecidableEqModuleKind___boxed(lean_object* v_x_115_, lean_object* v_y_116_){
_start:
{
uint8_t v_x_23__boxed_117_; uint8_t v_y_24__boxed_118_; uint8_t v_res_119_; lean_object* v_r_120_; 
v_x_23__boxed_117_ = lean_unbox(v_x_115_);
v_y_24__boxed_118_ = lean_unbox(v_y_116_);
v_res_119_ = l___private_Lake_CLI_Check_0__Lake_Check_instDecidableEqModuleKind(v_x_23__boxed_117_, v_y_24__boxed_118_);
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
lean_object* v_a_380_; lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_400_; 
v_a_380_ = lean_array_uget(v_as_368_, v_i_370_);
v_fst_381_ = lean_ctor_get(v_a_380_, 0);
v_snd_382_ = lean_ctor_get(v_a_380_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v_a_380_);
if (v_isSharedCheck_400_ == 0)
{
v___x_384_ = v_a_380_;
v_isShared_385_ = v_isSharedCheck_400_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_snd_382_);
lean_inc(v_fst_381_);
lean_dec(v_a_380_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_400_;
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
size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_397_ = ((size_t)0ULL);
v___x_398_ = lean_usize_of_nat(v___x_394_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(v_fst_381_, v_b_371_, v___x_397_, v___x_398_, v___x_395_);
lean_dec_ref(v_b_371_);
v___y_387_ = v___x_399_;
goto v___jp_386_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___boxed(lean_object* v_as_401_, lean_object* v_sz_402_, lean_object* v_i_403_, lean_object* v_b_404_, lean_object* v___y_405_){
_start:
{
size_t v_sz_boxed_406_; size_t v_i_boxed_407_; lean_object* v_res_408_; 
v_sz_boxed_406_ = lean_unbox_usize(v_sz_402_);
lean_dec(v_sz_402_);
v_i_boxed_407_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_res_408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2(v_as_401_, v_sz_boxed_406_, v_i_boxed_407_, v_b_404_);
lean_dec_ref(v_as_401_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(lean_object* v_spawnArgs_409_){
_start:
{
lean_object* v_envPass_411_; lean_object* v_envOverride_412_; lean_object* v_env_413_; size_t v_sz_414_; size_t v___x_415_; lean_object* v___x_416_; 
v_envPass_411_ = lean_ctor_get(v_spawnArgs_409_, 2);
v_envOverride_412_ = lean_ctor_get(v_spawnArgs_409_, 3);
v_env_413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___closed__0));
v_sz_414_ = lean_array_size(v_envPass_411_);
v___x_415_ = ((size_t)0ULL);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1(v_envPass_411_, v_sz_414_, v___x_415_, v_env_413_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; size_t v_sz_418_; lean_object* v___x_419_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_416_, 1);
v_sz_418_ = lean_array_size(v_envOverride_412_);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2(v_envOverride_412_, v_sz_418_, v___x_415_, v_a_417_);
return v___x_419_;
}
else
{
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv___boxed(lean_object* v_spawnArgs_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(v_spawnArgs_420_);
lean_dec_ref(v_spawnArgs_420_);
return v_res_422_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_425_ = lean_unsigned_to_nat(2u);
v___x_426_ = lean_mk_empty_array_with_capacity(v___x_425_);
v___x_427_ = lean_array_push(v___x_426_, v___x_424_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(lean_object* v_as_428_, size_t v_i_429_, size_t v_stop_430_, lean_object* v_b_431_){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = lean_usize_dec_eq(v_i_429_, v_stop_430_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; size_t v___x_437_; size_t v___x_438_; 
v___x_433_ = lean_array_uget_borrowed(v_as_428_, v_i_429_);
v___x_434_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1);
lean_inc(v___x_433_);
v___x_435_ = lean_array_push(v___x_434_, v___x_433_);
v___x_436_ = l_Array_append___redArg(v_b_431_, v___x_435_);
lean_dec_ref(v___x_435_);
v___x_437_ = ((size_t)1ULL);
v___x_438_ = lean_usize_add(v_i_429_, v___x_437_);
v_i_429_ = v___x_438_;
v_b_431_ = v___x_436_;
goto _start;
}
else
{
return v_b_431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___boxed(lean_object* v_as_440_, lean_object* v_i_441_, lean_object* v_stop_442_, lean_object* v_b_443_){
_start:
{
size_t v_i_boxed_444_; size_t v_stop_boxed_445_; lean_object* v_res_446_; 
v_i_boxed_444_ = lean_unbox_usize(v_i_441_);
lean_dec(v_i_441_);
v_stop_boxed_445_ = lean_unbox_usize(v_stop_442_);
lean_dec(v_stop_442_);
v_res_446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(v_as_440_, v_i_boxed_444_, v_stop_boxed_445_, v_b_443_);
lean_dec_ref(v_as_440_);
return v_res_446_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__0));
v___x_449_ = lean_unsigned_to_nat(3u);
v___x_450_ = lean_mk_empty_array_with_capacity(v___x_449_);
v___x_451_ = lean_array_push(v___x_450_, v___x_448_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(lean_object* v_as_452_, size_t v_i_453_, size_t v_stop_454_, lean_object* v_b_455_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = lean_usize_dec_eq(v_i_453_, v_stop_454_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; size_t v___x_462_; size_t v___x_463_; 
v___x_457_ = lean_array_uget_borrowed(v_as_452_, v_i_453_);
v___x_458_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1);
lean_inc_n(v___x_457_, 2);
v___x_459_ = lean_array_push(v___x_458_, v___x_457_);
v___x_460_ = lean_array_push(v___x_459_, v___x_457_);
v___x_461_ = l_Array_append___redArg(v_b_455_, v___x_460_);
lean_dec_ref(v___x_460_);
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_add(v_i_453_, v___x_462_);
v_i_453_ = v___x_463_;
v_b_455_ = v___x_461_;
goto _start;
}
else
{
return v_b_455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___boxed(lean_object* v_as_465_, lean_object* v_i_466_, lean_object* v_stop_467_, lean_object* v_b_468_){
_start:
{
size_t v_i_boxed_469_; size_t v_stop_boxed_470_; lean_object* v_res_471_; 
v_i_boxed_469_ = lean_unbox_usize(v_i_466_);
lean_dec(v_i_466_);
v_stop_boxed_470_ = lean_unbox_usize(v_stop_467_);
lean_dec(v_stop_467_);
v_res_471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(v_as_465_, v_i_boxed_469_, v_stop_boxed_470_, v_b_468_);
lean_dec_ref(v_as_465_);
return v_res_471_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__0));
v___x_474_ = lean_unsigned_to_nat(3u);
v___x_475_ = lean_mk_empty_array_with_capacity(v___x_474_);
v___x_476_ = lean_array_push(v___x_475_, v___x_473_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(lean_object* v_as_477_, size_t v_i_478_, size_t v_stop_479_, lean_object* v_b_480_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = lean_usize_dec_eq(v_i_478_, v_stop_479_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; size_t v___x_487_; size_t v___x_488_; 
v___x_482_ = lean_array_uget_borrowed(v_as_477_, v_i_478_);
v___x_483_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1);
lean_inc_n(v___x_482_, 2);
v___x_484_ = lean_array_push(v___x_483_, v___x_482_);
v___x_485_ = lean_array_push(v___x_484_, v___x_482_);
v___x_486_ = l_Array_append___redArg(v_b_480_, v___x_485_);
lean_dec_ref(v___x_485_);
v___x_487_ = ((size_t)1ULL);
v___x_488_ = lean_usize_add(v_i_478_, v___x_487_);
v_i_478_ = v___x_488_;
v_b_480_ = v___x_486_;
goto _start;
}
else
{
return v_b_480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___boxed(lean_object* v_as_490_, lean_object* v_i_491_, lean_object* v_stop_492_, lean_object* v_b_493_){
_start:
{
size_t v_i_boxed_494_; size_t v_stop_boxed_495_; lean_object* v_res_496_; 
v_i_boxed_494_ = lean_unbox_usize(v_i_491_);
lean_dec(v_i_491_);
v_stop_boxed_495_ = lean_unbox_usize(v_stop_492_);
lean_dec(v_stop_492_);
v_res_496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(v_as_490_, v_i_boxed_494_, v_stop_boxed_495_, v_b_493_);
lean_dec_ref(v_as_490_);
return v_res_496_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__0));
v___x_499_ = lean_unsigned_to_nat(3u);
v___x_500_ = lean_mk_empty_array_with_capacity(v___x_499_);
v___x_501_ = lean_array_push(v___x_500_, v___x_498_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(lean_object* v_as_502_, size_t v_i_503_, size_t v_stop_504_, lean_object* v_b_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = lean_usize_dec_eq(v_i_503_, v_stop_504_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v_fst_508_; lean_object* v_snd_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; size_t v___x_514_; size_t v___x_515_; 
v___x_507_ = lean_array_uget_borrowed(v_as_502_, v_i_503_);
v_fst_508_ = lean_ctor_get(v___x_507_, 0);
v_snd_509_ = lean_ctor_get(v___x_507_, 1);
v___x_510_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1);
lean_inc(v_fst_508_);
v___x_511_ = lean_array_push(v___x_510_, v_fst_508_);
lean_inc(v_snd_509_);
v___x_512_ = lean_array_push(v___x_511_, v_snd_509_);
v___x_513_ = l_Array_append___redArg(v_b_505_, v___x_512_);
lean_dec_ref(v___x_512_);
v___x_514_ = ((size_t)1ULL);
v___x_515_ = lean_usize_add(v_i_503_, v___x_514_);
v_i_503_ = v___x_515_;
v_b_505_ = v___x_513_;
goto _start;
}
else
{
return v_b_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___boxed(lean_object* v_as_517_, lean_object* v_i_518_, lean_object* v_stop_519_, lean_object* v_b_520_){
_start:
{
size_t v_i_boxed_521_; size_t v_stop_boxed_522_; lean_object* v_res_523_; 
v_i_boxed_521_ = lean_unbox_usize(v_i_518_);
lean_dec(v_i_518_);
v_stop_boxed_522_ = lean_unbox_usize(v_stop_519_);
lean_dec(v_stop_519_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(v_as_517_, v_i_boxed_521_, v_stop_boxed_522_, v_b_520_);
lean_dec_ref(v_as_517_);
return v_res_523_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__0));
v___x_527_ = lean_unsigned_to_nat(18u);
v___x_528_ = lean_mk_empty_array_with_capacity(v___x_527_);
v___x_529_ = lean_array_push(v___x_528_, v___x_526_);
return v___x_529_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__0));
v___x_531_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2);
v___x_532_ = lean_array_push(v___x_531_, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__0));
v___x_534_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3);
v___x_535_ = lean_array_push(v___x_534_, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_537_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4);
v___x_538_ = lean_array_push(v___x_537_, v___x_536_);
return v___x_538_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__1));
v___x_540_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5);
v___x_541_ = lean_array_push(v___x_540_, v___x_539_);
return v___x_541_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_543_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6);
v___x_544_ = lean_array_push(v___x_543_, v___x_542_);
return v___x_544_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_546_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__8));
v___x_547_ = lean_unsigned_to_nat(2u);
v___x_548_ = lean_mk_empty_array_with_capacity(v___x_547_);
v___x_549_ = lean_array_push(v___x_548_, v___x_546_);
return v___x_549_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_551_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__10));
v___x_552_ = lean_unsigned_to_nat(2u);
v___x_553_ = lean_mk_empty_array_with_capacity(v___x_552_);
v___x_554_ = lean_array_push(v___x_553_, v___x_551_);
return v___x_554_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__12));
v___x_557_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7);
v___x_558_ = lean_array_push(v___x_557_, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_560_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13);
v___x_561_ = lean_array_push(v___x_560_, v___x_559_);
return v___x_561_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__15));
v___x_595_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14);
v___x_596_ = lean_array_push(v___x_595_, v___x_594_);
return v___x_596_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_598_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31);
v___x_599_ = lean_array_push(v___x_598_, v___x_597_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__16));
v___x_601_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32);
v___x_602_ = lean_array_push(v___x_601_, v___x_600_);
return v___x_602_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__17));
v___x_604_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33);
v___x_605_ = lean_array_push(v___x_604_, v___x_603_);
return v___x_605_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__18));
v___x_607_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34);
v___x_608_ = lean_array_push(v___x_607_, v___x_606_);
return v___x_608_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__26));
v___x_610_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35);
v___x_611_ = lean_array_push(v___x_610_, v___x_609_);
return v___x_611_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_612_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__27));
v___x_613_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36);
v___x_614_ = lean_array_push(v___x_613_, v___x_612_);
return v___x_614_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__28));
v___x_616_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37);
v___x_617_ = lean_array_push(v___x_616_, v___x_615_);
return v___x_617_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__29));
v___x_619_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38);
v___x_620_ = lean_array_push(v___x_619_, v___x_618_);
return v___x_620_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_args_623_; 
v___x_621_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__30));
v___x_622_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39);
v_args_623_ = lean_array_push(v___x_622_, v___x_621_);
return v_args_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs(lean_object* v_spawnArgs_624_, lean_object* v_env_625_, lean_object* v_projectDir_626_){
_start:
{
lean_object* v_cmd_627_; lean_object* v_args_628_; lean_object* v_readablePaths_629_; lean_object* v_writablePaths_630_; lean_object* v_tmpfsPaths_631_; uint8_t v_network_632_; lean_object* v_cwd_633_; lean_object* v___y_635_; lean_object* v___y_641_; lean_object* v___y_650_; lean_object* v_args_655_; lean_object* v___x_656_; lean_object* v___y_658_; lean_object* v___y_665_; lean_object* v___y_672_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_cmd_627_ = lean_ctor_get(v_spawnArgs_624_, 0);
lean_inc_ref(v_cmd_627_);
v_args_628_ = lean_ctor_get(v_spawnArgs_624_, 1);
lean_inc_ref(v_args_628_);
v_readablePaths_629_ = lean_ctor_get(v_spawnArgs_624_, 4);
lean_inc_ref(v_readablePaths_629_);
v_writablePaths_630_ = lean_ctor_get(v_spawnArgs_624_, 5);
lean_inc_ref(v_writablePaths_630_);
v_tmpfsPaths_631_ = lean_ctor_get(v_spawnArgs_624_, 6);
lean_inc_ref(v_tmpfsPaths_631_);
v_network_632_ = lean_ctor_get_uint8(v_spawnArgs_624_, sizeof(void*)*8);
v_cwd_633_ = lean_ctor_get(v_spawnArgs_624_, 7);
lean_inc(v_cwd_633_);
lean_dec_ref(v_spawnArgs_624_);
v_args_655_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_array_get_size(v_tmpfsPaths_631_);
v___x_679_ = lean_nat_dec_lt(v___x_656_, v___x_678_);
if (v___x_679_ == 0)
{
lean_dec_ref(v_tmpfsPaths_631_);
v___y_672_ = v_args_655_;
goto v___jp_671_;
}
else
{
size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v___x_680_ = ((size_t)0ULL);
v___x_681_ = lean_usize_of_nat(v___x_678_);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(v_tmpfsPaths_631_, v___x_680_, v___x_681_, v_args_655_);
lean_dec_ref(v_tmpfsPaths_631_);
v___y_672_ = v___x_682_;
goto v___jp_671_;
}
v___jp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_636_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9);
v___x_637_ = lean_array_push(v___x_636_, v_cmd_627_);
v___x_638_ = l_Array_append___redArg(v___y_635_, v___x_637_);
lean_dec_ref(v___x_637_);
v___x_639_ = l_Array_append___redArg(v___x_638_, v_args_628_);
lean_dec_ref(v_args_628_);
return v___x_639_;
}
v___jp_640_:
{
if (lean_obj_tag(v_cwd_633_) == 1)
{
lean_object* v_val_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec_ref(v_projectDir_626_);
v_val_642_ = lean_ctor_get(v_cwd_633_, 0);
lean_inc(v_val_642_);
lean_dec_ref_known(v_cwd_633_, 1);
v___x_643_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11);
v___x_644_ = lean_array_push(v___x_643_, v_val_642_);
v___x_645_ = l_Array_append___redArg(v___y_641_, v___x_644_);
lean_dec_ref(v___x_644_);
v___y_635_ = v___x_645_;
goto v___jp_634_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec(v_cwd_633_);
v___x_646_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11);
v___x_647_ = lean_array_push(v___x_646_, v_projectDir_626_);
v___x_648_ = l_Array_append___redArg(v___y_641_, v___x_647_);
lean_dec_ref(v___x_647_);
v___y_635_ = v___x_648_;
goto v___jp_634_;
}
}
v___jp_649_:
{
lean_object* v___x_651_; lean_object* v_args_652_; 
v___x_651_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__23));
v_args_652_ = l_Array_append___redArg(v___y_650_, v___x_651_);
if (v_network_632_ == 0)
{
v___y_641_ = v_args_652_;
goto v___jp_640_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__25));
v___x_654_ = l_Array_append___redArg(v_args_652_, v___x_653_);
v___y_641_ = v___x_654_;
goto v___jp_640_;
}
}
v___jp_657_:
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = lean_array_get_size(v_env_625_);
v___x_660_ = lean_nat_dec_lt(v___x_656_, v___x_659_);
if (v___x_660_ == 0)
{
v___y_650_ = v___y_658_;
goto v___jp_649_;
}
else
{
size_t v___x_661_; size_t v___x_662_; lean_object* v___x_663_; 
v___x_661_ = ((size_t)0ULL);
v___x_662_ = lean_usize_of_nat(v___x_659_);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(v_env_625_, v___x_661_, v___x_662_, v___y_658_);
v___y_650_ = v___x_663_;
goto v___jp_649_;
}
}
v___jp_664_:
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_array_get_size(v_writablePaths_630_);
v___x_667_ = lean_nat_dec_lt(v___x_656_, v___x_666_);
if (v___x_667_ == 0)
{
lean_dec_ref(v_writablePaths_630_);
v___y_658_ = v___y_665_;
goto v___jp_657_;
}
else
{
size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; 
v___x_668_ = ((size_t)0ULL);
v___x_669_ = lean_usize_of_nat(v___x_666_);
v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(v_writablePaths_630_, v___x_668_, v___x_669_, v___y_665_);
lean_dec_ref(v_writablePaths_630_);
v___y_658_ = v___x_670_;
goto v___jp_657_;
}
}
v___jp_671_:
{
lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = lean_array_get_size(v_readablePaths_629_);
v___x_674_ = lean_nat_dec_lt(v___x_656_, v___x_673_);
if (v___x_674_ == 0)
{
lean_dec_ref(v_readablePaths_629_);
v___y_665_ = v___y_672_;
goto v___jp_664_;
}
else
{
size_t v___x_675_; size_t v___x_676_; lean_object* v___x_677_; 
v___x_675_ = ((size_t)0ULL);
v___x_676_ = lean_usize_of_nat(v___x_673_);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(v_readablePaths_629_, v___x_675_, v___x_676_, v___y_672_);
lean_dec_ref(v_readablePaths_629_);
v___y_665_ = v___x_677_;
goto v___jp_664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___boxed(lean_object* v_spawnArgs_683_, lean_object* v_env_684_, lean_object* v_projectDir_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs(v_spawnArgs_683_, v_env_684_, v_projectDir_685_);
lean_dec_ref(v_env_684_);
return v_res_686_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_688_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__0));
v___x_689_ = lean_unsigned_to_nat(2u);
v___x_690_ = lean_mk_empty_array_with_capacity(v___x_689_);
v___x_691_ = lean_array_push(v___x_690_, v___x_688_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(lean_object* v_spawnArgs_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_whichSandbox_695_; 
v_whichSandbox_695_ = lean_ctor_get(v_a_693_, 9);
if (lean_obj_tag(v_whichSandbox_695_) == 0)
{
lean_object* v_projectDir_696_; lean_object* v___x_697_; lean_object* v_cmd_698_; lean_object* v_args_699_; lean_object* v_envOverride_700_; lean_object* v_cwd_701_; lean_object* v___y_703_; 
v_projectDir_696_ = lean_ctor_get(v_a_693_, 0);
v___x_697_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v_cmd_698_ = lean_ctor_get(v_spawnArgs_692_, 0);
lean_inc_ref(v_cmd_698_);
v_args_699_ = lean_ctor_get(v_spawnArgs_692_, 1);
lean_inc_ref(v_args_699_);
v_envOverride_700_ = lean_ctor_get(v_spawnArgs_692_, 3);
lean_inc_ref(v_envOverride_700_);
v_cwd_701_ = lean_ctor_get(v_spawnArgs_692_, 7);
lean_inc(v_cwd_701_);
lean_dec_ref(v_spawnArgs_692_);
if (lean_obj_tag(v_cwd_701_) == 1)
{
v___y_703_ = v_cwd_701_;
goto v___jp_702_;
}
else
{
lean_object* v___x_708_; 
lean_dec(v_cwd_701_);
lean_inc_ref(v_projectDir_696_);
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v_projectDir_696_);
v___y_703_ = v___x_708_;
goto v___jp_702_;
}
v___jp_702_:
{
uint8_t v___x_704_; uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_704_ = 1;
v___x_705_ = 0;
v___x_706_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_706_, 0, v___x_697_);
lean_ctor_set(v___x_706_, 1, v_cmd_698_);
lean_ctor_set(v___x_706_, 2, v_args_699_);
lean_ctor_set(v___x_706_, 3, v___y_703_);
lean_ctor_set(v___x_706_, 4, v_envOverride_700_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*5, v___x_704_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*5 + 1, v___x_705_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
else
{
lean_object* v_projectDir_709_; lean_object* v_whichEnvBin_710_; lean_object* v_path_711_; lean_object* v___x_712_; 
v_projectDir_709_ = lean_ctor_get(v_a_693_, 0);
v_whichEnvBin_710_ = lean_ctor_get(v_a_693_, 14);
v_path_711_ = lean_ctor_get(v_whichSandbox_695_, 0);
v___x_712_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(v_spawnArgs_692_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_730_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_730_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_730_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_730_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_717_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v___x_718_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1, &l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1);
lean_inc_ref(v_path_711_);
v___x_719_ = lean_array_push(v___x_718_, v_path_711_);
lean_inc_ref_n(v_projectDir_709_, 2);
v___x_720_ = l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs(v_spawnArgs_692_, v_a_713_, v_projectDir_709_);
lean_dec(v_a_713_);
v___x_721_ = l_Array_append___redArg(v___x_719_, v___x_720_);
lean_dec_ref(v___x_720_);
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v_projectDir_709_);
v___x_723_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__2));
v___x_724_ = 1;
v___x_725_ = 0;
lean_inc_ref(v_whichEnvBin_710_);
v___x_726_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_726_, 0, v___x_717_);
lean_ctor_set(v___x_726_, 1, v_whichEnvBin_710_);
lean_ctor_set(v___x_726_, 2, v___x_721_);
lean_ctor_set(v___x_726_, 3, v___x_722_);
lean_ctor_set(v___x_726_, 4, v___x_723_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*5, v___x_724_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*5 + 1, v___x_725_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_726_);
v___x_728_ = v___x_715_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v_spawnArgs_692_);
v_a_731_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_712_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_712_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___boxed(lean_object* v_spawnArgs_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_739_, v_a_740_);
lean_dec_ref(v_a_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(lean_object* v_handle_743_, lean_object* v_child_744_){
_start:
{
lean_object* v_stdout_746_; size_t v___x_747_; lean_object* v___x_748_; 
v_stdout_746_ = lean_ctor_get(v_child_744_, 1);
v___x_747_ = ((size_t)4096ULL);
v___x_748_ = lean_io_prim_handle_read(v_stdout_746_, v___x_747_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; uint8_t v___x_750_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v___x_750_ = l_ByteArray_isEmpty(v_a_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
v___x_751_ = lean_io_prim_handle_write(v_handle_743_, v_a_749_);
lean_dec(v_a_749_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_dec_ref_known(v___x_751_, 1);
goto _start;
}
else
{
return v___x_751_;
}
}
else
{
lean_object* v___x_753_; 
lean_dec(v_a_749_);
v___x_753_ = lean_io_prim_handle_flush(v_handle_743_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_761_; 
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v___x_753_, 0);
lean_dec(v_unused_762_);
v___x_755_ = v___x_753_;
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
else
{
lean_dec(v___x_753_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = lean_box(0);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_757_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
else
{
return v___x_753_;
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
v_a_763_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_748_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_748_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg___boxed(lean_object* v_handle_771_, lean_object* v_child_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(v_handle_771_, v_child_772_);
lean_dec_ref(v_child_772_);
lean_dec(v_handle_771_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop(lean_object* v_handle_775_, lean_object* v_args_776_, lean_object* v_child_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(v_handle_775_, v_child_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___boxed(lean_object* v_handle_780_, lean_object* v_args_781_, lean_object* v_child_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop(v_handle_780_, v_args_781_, v_child_782_);
lean_dec_ref(v_child_782_);
lean_dec_ref(v_args_781_);
lean_dec(v_handle_780_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(lean_object* v_e_785_){
_start:
{
if (lean_obj_tag(v_e_785_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_796_; 
v_a_787_ = lean_ctor_get(v_e_785_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_e_785_);
if (v_isSharedCheck_796_ == 0)
{
v___x_789_ = v_e_785_;
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v_e_785_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_791_ = lean_io_error_to_string(v_a_787_);
v___x_792_ = lean_mk_io_user_error(v___x_791_);
if (v_isShared_790_ == 0)
{
lean_ctor_set_tag(v___x_789_, 1);
lean_ctor_set(v___x_789_, 0, v___x_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_a_797_ = lean_ctor_get(v_e_785_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v_e_785_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v_e_785_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v_e_785_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set_tag(v___x_799_, 0);
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg___boxed(lean_object* v_e_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(v_e_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0(lean_object* v_00_u03b1_808_, lean_object* v_e_809_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(v_e_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___boxed(lean_object* v_00_u03b1_812_, lean_object* v_e_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0(v_00_u03b1_812_, v_e_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0(lean_object* v_handle_816_, lean_object* v_a_817_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(v_handle_816_, v_a_817_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 1);
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
v_a_828_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_819_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_819_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set_tag(v___x_830_, 0);
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0___boxed(lean_object* v_handle_836_, lean_object* v_a_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0(v_handle_836_, v_a_837_);
lean_dec_ref(v_a_837_);
lean_dec(v_handle_836_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(lean_object* v_handle_843_, lean_object* v_args_844_){
_start:
{
lean_object* v___x_846_; lean_object* v_cmd_847_; lean_object* v_args_848_; lean_object* v_cwd_849_; lean_object* v_env_850_; uint8_t v_inheritEnv_851_; uint8_t v_setsid_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_912_; 
v___x_846_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___closed__0));
v_cmd_847_ = lean_ctor_get(v_args_844_, 1);
v_args_848_ = lean_ctor_get(v_args_844_, 2);
v_cwd_849_ = lean_ctor_get(v_args_844_, 3);
v_env_850_ = lean_ctor_get(v_args_844_, 4);
v_inheritEnv_851_ = lean_ctor_get_uint8(v_args_844_, sizeof(void*)*5);
v_setsid_852_ = lean_ctor_get_uint8(v_args_844_, sizeof(void*)*5 + 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v_args_844_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v_args_844_, 0);
lean_dec(v_unused_913_);
v___x_854_ = v_args_844_;
v_isShared_855_ = v_isSharedCheck_912_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_env_850_);
lean_inc(v_cwd_849_);
lean_inc(v_args_848_);
lean_inc(v_cmd_847_);
lean_dec(v_args_844_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_912_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_846_);
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_cmd_847_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_args_848_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v_cwd_849_);
lean_ctor_set(v_reuseFailAlloc_911_, 4, v_env_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, sizeof(void*)*5, v_inheritEnv_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, sizeof(void*)*5 + 1, v_setsid_852_);
v___x_857_ = v_reuseFailAlloc_911_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = lean_io_process_spawn(v___x_857_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___f_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_stderr_863_; lean_object* v___x_864_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc_n(v_a_859_, 2);
lean_dec_ref_known(v___x_858_, 1);
v___f_860_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0___boxed), 3, 2);
lean_closure_set(v___f_860_, 0, v_handle_843_);
lean_closure_set(v___f_860_, 1, v_a_859_);
v___x_861_ = lean_unsigned_to_nat(9u);
v___x_862_ = lean_io_as_task(v___f_860_, v___x_861_);
v_stderr_863_ = lean_ctor_get(v_a_859_, 2);
v___x_864_ = l_IO_FS_Handle_readToEnd(v_stderr_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_866_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_864_, 1);
v___x_866_ = lean_io_process_child_wait(v___x_846_, v_a_859_);
lean_dec(v_a_859_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_868_ = lean_task_get_own(v___x_862_);
v___x_869_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(v___x_868_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_877_; 
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; 
v_unused_878_ = lean_ctor_get(v___x_869_, 0);
lean_dec(v_unused_878_);
v___x_871_ = v___x_869_;
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
else
{
lean_dec(v___x_869_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_a_865_);
lean_ctor_set(v___x_873_, 1, v_a_867_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_873_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec(v_a_867_);
lean_dec(v_a_865_);
v_a_879_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_869_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_869_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec(v_a_865_);
lean_dec_ref(v___x_862_);
v_a_887_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_866_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_866_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v___x_862_);
lean_dec(v_a_859_);
v_a_895_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_864_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_864_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_handle_843_);
v_a_903_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_858_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_858_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___boxed(lean_object* v_handle_914_, lean_object* v_args_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(v_handle_914_, v_args_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(lean_object* v_s_918_){
_start:
{
lean_object* v___x_920_; lean_object* v_putStr_921_; lean_object* v___x_922_; 
v___x_920_ = lean_get_stderr();
v_putStr_921_ = lean_ctor_get(v___x_920_, 4);
lean_inc_ref(v_putStr_921_);
lean_dec_ref(v___x_920_);
v___x_922_ = lean_apply_2(v_putStr_921_, v_s_918_, lean_box(0));
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0___boxed(lean_object* v_s_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v_s_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(lean_object* v_handle_927_, lean_object* v_spawnArgs_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_928_, v_a_929_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(v_handle_927_, v_a_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v_fst_935_; lean_object* v_snd_936_; lean_object* v___x_937_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 1);
v_fst_935_ = lean_ctor_get(v_a_934_, 0);
lean_inc(v_fst_935_);
v_snd_936_ = lean_ctor_get(v_a_934_, 1);
lean_inc(v_snd_936_);
lean_dec(v_a_934_);
v___x_937_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v_fst_935_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_957_; 
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_957_ == 0)
{
lean_object* v_unused_958_; 
v_unused_958_ = lean_ctor_get(v___x_937_, 0);
lean_dec(v_unused_958_);
v___x_939_ = v___x_937_;
v_isShared_940_ = v_isSharedCheck_957_;
goto v_resetjp_938_;
}
else
{
lean_dec(v___x_937_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_957_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
uint32_t v___x_941_; uint32_t v___x_942_; uint8_t v___x_943_; 
v___x_941_ = 0;
v___x_942_ = lean_unbox_uint32(v_snd_936_);
v___x_943_ = lean_uint32_dec_eq(v___x_942_, v___x_941_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; uint32_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_944_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0));
v___x_945_ = lean_unbox_uint32(v_snd_936_);
lean_dec(v_snd_936_);
v___x_946_ = lean_uint32_to_nat(v___x_945_);
v___x_947_ = l_Nat_reprFast(v___x_946_);
v___x_948_ = lean_string_append(v___x_944_, v___x_947_);
lean_dec_ref(v___x_947_);
v___x_949_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 1);
lean_ctor_set(v___x_939_, 0, v___x_949_);
v___x_951_ = v___x_939_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
else
{
lean_object* v___x_953_; lean_object* v___x_955_; 
lean_dec(v_snd_936_);
v___x_953_ = lean_box(0);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_953_);
v___x_955_ = v___x_939_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_dec(v_snd_936_);
return v___x_937_;
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v_a_959_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_933_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_933_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_handle_927_);
v_a_967_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_931_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_931_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___boxed(lean_object* v_handle_975_, lean_object* v_spawnArgs_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_handle_975_, v_spawnArgs_976_, v_a_977_);
lean_dec_ref(v_a_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(lean_object* v_spawnArgs_980_, lean_object* v_a_981_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_980_, v_a_981_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = lean_box(0);
v___x_986_ = l_IO_Process_output(v_a_984_, v___x_985_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; uint32_t v_exitCode_988_; lean_object* v_stdout_989_; lean_object* v_stderr_990_; lean_object* v___x_991_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v_exitCode_988_ = lean_ctor_get_uint32(v_a_987_, sizeof(void*)*2);
v_stdout_989_ = lean_ctor_get(v_a_987_, 0);
lean_inc_ref(v_stdout_989_);
v_stderr_990_ = lean_ctor_get(v_a_987_, 1);
lean_inc_ref(v_stderr_990_);
lean_dec(v_a_987_);
v___x_991_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v_stderr_990_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1008_; 
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1008_ == 0)
{
lean_object* v_unused_1009_; 
v_unused_1009_ = lean_ctor_get(v___x_991_, 0);
lean_dec(v_unused_1009_);
v___x_993_ = v___x_991_;
v_isShared_994_ = v_isSharedCheck_1008_;
goto v_resetjp_992_;
}
else
{
lean_dec(v___x_991_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1008_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
uint32_t v___x_995_; uint8_t v___x_996_; 
v___x_995_ = 0;
v___x_996_ = lean_uint32_dec_eq(v_exitCode_988_, v___x_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
lean_dec_ref(v_stdout_989_);
v___x_997_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0));
v___x_998_ = lean_uint32_to_nat(v_exitCode_988_);
v___x_999_ = l_Nat_reprFast(v___x_998_);
v___x_1000_ = lean_string_append(v___x_997_, v___x_999_);
lean_dec_ref(v___x_999_);
v___x_1001_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 1);
lean_ctor_set(v___x_993_, 0, v___x_1001_);
v___x_1003_ = v___x_993_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
else
{
lean_object* v___x_1006_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v_stdout_989_);
v___x_1006_ = v___x_993_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_stdout_989_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref(v_stdout_989_);
v_a_1010_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_991_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_991_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_986_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_986_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1026_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_983_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_983_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___boxed(lean_object* v_spawnArgs_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v_spawnArgs_1034_, v_a_1035_);
lean_dec_ref(v_a_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(lean_object* v_spawnArgs_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_1038_, v_a_1039_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = lean_io_process_spawn(v_a_1042_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v___x_1046_ = lean_io_process_child_wait(v___x_1045_, v_a_1044_);
lean_dec(v_a_1044_);
return v___x_1046_;
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
v_a_1047_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1043_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1043_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_a_1055_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1041_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1041_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode___boxed(lean_object* v_spawnArgs_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v_spawnArgs_1063_, v_a_1064_);
lean_dec_ref(v_a_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(lean_object* v_spawnArgs_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v_spawnArgs_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1091_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1091_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1091_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
uint32_t v___x_1075_; uint32_t v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = 0;
v___x_1076_ = lean_unbox_uint32(v_a_1071_);
v___x_1077_ = lean_uint32_dec_eq(v___x_1076_, v___x_1075_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; uint32_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1078_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0));
v___x_1079_ = lean_unbox_uint32(v_a_1071_);
lean_dec(v_a_1071_);
v___x_1080_ = lean_uint32_to_nat(v___x_1079_);
v___x_1081_ = l_Nat_reprFast(v___x_1080_);
v___x_1082_ = lean_string_append(v___x_1078_, v___x_1081_);
lean_dec_ref(v___x_1081_);
v___x_1083_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set_tag(v___x_1073_, 1);
lean_ctor_set(v___x_1073_, 0, v___x_1083_);
v___x_1085_ = v___x_1073_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
lean_dec(v_a_1071_);
v___x_1087_ = lean_box(0);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1087_);
v___x_1089_ = v___x_1073_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_a_1092_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1070_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1070_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed___boxed(lean_object* v_spawnArgs_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v_spawnArgs_1100_, v_a_1101_);
lean_dec_ref(v_a_1101_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(lean_object* v_s_1105_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1106_ = lean_string_utf8_byte_size(v_s_1105_);
v___x_1107_ = lean_unsigned_to_nat(10u);
v___x_1108_ = lean_nat_dec_le(v___x_1107_, v___x_1106_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; 
lean_dec_ref(v_s_1105_);
v___x_1109_ = lean_box(0);
return v___x_1109_;
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1110_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0));
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = lean_string_memcmp(v_s_1105_, v___x_1110_, v___x_1111_, v___x_1111_, v___x_1107_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
lean_dec_ref(v_s_1105_);
v___x_1113_ = lean_box(0);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_inc_ref(v_s_1105_);
v___x_1114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1114_, 0, v_s_1105_);
lean_ctor_set(v___x_1114_, 1, v___x_1111_);
lean_ctor_set(v___x_1114_, 2, v___x_1106_);
v___x_1115_ = l_String_Slice_pos_x21(v___x_1114_, v___x_1107_);
lean_dec_ref_known(v___x_1114_, 3);
v___x_1116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1116_, 0, v_s_1105_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
lean_ctor_set(v___x_1116_, 2, v___x_1106_);
v___x_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(lean_object* v_s_1118_, lean_object* v_pat_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_s_1118_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___boxed(lean_object* v_s_1121_, lean_object* v_pat_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(v_s_1121_, v_pat_1122_);
lean_dec_ref(v_pat_1122_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(lean_object* v_s_1125_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1126_ = lean_string_utf8_byte_size(v_s_1125_);
v___x_1127_ = lean_unsigned_to_nat(5u);
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
v___x_1130_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0));
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
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(lean_object* v_s_1138_, lean_object* v_pat_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_s_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___boxed(lean_object* v_s_1141_, lean_object* v_pat_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(v_s_1141_, v_pat_1142_);
lean_dec_ref(v_pat_1142_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg(){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___closed__0));
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___boxed(lean_object* v___dummy_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg();
return v_res_1149_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg();
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(lean_object* v_s_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___boxed(lean_object* v_s_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(v_s_1153_);
lean_dec_ref(v_s_1153_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(lean_object* v_a_1155_, lean_object* v___x_1156_, lean_object* v___x_1157_, lean_object* v_a_1158_, lean_object* v_b_1159_){
_start:
{
lean_object* v_it_1161_; lean_object* v_startInclusive_1162_; lean_object* v_endExclusive_1163_; 
if (lean_obj_tag(v_a_1158_) == 0)
{
lean_object* v_currPos_1168_; lean_object* v_searcher_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1192_; 
v_currPos_1168_ = lean_ctor_get(v_a_1158_, 0);
v_searcher_1169_ = lean_ctor_get(v_a_1158_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_a_1158_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1171_ = v_a_1158_;
v_isShared_1172_ = v_isSharedCheck_1192_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_searcher_1169_);
lean_inc(v_currPos_1168_);
lean_dec(v_a_1158_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1192_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
uint8_t v_decide_1173_; 
v_decide_1173_ = lean_nat_dec_eq(v_searcher_1169_, v___x_1157_);
if (v_decide_1173_ == 0)
{
uint32_t v___x_1174_; uint32_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = 10;
v___x_1175_ = lean_string_utf8_get_fast(v_a_1155_, v_searcher_1169_);
v___x_1176_ = lean_uint32_dec_eq(v___x_1175_, v___x_1174_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = lean_string_utf8_next_fast(v_a_1155_, v_searcher_1169_);
lean_dec(v_searcher_1169_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 1, v___x_1177_);
v___x_1179_ = v___x_1171_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_currPos_1168_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
v_a_1158_ = v___x_1179_;
goto _start;
}
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v_slice_1185_; lean_object* v_nextIt_1187_; 
v___x_1182_ = lean_string_utf8_next_fast(v_a_1155_, v_searcher_1169_);
v___x_1183_ = lean_nat_sub(v___x_1182_, v_searcher_1169_);
v___x_1184_ = lean_nat_add(v_searcher_1169_, v___x_1183_);
lean_dec(v___x_1183_);
v_slice_1185_ = l_String_Slice_subslice_x21(v___x_1156_, v_currPos_1168_, v_searcher_1169_);
lean_inc(v___x_1184_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 1, v___x_1184_);
lean_ctor_set(v___x_1171_, 0, v___x_1184_);
v_nextIt_1187_ = v___x_1171_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1184_);
v_nextIt_1187_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v_startInclusive_1188_; lean_object* v_endExclusive_1189_; 
v_startInclusive_1188_ = lean_ctor_get(v_slice_1185_, 0);
lean_inc(v_startInclusive_1188_);
v_endExclusive_1189_ = lean_ctor_get(v_slice_1185_, 1);
lean_inc(v_endExclusive_1189_);
lean_dec_ref(v_slice_1185_);
v_it_1161_ = v_nextIt_1187_;
v_startInclusive_1162_ = v_startInclusive_1188_;
v_endExclusive_1163_ = v_endExclusive_1189_;
goto v___jp_1160_;
}
}
}
else
{
lean_object* v___x_1191_; 
lean_del_object(v___x_1171_);
lean_dec(v_searcher_1169_);
v___x_1191_ = lean_box(1);
lean_inc(v___x_1157_);
v_it_1161_ = v___x_1191_;
v_startInclusive_1162_ = v_currPos_1168_;
v_endExclusive_1163_ = v___x_1157_;
goto v___jp_1160_;
}
}
}
else
{
lean_dec(v___x_1157_);
lean_dec_ref(v_a_1155_);
return v_b_1159_;
}
v___jp_1160_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_inc_ref(v_a_1155_);
v___x_1164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1164_, 0, v_a_1155_);
lean_ctor_set(v___x_1164_, 1, v_startInclusive_1162_);
lean_ctor_set(v___x_1164_, 2, v_endExclusive_1163_);
v___x_1165_ = l_String_Slice_toString(v___x_1164_);
lean_dec_ref_known(v___x_1164_, 3);
v___x_1166_ = lean_array_push(v_b_1159_, v___x_1165_);
v_a_1158_ = v_it_1161_;
v_b_1159_ = v___x_1166_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg___boxed(lean_object* v_a_1193_, lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v_a_1196_, lean_object* v_b_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1193_, v___x_1194_, v___x_1195_, v_a_1196_, v_b_1197_);
lean_dec_ref(v___x_1194_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(lean_object* v_as_x27_1199_, lean_object* v_b_1200_){
_start:
{
if (lean_obj_tag(v_as_x27_1199_) == 0)
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v_b_1200_);
return v___x_1202_;
}
else
{
lean_object* v_head_1203_; lean_object* v_tail_1204_; lean_object* v_fst_1205_; lean_object* v_snd_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1228_; 
v_head_1203_ = lean_ctor_get(v_as_x27_1199_, 0);
v_tail_1204_ = lean_ctor_get(v_as_x27_1199_, 1);
v_fst_1205_ = lean_ctor_get(v_b_1200_, 0);
v_snd_1206_ = lean_ctor_get(v_b_1200_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_b_1200_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1208_ = v_b_1200_;
v_isShared_1209_ = v_isSharedCheck_1228_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_snd_1206_);
lean_inc(v_fst_1205_);
lean_dec(v_b_1200_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1228_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; 
lean_inc(v_head_1203_);
v___x_1210_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_head_1203_);
if (lean_obj_tag(v___x_1210_) == 1)
{
lean_object* v_val_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
lean_dec(v_fst_1205_);
v_val_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_val_1211_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1212_ = l_String_Slice_toString(v_val_1211_);
lean_dec(v_val_1211_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1212_);
v___x_1214_ = v___x_1208_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_snd_1206_);
v___x_1214_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
v_as_x27_1199_ = v_tail_1204_;
v_b_1200_ = v___x_1214_;
goto _start;
}
}
else
{
lean_object* v___x_1217_; 
lean_dec(v___x_1210_);
lean_inc(v_head_1203_);
v___x_1217_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_head_1203_);
if (lean_obj_tag(v___x_1217_) == 1)
{
lean_object* v_val_1218_; lean_object* v___x_1219_; lean_object* v___x_1221_; 
lean_dec(v_snd_1206_);
v_val_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_val_1218_);
lean_dec_ref_known(v___x_1217_, 1);
v___x_1219_ = l_String_Slice_toString(v_val_1218_);
lean_dec(v_val_1218_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 1, v___x_1219_);
v___x_1221_ = v___x_1208_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_fst_1205_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
v_as_x27_1199_ = v_tail_1204_;
v_b_1200_ = v___x_1221_;
goto _start;
}
}
else
{
lean_object* v___x_1225_; 
lean_dec(v___x_1217_);
if (v_isShared_1209_ == 0)
{
v___x_1225_ = v___x_1208_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_fst_1205_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_snd_1206_);
v___x_1225_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
v_as_x27_1199_ = v_tail_1204_;
v_b_1200_ = v___x_1225_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg___boxed(lean_object* v_as_x27_1229_, lean_object* v_b_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_1229_, v_b_1230_);
lean_dec(v_as_x27_1229_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(lean_object* v_s_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v_putStr_1236_; lean_object* v___x_1237_; 
v___x_1235_ = lean_get_stdout();
v_putStr_1236_ = lean_ctor_get(v___x_1235_, 4);
lean_inc_ref(v_putStr_1236_);
lean_dec_ref(v___x_1235_);
v___x_1237_ = lean_apply_2(v_putStr_1236_, v_s_1233_, lean_box(0));
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2___boxed(lean_object* v_s_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v_s_1238_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(lean_object* v_s_1241_){
_start:
{
uint32_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = 10;
v___x_1244_ = lean_string_push(v_s_1241_, v___x_1243_);
v___x_1245_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2___boxed(lean_object* v_s_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v_s_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(lean_object* v_a_1282_){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_1288_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1287_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_projectDir_1289_; lean_object* v_leanPrefix_1290_; lean_object* v_whichLake_1291_; lean_object* v_lakeHome_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___y_1296_; lean_object* v_leanPrefix_1297_; lean_object* v_whichLake_1298_; lean_object* v_lakeHome_1299_; uint8_t v___x_1354_; 
lean_dec_ref_known(v___x_1288_, 1);
v_projectDir_1289_ = lean_ctor_get(v_a_1282_, 0);
v_leanPrefix_1290_ = lean_ctor_get(v_a_1282_, 6);
v_whichLake_1291_ = lean_ctor_get(v_a_1282_, 10);
v_lakeHome_1292_ = lean_ctor_get(v_a_1282_, 11);
v___x_1293_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1289_);
v___x_1294_ = l_System_FilePath_join(v_projectDir_1289_, v___x_1293_);
v___x_1354_ = l_System_FilePath_pathExists(v___x_1294_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_io_create_dir(v___x_1294_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_dec_ref_known(v___x_1355_, 1);
v___y_1296_ = v_a_1282_;
v_leanPrefix_1297_ = v_leanPrefix_1290_;
v_whichLake_1298_ = v_whichLake_1291_;
v_lakeHome_1299_ = v_lakeHome_1292_;
goto v___jp_1295_;
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec_ref(v___x_1294_);
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
v___y_1296_ = v_a_1282_;
v_leanPrefix_1297_ = v_leanPrefix_1290_;
v_whichLake_1298_ = v_whichLake_1291_;
v_lakeHome_1299_ = v_lakeHome_1292_;
goto v___jp_1295_;
}
v___jp_1295_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1300_ = lean_unsigned_to_nat(1u);
v___x_1301_ = lean_mk_empty_array_with_capacity(v___x_1300_);
v___x_1302_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__5));
v___x_1303_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8));
v___x_1304_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1305_ = lean_unsigned_to_nat(3u);
v___x_1306_ = lean_mk_empty_array_with_capacity(v___x_1305_);
lean_inc_ref(v_projectDir_1289_);
v___x_1307_ = lean_array_push(v___x_1306_, v_projectDir_1289_);
lean_inc_ref(v_leanPrefix_1297_);
v___x_1308_ = lean_array_push(v___x_1307_, v_leanPrefix_1297_);
lean_inc_ref(v_lakeHome_1299_);
v___x_1309_ = lean_array_push(v___x_1308_, v_lakeHome_1299_);
v___x_1310_ = lean_array_push(v___x_1301_, v___x_1294_);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1313_ = 1;
v___x_1314_ = lean_box(0);
lean_inc_ref(v_whichLake_1298_);
v___x_1315_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1315_, 0, v_whichLake_1298_);
lean_ctor_set(v___x_1315_, 1, v___x_1302_);
lean_ctor_set(v___x_1315_, 2, v___x_1303_);
lean_ctor_set(v___x_1315_, 3, v___x_1304_);
lean_ctor_set(v___x_1315_, 4, v___x_1309_);
lean_ctor_set(v___x_1315_, 5, v___x_1310_);
lean_ctor_set(v___x_1315_, 6, v___x_1312_);
lean_ctor_set(v___x_1315_, 7, v___x_1314_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*8, v___x_1313_);
v___x_1316_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v___x_1315_, v___y_1296_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1345_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc_n(v_a_1317_, 2);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = lean_string_utf8_byte_size(v_a_1317_);
v___x_1319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1319_, 0, v_a_1317_);
lean_ctor_set(v___x_1319_, 1, v___x_1311_);
lean_ctor_set(v___x_1319_, 2, v___x_1318_);
v___x_1320_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0);
v___x_1321_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1317_, v___x_1319_, v___x_1318_, v___x_1320_, v___x_1312_);
lean_dec_ref_known(v___x_1319_, 3);
v___x_1322_ = lean_array_to_list(v___x_1321_);
v___x_1323_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__15));
v___x_1324_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v___x_1322_, v___x_1323_);
lean_dec(v___x_1322_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1345_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1345_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v_fst_1329_; lean_object* v_snd_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1344_; 
v_fst_1329_ = lean_ctor_get(v_a_1325_, 0);
v_snd_1330_ = lean_ctor_get(v_a_1325_, 1);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_a_1325_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1332_ = v_a_1325_;
v_isShared_1333_ = v_isSharedCheck_1344_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_snd_1330_);
lean_inc(v_fst_1329_);
lean_dec(v_a_1325_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1344_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = lean_string_utf8_byte_size(v_fst_1329_);
v___x_1335_ = lean_nat_dec_eq(v___x_1334_, v___x_1311_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_string_utf8_byte_size(v_snd_1330_);
v___x_1337_ = lean_nat_dec_eq(v___x_1336_, v___x_1311_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1339_; 
if (v_isShared_1333_ == 0)
{
v___x_1339_ = v___x_1332_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_fst_1329_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_snd_1330_);
v___x_1339_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1341_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1339_);
v___x_1341_ = v___x_1327_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
else
{
lean_del_object(v___x_1332_);
lean_dec(v_snd_1330_);
lean_dec(v_fst_1329_);
lean_del_object(v___x_1327_);
goto v___jp_1284_;
}
}
else
{
lean_del_object(v___x_1332_);
lean_dec(v_snd_1330_);
lean_dec(v_fst_1329_);
lean_del_object(v___x_1327_);
goto v___jp_1284_;
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
v_a_1346_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1316_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1316_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
v_a_1364_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1288_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1288_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
v___jp_1284_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__1));
v___x_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___boxed(lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v_a_1372_);
lean_dec_ref(v_a_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(lean_object* v_a_1375_, lean_object* v___x_1376_, lean_object* v___x_1377_, lean_object* v_inst_1378_, lean_object* v_R_1379_, lean_object* v_a_1380_, lean_object* v_b_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1375_, v___x_1376_, v___x_1377_, v_a_1380_, v_b_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___boxed(lean_object* v_a_1383_, lean_object* v___x_1384_, lean_object* v___x_1385_, lean_object* v_inst_1386_, lean_object* v_R_1387_, lean_object* v_a_1388_, lean_object* v_b_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(v_a_1383_, v___x_1384_, v___x_1385_, v_inst_1386_, v_R_1387_, v_a_1388_, v_b_1389_);
lean_dec_ref(v___x_1384_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(lean_object* v_as_1391_, lean_object* v_as_x27_1392_, lean_object* v_b_1393_, lean_object* v_a_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_1392_, v_b_1393_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___boxed(lean_object* v_as_1398_, lean_object* v_as_x27_1399_, lean_object* v_b_1400_, lean_object* v_a_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(v_as_1398_, v_as_x27_1399_, v_b_1400_, v_a_1401_, v___y_1402_);
lean_dec_ref(v___y_1402_);
lean_dec(v_as_x27_1399_);
lean_dec(v_as_1398_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(lean_object* v_a_1418_){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_1421_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1420_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_projectDir_1422_; lean_object* v_leanPrefix_1423_; lean_object* v_whichLake_1424_; lean_object* v_lakeHome_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___y_1429_; lean_object* v_leanPrefix_1430_; lean_object* v_whichLake_1431_; lean_object* v_lakeHome_1432_; uint8_t v___x_1449_; 
lean_dec_ref_known(v___x_1421_, 1);
v_projectDir_1422_ = lean_ctor_get(v_a_1418_, 0);
v_leanPrefix_1423_ = lean_ctor_get(v_a_1418_, 6);
v_whichLake_1424_ = lean_ctor_get(v_a_1418_, 10);
v_lakeHome_1425_ = lean_ctor_get(v_a_1418_, 11);
v___x_1426_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1422_);
v___x_1427_ = l_System_FilePath_join(v_projectDir_1422_, v___x_1426_);
v___x_1449_ = l_System_FilePath_pathExists(v___x_1427_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_io_create_dir(v___x_1427_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_dec_ref_known(v___x_1450_, 1);
v___y_1429_ = v_a_1418_;
v_leanPrefix_1430_ = v_leanPrefix_1423_;
v_whichLake_1431_ = v_whichLake_1424_;
v_lakeHome_1432_ = v_lakeHome_1425_;
goto v___jp_1428_;
}
else
{
lean_dec_ref(v___x_1427_);
return v___x_1450_;
}
}
else
{
v___y_1429_ = v_a_1418_;
v_leanPrefix_1430_ = v_leanPrefix_1423_;
v_whichLake_1431_ = v_whichLake_1424_;
v_lakeHome_1432_ = v_lakeHome_1425_;
goto v___jp_1428_;
}
v___jp_1428_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1433_ = lean_unsigned_to_nat(1u);
v___x_1434_ = lean_mk_empty_array_with_capacity(v___x_1433_);
v___x_1435_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__1));
v___x_1436_ = lean_unsigned_to_nat(3u);
v___x_1437_ = lean_mk_empty_array_with_capacity(v___x_1436_);
v___x_1438_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2));
v___x_1439_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
lean_inc_ref(v_projectDir_1422_);
v___x_1440_ = lean_array_push(v___x_1437_, v_projectDir_1422_);
lean_inc_ref(v_leanPrefix_1430_);
v___x_1441_ = lean_array_push(v___x_1440_, v_leanPrefix_1430_);
lean_inc_ref(v_lakeHome_1432_);
v___x_1442_ = lean_array_push(v___x_1441_, v_lakeHome_1432_);
v___x_1443_ = lean_array_push(v___x_1434_, v___x_1427_);
v___x_1444_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1445_ = 1;
v___x_1446_ = lean_box(0);
lean_inc_ref(v_whichLake_1431_);
v___x_1447_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1447_, 0, v_whichLake_1431_);
lean_ctor_set(v___x_1447_, 1, v___x_1435_);
lean_ctor_set(v___x_1447_, 2, v___x_1438_);
lean_ctor_set(v___x_1447_, 3, v___x_1439_);
lean_ctor_set(v___x_1447_, 4, v___x_1442_);
lean_ctor_set(v___x_1447_, 5, v___x_1443_);
lean_ctor_set(v___x_1447_, 6, v___x_1444_);
lean_ctor_set(v___x_1447_, 7, v___x_1446_);
lean_ctor_set_uint8(v___x_1447_, sizeof(void*)*8, v___x_1445_);
v___x_1448_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_1447_, v___y_1429_);
return v___x_1448_;
}
}
else
{
return v___x_1421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___boxed(lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_1451_);
lean_dec_ref(v_a_1451_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(lean_object* v_f_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v_fst_1468_; lean_object* v_snd_1469_; lean_object* v_r_1470_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v_fst_1468_ = lean_ctor_get(v_a_1467_, 0);
lean_inc(v_fst_1468_);
v_snd_1469_ = lean_ctor_get(v_a_1467_, 1);
lean_inc_n(v_snd_1469_, 2);
lean_dec(v_a_1467_);
lean_inc_ref(v___y_1464_);
v_r_1470_ = lean_apply_4(v_f_1463_, v_fst_1468_, v_snd_1469_, v___y_1464_, lean_box(0));
if (lean_obj_tag(v_r_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_ctor_get(v_r_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v_r_1470_, 1);
v___x_1472_ = lean_io_remove_file(v_snd_1469_);
lean_dec(v_snd_1469_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; 
v_unused_1480_ = lean_ctor_get(v___x_1472_, 0);
lean_dec(v_unused_1480_);
v___x_1474_ = v___x_1472_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_dec(v___x_1472_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v_a_1471_);
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1471_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec(v_a_1471_);
v_a_1481_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1472_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1472_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1490_; 
v_a_1489_ = lean_ctor_get(v_r_1470_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v_r_1470_, 1);
v___x_1490_ = lean_io_remove_file(v_snd_1469_);
lean_dec(v_snd_1469_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; 
v_unused_1498_ = lean_ctor_get(v___x_1490_, 0);
lean_dec(v_unused_1498_);
v___x_1492_ = v___x_1490_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_dec(v___x_1490_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 1);
lean_ctor_set(v___x_1492_, 0, v_a_1489_);
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1489_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_a_1489_);
v_a_1499_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1490_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1490_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec_ref(v_f_1463_);
v_a_1507_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1466_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1466_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg___boxed(lean_object* v_f_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v_f_1515_, v___y_1516_);
lean_dec_ref(v___y_1516_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1(lean_object* v_00_u03b1_1519_, lean_object* v_f_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v_f_1520_, v___y_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___boxed(lean_object* v_00_u03b1_1524_, lean_object* v_f_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1(v_00_u03b1_1524_, v_f_1525_, v___y_1526_);
lean_dec_ref(v___y_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0(lean_object* v_projectDir_1544_, lean_object* v_f_1545_, lean_object* v_handle_1546_, lean_object* v_path_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_leanPrefix_1550_; lean_object* v_whichLake_1551_; lean_object* v_lakeHome_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_leanPrefix_1550_ = lean_ctor_get(v___y_1548_, 6);
v_whichLake_1551_ = lean_ctor_get(v___y_1548_, 10);
v_lakeHome_1552_ = lean_ctor_get(v___y_1548_, 11);
v___x_1553_ = lean_unsigned_to_nat(1u);
v___x_1554_ = lean_mk_empty_array_with_capacity(v___x_1553_);
v___x_1555_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__1));
v___x_1556_ = lean_unsigned_to_nat(3u);
v___x_1557_ = lean_mk_empty_array_with_capacity(v___x_1556_);
v___x_1558_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2));
v___x_1559_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__4));
lean_inc_ref(v_projectDir_1544_);
v___x_1560_ = lean_array_push(v___x_1557_, v_projectDir_1544_);
lean_inc_ref(v_leanPrefix_1550_);
v___x_1561_ = lean_array_push(v___x_1560_, v_leanPrefix_1550_);
lean_inc_ref(v_lakeHome_1552_);
v___x_1562_ = lean_array_push(v___x_1561_, v_lakeHome_1552_);
v___x_1563_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
v___x_1564_ = l_System_FilePath_join(v_projectDir_1544_, v___x_1563_);
v___x_1565_ = lean_array_push(v___x_1554_, v___x_1564_);
v___x_1566_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1567_ = 0;
v___x_1568_ = lean_box(0);
lean_inc_ref(v_whichLake_1551_);
v___x_1569_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1569_, 0, v_whichLake_1551_);
lean_ctor_set(v___x_1569_, 1, v___x_1555_);
lean_ctor_set(v___x_1569_, 2, v___x_1558_);
lean_ctor_set(v___x_1569_, 3, v___x_1559_);
lean_ctor_set(v___x_1569_, 4, v___x_1562_);
lean_ctor_set(v___x_1569_, 5, v___x_1565_);
lean_ctor_set(v___x_1569_, 6, v___x_1566_);
lean_ctor_set(v___x_1569_, 7, v___x_1568_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*8, v___x_1567_);
v___x_1570_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_handle_1546_, v___x_1569_, v___y_1548_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v___x_1571_; 
lean_dec_ref_known(v___x_1570_, 1);
lean_inc_ref(v___y_1548_);
v___x_1571_ = lean_apply_3(v_f_1545_, v_path_1547_, v___y_1548_, lean_box(0));
return v___x_1571_;
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec_ref(v_path_1547_);
lean_dec_ref(v_f_1545_);
v_a_1572_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1570_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1570_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___boxed(lean_object* v_projectDir_1580_, lean_object* v_f_1581_, lean_object* v_handle_1582_, lean_object* v_path_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0(v_projectDir_1580_, v_f_1581_, v_handle_1582_, v_path_1583_, v___y_1584_);
lean_dec_ref(v___y_1584_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(uint8_t v_a_1587_, lean_object* v_x_1588_){
_start:
{
if (lean_obj_tag(v_x_1588_) == 0)
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_box(0);
return v___x_1589_;
}
else
{
lean_object* v_key_1590_; lean_object* v_value_1591_; lean_object* v_tail_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v_key_1590_ = lean_ctor_get(v_x_1588_, 0);
v_value_1591_ = lean_ctor_get(v_x_1588_, 1);
v_tail_1592_ = lean_ctor_get(v_x_1588_, 2);
v___x_1593_ = lean_obj_tag_nat(v_key_1590_);
v___x_1594_ = lean_box(v_a_1587_);
v___x_1595_ = lean_obj_tag_nat(v___x_1594_);
lean_dec(v___x_1594_);
v___x_1596_ = lean_nat_dec_eq(v___x_1593_, v___x_1595_);
if (v___x_1596_ == 0)
{
v_x_1588_ = v_tail_1592_;
goto _start;
}
else
{
lean_object* v___x_1598_; 
lean_inc(v_value_1591_);
v___x_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1598_, 0, v_value_1591_);
return v___x_1598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg___boxed(lean_object* v_a_1599_, lean_object* v_x_1600_){
_start:
{
uint8_t v_a_boxed_1601_; lean_object* v_res_1602_; 
v_a_boxed_1601_ = lean_unbox(v_a_1599_);
v_res_1602_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(v_a_boxed_1601_, v_x_1600_);
lean_dec(v_x_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(lean_object* v_m_1603_, uint8_t v_a_1604_){
_start:
{
lean_object* v_buckets_1605_; lean_object* v___x_1606_; uint64_t v___x_1607_; uint64_t v___x_1608_; uint64_t v___x_1609_; uint64_t v_fold_1610_; uint64_t v___x_1611_; uint64_t v___x_1612_; uint64_t v___x_1613_; size_t v___x_1614_; size_t v___x_1615_; size_t v___x_1616_; size_t v___x_1617_; size_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_buckets_1605_ = lean_ctor_get(v_m_1603_, 1);
v___x_1606_ = lean_array_get_size(v_buckets_1605_);
v___x_1607_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_a_1604_);
v___x_1608_ = 32ULL;
v___x_1609_ = lean_uint64_shift_right(v___x_1607_, v___x_1608_);
v_fold_1610_ = lean_uint64_xor(v___x_1607_, v___x_1609_);
v___x_1611_ = 16ULL;
v___x_1612_ = lean_uint64_shift_right(v_fold_1610_, v___x_1611_);
v___x_1613_ = lean_uint64_xor(v_fold_1610_, v___x_1612_);
v___x_1614_ = lean_uint64_to_usize(v___x_1613_);
v___x_1615_ = lean_usize_of_nat(v___x_1606_);
v___x_1616_ = ((size_t)1ULL);
v___x_1617_ = lean_usize_sub(v___x_1615_, v___x_1616_);
v___x_1618_ = lean_usize_land(v___x_1614_, v___x_1617_);
v___x_1619_ = lean_array_uget_borrowed(v_buckets_1605_, v___x_1618_);
v___x_1620_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(v_a_1604_, v___x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg___boxed(lean_object* v_m_1621_, lean_object* v_a_1622_){
_start:
{
uint8_t v_a_boxed_1623_; lean_object* v_res_1624_; 
v_a_boxed_1623_ = lean_unbox(v_a_1622_);
v_res_1624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_m_1621_, v_a_boxed_1623_);
lean_dec_ref(v_m_1621_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(lean_object* v_f_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v_projectDir_1629_; lean_object* v_moduleStore_1630_; uint8_t v___x_1631_; lean_object* v___x_1632_; 
v_projectDir_1629_ = lean_ctor_get(v_a_1627_, 0);
v_moduleStore_1630_ = lean_ctor_get(v_a_1627_, 17);
v___x_1631_ = 0;
v___x_1632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_moduleStore_1630_, v___x_1631_);
if (lean_obj_tag(v___x_1632_) == 1)
{
lean_object* v_val_1633_; lean_object* v___x_1634_; 
v_val_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_val_1633_);
lean_dec_ref_known(v___x_1632_, 1);
lean_inc_ref(v_a_1627_);
v___x_1634_ = lean_apply_3(v_f_1626_, v_val_1633_, v_a_1627_, lean_box(0));
return v___x_1634_;
}
else
{
lean_object* v___f_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec(v___x_1632_);
lean_inc_ref(v_projectDir_1629_);
v___f_1635_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_1635_, 0, v_projectDir_1629_);
lean_closure_set(v___f_1635_, 1, v_f_1626_);
v___x_1636_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___closed__0));
v___x_1637_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1636_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v___x_1638_; 
lean_dec_ref_known(v___x_1637_, 1);
v___x_1638_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v___f_1635_, v_a_1627_);
return v___x_1638_;
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec_ref(v___f_1635_);
v_a_1639_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1637_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1637_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___boxed(lean_object* v_f_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v_f_1647_, v_a_1648_);
lean_dec_ref(v_a_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport(lean_object* v_00_u03b1_1651_, lean_object* v_f_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v_f_1652_, v_a_1653_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___boxed(lean_object* v_00_u03b1_1656_, lean_object* v_f_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport(v_00_u03b1_1656_, v_f_1657_, v_a_1658_);
lean_dec_ref(v_a_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0(lean_object* v_00_u03b2_1661_, lean_object* v_m_1662_, uint8_t v_a_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_m_1662_, v_a_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___boxed(lean_object* v_00_u03b2_1665_, lean_object* v_m_1666_, lean_object* v_a_1667_){
_start:
{
uint8_t v_a_boxed_1668_; lean_object* v_res_1669_; 
v_a_boxed_1668_ = lean_unbox(v_a_1667_);
v_res_1669_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0(v_00_u03b2_1665_, v_m_1666_, v_a_boxed_1668_);
lean_dec_ref(v_m_1666_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0(lean_object* v_00_u03b2_1670_, uint8_t v_a_1671_, lean_object* v_x_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(v_a_1671_, v_x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1674_, lean_object* v_a_1675_, lean_object* v_x_1676_){
_start:
{
uint8_t v_a_boxed_1677_; lean_object* v_res_1678_; 
v_a_boxed_1677_ = lean_unbox(v_a_1675_);
v_res_1678_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0(v_00_u03b2_1674_, v_a_boxed_1677_, v_x_1676_);
lean_dec(v_x_1676_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(size_t v_sz_1679_, size_t v_i_1680_, lean_object* v_bs_1681_){
_start:
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_usize_dec_lt(v_i_1680_, v_sz_1679_);
if (v___x_1682_ == 0)
{
return v_bs_1681_;
}
else
{
lean_object* v_v_1683_; lean_object* v___x_1684_; lean_object* v_bs_x27_1685_; lean_object* v___x_1686_; size_t v___x_1687_; size_t v___x_1688_; lean_object* v___x_1689_; 
v_v_1683_ = lean_array_uget(v_bs_1681_, v_i_1680_);
v___x_1684_ = lean_unsigned_to_nat(0u);
v_bs_x27_1685_ = lean_array_uset(v_bs_1681_, v_i_1680_, v___x_1684_);
v___x_1686_ = l_Lean_Name_toString(v_v_1683_, v___x_1682_);
v___x_1687_ = ((size_t)1ULL);
v___x_1688_ = lean_usize_add(v_i_1680_, v___x_1687_);
v___x_1689_ = lean_array_uset(v_bs_x27_1685_, v_i_1680_, v___x_1686_);
v_i_1680_ = v___x_1688_;
v_bs_1681_ = v___x_1689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0___boxed(lean_object* v_sz_1691_, lean_object* v_i_1692_, lean_object* v_bs_1693_){
_start:
{
size_t v_sz_boxed_1694_; size_t v_i_boxed_1695_; lean_object* v_res_1696_; 
v_sz_boxed_1694_ = lean_unbox_usize(v_sz_1691_);
lean_dec(v_sz_1691_);
v_i_boxed_1695_ = lean_unbox_usize(v_i_1692_);
lean_dec(v_i_1692_);
v_res_1696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_boxed_1694_, v_i_boxed_1695_, v_bs_1693_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(lean_object* v_targets_1704_, lean_object* v_a_1705_){
_start:
{
size_t v_sz_1707_; size_t v___x_1708_; lean_object* v_targetArgs_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v_targetList_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_sz_1707_ = lean_array_size(v_targets_1704_);
v___x_1708_ = ((size_t)0ULL);
v_targetArgs_1709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_1707_, v___x_1708_, v_targets_1704_);
v___x_1710_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
lean_inc_ref(v_targetArgs_1709_);
v___x_1711_ = lean_array_to_list(v_targetArgs_1709_);
v_targetList_1712_ = l_String_intercalate(v___x_1710_, v___x_1711_);
v___x_1713_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1));
v___x_1714_ = lean_string_append(v___x_1713_, v_targetList_1712_);
lean_dec_ref(v_targetList_1712_);
v___x_1715_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1714_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_projectDir_1716_; lean_object* v_leanPrefix_1717_; lean_object* v_whichLake_1718_; lean_object* v_lakeHome_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___y_1723_; lean_object* v_leanPrefix_1724_; lean_object* v_whichLake_1725_; lean_object* v_lakeHome_1726_; uint8_t v___x_1744_; 
lean_dec_ref_known(v___x_1715_, 1);
v_projectDir_1716_ = lean_ctor_get(v_a_1705_, 0);
v_leanPrefix_1717_ = lean_ctor_get(v_a_1705_, 6);
v_whichLake_1718_ = lean_ctor_get(v_a_1705_, 10);
v_lakeHome_1719_ = lean_ctor_get(v_a_1705_, 11);
v___x_1720_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1716_);
v___x_1721_ = l_System_FilePath_join(v_projectDir_1716_, v___x_1720_);
v___x_1744_ = l_System_FilePath_pathExists(v___x_1721_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_io_create_dir(v___x_1721_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_dec_ref_known(v___x_1745_, 1);
v___y_1723_ = v_a_1705_;
v_leanPrefix_1724_ = v_leanPrefix_1717_;
v_whichLake_1725_ = v_whichLake_1718_;
v_lakeHome_1726_ = v_lakeHome_1719_;
goto v___jp_1722_;
}
else
{
lean_dec_ref(v___x_1721_);
lean_dec_ref(v_targetArgs_1709_);
return v___x_1745_;
}
}
else
{
v___y_1723_ = v_a_1705_;
v_leanPrefix_1724_ = v_leanPrefix_1717_;
v_whichLake_1725_ = v_whichLake_1718_;
v_lakeHome_1726_ = v_lakeHome_1719_;
goto v___jp_1722_;
}
v___jp_1722_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1727_ = lean_unsigned_to_nat(1u);
v___x_1728_ = lean_mk_empty_array_with_capacity(v___x_1727_);
v___x_1729_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3));
v___x_1730_ = l_Array_append___redArg(v___x_1729_, v_targetArgs_1709_);
lean_dec_ref(v_targetArgs_1709_);
v___x_1731_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8));
v___x_1732_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1733_ = lean_unsigned_to_nat(3u);
v___x_1734_ = lean_mk_empty_array_with_capacity(v___x_1733_);
lean_inc_ref(v_projectDir_1716_);
v___x_1735_ = lean_array_push(v___x_1734_, v_projectDir_1716_);
lean_inc_ref(v_leanPrefix_1724_);
v___x_1736_ = lean_array_push(v___x_1735_, v_leanPrefix_1724_);
lean_inc_ref(v_lakeHome_1726_);
v___x_1737_ = lean_array_push(v___x_1736_, v_lakeHome_1726_);
v___x_1738_ = lean_array_push(v___x_1728_, v___x_1721_);
v___x_1739_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1740_ = 0;
v___x_1741_ = lean_box(0);
lean_inc_ref(v_whichLake_1725_);
v___x_1742_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1742_, 0, v_whichLake_1725_);
lean_ctor_set(v___x_1742_, 1, v___x_1730_);
lean_ctor_set(v___x_1742_, 2, v___x_1731_);
lean_ctor_set(v___x_1742_, 3, v___x_1732_);
lean_ctor_set(v___x_1742_, 4, v___x_1737_);
lean_ctor_set(v___x_1742_, 5, v___x_1738_);
lean_ctor_set(v___x_1742_, 6, v___x_1739_);
lean_ctor_set(v___x_1742_, 7, v___x_1741_);
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*8, v___x_1740_);
v___x_1743_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_1742_, v___y_1723_);
return v___x_1743_;
}
}
else
{
lean_dec_ref(v_targetArgs_1709_);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___boxed(lean_object* v_targets_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v_targets_1746_, v_a_1747_);
lean_dec_ref(v_a_1747_);
return v_res_1749_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1759_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11));
v___x_1760_ = lean_unsigned_to_nat(3u);
v___x_1761_ = lean_mk_empty_array_with_capacity(v___x_1760_);
v___x_1762_ = lean_array_push(v___x_1761_, v___x_1759_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(lean_object* v_projectDir_1763_, lean_object* v_whichLean4Export_1764_, lean_object* v_args_1765_, lean_object* v_f_1766_, lean_object* v_exportHandle_1767_, lean_object* v_exportPath_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_leanPrefix_1771_; lean_object* v_leanPath_1772_; lean_object* v_binPath_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v_leanPrefix_1771_ = lean_ctor_get(v___y_1769_, 6);
v_leanPath_1772_ = lean_ctor_get(v___y_1769_, 7);
v_binPath_1773_ = lean_ctor_get(v___y_1769_, 8);
v___x_1774_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6));
v___x_1775_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__0));
v___x_1776_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__1));
lean_inc_ref(v_leanPath_1772_);
v___x_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_leanPath_1772_);
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1775_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
lean_inc_ref(v_binPath_1773_);
v___x_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1779_, 0, v_binPath_1773_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1774_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2);
v___x_1782_ = lean_array_push(v___x_1781_, v___x_1778_);
v___x_1783_ = lean_array_push(v___x_1782_, v___x_1780_);
v___x_1784_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1763_);
v___x_1785_ = l_System_FilePath_join(v_projectDir_1763_, v___x_1784_);
v___x_1786_ = lean_unsigned_to_nat(4u);
v___x_1787_ = lean_mk_empty_array_with_capacity(v___x_1786_);
v___x_1788_ = lean_array_push(v___x_1787_, v_projectDir_1763_);
v___x_1789_ = lean_array_push(v___x_1788_, v___x_1785_);
lean_inc_ref(v_leanPrefix_1771_);
v___x_1790_ = lean_array_push(v___x_1789_, v_leanPrefix_1771_);
lean_inc_ref(v_whichLean4Export_1764_);
v___x_1791_ = lean_array_push(v___x_1790_, v_whichLean4Export_1764_);
v___x_1792_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1793_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1794_ = 0;
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1796_, 0, v_whichLean4Export_1764_);
lean_ctor_set(v___x_1796_, 1, v_args_1765_);
lean_ctor_set(v___x_1796_, 2, v___x_1776_);
lean_ctor_set(v___x_1796_, 3, v___x_1783_);
lean_ctor_set(v___x_1796_, 4, v___x_1791_);
lean_ctor_set(v___x_1796_, 5, v___x_1792_);
lean_ctor_set(v___x_1796_, 6, v___x_1793_);
lean_ctor_set(v___x_1796_, 7, v___x_1795_);
lean_ctor_set_uint8(v___x_1796_, sizeof(void*)*8, v___x_1794_);
v___x_1797_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_exportHandle_1767_, v___x_1796_, v___y_1769_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v___x_1798_; 
lean_dec_ref_known(v___x_1797_, 1);
lean_inc_ref(v___y_1769_);
v___x_1798_ = lean_apply_3(v_f_1766_, v_exportPath_1768_, v___y_1769_, lean_box(0));
return v___x_1798_;
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref(v_exportPath_1768_);
lean_dec_ref(v_f_1766_);
v_a_1799_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1797_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1797_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___boxed(lean_object* v_projectDir_1807_, lean_object* v_whichLean4Export_1808_, lean_object* v_args_1809_, lean_object* v_f_1810_, lean_object* v_exportHandle_1811_, lean_object* v_exportPath_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(v_projectDir_1807_, v_whichLean4Export_1808_, v_args_1809_, v_f_1810_, v_exportHandle_1811_, v_exportPath_1812_, v___y_1813_);
lean_dec_ref(v___y_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(lean_object* v_args_1816_, lean_object* v_f_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_projectDir_1820_; lean_object* v_whichLean4Export_1821_; lean_object* v___f_1822_; lean_object* v___x_1823_; 
v_projectDir_1820_ = lean_ctor_get(v_a_1818_, 0);
v_whichLean4Export_1821_ = lean_ctor_get(v_a_1818_, 12);
lean_inc_ref(v_whichLean4Export_1821_);
lean_inc_ref(v_projectDir_1820_);
v___f_1822_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_1822_, 0, v_projectDir_1820_);
lean_closure_set(v___f_1822_, 1, v_whichLean4Export_1821_);
lean_closure_set(v___f_1822_, 2, v_args_1816_);
lean_closure_set(v___f_1822_, 3, v_f_1817_);
v___x_1823_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v___f_1822_, v_a_1818_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___boxed(lean_object* v_args_1824_, lean_object* v_f_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v_args_1824_, v_f_1825_, v_a_1826_);
lean_dec_ref(v_a_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(lean_object* v_00_u03b1_1829_, lean_object* v_args_1830_, lean_object* v_f_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v_args_1830_, v_f_1831_, v_a_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___boxed(lean_object* v_00_u03b1_1835_, lean_object* v_args_1836_, lean_object* v_f_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(v_00_u03b1_1835_, v_args_1836_, v_f_1837_, v_a_1838_);
lean_dec_ref(v_a_1838_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0(lean_object* v_x_1842_, lean_object* v_x_1843_){
_start:
{
if (lean_obj_tag(v_x_1843_) == 0)
{
return v_x_1842_;
}
else
{
lean_object* v_head_1844_; lean_object* v_tail_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_head_1844_ = lean_ctor_get(v_x_1843_, 0);
lean_inc(v_head_1844_);
v_tail_1845_ = lean_ctor_get(v_x_1843_, 1);
lean_inc(v_tail_1845_);
lean_dec_ref_known(v_x_1843_, 2);
v___x_1846_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0));
v___x_1847_ = lean_string_append(v_x_1842_, v___x_1846_);
v___x_1848_ = 1;
v___x_1849_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1844_, v___x_1848_);
v___x_1850_ = lean_string_append(v___x_1847_, v___x_1849_);
lean_dec_ref(v___x_1849_);
v_x_1842_ = v___x_1850_;
v_x_1843_ = v_tail_1845_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0(lean_object* v_x_1855_){
_start:
{
if (lean_obj_tag(v_x_1855_) == 0)
{
lean_object* v___x_1856_; 
v___x_1856_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__0));
return v___x_1856_;
}
else
{
lean_object* v_tail_1857_; 
v_tail_1857_ = lean_ctor_get(v_x_1855_, 1);
if (lean_obj_tag(v_tail_1857_) == 0)
{
lean_object* v_head_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_head_1858_ = lean_ctor_get(v_x_1855_, 0);
lean_inc(v_head_1858_);
lean_dec_ref_known(v_x_1855_, 2);
v___x_1859_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_1860_ = 1;
v___x_1861_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1858_, v___x_1860_);
v___x_1862_ = lean_string_append(v___x_1859_, v___x_1861_);
lean_dec_ref(v___x_1861_);
v___x_1863_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__2));
v___x_1864_ = lean_string_append(v___x_1862_, v___x_1863_);
return v___x_1864_;
}
else
{
lean_object* v_head_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint32_t v___x_1871_; lean_object* v___x_1872_; 
lean_inc(v_tail_1857_);
v_head_1865_ = lean_ctor_get(v_x_1855_, 0);
lean_inc(v_head_1865_);
lean_dec_ref_known(v_x_1855_, 2);
v___x_1866_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_1867_ = 1;
v___x_1868_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1865_, v___x_1867_);
v___x_1869_ = lean_string_append(v___x_1866_, v___x_1868_);
lean_dec_ref(v___x_1868_);
v___x_1870_ = l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0(v___x_1869_, v_tail_1857_);
v___x_1871_ = 93;
v___x_1872_ = lean_string_push(v___x_1870_, v___x_1871_);
return v___x_1872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(size_t v_sz_1873_, size_t v_i_1874_, lean_object* v_bs_1875_){
_start:
{
uint8_t v___x_1876_; 
v___x_1876_ = lean_usize_dec_lt(v_i_1874_, v_sz_1873_);
if (v___x_1876_ == 0)
{
return v_bs_1875_;
}
else
{
lean_object* v_v_1877_; lean_object* v___x_1878_; lean_object* v_bs_x27_1879_; lean_object* v___x_1880_; size_t v___x_1881_; size_t v___x_1882_; lean_object* v___x_1883_; 
v_v_1877_ = lean_array_uget(v_bs_1875_, v_i_1874_);
v___x_1878_ = lean_unsigned_to_nat(0u);
v_bs_x27_1879_ = lean_array_uset(v_bs_1875_, v_i_1874_, v___x_1878_);
v___x_1880_ = l_Lean_Name_toString(v_v_1877_, v___x_1876_);
v___x_1881_ = ((size_t)1ULL);
v___x_1882_ = lean_usize_add(v_i_1874_, v___x_1881_);
v___x_1883_ = lean_array_uset(v_bs_x27_1879_, v_i_1874_, v___x_1880_);
v_i_1874_ = v___x_1882_;
v_bs_1875_ = v___x_1883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1___boxed(lean_object* v_sz_1885_, lean_object* v_i_1886_, lean_object* v_bs_1887_){
_start:
{
size_t v_sz_boxed_1888_; size_t v_i_boxed_1889_; lean_object* v_res_1890_; 
v_sz_boxed_1888_ = lean_unbox_usize(v_sz_1885_);
lean_dec(v_sz_1885_);
v_i_boxed_1889_ = lean_unbox_usize(v_i_1886_);
lean_dec(v_i_1886_);
v_res_1890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(v_sz_boxed_1888_, v_i_boxed_1889_, v_bs_1887_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(lean_object* v_module_1894_, lean_object* v_decls_1895_, lean_object* v_f_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1899_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__0));
v___x_1900_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__1));
lean_inc_ref(v_decls_1895_);
v___x_1901_ = lean_array_to_list(v_decls_1895_);
v___x_1902_ = l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0(v___x_1901_);
v___x_1903_ = lean_string_append(v___x_1900_, v___x_1902_);
lean_dec_ref(v___x_1902_);
v___x_1904_ = lean_string_append(v___x_1899_, v___x_1903_);
lean_dec_ref(v___x_1903_);
v___x_1905_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__2));
v___x_1906_ = lean_string_append(v___x_1904_, v___x_1905_);
v___x_1907_ = 1;
lean_inc(v_module_1894_);
v___x_1908_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_1894_, v___x_1907_);
v___x_1909_ = lean_string_append(v___x_1906_, v___x_1908_);
lean_dec_ref(v___x_1908_);
v___x_1910_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1909_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; size_t v_sz_1917_; size_t v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec_ref_known(v___x_1910_, 1);
v___x_1911_ = l_Lean_Name_toString(v_module_1894_, v___x_1907_);
v___x_1912_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__8));
v___x_1913_ = lean_unsigned_to_nat(2u);
v___x_1914_ = lean_mk_empty_array_with_capacity(v___x_1913_);
v___x_1915_ = lean_array_push(v___x_1914_, v___x_1911_);
v___x_1916_ = lean_array_push(v___x_1915_, v___x_1912_);
v_sz_1917_ = lean_array_size(v_decls_1895_);
v___x_1918_ = ((size_t)0ULL);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(v_sz_1917_, v___x_1918_, v_decls_1895_);
v___x_1920_ = l_Array_append___redArg(v___x_1916_, v___x_1919_);
lean_dec_ref(v___x_1919_);
v___x_1921_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v___x_1920_, v_f_1896_, v_a_1897_);
return v___x_1921_;
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec_ref(v_f_1896_);
lean_dec_ref(v_decls_1895_);
lean_dec(v_module_1894_);
v_a_1922_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1910_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1910_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___boxed(lean_object* v_module_1930_, lean_object* v_decls_1931_, lean_object* v_f_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1930_, v_decls_1931_, v_f_1932_, v_a_1933_);
lean_dec_ref(v_a_1933_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(lean_object* v_00_u03b1_1936_, lean_object* v_module_1937_, lean_object* v_decls_1938_, lean_object* v_f_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1937_, v_decls_1938_, v_f_1939_, v_a_1940_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___boxed(lean_object* v_00_u03b1_1943_, lean_object* v_module_1944_, lean_object* v_decls_1945_, lean_object* v_f_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(v_00_u03b1_1943_, v_module_1944_, v_decls_1945_, v_f_1946_, v_a_1947_);
lean_dec_ref(v_a_1947_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(uint8_t v_kind_1950_, lean_object* v_module_1951_, lean_object* v_decls_1952_, lean_object* v_f_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_moduleStore_1956_; lean_object* v___x_1957_; 
v_moduleStore_1956_ = lean_ctor_get(v_a_1954_, 17);
v___x_1957_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_moduleStore_1956_, v_kind_1950_);
if (lean_obj_tag(v___x_1957_) == 1)
{
lean_object* v_val_1958_; lean_object* v___x_1959_; 
lean_dec_ref(v_decls_1952_);
lean_dec(v_module_1951_);
v_val_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_val_1958_);
lean_dec_ref_known(v___x_1957_, 1);
lean_inc_ref(v_a_1954_);
v___x_1959_ = lean_apply_3(v_f_1953_, v_val_1958_, v_a_1954_, lean_box(0));
return v___x_1959_;
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_dec(v___x_1957_);
v___x_1960_ = lean_unsigned_to_nat(1u);
v___x_1961_ = lean_mk_empty_array_with_capacity(v___x_1960_);
lean_inc(v_module_1951_);
v___x_1962_ = lean_array_push(v___x_1961_, v_module_1951_);
v___x_1963_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v___x_1962_, v_a_1954_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v___x_1964_; 
lean_dec_ref_known(v___x_1963_, 1);
v___x_1964_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1951_, v_decls_1952_, v_f_1953_, v_a_1954_);
return v___x_1964_;
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec_ref(v_f_1953_);
lean_dec_ref(v_decls_1952_);
lean_dec(v_module_1951_);
v_a_1965_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1963_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1963_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___boxed(lean_object* v_kind_1973_, lean_object* v_module_1974_, lean_object* v_decls_1975_, lean_object* v_f_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
uint8_t v_kind_boxed_1979_; lean_object* v_res_1980_; 
v_kind_boxed_1979_ = lean_unbox(v_kind_1973_);
v_res_1980_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v_kind_boxed_1979_, v_module_1974_, v_decls_1975_, v_f_1976_, v_a_1977_);
lean_dec_ref(v_a_1977_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(lean_object* v_00_u03b1_1981_, uint8_t v_kind_1982_, lean_object* v_module_1983_, lean_object* v_decls_1984_, lean_object* v_f_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v_kind_1982_, v_module_1983_, v_decls_1984_, v_f_1985_, v_a_1986_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___boxed(lean_object* v_00_u03b1_1989_, lean_object* v_kind_1990_, lean_object* v_module_1991_, lean_object* v_decls_1992_, lean_object* v_f_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
uint8_t v_kind_boxed_1996_; lean_object* v_res_1997_; 
v_kind_boxed_1996_ = lean_unbox(v_kind_1990_);
v_res_1997_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(v_00_u03b1_1989_, v_kind_boxed_1996_, v_module_1991_, v_decls_1992_, v_f_1993_, v_a_1994_);
lean_dec_ref(v_a_1994_);
return v_res_1997_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(lean_object* v_s_1998_, lean_object* v_a_1999_, uint8_t v_b_2000_){
_start:
{
uint8_t v___x_2001_; 
v___x_2001_ = 0;
switch(lean_obj_tag(v_a_1999_))
{
case 0:
{
lean_object* v_pos_2002_; lean_object* v_startInclusive_2003_; lean_object* v_endExclusive_2004_; lean_object* v___x_2005_; uint8_t v_decide_2006_; 
v_pos_2002_ = lean_ctor_get(v_a_1999_, 0);
lean_inc(v_pos_2002_);
lean_dec_ref_known(v_a_1999_, 1);
v_startInclusive_2003_ = lean_ctor_get(v_s_1998_, 1);
v_endExclusive_2004_ = lean_ctor_get(v_s_1998_, 2);
v___x_2005_ = lean_nat_sub(v_endExclusive_2004_, v_startInclusive_2003_);
v_decide_2006_ = lean_nat_dec_eq(v_pos_2002_, v___x_2005_);
lean_dec(v___x_2005_);
lean_dec(v_pos_2002_);
if (v_decide_2006_ == 0)
{
uint8_t v___x_2007_; 
v___x_2007_ = 1;
return v___x_2007_;
}
else
{
return v_decide_2006_;
}
}
case 1:
{
lean_object* v_pos_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2021_; 
v_pos_2008_ = lean_ctor_get(v_a_1999_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_a_1999_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2010_ = v_a_1999_;
v_isShared_2011_ = v_isSharedCheck_2021_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_pos_2008_);
lean_dec(v_a_1999_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2021_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_str_2012_; lean_object* v_startInclusive_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
v_str_2012_ = lean_ctor_get(v_s_1998_, 0);
v_startInclusive_2013_ = lean_ctor_get(v_s_1998_, 1);
v___x_2014_ = lean_nat_add(v_startInclusive_2013_, v_pos_2008_);
lean_dec(v_pos_2008_);
v___x_2015_ = lean_string_utf8_next_fast(v_str_2012_, v___x_2014_);
lean_dec(v___x_2014_);
v___x_2016_ = lean_nat_sub(v___x_2015_, v_startInclusive_2013_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set_tag(v___x_2010_, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2016_);
v___x_2018_ = v___x_2010_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
v_a_1999_ = v___x_2018_;
v_b_2000_ = v___x_2001_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2022_; lean_object* v_table_2023_; lean_object* v_stackPos_2024_; lean_object* v_needlePos_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2080_; 
v_needle_2022_ = lean_ctor_get(v_a_1999_, 0);
v_table_2023_ = lean_ctor_get(v_a_1999_, 1);
v_stackPos_2024_ = lean_ctor_get(v_a_1999_, 2);
v_needlePos_2025_ = lean_ctor_get(v_a_1999_, 3);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_a_1999_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2027_ = v_a_1999_;
v_isShared_2028_ = v_isSharedCheck_2080_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_needlePos_2025_);
lean_inc(v_stackPos_2024_);
lean_inc(v_table_2023_);
lean_inc(v_needle_2022_);
lean_dec(v_a_1999_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2080_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v_str_2029_; lean_object* v_startInclusive_2030_; lean_object* v_endExclusive_2031_; lean_object* v_str_2032_; lean_object* v_startInclusive_2033_; lean_object* v_endExclusive_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v_str_2029_ = lean_ctor_get(v_needle_2022_, 0);
v_startInclusive_2030_ = lean_ctor_get(v_needle_2022_, 1);
v_endExclusive_2031_ = lean_ctor_get(v_needle_2022_, 2);
v_str_2032_ = lean_ctor_get(v_s_1998_, 0);
v_startInclusive_2033_ = lean_ctor_get(v_s_1998_, 1);
v_endExclusive_2034_ = lean_ctor_get(v_s_1998_, 2);
v___x_2035_ = lean_nat_sub(v_stackPos_2024_, v_needlePos_2025_);
v___x_2036_ = lean_nat_sub(v_endExclusive_2031_, v_startInclusive_2030_);
v___x_2037_ = lean_nat_add(v___x_2035_, v___x_2036_);
v___x_2038_ = lean_nat_sub(v_endExclusive_2034_, v_startInclusive_2033_);
v___x_2039_ = lean_nat_dec_le(v___x_2037_, v___x_2038_);
lean_dec(v___x_2037_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
lean_dec(v___x_2036_);
lean_del_object(v___x_2027_);
lean_dec(v_needlePos_2025_);
lean_dec(v_stackPos_2024_);
lean_dec_ref(v_table_2023_);
lean_dec_ref(v_needle_2022_);
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_nat_add(v___x_2035_, v___x_2040_);
lean_dec(v___x_2035_);
v___x_2042_ = lean_nat_dec_le(v___x_2041_, v___x_2038_);
lean_dec(v___x_2038_);
lean_dec(v___x_2041_);
if (v___x_2042_ == 0)
{
return v_b_2000_;
}
else
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_box(3);
v_a_1999_ = v___x_2043_;
v_b_2000_ = v___x_2001_;
goto _start;
}
}
else
{
lean_object* v___x_2045_; uint8_t v_stackByte_2046_; lean_object* v___x_2047_; uint8_t v_patByte_2048_; uint8_t v___x_2049_; 
lean_dec(v___x_2038_);
lean_dec(v___x_2035_);
v___x_2045_ = lean_nat_add(v_startInclusive_2033_, v_stackPos_2024_);
v_stackByte_2046_ = lean_string_get_byte_fast(v_str_2032_, v___x_2045_);
v___x_2047_ = lean_nat_add(v_startInclusive_2030_, v_needlePos_2025_);
v_patByte_2048_ = lean_string_get_byte_fast(v_str_2029_, v___x_2047_);
v___x_2049_ = lean_uint8_dec_eq(v_stackByte_2046_, v_patByte_2048_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; uint8_t v_decide_2051_; 
lean_dec(v___x_2036_);
v___x_2050_ = lean_unsigned_to_nat(0u);
v_decide_2051_ = lean_nat_dec_eq(v_needlePos_2025_, v___x_2050_);
if (v_decide_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_newNeedlePos_2054_; uint8_t v___x_2055_; 
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = lean_nat_sub(v_needlePos_2025_, v___x_2052_);
lean_dec(v_needlePos_2025_);
v_newNeedlePos_2054_ = lean_array_fget_borrowed(v_table_2023_, v___x_2053_);
lean_dec(v___x_2053_);
v___x_2055_ = lean_nat_dec_eq(v_newNeedlePos_2054_, v___x_2050_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2057_; 
lean_inc(v_newNeedlePos_2054_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 3, v_newNeedlePos_2054_);
v___x_2057_ = v___x_2027_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_needle_2022_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_table_2023_);
lean_ctor_set(v_reuseFailAlloc_2059_, 2, v_stackPos_2024_);
lean_ctor_set(v_reuseFailAlloc_2059_, 3, v_newNeedlePos_2054_);
v___x_2057_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
v_a_1999_ = v___x_2057_;
v_b_2000_ = v___x_2001_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2060_; lean_object* v___x_2062_; 
v_nextStackPos_2060_ = l_String_Slice_posGE___redArg(v_s_1998_, v_stackPos_2024_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 3, v___x_2050_);
lean_ctor_set(v___x_2027_, 2, v_nextStackPos_2060_);
v___x_2062_ = v___x_2027_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_needle_2022_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_table_2023_);
lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_nextStackPos_2060_);
lean_ctor_set(v_reuseFailAlloc_2064_, 3, v___x_2050_);
v___x_2062_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
v_a_1999_ = v___x_2062_;
v_b_2000_ = v___x_2001_;
goto _start;
}
}
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v_nextStackPos_2067_; lean_object* v___x_2069_; 
lean_dec(v_needlePos_2025_);
v___x_2065_ = lean_unsigned_to_nat(1u);
v___x_2066_ = lean_nat_add(v_stackPos_2024_, v___x_2065_);
lean_dec(v_stackPos_2024_);
v_nextStackPos_2067_ = l_String_Slice_posGE___redArg(v_s_1998_, v___x_2066_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 3, v___x_2050_);
lean_ctor_set(v___x_2027_, 2, v_nextStackPos_2067_);
v___x_2069_ = v___x_2027_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_needle_2022_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_table_2023_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_nextStackPos_2067_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v___x_2050_);
v___x_2069_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
v_a_1999_ = v___x_2069_;
v_b_2000_ = v___x_2001_;
goto _start;
}
}
}
else
{
lean_object* v___x_2072_; lean_object* v_nextNeedlePos_2073_; uint8_t v_decide_2074_; 
v___x_2072_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2073_ = lean_nat_add(v_needlePos_2025_, v___x_2072_);
lean_dec(v_needlePos_2025_);
v_decide_2074_ = lean_nat_dec_eq(v_nextNeedlePos_2073_, v___x_2036_);
lean_dec(v___x_2036_);
if (v_decide_2074_ == 0)
{
lean_object* v_nextStackPos_2075_; lean_object* v___x_2077_; 
v_nextStackPos_2075_ = lean_nat_add(v_stackPos_2024_, v___x_2072_);
lean_dec(v_stackPos_2024_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 3, v_nextNeedlePos_2073_);
lean_ctor_set(v___x_2027_, 2, v_nextStackPos_2075_);
v___x_2077_ = v___x_2027_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_needle_2022_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_table_2023_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_nextStackPos_2075_);
lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_nextNeedlePos_2073_);
v___x_2077_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
v_a_1999_ = v___x_2077_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2073_);
lean_del_object(v___x_2027_);
lean_dec(v_stackPos_2024_);
lean_dec_ref(v_table_2023_);
lean_dec_ref(v_needle_2022_);
return v_decide_2074_;
}
}
}
}
}
default: 
{
return v_b_2000_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg___boxed(lean_object* v_s_2081_, lean_object* v_a_2082_, lean_object* v_b_2083_){
_start:
{
uint8_t v_b_boxed_2084_; uint8_t v_res_2085_; lean_object* v_r_2086_; 
v_b_boxed_2084_ = lean_unbox(v_b_2083_);
v_res_2085_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_2081_, v_a_2082_, v_b_boxed_2084_);
lean_dec_ref(v_s_2081_);
v_r_2086_ = lean_box(v_res_2085_);
return v_r_2086_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1));
v___x_2093_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2092_);
return v___x_2093_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2);
v___x_2096_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1));
v___x_2097_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v___x_2095_);
lean_ctor_set(v___x_2097_, 2, v___x_2094_);
lean_ctor_set(v___x_2097_, 3, v___x_2094_);
return v___x_2097_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(lean_object* v_s_2098_){
_start:
{
lean_object* v___x_2099_; uint8_t v___x_2100_; uint8_t v___x_2101_; 
v___x_2099_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3);
v___x_2100_ = 0;
v___x_2101_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_2098_, v___x_2099_, v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___boxed(lean_object* v_s_2102_){
_start:
{
uint8_t v_res_2103_; lean_object* v_r_2104_; 
v_res_2103_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v_s_2102_);
lean_dec_ref(v_s_2102_);
v_r_2104_ = lean_box(v_res_2103_);
return v_r_2104_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(lean_object* v_kernelName_2105_){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2106_ = lean_unsigned_to_nat(0u);
v___x_2107_ = lean_string_utf8_byte_size(v_kernelName_2105_);
v___x_2108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2108_, 0, v_kernelName_2105_);
lean_ctor_set(v___x_2108_, 1, v___x_2106_);
lean_ctor_set(v___x_2108_, 2, v___x_2107_);
v___x_2109_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v___x_2108_);
lean_dec_ref_known(v___x_2108_, 3);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel___boxed(lean_object* v_kernelName_2110_){
_start:
{
uint8_t v_res_2111_; lean_object* v_r_2112_; 
v_res_2111_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_2110_);
v_r_2112_ = lean_box(v_res_2111_);
return v_r_2112_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(lean_object* v_s_2113_, lean_object* v_inst_2114_, lean_object* v_R_2115_, lean_object* v_a_2116_, uint8_t v_b_2117_, lean_object* v_c_2118_){
_start:
{
uint8_t v___x_2119_; 
v___x_2119_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_2113_, v_a_2116_, v_b_2117_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___boxed(lean_object* v_s_2120_, lean_object* v_inst_2121_, lean_object* v_R_2122_, lean_object* v_a_2123_, lean_object* v_b_2124_, lean_object* v_c_2125_){
_start:
{
uint8_t v_b_boxed_2126_; uint8_t v_res_2127_; lean_object* v_r_2128_; 
v_b_boxed_2126_ = lean_unbox(v_b_2124_);
v_res_2127_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(v_s_2120_, v_inst_2121_, v_R_2122_, v_a_2123_, v_b_boxed_2126_, v_c_2125_);
lean_dec_ref(v_s_2120_);
v_r_2128_ = lean_box(v_res_2127_);
return v_r_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(lean_object* v_a_2129_, lean_object* v_b_2130_){
_start:
{
lean_object* v_array_2131_; lean_object* v_start_2132_; lean_object* v_stop_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2146_; 
v_array_2131_ = lean_ctor_get(v_a_2129_, 0);
v_start_2132_ = lean_ctor_get(v_a_2129_, 1);
v_stop_2133_ = lean_ctor_get(v_a_2129_, 2);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_a_2129_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2135_ = v_a_2129_;
v_isShared_2136_ = v_isSharedCheck_2146_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_stop_2133_);
lean_inc(v_start_2132_);
lean_inc(v_array_2131_);
lean_dec(v_a_2129_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2146_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
uint8_t v___x_2137_; 
v___x_2137_ = lean_nat_dec_lt(v_start_2132_, v_stop_2133_);
if (v___x_2137_ == 0)
{
lean_del_object(v___x_2135_);
lean_dec(v_stop_2133_);
lean_dec(v_start_2132_);
lean_dec_ref(v_array_2131_);
return v_b_2130_;
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2138_ = lean_unsigned_to_nat(1u);
v___x_2139_ = lean_nat_add(v_start_2132_, v___x_2138_);
lean_inc_ref(v_array_2131_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 1, v___x_2139_);
v___x_2141_ = v___x_2135_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_array_2131_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_stop_2133_);
v___x_2141_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_array_fget(v_array_2131_, v_start_2132_);
lean_dec(v_start_2132_);
lean_dec_ref(v_array_2131_);
v___x_2143_ = lean_array_push(v_b_2130_, v___x_2142_);
v_a_2129_ = v___x_2141_;
v_b_2130_ = v___x_2143_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(size_t v_sz_2147_, size_t v_i_2148_, lean_object* v_bs_2149_){
_start:
{
uint8_t v___x_2150_; 
v___x_2150_ = lean_usize_dec_lt(v_i_2148_, v_sz_2147_);
if (v___x_2150_ == 0)
{
return v_bs_2149_;
}
else
{
lean_object* v_v_2151_; lean_object* v___x_2152_; lean_object* v_bs_x27_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; size_t v___x_2156_; size_t v___x_2157_; lean_object* v___x_2158_; 
v_v_2151_ = lean_array_uget(v_bs_2149_, v_i_2148_);
v___x_2152_ = lean_unsigned_to_nat(0u);
v_bs_x27_2153_ = lean_array_uset(v_bs_2149_, v_i_2148_, v___x_2152_);
v___x_2154_ = l_Lean_Name_toString(v_v_2151_, v___x_2150_);
v___x_2155_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
v___x_2156_ = ((size_t)1ULL);
v___x_2157_ = lean_usize_add(v_i_2148_, v___x_2156_);
v___x_2158_ = lean_array_uset(v_bs_x27_2153_, v_i_2148_, v___x_2155_);
v_i_2148_ = v___x_2157_;
v_bs_2149_ = v___x_2158_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0___boxed(lean_object* v_sz_2160_, lean_object* v_i_2161_, lean_object* v_bs_2162_){
_start:
{
size_t v_sz_boxed_2163_; size_t v_i_boxed_2164_; lean_object* v_res_2165_; 
v_sz_boxed_2163_ = lean_unbox_usize(v_sz_2160_);
lean_dec(v_sz_2160_);
v_i_boxed_2164_ = lean_unbox_usize(v_i_2161_);
lean_dec(v_i_2161_);
v_res_2165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_boxed_2163_, v_i_boxed_2164_, v_bs_2162_);
return v_res_2165_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = lean_unsigned_to_nat(4u);
v___x_2190_ = l_Lean_JsonNumber_fromNat(v___x_2189_);
return v___x_2190_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15);
v___x_2192_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
return v___x_2192_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16);
v___x_2194_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14));
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
lean_ctor_set(v___x_2195_, 1, v___x_2193_);
return v___x_2195_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24));
v___x_2213_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17);
v___x_2214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
lean_ctor_set(v___x_2214_, 1, v___x_2212_);
return v___x_2214_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25);
v___x_2216_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13));
v___x_2217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v___x_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(lean_object* v_kernelName_2218_, lean_object* v_solutionPath_2219_, lean_object* v___x_2220_, lean_object* v_kernelCommand_2221_, lean_object* v_configHandle_2222_, lean_object* v_configPath_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_a_2227_; lean_object* v_legalAxioms_2254_; uint8_t v___x_2255_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v_kernelArgs_2329_; lean_object* v___y_2330_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; size_t v_sz_2341_; size_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v_legalAxioms_2254_ = lean_ctor_get(v___y_2224_, 5);
v___x_2255_ = 0;
v___x_2336_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9));
v___x_2337_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10));
lean_inc_ref(v_solutionPath_2219_);
v___x_2338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2338_, 0, v_solutionPath_2219_);
v___x_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2337_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
v___x_2340_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
v_sz_2341_ = lean_array_size(v_legalAxioms_2254_);
v___x_2342_ = ((size_t)0ULL);
lean_inc_ref(v_legalAxioms_2254_);
v___x_2343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_2341_, v___x_2342_, v_legalAxioms_2254_);
v___x_2344_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
v___x_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2340_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
v___x_2346_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26);
v___x_2347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2339_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2336_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = l_Lean_Json_mkObj(v___x_2349_);
lean_dec_ref_known(v___x_2349_, 2);
v___x_2351_ = l_Lean_Json_compress(v___x_2350_);
v___x_2352_ = lean_io_prim_handle_put_str(v_configHandle_2222_, v___x_2351_);
lean_dec_ref(v___x_2351_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v___x_2353_; 
lean_dec_ref_known(v___x_2352_, 1);
v___x_2353_ = lean_io_prim_handle_flush(v_configHandle_2222_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
lean_dec_ref_known(v___x_2353_, 1);
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = lean_array_get_size(v_kernelCommand_2221_);
lean_inc_ref(v_kernelCommand_2221_);
v___x_2356_ = l_Array_toSubarray___redArg(v_kernelCommand_2221_, v___x_2354_, v___x_2355_);
v___x_2357_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_2358_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v___x_2356_, v___x_2357_);
lean_inc_ref(v_kernelName_2218_);
v___x_2359_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_2218_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; 
lean_inc_ref(v_solutionPath_2219_);
v___x_2360_ = lean_array_push(v___x_2358_, v_solutionPath_2219_);
v_kernelArgs_2329_ = v___x_2360_;
v___y_2330_ = v___y_2224_;
goto v___jp_2328_;
}
else
{
lean_object* v___x_2361_; 
lean_inc_ref(v_configPath_2223_);
v___x_2361_ = lean_array_push(v___x_2358_, v_configPath_2223_);
v_kernelArgs_2329_ = v___x_2361_;
v___y_2330_ = v___y_2224_;
goto v___jp_2328_;
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec_ref(v_configPath_2223_);
lean_dec_ref(v_kernelCommand_2221_);
lean_dec_ref(v_solutionPath_2219_);
lean_dec_ref(v_kernelName_2218_);
v_a_2362_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2353_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2353_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_dec_ref(v_configPath_2223_);
lean_dec_ref(v_kernelCommand_2221_);
lean_dec_ref(v_solutionPath_2219_);
lean_dec_ref(v_kernelName_2218_);
v_a_2370_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2352_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2352_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
v___jp_2226_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2228_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__0));
v___x_2229_ = lean_string_append(v___x_2228_, v_kernelName_2218_);
lean_dec_ref(v_kernelName_2218_);
v___x_2230_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__1));
lean_inc_ref(v___x_2229_);
v___x_2231_ = lean_string_append(v___x_2229_, v___x_2230_);
v___x_2232_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2231_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2244_; 
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2244_ == 0)
{
lean_object* v_unused_2245_; 
v_unused_2245_ = lean_ctor_get(v___x_2232_, 0);
lean_dec(v_unused_2245_);
v___x_2234_ = v___x_2232_;
v_isShared_2235_ = v_isSharedCheck_2244_;
goto v_resetjp_2233_;
}
else
{
lean_dec(v___x_2232_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2244_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2236_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__2));
v___x_2237_ = lean_string_append(v___x_2229_, v___x_2236_);
v___x_2238_ = lean_io_error_to_string(v_a_2227_);
v___x_2239_ = lean_string_append(v___x_2237_, v___x_2238_);
lean_dec_ref(v___x_2238_);
v___x_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2240_);
v___x_2242_ = v___x_2234_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec_ref(v___x_2229_);
lean_dec(v_a_2227_);
v_a_2246_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2232_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2232_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
v___jp_2256_:
{
lean_object* v_leanPrefix_2261_; lean_object* v___x_2262_; 
v_leanPrefix_2261_ = lean_ctor_get(v___y_2259_, 6);
v___x_2262_ = lean_uv_os_tmpdir();
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2264_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__4));
v___x_2265_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_2266_ = lean_unsigned_to_nat(4u);
v___x_2267_ = lean_mk_empty_array_with_capacity(v___x_2266_);
v___x_2268_ = lean_array_push(v___x_2267_, v_configPath_2223_);
v___x_2269_ = lean_array_push(v___x_2268_, v_solutionPath_2219_);
lean_inc_ref(v___y_2260_);
v___x_2270_ = lean_array_push(v___x_2269_, v___y_2260_);
lean_inc_ref(v_leanPrefix_2261_);
v___x_2271_ = lean_array_push(v___x_2270_, v_leanPrefix_2261_);
v___x_2272_ = lean_mk_empty_array_with_capacity(v___y_2257_);
v___x_2273_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2274_, 0, v_a_2263_);
v___x_2275_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_2275_, 0, v___y_2260_);
lean_ctor_set(v___x_2275_, 1, v___y_2258_);
lean_ctor_set(v___x_2275_, 2, v___x_2264_);
lean_ctor_set(v___x_2275_, 3, v___x_2265_);
lean_ctor_set(v___x_2275_, 4, v___x_2271_);
lean_ctor_set(v___x_2275_, 5, v___x_2272_);
lean_ctor_set(v___x_2275_, 6, v___x_2273_);
lean_ctor_set(v___x_2275_, 7, v___x_2274_);
lean_ctor_set_uint8(v___x_2275_, sizeof(void*)*8, v___x_2255_);
v___x_2276_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v___x_2275_, v___y_2259_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2318_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2318_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2318_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
uint32_t v___x_2281_; uint32_t v___x_2282_; uint8_t v___x_2283_; 
v___x_2281_ = 0;
v___x_2282_ = lean_unbox_uint32(v_a_2277_);
v___x_2283_ = lean_uint32_dec_eq(v___x_2282_, v___x_2281_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5));
lean_inc_ref(v_kernelName_2218_);
v___x_2285_ = lean_string_append(v_kernelName_2218_, v___x_2284_);
v___x_2286_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2285_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2302_; 
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2302_ == 0)
{
lean_object* v_unused_2303_; 
v_unused_2303_ = lean_ctor_get(v___x_2286_, 0);
lean_dec(v_unused_2303_);
v___x_2288_ = v___x_2286_;
v_isShared_2289_ = v_isSharedCheck_2302_;
goto v_resetjp_2287_;
}
else
{
lean_dec(v___x_2286_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2302_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; uint32_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2290_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6));
v___x_2291_ = lean_string_append(v_kernelName_2218_, v___x_2290_);
v___x_2292_ = lean_unbox_uint32(v_a_2277_);
lean_dec(v_a_2277_);
v___x_2293_ = lean_uint32_to_nat(v___x_2292_);
v___x_2294_ = l_Nat_reprFast(v___x_2293_);
v___x_2295_ = lean_string_append(v___x_2291_, v___x_2294_);
lean_dec_ref(v___x_2294_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set_tag(v___x_2279_, 1);
lean_ctor_set(v___x_2279_, 0, v___x_2295_);
v___x_2297_ = v___x_2279_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2299_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2297_);
v___x_2299_ = v___x_2288_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v_a_2304_; 
lean_del_object(v___x_2279_);
lean_dec(v_a_2277_);
v_a_2304_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2286_, 1);
v_a_2227_ = v_a_2304_;
goto v___jp_2226_;
}
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_del_object(v___x_2279_);
lean_dec(v_a_2277_);
v___x_2305_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7));
lean_inc_ref(v_kernelName_2218_);
v___x_2306_ = lean_string_append(v_kernelName_2218_, v___x_2305_);
v___x_2307_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2306_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_kernelName_2218_);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; 
v_unused_2316_ = lean_ctor_get(v___x_2307_, 0);
lean_dec(v_unused_2316_);
v___x_2309_ = v___x_2307_;
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
else
{
lean_dec(v___x_2307_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_box(0);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2311_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
else
{
lean_object* v_a_2317_; 
v_a_2317_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2307_, 1);
v_a_2227_ = v_a_2317_;
goto v___jp_2226_;
}
}
}
}
else
{
lean_object* v_a_2319_; 
v_a_2319_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2276_, 1);
v_a_2227_ = v_a_2319_;
goto v___jp_2226_;
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec_ref(v___y_2260_);
lean_dec_ref(v___y_2258_);
lean_dec_ref(v_configPath_2223_);
lean_dec_ref(v_solutionPath_2219_);
lean_dec_ref(v_kernelName_2218_);
v_a_2320_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2262_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2262_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
v___jp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v_a_2334_; 
v___x_2331_ = lean_unsigned_to_nat(0u);
v___x_2332_ = lean_array_get(v___x_2220_, v_kernelCommand_2221_, v___x_2331_);
lean_dec_ref(v_kernelCommand_2221_);
lean_inc(v___x_2332_);
v___x_2333_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_2332_);
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref(v___x_2333_);
if (lean_obj_tag(v_a_2334_) == 0)
{
v___y_2257_ = v___x_2331_;
v___y_2258_ = v_kernelArgs_2329_;
v___y_2259_ = v___y_2330_;
v___y_2260_ = v___x_2332_;
goto v___jp_2256_;
}
else
{
lean_object* v_val_2335_; 
lean_dec(v___x_2332_);
v_val_2335_ = lean_ctor_get(v_a_2334_, 0);
lean_inc(v_val_2335_);
lean_dec_ref_known(v_a_2334_, 1);
v___y_2257_ = v___x_2331_;
v___y_2258_ = v_kernelArgs_2329_;
v___y_2259_ = v___y_2330_;
v___y_2260_ = v_val_2335_;
goto v___jp_2256_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed(lean_object* v_kernelName_2378_, lean_object* v_solutionPath_2379_, lean_object* v___x_2380_, lean_object* v_kernelCommand_2381_, lean_object* v_configHandle_2382_, lean_object* v_configPath_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(v_kernelName_2378_, v_solutionPath_2379_, v___x_2380_, v_kernelCommand_2381_, v_configHandle_2382_, v_configPath_2383_, v___y_2384_);
lean_dec_ref(v___y_2384_);
lean_dec(v_configHandle_2382_);
lean_dec_ref(v___x_2380_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(lean_object* v_kernelName_2389_, lean_object* v_kernelCommand_2390_, lean_object* v_solutionPath_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v___x_2394_; lean_object* v___f_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2394_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
lean_inc_ref(v_kernelName_2389_);
v___f_2395_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed), 8, 4);
lean_closure_set(v___f_2395_, 0, v_kernelName_2389_);
lean_closure_set(v___f_2395_, 1, v_solutionPath_2391_);
lean_closure_set(v___f_2395_, 2, v___x_2394_);
lean_closure_set(v___f_2395_, 3, v_kernelCommand_2390_);
v___x_2396_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0));
v___x_2397_ = lean_string_append(v___x_2396_, v_kernelName_2389_);
lean_dec_ref(v_kernelName_2389_);
v___x_2398_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1));
v___x_2399_ = lean_string_append(v___x_2397_, v___x_2398_);
v___x_2400_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2399_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v___x_2401_; 
lean_dec_ref_known(v___x_2400_, 1);
v___x_2401_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v___f_2395_, v_a_2392_);
return v___x_2401_;
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec_ref(v___f_2395_);
v_a_2402_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2400_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2400_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___boxed(lean_object* v_kernelName_2410_, lean_object* v_kernelCommand_2411_, lean_object* v_solutionPath_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_kernelName_2410_, v_kernelCommand_2411_, v_solutionPath_2412_, v_a_2413_);
lean_dec_ref(v_a_2413_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1(lean_object* v_inst_2416_, lean_object* v_R_2417_, lean_object* v_a_2418_, lean_object* v_b_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v_a_2418_, v_b_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(lean_object* v_solutionPath_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_whichLeanChecker_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_whichLeanChecker_2427_ = lean_ctor_get(v_a_2425_, 13);
v___x_2428_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0));
v___x_2429_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_2430_ = lean_unsigned_to_nat(3u);
v___x_2431_ = lean_mk_empty_array_with_capacity(v___x_2430_);
lean_inc_ref(v_whichLeanChecker_2427_);
v___x_2432_ = lean_array_push(v___x_2431_, v_whichLeanChecker_2427_);
v___x_2433_ = lean_array_push(v___x_2432_, v___x_2428_);
v___x_2434_ = lean_array_push(v___x_2433_, v___x_2429_);
v___x_2435_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2));
v___x_2436_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v___x_2435_, v___x_2434_, v_solutionPath_2424_, v_a_2425_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___boxed(lean_object* v_solutionPath_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_solutionPath_2437_, v_a_2438_);
lean_dec_ref(v_a_2438_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(lean_object* v_exportPath_2441_, lean_object* v_as_2442_, size_t v_sz_2443_, size_t v_i_2444_, lean_object* v_b_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_a_2449_; uint8_t v___x_2453_; 
v___x_2453_ = lean_usize_dec_lt(v_i_2444_, v_sz_2443_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_dec_ref(v_exportPath_2441_);
v___x_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2454_, 0, v_b_2445_);
return v___x_2454_;
}
else
{
lean_object* v_a_2455_; lean_object* v_fst_2456_; lean_object* v_snd_2457_; lean_object* v___x_2458_; 
v_a_2455_ = lean_array_uget_borrowed(v_as_2442_, v_i_2444_);
v_fst_2456_ = lean_ctor_get(v_a_2455_, 0);
v_snd_2457_ = lean_ctor_get(v_a_2455_, 1);
lean_inc_ref(v_exportPath_2441_);
lean_inc(v_snd_2457_);
lean_inc(v_fst_2456_);
v___x_2458_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_fst_2456_, v_snd_2457_, v_exportPath_2441_, v___y_2446_);
if (lean_obj_tag(v___x_2458_) == 0)
{
if (lean_obj_tag(v_b_2445_) == 0)
{
lean_object* v_a_2459_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v_a_2449_ = v_a_2459_;
goto v___jp_2448_;
}
else
{
lean_dec_ref_known(v___x_2458_, 1);
v_a_2449_ = v_b_2445_;
goto v___jp_2448_;
}
}
else
{
lean_dec(v_b_2445_);
lean_dec_ref(v_exportPath_2441_);
return v___x_2458_;
}
}
v___jp_2448_:
{
size_t v___x_2450_; size_t v___x_2451_; 
v___x_2450_ = ((size_t)1ULL);
v___x_2451_ = lean_usize_add(v_i_2444_, v___x_2450_);
v_i_2444_ = v___x_2451_;
v_b_2445_ = v_a_2449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0___boxed(lean_object* v_exportPath_2460_, lean_object* v_as_2461_, lean_object* v_sz_2462_, lean_object* v_i_2463_, lean_object* v_b_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
size_t v_sz_boxed_2467_; size_t v_i_boxed_2468_; lean_object* v_res_2469_; 
v_sz_boxed_2467_ = lean_unbox_usize(v_sz_2462_);
lean_dec(v_sz_2462_);
v_i_boxed_2468_ = lean_unbox_usize(v_i_2463_);
lean_dec(v_i_2463_);
v_res_2469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(v_exportPath_2460_, v_as_2461_, v_sz_boxed_2467_, v_i_boxed_2468_, v_b_2464_, v___y_2465_);
lean_dec_ref(v___y_2465_);
lean_dec_ref(v_as_2461_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(lean_object* v_exportPath_2470_, lean_object* v_init_2471_, lean_object* v_x_2472_, lean_object* v___y_2473_){
_start:
{
if (lean_obj_tag(v_x_2472_) == 0)
{
lean_object* v_k_2475_; lean_object* v_v_2476_; lean_object* v_l_2477_; lean_object* v_r_2478_; lean_object* v___x_2479_; 
v_k_2475_ = lean_ctor_get(v_x_2472_, 1);
lean_inc(v_k_2475_);
v_v_2476_ = lean_ctor_get(v_x_2472_, 2);
lean_inc(v_v_2476_);
v_l_2477_ = lean_ctor_get(v_x_2472_, 3);
lean_inc(v_l_2477_);
v_r_2478_ = lean_ctor_get(v_x_2472_, 4);
lean_inc(v_r_2478_);
lean_dec_ref_known(v_x_2472_, 5);
lean_inc_ref(v_exportPath_2470_);
v___x_2479_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(v_exportPath_2470_, v_init_2471_, v_l_2477_, v___y_2473_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v_a_2481_; lean_object* v___x_2482_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref_known(v___x_2479_, 1);
v_a_2481_ = lean_ctor_get(v_a_2480_, 0);
lean_inc(v_a_2481_);
lean_dec(v_a_2480_);
lean_inc_ref(v_exportPath_2470_);
v___x_2482_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_k_2475_, v_v_2476_, v_exportPath_2470_, v___y_2473_);
if (lean_obj_tag(v___x_2482_) == 0)
{
if (lean_obj_tag(v_a_2481_) == 0)
{
lean_object* v_a_2483_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2482_, 1);
v_init_2471_ = v_a_2483_;
v_x_2472_ = v_r_2478_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_2482_, 1);
v_init_2471_ = v_a_2481_;
v_x_2472_ = v_r_2478_;
goto _start;
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v_a_2481_);
lean_dec(v_r_2478_);
lean_dec_ref(v_exportPath_2470_);
v_a_2486_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2482_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2482_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
else
{
lean_dec(v_r_2478_);
lean_dec(v_v_2476_);
lean_dec(v_k_2475_);
lean_dec_ref(v_exportPath_2470_);
return v___x_2479_;
}
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
lean_dec_ref(v_exportPath_2470_);
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v_init_2471_);
v___x_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
return v___x_2495_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1___boxed(lean_object* v_exportPath_2496_, lean_object* v_init_2497_, lean_object* v_x_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(v_exportPath_2496_, v_init_2497_, v_x_2498_, v___y_2499_);
lean_dec_ref(v___y_2499_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runKernels(lean_object* v_exportPath_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v_val_2506_; lean_object* v_externalKernels_2509_; lean_object* v_bundledKernels_2510_; lean_object* v_a_2512_; lean_object* v_result_2545_; lean_object* v___x_2546_; 
v_externalKernels_2509_ = lean_ctor_get(v_a_2503_, 15);
v_bundledKernels_2510_ = lean_ctor_get(v_a_2503_, 16);
v_result_2545_ = lean_box(0);
lean_inc(v_externalKernels_2509_);
lean_inc_ref(v_exportPath_2502_);
v___x_2546_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(v_exportPath_2502_, v_result_2545_, v_externalKernels_2509_, v_a_2503_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v_a_2548_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2546_, 1);
v_a_2548_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_a_2548_);
lean_dec(v_a_2547_);
v_a_2512_ = v_a_2548_;
goto v___jp_2511_;
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec_ref(v_exportPath_2502_);
v_a_2549_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2546_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2546_);
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
v___jp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = lean_mk_io_user_error(v_val_2506_);
v___x_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
return v___x_2508_;
}
v___jp_2511_:
{
size_t v_sz_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v_sz_2513_ = lean_array_size(v_bundledKernels_2510_);
v___x_2514_ = ((size_t)0ULL);
lean_inc_ref(v_exportPath_2502_);
v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(v_exportPath_2502_, v_bundledKernels_2510_, v_sz_2513_, v___x_2514_, v_a_2512_, v_a_2503_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2517_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2517_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_exportPath_2502_, v_a_2503_);
if (lean_obj_tag(v___x_2517_) == 0)
{
if (lean_obj_tag(v_a_2516_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2527_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2527_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2527_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
if (lean_obj_tag(v_a_2518_) == 1)
{
lean_object* v_val_2522_; 
lean_del_object(v___x_2520_);
v_val_2522_ = lean_ctor_get(v_a_2518_, 0);
lean_inc(v_val_2522_);
lean_dec_ref_known(v_a_2518_, 1);
v_val_2506_ = v_val_2522_;
goto v___jp_2505_;
}
else
{
lean_object* v___x_2523_; lean_object* v___x_2525_; 
lean_dec(v_a_2518_);
v___x_2523_ = lean_box(0);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2523_);
v___x_2525_ = v___x_2520_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
else
{
lean_object* v_val_2528_; 
lean_dec_ref_known(v___x_2517_, 1);
v_val_2528_ = lean_ctor_get(v_a_2516_, 0);
lean_inc(v_val_2528_);
lean_dec_ref_known(v_a_2516_, 1);
v_val_2506_ = v_val_2528_;
goto v___jp_2505_;
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_dec(v_a_2516_);
v_a_2529_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2517_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2517_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref(v_exportPath_2502_);
v_a_2537_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2515_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2515_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runKernels___boxed(lean_object* v_exportPath_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l___private_Lake_CLI_Check_0__Lake_Check_runKernels(v_exportPath_2557_, v_a_2558_);
lean_dec_ref(v_a_2558_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg(){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__52));
v___x_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___boxed(lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(lean_object* v_a_2715_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___boxed(lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(v_a_2718_);
lean_dec_ref(v_a_2718_);
return v_res_2720_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(lean_object* v_a_2721_, lean_object* v_as_2722_, size_t v_i_2723_, size_t v_stop_2724_){
_start:
{
uint8_t v___x_2725_; 
v___x_2725_ = lean_usize_dec_eq(v_i_2723_, v_stop_2724_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2726_ = lean_array_uget_borrowed(v_as_2722_, v_i_2723_);
v___x_2727_ = lean_name_eq(v_a_2721_, v___x_2726_);
if (v___x_2727_ == 0)
{
size_t v___x_2728_; size_t v___x_2729_; 
v___x_2728_ = ((size_t)1ULL);
v___x_2729_ = lean_usize_add(v_i_2723_, v___x_2728_);
v_i_2723_ = v___x_2729_;
goto _start;
}
else
{
return v___x_2727_;
}
}
else
{
uint8_t v___x_2731_; 
v___x_2731_ = 0;
return v___x_2731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0___boxed(lean_object* v_a_2732_, lean_object* v_as_2733_, lean_object* v_i_2734_, lean_object* v_stop_2735_){
_start:
{
size_t v_i_boxed_2736_; size_t v_stop_boxed_2737_; uint8_t v_res_2738_; lean_object* v_r_2739_; 
v_i_boxed_2736_ = lean_unbox_usize(v_i_2734_);
lean_dec(v_i_2734_);
v_stop_boxed_2737_ = lean_unbox_usize(v_stop_2735_);
lean_dec(v_stop_2735_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_2732_, v_as_2733_, v_i_boxed_2736_, v_stop_boxed_2737_);
lean_dec_ref(v_as_2733_);
lean_dec(v_a_2732_);
v_r_2739_ = lean_box(v_res_2738_);
return v_r_2739_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(lean_object* v_as_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; 
v___x_2742_ = lean_unsigned_to_nat(0u);
v___x_2743_ = lean_array_get_size(v_as_2740_);
v___x_2744_ = lean_nat_dec_lt(v___x_2742_, v___x_2743_);
if (v___x_2744_ == 0)
{
return v___x_2744_;
}
else
{
size_t v___x_2745_; size_t v___x_2746_; uint8_t v___x_2747_; 
v___x_2745_ = ((size_t)0ULL);
v___x_2746_ = lean_usize_of_nat(v___x_2743_);
v___x_2747_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_2741_, v_as_2740_, v___x_2745_, v___x_2746_);
return v___x_2747_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0___boxed(lean_object* v_as_2748_, lean_object* v_a_2749_){
_start:
{
uint8_t v_res_2750_; lean_object* v_r_2751_; 
v_res_2750_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_as_2748_, v_a_2749_);
lean_dec(v_a_2749_);
lean_dec_ref(v_as_2748_);
v_r_2751_ = lean_box(v_res_2750_);
return v_r_2751_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11(void){
_start:
{
lean_object* v___x_2782_; lean_object* v_additional_2783_; lean_object* v___x_2784_; 
v___x_2782_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__10));
v_additional_2783_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_2784_ = l_Array_append___redArg(v_additional_2783_, v___x_2782_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(lean_object* v_a_2785_){
_start:
{
lean_object* v_legalAxioms_2787_; lean_object* v_additional_2788_; lean_object* v___x_2789_; uint8_t v___x_2790_; 
v_legalAxioms_2787_ = lean_ctor_get(v_a_2785_, 5);
v_additional_2788_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_2789_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3));
v___x_2790_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_legalAxioms_2787_, v___x_2789_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_additional_2788_);
return v___x_2791_;
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___boxed(lean_object* v_a_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_2794_);
lean_dec_ref(v_a_2794_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(lean_object* v_e_2797_){
_start:
{
if (lean_obj_tag(v_e_2797_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2807_; 
v_a_2799_ = lean_ctor_get(v_e_2797_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_e_2797_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2801_ = v_e_2797_;
v_isShared_2802_ = v_isSharedCheck_2807_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v_e_2797_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2807_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2803_; lean_object* v___x_2805_; 
v___x_2803_ = lean_mk_io_user_error(v_a_2799_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set_tag(v___x_2801_, 1);
lean_ctor_set(v___x_2801_, 0, v___x_2803_);
v___x_2805_ = v___x_2801_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2803_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
v_a_2808_ = lean_ctor_get(v_e_2797_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_e_2797_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v_e_2797_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v_e_2797_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
lean_ctor_set_tag(v___x_2810_, 0);
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg___boxed(lean_object* v_e_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v_e_2816_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(lean_object* v_00_u03b1_2819_, lean_object* v_e_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v_e_2820_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___boxed(lean_object* v_00_u03b1_2823_, lean_object* v_e_2824_, lean_object* v_a_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(v_00_u03b1_2823_, v_e_2824_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(lean_object* v_challengeExportPath_2827_, lean_object* v_solutionExportPath_2828_, lean_object* v_a_2829_){
_start:
{
uint8_t v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = 0;
v___x_2832_ = lean_io_prim_handle_mk(v_challengeExportPath_2827_, v___x_2831_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2832_, 1);
v___x_2834_ = lean_stream_of_handle(v_a_2833_);
v___x_2835_ = l_LeanExport_parseStream(v___x_2834_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2837_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2835_, 1);
v___x_2837_ = lean_io_prim_handle_mk(v_solutionExportPath_2828_, v___x_2831_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v___x_2837_, 1);
v___x_2839_ = lean_stream_of_handle(v_a_2838_);
v___x_2840_ = l_LeanExport_parseStream(v___x_2839_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v_theoremNames_2842_; lean_object* v_definitionNames_2843_; lean_object* v_legalAxioms_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc_n(v_a_2841_, 2);
lean_dec_ref_known(v___x_2840_, 1);
v_theoremNames_2842_ = lean_ctor_get(v_a_2829_, 3);
v_definitionNames_2843_ = lean_ctor_get(v_a_2829_, 4);
v_legalAxioms_2844_ = lean_ctor_get(v_a_2829_, 5);
lean_inc_ref(v_theoremNames_2842_);
v___x_2845_ = l_Array_append___redArg(v_theoremNames_2842_, v_legalAxioms_2844_);
v___x_2846_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref(v___x_2846_);
v___x_2848_ = l_Lake_Check_compareAt(v_a_2836_, v_a_2841_, v___x_2845_, v_definitionNames_2843_, v_a_2847_);
lean_dec_ref(v___x_2845_);
v___x_2849_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v___x_2848_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
lean_dec_ref_known(v___x_2849_, 1);
v___x_2850_ = l_Lake_Check_checkAxioms(v_a_2841_, v_theoremNames_2842_, v_definitionNames_2843_, v_legalAxioms_2844_);
v___x_2851_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v___x_2850_);
return v___x_2851_;
}
else
{
lean_dec(v_a_2841_);
return v___x_2849_;
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v_a_2836_);
v_a_2852_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2840_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2840_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec(v_a_2836_);
v_a_2860_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2837_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2837_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
v_a_2868_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2835_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2835_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
v_a_2876_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2832_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2832_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare___boxed(lean_object* v_challengeExportPath_2884_, lean_object* v_solutionExportPath_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(v_challengeExportPath_2884_, v_solutionExportPath_2885_, v_a_2886_);
lean_dec_ref(v_a_2886_);
lean_dec_ref(v_solutionExportPath_2885_);
lean_dec_ref(v_challengeExportPath_2884_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(lean_object* v_challengeExportPath_2889_, lean_object* v_solutionExportPath_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(v_challengeExportPath_2889_, v_solutionExportPath_2890_, v_a_2891_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v___x_2894_; 
lean_dec_ref_known(v___x_2893_, 1);
v___x_2894_ = l___private_Lake_CLI_Check_0__Lake_Check_runKernels(v_solutionExportPath_2890_, v_a_2891_);
return v___x_2894_;
}
else
{
lean_dec_ref(v_solutionExportPath_2890_);
return v___x_2893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch___boxed(lean_object* v_challengeExportPath_2895_, lean_object* v_solutionExportPath_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExportPath_2895_, v_solutionExportPath_2896_, v_a_2897_);
lean_dec_ref(v_a_2897_);
lean_dec_ref(v_challengeExportPath_2895_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0(lean_object* v_challengeExportPath_2901_, lean_object* v_solutionExportPath_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExportPath_2901_, v_solutionExportPath_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_dec_ref_known(v___x_2905_, 1);
v___x_2906_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___closed__0));
v___x_2907_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2906_);
return v___x_2907_;
}
else
{
return v___x_2905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___boxed(lean_object* v_challengeExportPath_2908_, lean_object* v_solutionExportPath_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0(v_challengeExportPath_2908_, v_solutionExportPath_2909_, v___y_2910_);
lean_dec_ref(v___y_2910_);
lean_dec_ref(v_challengeExportPath_2908_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1(lean_object* v___x_2913_, lean_object* v_challengeExportPath_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_solutionModule_2917_; lean_object* v___f_2918_; uint8_t v___x_2919_; lean_object* v___x_2920_; 
v_solutionModule_2917_ = lean_ctor_get(v___y_2915_, 2);
v___f_2918_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2918_, 0, v_challengeExportPath_2914_);
v___x_2919_ = 1;
lean_inc(v_solutionModule_2917_);
v___x_2920_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v___x_2919_, v_solutionModule_2917_, v___x_2913_, v___f_2918_, v___y_2915_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1___boxed(lean_object* v___x_2921_, lean_object* v_challengeExportPath_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1(v___x_2921_, v_challengeExportPath_2922_, v___y_2923_);
lean_dec_ref(v___y_2923_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt(lean_object* v_a_2926_){
_start:
{
lean_object* v___x_2928_; lean_object* v_a_2929_; lean_object* v_challengeModule_2930_; lean_object* v_theoremNames_2931_; lean_object* v_definitionNames_2932_; lean_object* v_legalAxioms_2933_; lean_object* v___x_2934_; lean_object* v_a_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___f_2940_; uint8_t v___x_2941_; lean_object* v___x_2942_; 
v___x_2928_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_2926_);
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref(v___x_2928_);
v_challengeModule_2930_ = lean_ctor_get(v_a_2926_, 1);
v_theoremNames_2931_ = lean_ctor_get(v_a_2926_, 3);
v_definitionNames_2932_ = lean_ctor_get(v_a_2926_, 4);
v_legalAxioms_2933_ = lean_ctor_get(v_a_2926_, 5);
v___x_2934_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref(v___x_2934_);
v___x_2936_ = l_Array_append___redArg(v_a_2929_, v_theoremNames_2931_);
v___x_2937_ = l_Array_append___redArg(v___x_2936_, v_legalAxioms_2933_);
v___x_2938_ = l_Array_append___redArg(v___x_2937_, v_a_2935_);
lean_dec(v_a_2935_);
v___x_2939_ = l_Array_append___redArg(v___x_2938_, v_definitionNames_2932_);
lean_inc_ref(v___x_2939_);
v___f_2940_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2940_, 0, v___x_2939_);
v___x_2941_ = 2;
lean_inc(v_challengeModule_2930_);
v___x_2942_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v___x_2941_, v_challengeModule_2930_, v___x_2939_, v___f_2940_, v_a_2926_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___boxed(lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt(v_a_2943_);
lean_dec_ref(v_a_2943_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(lean_object* v_j_2946_, lean_object* v_k_2947_){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = l_Lean_Json_getObjValD(v_j_2946_, v_k_2947_);
v___x_2949_ = l_Lean_Json_getStr_x3f(v___x_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0___boxed(lean_object* v_j_2950_, lean_object* v_k_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_j_2950_, v_k_2951_);
lean_dec_ref(v_k_2951_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(size_t v_sz_2953_, size_t v_i_2954_, lean_object* v_bs_2955_){
_start:
{
uint8_t v___x_2956_; 
v___x_2956_ = lean_usize_dec_lt(v_i_2954_, v_sz_2953_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; 
v___x_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2957_, 0, v_bs_2955_);
return v___x_2957_;
}
else
{
lean_object* v_v_2958_; lean_object* v___x_2959_; 
v_v_2958_ = lean_array_uget_borrowed(v_bs_2955_, v_i_2954_);
lean_inc(v_v_2958_);
v___x_2959_ = l_Lean_Json_getStr_x3f(v_v_2958_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref(v_bs_2955_);
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2959_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2969_; lean_object* v_bs_x27_2970_; size_t v___x_2971_; size_t v___x_2972_; lean_object* v___x_2973_; 
v_a_2968_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2959_, 1);
v___x_2969_ = lean_unsigned_to_nat(0u);
v_bs_x27_2970_ = lean_array_uset(v_bs_2955_, v_i_2954_, v___x_2969_);
v___x_2971_ = ((size_t)1ULL);
v___x_2972_ = lean_usize_add(v_i_2954_, v___x_2971_);
v___x_2973_ = lean_array_uset(v_bs_x27_2970_, v_i_2954_, v_a_2968_);
v_i_2954_ = v___x_2972_;
v_bs_2955_ = v___x_2973_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2975_, lean_object* v_i_2976_, lean_object* v_bs_2977_){
_start:
{
size_t v_sz_boxed_2978_; size_t v_i_boxed_2979_; lean_object* v_res_2980_; 
v_sz_boxed_2978_ = lean_unbox_usize(v_sz_2975_);
lean_dec(v_sz_2975_);
v_i_boxed_2979_ = lean_unbox_usize(v_i_2976_);
lean_dec(v_i_2976_);
v_res_2980_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_2978_, v_i_boxed_2979_, v_bs_2977_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(lean_object* v_x_2983_){
_start:
{
if (lean_obj_tag(v_x_2983_) == 4)
{
lean_object* v_elems_2984_; size_t v_sz_2985_; size_t v___x_2986_; lean_object* v___x_2987_; 
v_elems_2984_ = lean_ctor_get(v_x_2983_, 0);
lean_inc_ref(v_elems_2984_);
lean_dec_ref_known(v_x_2983_, 1);
v_sz_2985_ = lean_array_size(v_elems_2984_);
v___x_2986_ = ((size_t)0ULL);
v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_2985_, v___x_2986_, v_elems_2984_);
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2988_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__0));
v___x_2989_ = lean_unsigned_to_nat(80u);
v___x_2990_ = l_Lean_Json_pretty(v_x_2983_, v___x_2989_);
v___x_2991_ = lean_string_append(v___x_2988_, v___x_2990_);
lean_dec_ref(v___x_2990_);
v___x_2992_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_2993_ = lean_string_append(v___x_2991_, v___x_2992_);
v___x_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
return v___x_2994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(lean_object* v_x_2997_){
_start:
{
if (lean_obj_tag(v_x_2997_) == 0)
{
lean_object* v___x_2998_; 
v___x_2998_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3___closed__0));
return v___x_2998_;
}
else
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_x_2997_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2999_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2999_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3016_; 
v_a_3008_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3010_ = v___x_2999_;
v_isShared_3011_ = v_isSharedCheck_3016_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2999_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3016_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3012_, 0, v_a_3008_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3012_);
v___x_3014_ = v___x_3010_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(lean_object* v_j_3017_, lean_object* v_k_3018_){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = l_Lean_Json_getObjValD(v_j_3017_, v_k_3018_);
v___x_3020_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2___boxed(lean_object* v_j_3021_, lean_object* v_k_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_j_3021_, v_k_3022_);
lean_dec_ref(v_k_3022_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(lean_object* v_x_3026_){
_start:
{
if (lean_obj_tag(v_x_3026_) == 0)
{
lean_object* v___x_3027_; 
v___x_3027_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___closed__0));
return v___x_3027_;
}
else
{
lean_object* v___x_3028_; 
v___x_3028_ = l_Lean_Json_getBool_x3f(v_x_3026_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3045_; 
v_a_3037_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3039_ = v___x_3028_;
v_isShared_3040_ = v_isSharedCheck_3045_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3028_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3045_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3041_; lean_object* v___x_3043_; 
v___x_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3041_, 0, v_a_3037_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v___x_3041_);
v___x_3043_ = v___x_3039_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___boxed(lean_object* v_x_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v_x_3046_);
lean_dec(v_x_3046_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(lean_object* v_j_3048_, lean_object* v_k_3049_){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = l_Lean_Json_getObjValD(v_j_3048_, v_k_3049_);
v___x_3051_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v___x_3050_);
lean_dec(v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3___boxed(lean_object* v_j_3052_, lean_object* v_k_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_j_3052_, v_k_3053_);
lean_dec_ref(v_k_3053_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_cmp_3055_, lean_object* v_k_3056_, lean_object* v_v_3057_, lean_object* v_t_3058_){
_start:
{
if (lean_obj_tag(v_t_3058_) == 0)
{
lean_object* v_size_3059_; lean_object* v_k_3060_; lean_object* v_v_3061_; lean_object* v_l_3062_; lean_object* v_r_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3344_; 
v_size_3059_ = lean_ctor_get(v_t_3058_, 0);
v_k_3060_ = lean_ctor_get(v_t_3058_, 1);
v_v_3061_ = lean_ctor_get(v_t_3058_, 2);
v_l_3062_ = lean_ctor_get(v_t_3058_, 3);
v_r_3063_ = lean_ctor_get(v_t_3058_, 4);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_t_3058_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3065_ = v_t_3058_;
v_isShared_3066_ = v_isSharedCheck_3344_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_r_3063_);
lean_inc(v_l_3062_);
lean_inc(v_v_3061_);
lean_inc(v_k_3060_);
lean_inc(v_size_3059_);
lean_dec(v_t_3058_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3344_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3067_; uint8_t v___x_3068_; 
lean_inc_ref(v_cmp_3055_);
lean_inc(v_k_3060_);
lean_inc_ref(v_k_3056_);
v___x_3067_ = lean_apply_2(v_cmp_3055_, v_k_3056_, v_k_3060_);
v___x_3068_ = lean_unbox(v___x_3067_);
switch(v___x_3068_)
{
case 0:
{
lean_object* v_impl_3069_; lean_object* v___x_3070_; 
lean_dec(v_size_3059_);
v_impl_3069_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3055_, v_k_3056_, v_v_3057_, v_l_3062_);
v___x_3070_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3063_) == 0)
{
lean_object* v_size_3071_; lean_object* v_size_3072_; lean_object* v_k_3073_; lean_object* v_v_3074_; lean_object* v_l_3075_; lean_object* v_r_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v_size_3071_ = lean_ctor_get(v_r_3063_, 0);
v_size_3072_ = lean_ctor_get(v_impl_3069_, 0);
v_k_3073_ = lean_ctor_get(v_impl_3069_, 1);
v_v_3074_ = lean_ctor_get(v_impl_3069_, 2);
v_l_3075_ = lean_ctor_get(v_impl_3069_, 3);
v_r_3076_ = lean_ctor_get(v_impl_3069_, 4);
lean_inc(v_r_3076_);
v___x_3077_ = lean_unsigned_to_nat(3u);
v___x_3078_ = lean_nat_mul(v___x_3077_, v_size_3071_);
v___x_3079_ = lean_nat_dec_lt(v___x_3078_, v_size_3072_);
lean_dec(v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3083_; 
lean_dec(v_r_3076_);
v___x_3080_ = lean_nat_add(v___x_3070_, v_size_3072_);
v___x_3081_ = lean_nat_add(v___x_3080_, v_size_3071_);
lean_dec(v___x_3080_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 3, v_impl_3069_);
lean_ctor_set(v___x_3065_, 0, v___x_3081_);
v___x_3083_ = v___x_3065_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3081_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_k_3060_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v_v_3061_);
lean_ctor_set(v_reuseFailAlloc_3084_, 3, v_impl_3069_);
lean_ctor_set(v_reuseFailAlloc_3084_, 4, v_r_3063_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
else
{
lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3150_; 
lean_inc(v_l_3075_);
lean_inc(v_v_3074_);
lean_inc(v_k_3073_);
lean_inc(v_size_3072_);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_impl_3069_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; lean_object* v_unused_3152_; lean_object* v_unused_3153_; lean_object* v_unused_3154_; lean_object* v_unused_3155_; 
v_unused_3151_ = lean_ctor_get(v_impl_3069_, 4);
lean_dec(v_unused_3151_);
v_unused_3152_ = lean_ctor_get(v_impl_3069_, 3);
lean_dec(v_unused_3152_);
v_unused_3153_ = lean_ctor_get(v_impl_3069_, 2);
lean_dec(v_unused_3153_);
v_unused_3154_ = lean_ctor_get(v_impl_3069_, 1);
lean_dec(v_unused_3154_);
v_unused_3155_ = lean_ctor_get(v_impl_3069_, 0);
lean_dec(v_unused_3155_);
v___x_3086_ = v_impl_3069_;
v_isShared_3087_ = v_isSharedCheck_3150_;
goto v_resetjp_3085_;
}
else
{
lean_dec(v_impl_3069_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3150_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v_size_3088_; lean_object* v_size_3089_; lean_object* v_k_3090_; lean_object* v_v_3091_; lean_object* v_l_3092_; lean_object* v_r_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; uint8_t v___x_3096_; 
v_size_3088_ = lean_ctor_get(v_l_3075_, 0);
v_size_3089_ = lean_ctor_get(v_r_3076_, 0);
v_k_3090_ = lean_ctor_get(v_r_3076_, 1);
v_v_3091_ = lean_ctor_get(v_r_3076_, 2);
v_l_3092_ = lean_ctor_get(v_r_3076_, 3);
v_r_3093_ = lean_ctor_get(v_r_3076_, 4);
v___x_3094_ = lean_unsigned_to_nat(2u);
v___x_3095_ = lean_nat_mul(v___x_3094_, v_size_3088_);
v___x_3096_ = lean_nat_dec_lt(v_size_3089_, v___x_3095_);
lean_dec(v___x_3095_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3125_; 
lean_inc(v_r_3093_);
lean_inc(v_l_3092_);
lean_inc(v_v_3091_);
lean_inc(v_k_3090_);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_r_3076_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; lean_object* v_unused_3127_; lean_object* v_unused_3128_; lean_object* v_unused_3129_; lean_object* v_unused_3130_; 
v_unused_3126_ = lean_ctor_get(v_r_3076_, 4);
lean_dec(v_unused_3126_);
v_unused_3127_ = lean_ctor_get(v_r_3076_, 3);
lean_dec(v_unused_3127_);
v_unused_3128_ = lean_ctor_get(v_r_3076_, 2);
lean_dec(v_unused_3128_);
v_unused_3129_ = lean_ctor_get(v_r_3076_, 1);
lean_dec(v_unused_3129_);
v_unused_3130_ = lean_ctor_get(v_r_3076_, 0);
lean_dec(v_unused_3130_);
v___x_3098_ = v_r_3076_;
v_isShared_3099_ = v_isSharedCheck_3125_;
goto v_resetjp_3097_;
}
else
{
lean_dec(v_r_3076_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3125_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___x_3113_; lean_object* v___y_3115_; 
v___x_3100_ = lean_nat_add(v___x_3070_, v_size_3072_);
lean_dec(v_size_3072_);
v___x_3101_ = lean_nat_add(v___x_3100_, v_size_3071_);
lean_dec(v___x_3100_);
v___x_3113_ = lean_nat_add(v___x_3070_, v_size_3088_);
if (lean_obj_tag(v_l_3092_) == 0)
{
lean_object* v_size_3123_; 
v_size_3123_ = lean_ctor_get(v_l_3092_, 0);
lean_inc(v_size_3123_);
v___y_3115_ = v_size_3123_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3124_; 
v___x_3124_ = lean_unsigned_to_nat(0u);
v___y_3115_ = v___x_3124_;
goto v___jp_3114_;
}
v___jp_3102_:
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3106_ = lean_nat_add(v___y_3103_, v___y_3105_);
lean_dec(v___y_3105_);
lean_dec(v___y_3103_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 4, v_r_3063_);
lean_ctor_set(v___x_3098_, 3, v_r_3093_);
lean_ctor_set(v___x_3098_, 2, v_v_3061_);
lean_ctor_set(v___x_3098_, 1, v_k_3060_);
lean_ctor_set(v___x_3098_, 0, v___x_3106_);
v___x_3108_ = v___x_3098_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_k_3060_);
lean_ctor_set(v_reuseFailAlloc_3112_, 2, v_v_3061_);
lean_ctor_set(v_reuseFailAlloc_3112_, 3, v_r_3093_);
lean_ctor_set(v_reuseFailAlloc_3112_, 4, v_r_3063_);
v___x_3108_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3110_; 
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 4, v___x_3108_);
lean_ctor_set(v___x_3086_, 3, v___y_3104_);
lean_ctor_set(v___x_3086_, 2, v_v_3091_);
lean_ctor_set(v___x_3086_, 1, v_k_3090_);
lean_ctor_set(v___x_3086_, 0, v___x_3101_);
v___x_3110_ = v___x_3086_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_k_3090_);
lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_v_3091_);
lean_ctor_set(v_reuseFailAlloc_3111_, 3, v___y_3104_);
lean_ctor_set(v_reuseFailAlloc_3111_, 4, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
v___jp_3114_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = lean_nat_add(v___x_3113_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec(v___x_3113_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_l_3092_);
lean_ctor_set(v___x_3065_, 3, v_l_3075_);
lean_ctor_set(v___x_3065_, 2, v_v_3074_);
lean_ctor_set(v___x_3065_, 1, v_k_3073_);
lean_ctor_set(v___x_3065_, 0, v___x_3116_);
v___x_3118_ = v___x_3065_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_k_3073_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v_v_3074_);
lean_ctor_set(v_reuseFailAlloc_3122_, 3, v_l_3075_);
lean_ctor_set(v_reuseFailAlloc_3122_, 4, v_l_3092_);
v___x_3118_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_nat_add(v___x_3070_, v_size_3071_);
if (lean_obj_tag(v_r_3093_) == 0)
{
lean_object* v_size_3120_; 
v_size_3120_ = lean_ctor_get(v_r_3093_, 0);
lean_inc(v_size_3120_);
v___y_3103_ = v___x_3119_;
v___y_3104_ = v___x_3118_;
v___y_3105_ = v_size_3120_;
goto v___jp_3102_;
}
else
{
lean_object* v___x_3121_; 
v___x_3121_ = lean_unsigned_to_nat(0u);
v___y_3103_ = v___x_3119_;
v___y_3104_ = v___x_3118_;
v___y_3105_ = v___x_3121_;
goto v___jp_3102_;
}
}
}
}
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
lean_del_object(v___x_3065_);
v___x_3131_ = lean_nat_add(v___x_3070_, v_size_3072_);
lean_dec(v_size_3072_);
v___x_3132_ = lean_nat_add(v___x_3131_, v_size_3071_);
lean_dec(v___x_3131_);
v___x_3133_ = lean_nat_add(v___x_3070_, v_size_3071_);
v___x_3134_ = lean_nat_add(v___x_3133_, v_size_3089_);
lean_dec(v___x_3133_);
lean_inc_ref(v_r_3063_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 4, v_r_3063_);
lean_ctor_set(v___x_3086_, 3, v_r_3076_);
lean_ctor_set(v___x_3086_, 2, v_v_3061_);
lean_ctor_set(v___x_3086_, 1, v_k_3060_);
lean_ctor_set(v___x_3086_, 0, v___x_3134_);
v___x_3136_ = v___x_3086_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_k_3060_);
lean_ctor_set(v_reuseFailAlloc_3149_, 2, v_v_3061_);
lean_ctor_set(v_reuseFailAlloc_3149_, 3, v_r_3076_);
lean_ctor_set(v_reuseFailAlloc_3149_, 4, v_r_3063_);
v___x_3136_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v_isSharedCheck_3143_ = !lean_is_exclusive(v_r_3063_);
if (v_isSharedCheck_3143_ == 0)
{
lean_object* v_unused_3144_; lean_object* v_unused_3145_; lean_object* v_unused_3146_; lean_object* v_unused_3147_; lean_object* v_unused_3148_; 
v_unused_3144_ = lean_ctor_get(v_r_3063_, 4);
lean_dec(v_unused_3144_);
v_unused_3145_ = lean_ctor_get(v_r_3063_, 3);
lean_dec(v_unused_3145_);
v_unused_3146_ = lean_ctor_get(v_r_3063_, 2);
lean_dec(v_unused_3146_);
v_unused_3147_ = lean_ctor_get(v_r_3063_, 1);
lean_dec(v_unused_3147_);
v_unused_3148_ = lean_ctor_get(v_r_3063_, 0);
lean_dec(v_unused_3148_);
v___x_3138_ = v_r_3063_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_dec(v_r_3063_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 4, v___x_3136_);
lean_ctor_set(v___x_3138_, 3, v_l_3075_);
lean_ctor_set(v___x_3138_, 2, v_v_3074_);
lean_ctor_set(v___x_3138_, 1, v_k_3073_);
lean_ctor_set(v___x_3138_, 0, v___x_3132_);
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3132_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v_k_3073_);
lean_ctor_set(v_reuseFailAlloc_3142_, 2, v_v_3074_);
lean_ctor_set(v_reuseFailAlloc_3142_, 3, v_l_3075_);
lean_ctor_set(v_reuseFailAlloc_3142_, 4, v___x_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3156_; 
v_l_3156_ = lean_ctor_get(v_impl_3069_, 3);
if (lean_obj_tag(v_l_3156_) == 0)
{
lean_object* v_r_3157_; lean_object* v_k_3158_; lean_object* v_v_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3170_; 
lean_inc_ref(v_l_3156_);
v_r_3157_ = lean_ctor_get(v_impl_3069_, 4);
v_k_3158_ = lean_ctor_get(v_impl_3069_, 1);
v_v_3159_ = lean_ctor_get(v_impl_3069_, 2);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_impl_3069_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; lean_object* v_unused_3172_; 
v_unused_3171_ = lean_ctor_get(v_impl_3069_, 3);
lean_dec(v_unused_3171_);
v_unused_3172_ = lean_ctor_get(v_impl_3069_, 0);
lean_dec(v_unused_3172_);
v___x_3161_ = v_impl_3069_;
v_isShared_3162_ = v_isSharedCheck_3170_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_r_3157_);
lean_inc(v_v_3159_);
lean_inc(v_k_3158_);
lean_dec(v_impl_3069_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3170_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v___x_3165_; 
v___x_3163_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3157_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 3, v_r_3157_);
lean_ctor_set(v___x_3161_, 2, v_v_3061_);
lean_ctor_set(v___x_3161_, 1, v_k_3060_);
lean_ctor_set(v___x_3161_, 0, v___x_3070_);
v___x_3165_ = v___x_3161_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3070_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_k_3060_);
lean_ctor_set(v_reuseFailAlloc_3169_, 2, v_v_3061_);
lean_ctor_set(v_reuseFailAlloc_3169_, 3, v_r_3157_);
lean_ctor_set(v_reuseFailAlloc_3169_, 4, v_r_3157_);
v___x_3165_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___x_3167_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v___x_3165_);
lean_ctor_set(v___x_3065_, 3, v_l_3156_);
lean_ctor_set(v___x_3065_, 2, v_v_3159_);
lean_ctor_set(v___x_3065_, 1, v_k_3158_);
lean_ctor_set(v___x_3065_, 0, v___x_3163_);
v___x_3167_ = v___x_3065_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_k_3158_);
lean_ctor_set(v_reuseFailAlloc_3168_, 2, v_v_3159_);
lean_ctor_set(v_reuseFailAlloc_3168_, 3, v_l_3156_);
lean_ctor_set(v_reuseFailAlloc_3168_, 4, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
else
{
lean_object* v_r_3173_; 
v_r_3173_ = lean_ctor_get(v_impl_3069_, 4);
lean_inc(v_r_3173_);
if (lean_obj_tag(v_r_3173_) == 0)
{
lean_object* v_k_3174_; lean_object* v_v_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3198_; 
lean_inc(v_l_3156_);
v_k_3174_ = lean_ctor_get(v_impl_3069_, 1);
v_v_3175_ = lean_ctor_get(v_impl_3069_, 2);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_impl_3069_);
if (v_isSharedCheck_3198_ == 0)
{
lean_object* v_unused_3199_; lean_object* v_unused_3200_; lean_object* v_unused_3201_; 
v_unused_3199_ = lean_ctor_get(v_impl_3069_, 4);
lean_dec(v_unused_3199_);
v_unused_3200_ = lean_ctor_get(v_impl_3069_, 3);
lean_dec(v_unused_3200_);
v_unused_3201_ = lean_ctor_get(v_impl_3069_, 0);
lean_dec(v_unused_3201_);
v___x_3177_ = v_impl_3069_;
v_isShared_3178_ = v_isSharedCheck_3198_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_v_3175_);
lean_inc(v_k_3174_);
lean_dec(v_impl_3069_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3198_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v_k_3179_; lean_object* v_v_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3194_; 
v_k_3179_ = lean_ctor_get(v_r_3173_, 1);
v_v_3180_ = lean_ctor_get(v_r_3173_, 2);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_r_3173_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; lean_object* v_unused_3196_; lean_object* v_unused_3197_; 
v_unused_3195_ = lean_ctor_get(v_r_3173_, 4);
lean_dec(v_unused_3195_);
v_unused_3196_ = lean_ctor_get(v_r_3173_, 3);
lean_dec(v_unused_3196_);
v_unused_3197_ = lean_ctor_get(v_r_3173_, 0);
lean_dec(v_unused_3197_);
v___x_3182_ = v_r_3173_;
v_isShared_3183_ = v_isSharedCheck_3194_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_v_3180_);
lean_inc(v_k_3179_);
lean_dec(v_r_3173_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3194_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; lean_object* v___x_3186_; 
v___x_3184_ = lean_unsigned_to_nat(3u);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v_l_3156_);
lean_ctor_set(v___x_3182_, 3, v_l_3156_);
lean_ctor_set(v___x_3182_, 2, v_v_3175_);
lean_ctor_set(v___x_3182_, 1, v_k_3174_);
lean_ctor_set(v___x_3182_, 0, v___x_3070_);
v___x_3186_ = v___x_3182_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3070_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3193_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3193_, 3, v_l_3156_);
lean_ctor_set(v_reuseFailAlloc_3193_, 4, v_l_3156_);
v___x_3186_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
lean_object* v___x_3188_; 
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 4, v_l_3156_);
lean_ctor_set(v___x_3177_, 2, v_v_3061_);
lean_ctor_set(v___x_3177_, 1, v_k_3060_);
lean_ctor_set(v___x_3177_, 0, v___x_3070_);
v___x_3188_ = v___x_3177_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3070_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v_k_3060_);
lean_ctor_set(v_reuseFailAlloc_3192_, 2, v_v_3061_);
lean_ctor_set(v_reuseFailAlloc_3192_, 3, v_l_3156_);
lean_ctor_set(v_reuseFailAlloc_3192_, 4, v_l_3156_);
v___x_3188_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3190_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v___x_3188_);
lean_ctor_set(v___x_3065_, 3, v___x_3186_);
lean_ctor_set(v___x_3065_, 2, v_v_3180_);
lean_ctor_set(v___x_3065_, 1, v_k_3179_);
lean_ctor_set(v___x_3065_, 0, v___x_3184_);
v___x_3190_ = v___x_3065_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_k_3179_);
lean_ctor_set(v_reuseFailAlloc_3191_, 2, v_v_3180_);
lean_ctor_set(v_reuseFailAlloc_3191_, 3, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3191_, 4, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
}
}
else
{
lean_object* v___x_3202_; lean_object* v___x_3204_; 
v___x_3202_ = lean_unsigned_to_nat(2u);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_r_3173_);
lean_ctor_set(v___x_3065_, 3, v_impl_3069_);
lean_ctor_set(v___x_3065_, 0, v___x_3202_);
v___x_3204_ = v___x_3065_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v_k_3060_);
lean_ctor_set(v_reuseFailAlloc_3205_, 2, v_v_3061_);
lean_ctor_set(v_reuseFailAlloc_3205_, 3, v_impl_3069_);
lean_ctor_set(v_reuseFailAlloc_3205_, 4, v_r_3173_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3207_; 
lean_dec(v_v_3061_);
lean_dec(v_k_3060_);
lean_dec_ref(v_cmp_3055_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 2, v_v_3057_);
lean_ctor_set(v___x_3065_, 1, v_k_3056_);
v___x_3207_ = v___x_3065_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_size_3059_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_k_3056_);
lean_ctor_set(v_reuseFailAlloc_3208_, 2, v_v_3057_);
lean_ctor_set(v_reuseFailAlloc_3208_, 3, v_l_3062_);
lean_ctor_set(v_reuseFailAlloc_3208_, 4, v_r_3063_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
default: 
{
lean_object* v_impl_3209_; lean_object* v___x_3210_; 
lean_dec(v_size_3059_);
v_impl_3209_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3055_, v_k_3056_, v_v_3057_, v_r_3063_);
v___x_3210_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3062_) == 0)
{
lean_object* v_size_3211_; lean_object* v_size_3212_; lean_object* v_k_3213_; lean_object* v_v_3214_; lean_object* v_l_3215_; lean_object* v_r_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
v_size_3211_ = lean_ctor_get(v_l_3062_, 0);
v_size_3212_ = lean_ctor_get(v_impl_3209_, 0);
v_k_3213_ = lean_ctor_get(v_impl_3209_, 1);
v_v_3214_ = lean_ctor_get(v_impl_3209_, 2);
v_l_3215_ = lean_ctor_get(v_impl_3209_, 3);
lean_inc(v_l_3215_);
v_r_3216_ = lean_ctor_get(v_impl_3209_, 4);
v___x_3217_ = lean_unsigned_to_nat(3u);
v___x_3218_ = lean_nat_mul(v___x_3217_, v_size_3211_);
v___x_3219_ = lean_nat_dec_lt(v___x_3218_, v_size_3212_);
lean_dec(v___x_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3223_; 
lean_dec(v_l_3215_);
v___x_3220_ = lean_nat_add(v___x_3210_, v_size_3211_);
v___x_3221_ = lean_nat_add(v___x_3220_, v_size_3212_);
lean_dec(v___x_3220_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_impl_3209_);
lean_ctor_set(v___x_3065_, 0, v___x_3221_);
v___x_3223_ = v___x_3065_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v_k_3060_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v_v_3061_);
lean_ctor_set(v_reuseFailAlloc_3224_, 3, v_l_3062_);
lean_ctor_set(v_reuseFailAlloc_3224_, 4, v_impl_3209_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
else
{
lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3288_; 
lean_inc(v_r_3216_);
lean_inc(v_v_3214_);
lean_inc(v_k_3213_);
lean_inc(v_size_3212_);
v_isSharedCheck_3288_ = !lean_is_exclusive(v_impl_3209_);
if (v_isSharedCheck_3288_ == 0)
{
lean_object* v_unused_3289_; lean_object* v_unused_3290_; lean_object* v_unused_3291_; lean_object* v_unused_3292_; lean_object* v_unused_3293_; 
v_unused_3289_ = lean_ctor_get(v_impl_3209_, 4);
lean_dec(v_unused_3289_);
v_unused_3290_ = lean_ctor_get(v_impl_3209_, 3);
lean_dec(v_unused_3290_);
v_unused_3291_ = lean_ctor_get(v_impl_3209_, 2);
lean_dec(v_unused_3291_);
v_unused_3292_ = lean_ctor_get(v_impl_3209_, 1);
lean_dec(v_unused_3292_);
v_unused_3293_ = lean_ctor_get(v_impl_3209_, 0);
lean_dec(v_unused_3293_);
v___x_3226_ = v_impl_3209_;
v_isShared_3227_ = v_isSharedCheck_3288_;
goto v_resetjp_3225_;
}
else
{
lean_dec(v_impl_3209_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3288_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v_size_3228_; lean_object* v_k_3229_; lean_object* v_v_3230_; lean_object* v_l_3231_; lean_object* v_r_3232_; lean_object* v_size_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; uint8_t v___x_3236_; 
v_size_3228_ = lean_ctor_get(v_l_3215_, 0);
v_k_3229_ = lean_ctor_get(v_l_3215_, 1);
v_v_3230_ = lean_ctor_get(v_l_3215_, 2);
v_l_3231_ = lean_ctor_get(v_l_3215_, 3);
v_r_3232_ = lean_ctor_get(v_l_3215_, 4);
v_size_3233_ = lean_ctor_get(v_r_3216_, 0);
v___x_3234_ = lean_unsigned_to_nat(2u);
v___x_3235_ = lean_nat_mul(v___x_3234_, v_size_3233_);
v___x_3236_ = lean_nat_dec_lt(v_size_3228_, v___x_3235_);
lean_dec(v___x_3235_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3264_; 
lean_inc(v_r_3232_);
lean_inc(v_l_3231_);
lean_inc(v_v_3230_);
lean_inc(v_k_3229_);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_l_3215_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; lean_object* v_unused_3266_; lean_object* v_unused_3267_; lean_object* v_unused_3268_; lean_object* v_unused_3269_; 
v_unused_3265_ = lean_ctor_get(v_l_3215_, 4);
lean_dec(v_unused_3265_);
v_unused_3266_ = lean_ctor_get(v_l_3215_, 3);
lean_dec(v_unused_3266_);
v_unused_3267_ = lean_ctor_get(v_l_3215_, 2);
lean_dec(v_unused_3267_);
v_unused_3268_ = lean_ctor_get(v_l_3215_, 1);
lean_dec(v_unused_3268_);
v_unused_3269_ = lean_ctor_get(v_l_3215_, 0);
lean_dec(v_unused_3269_);
v___x_3238_ = v_l_3215_;
v_isShared_3239_ = v_isSharedCheck_3264_;
goto v_resetjp_3237_;
}
else
{
lean_dec(v_l_3215_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3264_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3254_; 
v___x_3240_ = lean_nat_add(v___x_3210_, v_size_3211_);
v___x_3241_ = lean_nat_add(v___x_3240_, v_size_3212_);
lean_dec(v_size_3212_);
if (lean_obj_tag(v_l_3231_) == 0)
{
lean_object* v_size_3262_; 
v_size_3262_ = lean_ctor_get(v_l_3231_, 0);
lean_inc(v_size_3262_);
v___y_3254_ = v_size_3262_;
goto v___jp_3253_;
}
else
{
lean_object* v___x_3263_; 
v___x_3263_ = lean_unsigned_to_nat(0u);
v___y_3254_ = v___x_3263_;
goto v___jp_3253_;
}
v___jp_3242_:
{
lean_object* v___x_3246_; lean_object* v___x_3248_; 
v___x_3246_ = lean_nat_add(v___y_3243_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec(v___y_3243_);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 4, v_r_3216_);
lean_ctor_set(v___x_3238_, 3, v_r_3232_);
lean_ctor_set(v___x_3238_, 2, v_v_3214_);
lean_ctor_set(v___x_3238_, 1, v_k_3213_);
lean_ctor_set(v___x_3238_, 0, v___x_3246_);
v___x_3248_ = v___x_3238_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3246_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v_k_3213_);
lean_ctor_set(v_reuseFailAlloc_3252_, 2, v_v_3214_);
lean_ctor_set(v_reuseFailAlloc_3252_, 3, v_r_3232_);
lean_ctor_set(v_reuseFailAlloc_3252_, 4, v_r_3216_);
v___x_3248_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3250_; 
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 4, v___x_3248_);
lean_ctor_set(v___x_3226_, 3, v___y_3244_);
lean_ctor_set(v___x_3226_, 2, v_v_3230_);
lean_ctor_set(v___x_3226_, 1, v_k_3229_);
lean_ctor_set(v___x_3226_, 0, v___x_3241_);
v___x_3250_ = v___x_3226_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v_k_3229_);
lean_ctor_set(v_reuseFailAlloc_3251_, 2, v_v_3230_);
lean_ctor_set(v_reuseFailAlloc_3251_, 3, v___y_3244_);
lean_ctor_set(v_reuseFailAlloc_3251_, 4, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
v___jp_3253_:
{
lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3255_ = lean_nat_add(v___x_3240_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec(v___x_3240_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_l_3231_);
lean_ctor_set(v___x_3065_, 0, v___x_3255_);
v___x_3257_ = v___x_3065_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v_k_3060_);
lean_ctor_set(v_reuseFailAlloc_3261_, 2, v_v_3061_);
lean_ctor_set(v_reuseFailAlloc_3261_, 3, v_l_3062_);
lean_ctor_set(v_reuseFailAlloc_3261_, 4, v_l_3231_);
v___x_3257_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3258_; 
v___x_3258_ = lean_nat_add(v___x_3210_, v_size_3233_);
if (lean_obj_tag(v_r_3232_) == 0)
{
lean_object* v_size_3259_; 
v_size_3259_ = lean_ctor_get(v_r_3232_, 0);
lean_inc(v_size_3259_);
v___y_3243_ = v___x_3258_;
v___y_3244_ = v___x_3257_;
v___y_3245_ = v_size_3259_;
goto v___jp_3242_;
}
else
{
lean_object* v___x_3260_; 
v___x_3260_ = lean_unsigned_to_nat(0u);
v___y_3243_ = v___x_3258_;
v___y_3244_ = v___x_3257_;
v___y_3245_ = v___x_3260_;
goto v___jp_3242_;
}
}
}
}
}
else
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3274_; 
lean_del_object(v___x_3065_);
v___x_3270_ = lean_nat_add(v___x_3210_, v_size_3211_);
v___x_3271_ = lean_nat_add(v___x_3270_, v_size_3212_);
lean_dec(v_size_3212_);
v___x_3272_ = lean_nat_add(v___x_3270_, v_size_3228_);
lean_dec(v___x_3270_);
lean_inc_ref(v_l_3062_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 4, v_l_3215_);
lean_ctor_set(v___x_3226_, 3, v_l_3062_);
lean_ctor_set(v___x_3226_, 2, v_v_3061_);
lean_ctor_set(v___x_3226_, 1, v_k_3060_);
lean_ctor_set(v___x_3226_, 0, v___x_3272_);
v___x_3274_ = v___x_3226_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3272_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_k_3060_);
lean_ctor_set(v_reuseFailAlloc_3287_, 2, v_v_3061_);
lean_ctor_set(v_reuseFailAlloc_3287_, 3, v_l_3062_);
lean_ctor_set(v_reuseFailAlloc_3287_, 4, v_l_3215_);
v___x_3274_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
v_isSharedCheck_3281_ = !lean_is_exclusive(v_l_3062_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; lean_object* v_unused_3283_; lean_object* v_unused_3284_; lean_object* v_unused_3285_; lean_object* v_unused_3286_; 
v_unused_3282_ = lean_ctor_get(v_l_3062_, 4);
lean_dec(v_unused_3282_);
v_unused_3283_ = lean_ctor_get(v_l_3062_, 3);
lean_dec(v_unused_3283_);
v_unused_3284_ = lean_ctor_get(v_l_3062_, 2);
lean_dec(v_unused_3284_);
v_unused_3285_ = lean_ctor_get(v_l_3062_, 1);
lean_dec(v_unused_3285_);
v_unused_3286_ = lean_ctor_get(v_l_3062_, 0);
lean_dec(v_unused_3286_);
v___x_3276_ = v_l_3062_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_dec(v_l_3062_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 4, v_r_3216_);
lean_ctor_set(v___x_3276_, 3, v___x_3274_);
lean_ctor_set(v___x_3276_, 2, v_v_3214_);
lean_ctor_set(v___x_3276_, 1, v_k_3213_);
lean_ctor_set(v___x_3276_, 0, v___x_3271_);
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3271_);
lean_ctor_set(v_reuseFailAlloc_3280_, 1, v_k_3213_);
lean_ctor_set(v_reuseFailAlloc_3280_, 2, v_v_3214_);
lean_ctor_set(v_reuseFailAlloc_3280_, 3, v___x_3274_);
lean_ctor_set(v_reuseFailAlloc_3280_, 4, v_r_3216_);
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
}
}
else
{
lean_object* v_l_3294_; 
v_l_3294_ = lean_ctor_get(v_impl_3209_, 3);
lean_inc(v_l_3294_);
if (lean_obj_tag(v_l_3294_) == 0)
{
lean_object* v_r_3295_; lean_object* v_k_3296_; lean_object* v_v_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3320_; 
v_r_3295_ = lean_ctor_get(v_impl_3209_, 4);
v_k_3296_ = lean_ctor_get(v_impl_3209_, 1);
v_v_3297_ = lean_ctor_get(v_impl_3209_, 2);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_impl_3209_);
if (v_isSharedCheck_3320_ == 0)
{
lean_object* v_unused_3321_; lean_object* v_unused_3322_; 
v_unused_3321_ = lean_ctor_get(v_impl_3209_, 3);
lean_dec(v_unused_3321_);
v_unused_3322_ = lean_ctor_get(v_impl_3209_, 0);
lean_dec(v_unused_3322_);
v___x_3299_ = v_impl_3209_;
v_isShared_3300_ = v_isSharedCheck_3320_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_r_3295_);
lean_inc(v_v_3297_);
lean_inc(v_k_3296_);
lean_dec(v_impl_3209_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3320_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v_k_3301_; lean_object* v_v_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3316_; 
v_k_3301_ = lean_ctor_get(v_l_3294_, 1);
v_v_3302_ = lean_ctor_get(v_l_3294_, 2);
v_isSharedCheck_3316_ = !lean_is_exclusive(v_l_3294_);
if (v_isSharedCheck_3316_ == 0)
{
lean_object* v_unused_3317_; lean_object* v_unused_3318_; lean_object* v_unused_3319_; 
v_unused_3317_ = lean_ctor_get(v_l_3294_, 4);
lean_dec(v_unused_3317_);
v_unused_3318_ = lean_ctor_get(v_l_3294_, 3);
lean_dec(v_unused_3318_);
v_unused_3319_ = lean_ctor_get(v_l_3294_, 0);
lean_dec(v_unused_3319_);
v___x_3304_ = v_l_3294_;
v_isShared_3305_ = v_isSharedCheck_3316_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_v_3302_);
lean_inc(v_k_3301_);
lean_dec(v_l_3294_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3316_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3306_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3295_, 2);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 4, v_r_3295_);
lean_ctor_set(v___x_3304_, 3, v_r_3295_);
lean_ctor_set(v___x_3304_, 2, v_v_3061_);
lean_ctor_set(v___x_3304_, 1, v_k_3060_);
lean_ctor_set(v___x_3304_, 0, v___x_3210_);
v___x_3308_ = v___x_3304_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_k_3060_);
lean_ctor_set(v_reuseFailAlloc_3315_, 2, v_v_3061_);
lean_ctor_set(v_reuseFailAlloc_3315_, 3, v_r_3295_);
lean_ctor_set(v_reuseFailAlloc_3315_, 4, v_r_3295_);
v___x_3308_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3310_; 
lean_inc(v_r_3295_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 3, v_r_3295_);
lean_ctor_set(v___x_3299_, 0, v___x_3210_);
v___x_3310_ = v___x_3299_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_k_3296_);
lean_ctor_set(v_reuseFailAlloc_3314_, 2, v_v_3297_);
lean_ctor_set(v_reuseFailAlloc_3314_, 3, v_r_3295_);
lean_ctor_set(v_reuseFailAlloc_3314_, 4, v_r_3295_);
v___x_3310_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
lean_object* v___x_3312_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v___x_3310_);
lean_ctor_set(v___x_3065_, 3, v___x_3308_);
lean_ctor_set(v___x_3065_, 2, v_v_3302_);
lean_ctor_set(v___x_3065_, 1, v_k_3301_);
lean_ctor_set(v___x_3065_, 0, v___x_3306_);
v___x_3312_ = v___x_3065_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3306_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_k_3301_);
lean_ctor_set(v_reuseFailAlloc_3313_, 2, v_v_3302_);
lean_ctor_set(v_reuseFailAlloc_3313_, 3, v___x_3308_);
lean_ctor_set(v_reuseFailAlloc_3313_, 4, v___x_3310_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
}
else
{
lean_object* v_r_3323_; 
v_r_3323_ = lean_ctor_get(v_impl_3209_, 4);
lean_inc(v_r_3323_);
if (lean_obj_tag(v_r_3323_) == 0)
{
lean_object* v_k_3324_; lean_object* v_v_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3336_; 
v_k_3324_ = lean_ctor_get(v_impl_3209_, 1);
v_v_3325_ = lean_ctor_get(v_impl_3209_, 2);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_impl_3209_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; lean_object* v_unused_3338_; lean_object* v_unused_3339_; 
v_unused_3337_ = lean_ctor_get(v_impl_3209_, 4);
lean_dec(v_unused_3337_);
v_unused_3338_ = lean_ctor_get(v_impl_3209_, 3);
lean_dec(v_unused_3338_);
v_unused_3339_ = lean_ctor_get(v_impl_3209_, 0);
lean_dec(v_unused_3339_);
v___x_3327_ = v_impl_3209_;
v_isShared_3328_ = v_isSharedCheck_3336_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_v_3325_);
lean_inc(v_k_3324_);
lean_dec(v_impl_3209_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3336_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3329_; lean_object* v___x_3331_; 
v___x_3329_ = lean_unsigned_to_nat(3u);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 4, v_l_3294_);
lean_ctor_set(v___x_3327_, 2, v_v_3061_);
lean_ctor_set(v___x_3327_, 1, v_k_3060_);
lean_ctor_set(v___x_3327_, 0, v___x_3210_);
v___x_3331_ = v___x_3327_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_k_3060_);
lean_ctor_set(v_reuseFailAlloc_3335_, 2, v_v_3061_);
lean_ctor_set(v_reuseFailAlloc_3335_, 3, v_l_3294_);
lean_ctor_set(v_reuseFailAlloc_3335_, 4, v_l_3294_);
v___x_3331_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
lean_object* v___x_3333_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_r_3323_);
lean_ctor_set(v___x_3065_, 3, v___x_3331_);
lean_ctor_set(v___x_3065_, 2, v_v_3325_);
lean_ctor_set(v___x_3065_, 1, v_k_3324_);
lean_ctor_set(v___x_3065_, 0, v___x_3329_);
v___x_3333_ = v___x_3065_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3329_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_k_3324_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_v_3325_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v___x_3331_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_r_3323_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
else
{
lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3340_ = lean_unsigned_to_nat(2u);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_impl_3209_);
lean_ctor_set(v___x_3065_, 3, v_r_3323_);
lean_ctor_set(v___x_3065_, 0, v___x_3340_);
v___x_3342_ = v___x_3065_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
lean_ctor_set(v_reuseFailAlloc_3343_, 1, v_k_3060_);
lean_ctor_set(v_reuseFailAlloc_3343_, 2, v_v_3061_);
lean_ctor_set(v_reuseFailAlloc_3343_, 3, v_r_3323_);
lean_ctor_set(v_reuseFailAlloc_3343_, 4, v_impl_3209_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
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
lean_object* v___x_3345_; lean_object* v___x_3346_; 
lean_dec_ref(v_cmp_3055_);
v___x_3345_ = lean_unsigned_to_nat(1u);
v___x_3346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3345_);
lean_ctor_set(v___x_3346_, 1, v_k_3056_);
lean_ctor_set(v___x_3346_, 2, v_v_3057_);
lean_ctor_set(v___x_3346_, 3, v_t_3058_);
lean_ctor_set(v___x_3346_, 4, v_t_3058_);
return v___x_3346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(lean_object* v_cmp_3347_, lean_object* v_init_3348_, lean_object* v_x_3349_){
_start:
{
if (lean_obj_tag(v_x_3349_) == 0)
{
lean_object* v_k_3350_; lean_object* v_v_3351_; lean_object* v_l_3352_; lean_object* v_r_3353_; lean_object* v___x_3354_; 
v_k_3350_ = lean_ctor_get(v_x_3349_, 1);
lean_inc(v_k_3350_);
v_v_3351_ = lean_ctor_get(v_x_3349_, 2);
lean_inc(v_v_3351_);
v_l_3352_ = lean_ctor_get(v_x_3349_, 3);
lean_inc(v_l_3352_);
v_r_3353_ = lean_ctor_get(v_x_3349_, 4);
lean_inc(v_r_3353_);
lean_dec_ref_known(v_x_3349_, 5);
lean_inc_ref(v_cmp_3347_);
v___x_3354_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_3347_, v_init_3348_, v_l_3352_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_dec(v_r_3353_);
lean_dec(v_v_3351_);
lean_dec(v_k_3350_);
lean_dec_ref(v_cmp_3347_);
return v___x_3354_;
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3356_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref_known(v___x_3354_, 1);
v___x_3356_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_v_3351_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec(v_a_3355_);
lean_dec(v_r_3353_);
lean_dec(v_k_3350_);
lean_dec_ref(v_cmp_3347_);
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3356_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3356_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3366_; 
v_a_3365_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3356_, 1);
lean_inc_ref(v_cmp_3347_);
v___x_3366_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3347_, v_k_3350_, v_a_3365_, v_a_3355_);
v_init_3348_ = v___x_3366_;
v_x_3349_ = v_r_3353_;
goto _start;
}
}
}
else
{
lean_object* v___x_3368_; 
lean_dec_ref(v_cmp_3347_);
v___x_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3368_, 0, v_init_3348_);
return v___x_3368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(lean_object* v_cmp_3369_, lean_object* v_j_3370_){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Lean_Json_getObj_x3f(v_j_3370_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
lean_dec_ref(v_cmp_3369_);
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___x_3371_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3371_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_a_3380_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3380_);
lean_dec_ref_known(v___x_3371_, 1);
v___x_3381_ = lean_box(1);
v___x_3382_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_3369_, v___x_3381_, v_a_3380_);
return v___x_3382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(lean_object* v_x_3386_){
_start:
{
if (lean_obj_tag(v_x_3386_) == 0)
{
lean_object* v___x_3387_; 
v___x_3387_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__0));
return v___x_3387_;
}
else
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3388_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__1));
v___x_3389_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(v___x_3388_, v_x_3386_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3389_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3389_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3406_; 
v_a_3398_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3400_ = v___x_3389_;
v_isShared_3401_ = v_isSharedCheck_3406_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3389_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3406_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3402_; lean_object* v___x_3404_; 
v___x_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3402_, 0, v_a_3398_);
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 0, v___x_3402_);
v___x_3404_ = v___x_3400_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(lean_object* v_j_3407_, lean_object* v_k_3408_){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = l_Lean_Json_getObjValD(v_j_3407_, v_k_3408_);
v___x_3410_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(v___x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4___boxed(lean_object* v_j_3411_, lean_object* v_k_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_j_3411_, v_k_3412_);
lean_dec_ref(v_k_3412_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(lean_object* v_j_3414_, lean_object* v_k_3415_){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = l_Lean_Json_getObjValD(v_j_3414_, v_k_3415_);
v___x_3417_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v___x_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1___boxed(lean_object* v_j_3418_, lean_object* v_k_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_j_3418_, v_k_3419_);
lean_dec_ref(v_k_3419_);
return v_res_3420_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = 1;
v___x_3430_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__4));
v___x_3431_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3430_, v___x_3429_);
return v___x_3431_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3433_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__6));
v___x_3434_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__5, &l_Lake_Check_instFromJsonConfig_fromJson___closed__5_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5);
v___x_3435_ = lean_string_append(v___x_3434_, v___x_3433_);
return v___x_3435_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = 1;
v___x_3439_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__8));
v___x_3440_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3439_, v___x_3438_);
return v___x_3440_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3441_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__9, &l_Lake_Check_instFromJsonConfig_fromJson___closed__9_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9);
v___x_3442_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3443_ = lean_string_append(v___x_3442_, v___x_3441_);
return v___x_3443_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3446_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__10, &l_Lake_Check_instFromJsonConfig_fromJson___closed__10_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10);
v___x_3447_ = lean_string_append(v___x_3446_, v___x_3445_);
return v___x_3447_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15(void){
_start:
{
uint8_t v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = 1;
v___x_3452_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__14));
v___x_3453_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3452_, v___x_3451_);
return v___x_3453_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16(void){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3454_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__15, &l_Lake_Check_instFromJsonConfig_fromJson___closed__15_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15);
v___x_3455_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3456_ = lean_string_append(v___x_3455_, v___x_3454_);
return v___x_3456_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3457_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3458_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__16, &l_Lake_Check_instFromJsonConfig_fromJson___closed__16_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16);
v___x_3459_ = lean_string_append(v___x_3458_, v___x_3457_);
return v___x_3459_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20(void){
_start:
{
uint8_t v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3463_ = 1;
v___x_3464_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__19));
v___x_3465_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3464_, v___x_3463_);
return v___x_3465_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21(void){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3466_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__20, &l_Lake_Check_instFromJsonConfig_fromJson___closed__20_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20);
v___x_3467_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3468_ = lean_string_append(v___x_3467_, v___x_3466_);
return v___x_3468_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22(void){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3470_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__21, &l_Lake_Check_instFromJsonConfig_fromJson___closed__21_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21);
v___x_3471_ = lean_string_append(v___x_3470_, v___x_3469_);
return v___x_3471_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25(void){
_start:
{
uint8_t v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3475_ = 1;
v___x_3476_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__24));
v___x_3477_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3476_, v___x_3475_);
return v___x_3477_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26(void){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__25, &l_Lake_Check_instFromJsonConfig_fromJson___closed__25_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25);
v___x_3479_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3480_ = lean_string_append(v___x_3479_, v___x_3478_);
return v___x_3480_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27(void){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3482_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__26, &l_Lake_Check_instFromJsonConfig_fromJson___closed__26_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26);
v___x_3483_ = lean_string_append(v___x_3482_, v___x_3481_);
return v___x_3483_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29(void){
_start:
{
uint8_t v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = 1;
v___x_3487_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__28));
v___x_3488_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3487_, v___x_3486_);
return v___x_3488_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__29, &l_Lake_Check_instFromJsonConfig_fromJson___closed__29_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29);
v___x_3490_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3491_ = lean_string_append(v___x_3490_, v___x_3489_);
return v___x_3491_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3492_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3493_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__30, &l_Lake_Check_instFromJsonConfig_fromJson___closed__30_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30);
v___x_3494_ = lean_string_append(v___x_3493_, v___x_3492_);
return v___x_3494_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35(void){
_start:
{
uint8_t v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3499_ = 1;
v___x_3500_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__34));
v___x_3501_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3500_, v___x_3499_);
return v___x_3501_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36(void){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3502_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__35, &l_Lake_Check_instFromJsonConfig_fromJson___closed__35_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35);
v___x_3503_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3504_ = lean_string_append(v___x_3503_, v___x_3502_);
return v___x_3504_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3505_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3506_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__36, &l_Lake_Check_instFromJsonConfig_fromJson___closed__36_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36);
v___x_3507_ = lean_string_append(v___x_3506_, v___x_3505_);
return v___x_3507_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41(void){
_start:
{
uint8_t v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = 1;
v___x_3513_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__40));
v___x_3514_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3513_, v___x_3512_);
return v___x_3514_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__41, &l_Lake_Check_instFromJsonConfig_fromJson___closed__41_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41);
v___x_3516_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3517_ = lean_string_append(v___x_3516_, v___x_3515_);
return v___x_3517_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3518_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3519_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__42, &l_Lake_Check_instFromJsonConfig_fromJson___closed__42_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42);
v___x_3520_ = lean_string_append(v___x_3519_, v___x_3518_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instFromJsonConfig_fromJson(lean_object* v_json_3521_){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3522_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
lean_inc(v_json_3521_);
v___x_3523_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_3521_, v___x_3522_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3533_; 
lean_dec(v_json_3521_);
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3526_ = v___x_3523_;
v_isShared_3527_ = v_isSharedCheck_3533_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3523_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3533_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3528_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__12, &l_Lake_Check_instFromJsonConfig_fromJson___closed__12_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12);
v___x_3529_ = lean_string_append(v___x_3528_, v_a_3524_);
lean_dec(v_a_3524_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 0, v___x_3529_);
v___x_3531_ = v___x_3526_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v_a_3534_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3523_, 1);
v___x_3535_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
lean_inc(v_json_3521_);
v___x_3536_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_3521_, v___x_3535_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v_a_3534_);
lean_dec(v_json_3521_);
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3539_ = v___x_3536_;
v_isShared_3540_ = v_isSharedCheck_3546_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3536_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3546_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3544_; 
v___x_3541_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__17, &l_Lake_Check_instFromJsonConfig_fromJson___closed__17_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17);
v___x_3542_ = lean_string_append(v___x_3541_, v_a_3537_);
lean_dec(v_a_3537_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3542_);
v___x_3544_ = v___x_3539_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v_a_3547_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3536_, 1);
v___x_3548_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
lean_inc(v_json_3521_);
v___x_3549_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_3521_, v___x_3548_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3559_; 
lean_dec(v_a_3547_);
lean_dec(v_a_3534_);
lean_dec(v_json_3521_);
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3552_ = v___x_3549_;
v_isShared_3553_ = v_isSharedCheck_3559_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3549_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3559_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3557_; 
v___x_3554_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__22, &l_Lake_Check_instFromJsonConfig_fromJson___closed__22_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22);
v___x_3555_ = lean_string_append(v___x_3554_, v_a_3550_);
lean_dec(v_a_3550_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v___x_3555_);
v___x_3557_ = v___x_3552_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3555_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v_a_3560_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3549_, 1);
v___x_3561_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
lean_inc(v_json_3521_);
v___x_3562_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_json_3521_, v___x_3561_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3572_; 
lean_dec(v_a_3560_);
lean_dec(v_a_3547_);
lean_dec(v_a_3534_);
lean_dec(v_json_3521_);
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3565_ = v___x_3562_;
v_isShared_3566_ = v_isSharedCheck_3572_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3562_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3572_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3567_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__27, &l_Lake_Check_instFromJsonConfig_fromJson___closed__27_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27);
v___x_3568_ = lean_string_append(v___x_3567_, v_a_3563_);
lean_dec(v_a_3563_);
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3568_);
v___x_3570_ = v___x_3565_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v_a_3573_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3573_);
lean_dec_ref_known(v___x_3562_, 1);
v___x_3574_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
lean_inc(v_json_3521_);
v___x_3575_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_3521_, v___x_3574_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v_a_3573_);
lean_dec(v_a_3560_);
lean_dec(v_a_3547_);
lean_dec(v_a_3534_);
lean_dec(v_json_3521_);
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3578_ = v___x_3575_;
v_isShared_3579_ = v_isSharedCheck_3585_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3585_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3580_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__31, &l_Lake_Check_instFromJsonConfig_fromJson___closed__31_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31);
v___x_3581_ = lean_string_append(v___x_3580_, v_a_3576_);
lean_dec(v_a_3576_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v___x_3581_);
v___x_3583_ = v___x_3578_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3581_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v_a_3586_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_a_3586_);
lean_dec_ref_known(v___x_3575_, 1);
v___x_3587_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
lean_inc(v_json_3521_);
v___x_3588_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_json_3521_, v___x_3587_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3598_; 
lean_dec(v_a_3586_);
lean_dec(v_a_3573_);
lean_dec(v_a_3560_);
lean_dec(v_a_3547_);
lean_dec(v_a_3534_);
lean_dec(v_json_3521_);
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3591_ = v___x_3588_;
v_isShared_3592_ = v_isSharedCheck_3598_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3588_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3598_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3593_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__37, &l_Lake_Check_instFromJsonConfig_fromJson___closed__37_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37);
v___x_3594_ = lean_string_append(v___x_3593_, v_a_3589_);
lean_dec(v_a_3589_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v___x_3594_);
v___x_3596_ = v___x_3591_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v_a_3599_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3588_, 1);
v___x_3600_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_3601_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_json_3521_, v___x_3600_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3611_; 
lean_dec(v_a_3599_);
lean_dec(v_a_3586_);
lean_dec(v_a_3573_);
lean_dec(v_a_3560_);
lean_dec(v_a_3547_);
lean_dec(v_a_3534_);
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3604_ = v___x_3601_;
v_isShared_3605_ = v_isSharedCheck_3611_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3611_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3609_; 
v___x_3606_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__43, &l_Lake_Check_instFromJsonConfig_fromJson___closed__43_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43);
v___x_3607_ = lean_string_append(v___x_3606_, v_a_3602_);
lean_dec(v_a_3602_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v___x_3607_);
v___x_3609_ = v___x_3604_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3620_; 
v_a_3612_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3614_ = v___x_3601_;
v_isShared_3615_ = v_isSharedCheck_3620_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3601_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3620_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3616_; lean_object* v___x_3618_; 
v___x_3616_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3616_, 0, v_a_3534_);
lean_ctor_set(v___x_3616_, 1, v_a_3547_);
lean_ctor_set(v___x_3616_, 2, v_a_3560_);
lean_ctor_set(v___x_3616_, 3, v_a_3573_);
lean_ctor_set(v___x_3616_, 4, v_a_3586_);
lean_ctor_set(v___x_3616_, 5, v_a_3599_);
lean_ctor_set(v___x_3616_, 6, v_a_3612_);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 0, v___x_3616_);
v___x_3618_ = v___x_3614_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3616_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10(lean_object* v_cmp_3621_, lean_object* v_00_u03b2_3622_, lean_object* v_k_3623_, lean_object* v_v_3624_, lean_object* v_t_3625_, lean_object* v_hl_3626_){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3621_, v_k_3623_, v_v_3624_, v_t_3625_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(lean_object* v_k_3630_, lean_object* v_x_3631_){
_start:
{
if (lean_obj_tag(v_x_3631_) == 0)
{
lean_object* v___x_3632_; 
lean_dec_ref(v_k_3630_);
v___x_3632_ = lean_box(0);
return v___x_3632_;
}
else
{
lean_object* v_val_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v_val_3633_ = lean_ctor_get(v_x_3631_, 0);
v___x_3634_ = lean_alloc_ctor(1, 0, 1);
v___x_3635_ = lean_unbox(v_val_3633_);
lean_ctor_set_uint8(v___x_3634_, 0, v___x_3635_);
v___x_3636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3636_, 0, v_k_3630_);
lean_ctor_set(v___x_3636_, 1, v___x_3634_);
v___x_3637_ = lean_box(0);
v___x_3638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3636_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2___boxed(lean_object* v_k_3639_, lean_object* v_x_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v_k_3639_, v_x_3640_);
lean_dec(v_x_3640_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(size_t v_sz_3642_, size_t v_i_3643_, lean_object* v_bs_3644_){
_start:
{
uint8_t v___x_3645_; 
v___x_3645_ = lean_usize_dec_lt(v_i_3643_, v_sz_3642_);
if (v___x_3645_ == 0)
{
return v_bs_3644_;
}
else
{
lean_object* v_v_3646_; lean_object* v___x_3647_; lean_object* v_bs_x27_3648_; lean_object* v___x_3649_; size_t v___x_3650_; size_t v___x_3651_; lean_object* v___x_3652_; 
v_v_3646_ = lean_array_uget(v_bs_3644_, v_i_3643_);
v___x_3647_ = lean_unsigned_to_nat(0u);
v_bs_x27_3648_ = lean_array_uset(v_bs_3644_, v_i_3643_, v___x_3647_);
v___x_3649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3649_, 0, v_v_3646_);
v___x_3650_ = ((size_t)1ULL);
v___x_3651_ = lean_usize_add(v_i_3643_, v___x_3650_);
v___x_3652_ = lean_array_uset(v_bs_x27_3648_, v_i_3643_, v___x_3649_);
v_i_3643_ = v___x_3651_;
v_bs_3644_ = v___x_3652_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3654_, lean_object* v_i_3655_, lean_object* v_bs_3656_){
_start:
{
size_t v_sz_boxed_3657_; size_t v_i_boxed_3658_; lean_object* v_res_3659_; 
v_sz_boxed_3657_ = lean_unbox_usize(v_sz_3654_);
lean_dec(v_sz_3654_);
v_i_boxed_3658_ = lean_unbox_usize(v_i_3655_);
lean_dec(v_i_3655_);
v_res_3659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_boxed_3657_, v_i_boxed_3658_, v_bs_3656_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(lean_object* v_a_3660_){
_start:
{
size_t v_sz_3661_; size_t v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v_sz_3661_ = lean_array_size(v_a_3660_);
v___x_3662_ = ((size_t)0ULL);
v___x_3663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_3661_, v___x_3662_, v_a_3660_);
v___x_3664_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(lean_object* v_x_3665_){
_start:
{
if (lean_obj_tag(v_x_3665_) == 0)
{
lean_object* v___x_3666_; 
v___x_3666_ = lean_box(0);
return v___x_3666_;
}
else
{
lean_object* v_val_3667_; lean_object* v___x_3668_; 
v_val_3667_ = lean_ctor_get(v_x_3665_, 0);
lean_inc(v_val_3667_);
lean_dec_ref_known(v_x_3665_, 1);
v___x_3668_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_val_3667_);
return v___x_3668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(lean_object* v_a_3669_, lean_object* v_a_3670_){
_start:
{
if (lean_obj_tag(v_a_3669_) == 0)
{
lean_object* v___x_3671_; 
v___x_3671_ = lean_array_to_list(v_a_3670_);
return v___x_3671_;
}
else
{
lean_object* v_head_3672_; lean_object* v_tail_3673_; lean_object* v___x_3674_; 
v_head_3672_ = lean_ctor_get(v_a_3669_, 0);
lean_inc(v_head_3672_);
v_tail_3673_ = lean_ctor_get(v_a_3669_, 1);
lean_inc(v_tail_3673_);
lean_dec_ref_known(v_a_3669_, 2);
v___x_3674_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_3670_, v_head_3672_);
v_a_3669_ = v_tail_3673_;
v_a_3670_ = v___x_3674_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(lean_object* v_t_3676_){
_start:
{
if (lean_obj_tag(v_t_3676_) == 0)
{
lean_object* v_size_3677_; lean_object* v_k_3678_; lean_object* v_v_3679_; lean_object* v_l_3680_; lean_object* v_r_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3691_; 
v_size_3677_ = lean_ctor_get(v_t_3676_, 0);
v_k_3678_ = lean_ctor_get(v_t_3676_, 1);
v_v_3679_ = lean_ctor_get(v_t_3676_, 2);
v_l_3680_ = lean_ctor_get(v_t_3676_, 3);
v_r_3681_ = lean_ctor_get(v_t_3676_, 4);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_t_3676_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3683_ = v_t_3676_;
v_isShared_3684_ = v_isSharedCheck_3691_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_r_3681_);
lean_inc(v_l_3680_);
lean_inc(v_v_3679_);
lean_inc(v_k_3678_);
lean_inc(v_size_3677_);
lean_dec(v_t_3676_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3691_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3689_; 
v___x_3685_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_v_3679_);
v___x_3686_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_l_3680_);
v___x_3687_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_r_3681_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 4, v___x_3687_);
lean_ctor_set(v___x_3683_, 3, v___x_3686_);
lean_ctor_set(v___x_3683_, 2, v___x_3685_);
v___x_3689_ = v___x_3683_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_size_3677_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_k_3678_);
lean_ctor_set(v_reuseFailAlloc_3690_, 2, v___x_3685_);
lean_ctor_set(v_reuseFailAlloc_3690_, 3, v___x_3686_);
lean_ctor_set(v_reuseFailAlloc_3690_, 4, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
else
{
lean_object* v___x_3692_; 
v___x_3692_ = lean_box(1);
return v___x_3692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(lean_object* v_map_3693_){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_map_3693_);
v___x_3695_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(lean_object* v_k_3696_, lean_object* v_x_3697_){
_start:
{
if (lean_obj_tag(v_x_3697_) == 0)
{
lean_object* v___x_3698_; 
lean_dec_ref(v_k_3696_);
v___x_3698_ = lean_box(0);
return v___x_3698_;
}
else
{
lean_object* v_val_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v_val_3699_ = lean_ctor_get(v_x_3697_, 0);
lean_inc(v_val_3699_);
lean_dec_ref_known(v_x_3697_, 1);
v___x_3700_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(v_val_3699_);
v___x_3701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3701_, 0, v_k_3696_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = lean_box(0);
v___x_3703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3701_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
return v___x_3703_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instToJsonConfig_toJson(lean_object* v_x_3706_){
_start:
{
lean_object* v_challenge__module_3707_; lean_object* v_solution__module_3708_; lean_object* v_theorem__names_3709_; lean_object* v_definition__names_3710_; lean_object* v_permitted__axioms_3711_; lean_object* v_enable__nanoda_x3f_3712_; lean_object* v_external__kernels_x3f_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v_challenge__module_3707_ = lean_ctor_get(v_x_3706_, 0);
lean_inc_ref(v_challenge__module_3707_);
v_solution__module_3708_ = lean_ctor_get(v_x_3706_, 1);
lean_inc_ref(v_solution__module_3708_);
v_theorem__names_3709_ = lean_ctor_get(v_x_3706_, 2);
lean_inc_ref(v_theorem__names_3709_);
v_definition__names_3710_ = lean_ctor_get(v_x_3706_, 3);
lean_inc(v_definition__names_3710_);
v_permitted__axioms_3711_ = lean_ctor_get(v_x_3706_, 4);
lean_inc_ref(v_permitted__axioms_3711_);
v_enable__nanoda_x3f_3712_ = lean_ctor_get(v_x_3706_, 5);
lean_inc(v_enable__nanoda_x3f_3712_);
v_external__kernels_x3f_3713_ = lean_ctor_get(v_x_3706_, 6);
lean_inc(v_external__kernels_x3f_3713_);
lean_dec_ref(v_x_3706_);
v___x_3714_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
v___x_3715_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3715_, 0, v_challenge__module_3707_);
v___x_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3714_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = lean_box(0);
v___x_3718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3716_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
v___x_3720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3720_, 0, v_solution__module_3708_);
v___x_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3719_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
lean_ctor_set(v___x_3722_, 1, v___x_3717_);
v___x_3723_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
v___x_3724_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_theorem__names_3709_);
v___x_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3723_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
lean_ctor_set(v___x_3726_, 1, v___x_3717_);
v___x_3727_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
v___x_3728_ = l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(v_definition__names_3710_);
v___x_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
lean_ctor_set(v___x_3730_, 1, v___x_3717_);
v___x_3731_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
v___x_3732_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_permitted__axioms_3711_);
v___x_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
lean_ctor_set(v___x_3734_, 1, v___x_3717_);
v___x_3735_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
v___x_3736_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v___x_3735_, v_enable__nanoda_x3f_3712_);
lean_dec(v_enable__nanoda_x3f_3712_);
v___x_3737_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_3738_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(v___x_3737_, v_external__kernels_x3f_3713_);
v___x_3739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
lean_ctor_set(v___x_3739_, 1, v___x_3717_);
v___x_3740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3736_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3734_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3730_);
lean_ctor_set(v___x_3742_, 1, v___x_3741_);
v___x_3743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3726_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
v___x_3744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3722_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3718_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = ((lean_object*)(l_Lake_Check_instToJsonConfig_toJson___closed__0));
v___x_3747_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(v___x_3745_, v___x_3746_);
v___x_3748_ = l_Lean_Json_mkObj(v___x_3747_);
lean_dec(v___x_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(lean_object* v_x_3757_, lean_object* v_x_3758_){
_start:
{
if (lean_obj_tag(v_x_3757_) == 0)
{
lean_object* v___x_3759_; 
v___x_3759_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3759_;
}
else
{
lean_object* v_val_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v_val_3760_ = lean_ctor_get(v_x_3757_, 0);
v___x_3761_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3762_ = lean_unbox(v_val_3760_);
v___x_3763_ = l_Bool_repr___redArg(v___x_3762_);
v___x_3764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3761_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = l_Repr_addAppParen(v___x_3764_, v_x_3758_);
return v___x_3765_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___boxed(lean_object* v_x_3766_, lean_object* v_x_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_x_3766_, v_x_3767_);
lean_dec(v_x_3767_);
lean_dec(v_x_3766_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_Check_instReprConfig_repr_spec__4(lean_object* v_a_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = lean_nat_to_int(v_a_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(lean_object* v_x_3771_, lean_object* v_x_3772_, lean_object* v_x_3773_){
_start:
{
if (lean_obj_tag(v_x_3773_) == 0)
{
lean_dec(v_x_3771_);
return v_x_3772_;
}
else
{
lean_object* v_head_3774_; lean_object* v_tail_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3786_; 
v_head_3774_ = lean_ctor_get(v_x_3773_, 0);
v_tail_3775_ = lean_ctor_get(v_x_3773_, 1);
v_isSharedCheck_3786_ = !lean_is_exclusive(v_x_3773_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3777_ = v_x_3773_;
v_isShared_3778_ = v_isSharedCheck_3786_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_tail_3775_);
lean_inc(v_head_3774_);
lean_dec(v_x_3773_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3786_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
lean_inc(v_x_3771_);
if (v_isShared_3778_ == 0)
{
lean_ctor_set_tag(v___x_3777_, 5);
lean_ctor_set(v___x_3777_, 1, v_x_3771_);
lean_ctor_set(v___x_3777_, 0, v_x_3772_);
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_x_3772_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v_x_3771_);
v___x_3780_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3781_ = l_String_quote(v_head_3774_);
v___x_3782_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3781_);
v___x_3783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3780_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
v_x_3772_ = v___x_3783_;
v_x_3773_ = v_tail_3775_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_3787_, lean_object* v_x_3788_, lean_object* v_x_3789_){
_start:
{
if (lean_obj_tag(v_x_3789_) == 0)
{
lean_dec(v_x_3787_);
return v_x_3788_;
}
else
{
lean_object* v_head_3790_; lean_object* v_tail_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3802_; 
v_head_3790_ = lean_ctor_get(v_x_3789_, 0);
v_tail_3791_ = lean_ctor_get(v_x_3789_, 1);
v_isSharedCheck_3802_ = !lean_is_exclusive(v_x_3789_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3793_ = v_x_3789_;
v_isShared_3794_ = v_isSharedCheck_3802_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_tail_3791_);
lean_inc(v_head_3790_);
lean_dec(v_x_3789_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3802_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
lean_inc(v_x_3787_);
if (v_isShared_3794_ == 0)
{
lean_ctor_set_tag(v___x_3793_, 5);
lean_ctor_set(v___x_3793_, 1, v_x_3787_);
lean_ctor_set(v___x_3793_, 0, v_x_3788_);
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_x_3788_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v_x_3787_);
v___x_3796_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3797_ = l_String_quote(v_head_3790_);
v___x_3798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
v___x_3799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3796_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
v___x_3800_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(v_x_3787_, v___x_3799_, v_tail_3791_);
return v___x_3800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(lean_object* v___y_3803_){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = l_String_quote(v___y_3803_);
v___x_3805_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3804_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(lean_object* v_x_3806_, lean_object* v_x_3807_){
_start:
{
if (lean_obj_tag(v_x_3806_) == 0)
{
lean_object* v___x_3808_; 
lean_dec(v_x_3807_);
v___x_3808_ = lean_box(0);
return v___x_3808_;
}
else
{
lean_object* v_tail_3809_; 
v_tail_3809_ = lean_ctor_get(v_x_3806_, 1);
if (lean_obj_tag(v_tail_3809_) == 0)
{
lean_object* v_head_3810_; lean_object* v___x_3811_; 
lean_dec(v_x_3807_);
v_head_3810_ = lean_ctor_get(v_x_3806_, 0);
lean_inc(v_head_3810_);
lean_dec_ref_known(v_x_3806_, 2);
v___x_3811_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3810_);
return v___x_3811_;
}
else
{
lean_object* v_head_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
lean_inc(v_tail_3809_);
v_head_3812_ = lean_ctor_get(v_x_3806_, 0);
lean_inc(v_head_3812_);
lean_dec_ref_known(v_x_3806_, 2);
v___x_3813_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3812_);
v___x_3814_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(v_x_3807_, v___x_3813_, v_tail_3809_);
return v___x_3814_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3822_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__0));
v___x_3823_ = lean_string_length(v___x_3822_);
return v___x_3823_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3824_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4);
v___x_3825_ = lean_nat_to_int(v___x_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(lean_object* v_xs_3833_){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v___x_3834_ = lean_array_get_size(v_xs_3833_);
v___x_3835_ = lean_unsigned_to_nat(0u);
v___x_3836_ = lean_nat_dec_eq(v___x_3834_, v___x_3835_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3837_ = lean_array_to_list(v_xs_3833_);
v___x_3838_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3839_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(v___x_3837_, v___x_3838_);
v___x_3840_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5);
v___x_3841_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__6));
v___x_3842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3841_);
lean_ctor_set(v___x_3842_, 1, v___x_3839_);
v___x_3843_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_3844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3842_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
v___x_3845_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3840_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = l_Std_Format_fill(v___x_3845_);
return v___x_3846_;
}
else
{
lean_object* v___x_3847_; 
lean_dec_ref(v_xs_3833_);
v___x_3847_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__9));
return v___x_3847_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(lean_object* v_x_3848_, lean_object* v_x_3849_){
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
lean_object* v_val_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v_val_3851_ = lean_ctor_get(v_x_3848_, 0);
lean_inc(v_val_3851_);
lean_dec_ref_known(v_x_3848_, 1);
v___x_3852_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3853_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_val_3851_);
v___x_3854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3852_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
v___x_3855_ = l_Repr_addAppParen(v___x_3854_, v_x_3849_);
return v___x_3855_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1___boxed(lean_object* v_x_3856_, lean_object* v_x_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_x_3856_, v_x_3857_);
lean_dec(v_x_3857_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(lean_object* v_init_3859_, lean_object* v_x_3860_){
_start:
{
if (lean_obj_tag(v_x_3860_) == 0)
{
lean_object* v_k_3861_; lean_object* v_v_3862_; lean_object* v_l_3863_; lean_object* v_r_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v_k_3861_ = lean_ctor_get(v_x_3860_, 1);
v_v_3862_ = lean_ctor_get(v_x_3860_, 2);
v_l_3863_ = lean_ctor_get(v_x_3860_, 3);
v_r_3864_ = lean_ctor_get(v_x_3860_, 4);
v___x_3865_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_3859_, v_r_3864_);
lean_inc(v_v_3862_);
lean_inc(v_k_3861_);
v___x_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3866_, 0, v_k_3861_);
lean_ctor_set(v___x_3866_, 1, v_v_3862_);
v___x_3867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
lean_ctor_set(v___x_3867_, 1, v___x_3865_);
v_init_3859_ = v___x_3867_;
v_x_3860_ = v_l_3863_;
goto _start;
}
else
{
return v_init_3859_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4___boxed(lean_object* v_init_3869_, lean_object* v_x_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_3869_, v_x_3870_);
lean_dec(v_x_3870_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(lean_object* v_x_3872_, lean_object* v_x_3873_, lean_object* v_x_3874_){
_start:
{
if (lean_obj_tag(v_x_3874_) == 0)
{
lean_dec(v_x_3872_);
return v_x_3873_;
}
else
{
lean_object* v_head_3875_; lean_object* v_tail_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3885_; 
v_head_3875_ = lean_ctor_get(v_x_3874_, 0);
v_tail_3876_ = lean_ctor_get(v_x_3874_, 1);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_x_3874_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3878_ = v_x_3874_;
v_isShared_3879_ = v_isSharedCheck_3885_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_tail_3876_);
lean_inc(v_head_3875_);
lean_dec(v_x_3874_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3885_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
lean_inc(v_x_3872_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set_tag(v___x_3878_, 5);
lean_ctor_set(v___x_3878_, 1, v_x_3872_);
lean_ctor_set(v___x_3878_, 0, v_x_3873_);
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_x_3873_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v_x_3872_);
v___x_3881_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
lean_object* v___x_3882_; 
v___x_3882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
lean_ctor_set(v___x_3882_, 1, v_head_3875_);
v_x_3873_ = v___x_3882_;
v_x_3874_ = v_tail_3876_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(lean_object* v_x_3886_, lean_object* v_x_3887_){
_start:
{
if (lean_obj_tag(v_x_3886_) == 0)
{
lean_object* v___x_3888_; 
lean_dec(v_x_3887_);
v___x_3888_ = lean_box(0);
return v___x_3888_;
}
else
{
lean_object* v_tail_3889_; 
v_tail_3889_ = lean_ctor_get(v_x_3886_, 1);
if (lean_obj_tag(v_tail_3889_) == 0)
{
lean_object* v_head_3890_; 
lean_dec(v_x_3887_);
v_head_3890_ = lean_ctor_get(v_x_3886_, 0);
lean_inc(v_head_3890_);
lean_dec_ref_known(v_x_3886_, 2);
return v_head_3890_;
}
else
{
lean_object* v_head_3891_; lean_object* v___x_3892_; 
lean_inc(v_tail_3889_);
v_head_3891_ = lean_ctor_get(v_x_3886_, 0);
lean_inc(v_head_3891_);
lean_dec_ref_known(v_x_3886_, 2);
v___x_3892_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(v_x_3887_, v_head_3891_, v_tail_3889_);
return v___x_3892_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3895_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__0));
v___x_3896_ = lean_string_length(v___x_3895_);
return v___x_3896_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2);
v___x_3898_ = lean_nat_to_int(v___x_3897_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(lean_object* v_x_3903_){
_start:
{
lean_object* v_fst_3904_; lean_object* v_snd_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3928_; 
v_fst_3904_ = lean_ctor_get(v_x_3903_, 0);
v_snd_3905_ = lean_ctor_get(v_x_3903_, 1);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_x_3903_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3907_ = v_x_3903_;
v_isShared_3908_ = v_isSharedCheck_3928_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_snd_3905_);
lean_inc(v_fst_3904_);
lean_dec(v_x_3903_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3928_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3909_ = l_String_quote(v_fst_3904_);
v___x_3910_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
v___x_3911_ = lean_box(0);
if (v_isShared_3908_ == 0)
{
lean_ctor_set_tag(v___x_3907_, 1);
lean_ctor_set(v___x_3907_, 1, v___x_3911_);
lean_ctor_set(v___x_3907_, 0, v___x_3910_);
v___x_3913_ = v___x_3907_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; uint8_t v___x_3925_; lean_object* v___x_3926_; 
v___x_3914_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_snd_3905_);
v___x_3915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
lean_ctor_set(v___x_3915_, 1, v___x_3913_);
v___x_3916_ = l_List_reverse___redArg(v___x_3915_);
v___x_3917_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3918_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(v___x_3916_, v___x_3917_);
v___x_3919_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3);
v___x_3920_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__4));
v___x_3921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
lean_ctor_set(v___x_3921_, 1, v___x_3918_);
v___x_3922_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__5));
v___x_3923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3919_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = 0;
v___x_3926_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3926_, 0, v___x_3924_);
lean_ctor_set_uint8(v___x_3926_, sizeof(void*)*1, v___x_3925_);
return v___x_3926_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(lean_object* v_x_3929_, lean_object* v_x_3930_, lean_object* v_x_3931_){
_start:
{
if (lean_obj_tag(v_x_3931_) == 0)
{
lean_dec(v_x_3929_);
return v_x_3930_;
}
else
{
lean_object* v_head_3932_; lean_object* v_tail_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3943_; 
v_head_3932_ = lean_ctor_get(v_x_3931_, 0);
v_tail_3933_ = lean_ctor_get(v_x_3931_, 1);
v_isSharedCheck_3943_ = !lean_is_exclusive(v_x_3931_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3935_ = v_x_3931_;
v_isShared_3936_ = v_isSharedCheck_3943_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_tail_3933_);
lean_inc(v_head_3932_);
lean_dec(v_x_3931_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3943_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
lean_inc(v_x_3929_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set_tag(v___x_3935_, 5);
lean_ctor_set(v___x_3935_, 1, v_x_3929_);
lean_ctor_set(v___x_3935_, 0, v_x_3930_);
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_x_3930_);
lean_ctor_set(v_reuseFailAlloc_3942_, 1, v_x_3929_);
v___x_3938_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3939_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3932_);
v___x_3940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3938_);
lean_ctor_set(v___x_3940_, 1, v___x_3939_);
v_x_3930_ = v___x_3940_;
v_x_3931_ = v_tail_3933_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(lean_object* v_x_3944_, lean_object* v_x_3945_, lean_object* v_x_3946_){
_start:
{
if (lean_obj_tag(v_x_3946_) == 0)
{
lean_dec(v_x_3944_);
return v_x_3945_;
}
else
{
lean_object* v_head_3947_; lean_object* v_tail_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3958_; 
v_head_3947_ = lean_ctor_get(v_x_3946_, 0);
v_tail_3948_ = lean_ctor_get(v_x_3946_, 1);
v_isSharedCheck_3958_ = !lean_is_exclusive(v_x_3946_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3950_ = v_x_3946_;
v_isShared_3951_ = v_isSharedCheck_3958_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_tail_3948_);
lean_inc(v_head_3947_);
lean_dec(v_x_3946_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3958_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
lean_inc(v_x_3944_);
if (v_isShared_3951_ == 0)
{
lean_ctor_set_tag(v___x_3950_, 5);
lean_ctor_set(v___x_3950_, 1, v_x_3944_);
lean_ctor_set(v___x_3950_, 0, v_x_3945_);
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_x_3945_);
lean_ctor_set(v_reuseFailAlloc_3957_, 1, v_x_3944_);
v___x_3953_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3954_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3947_);
v___x_3955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3953_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
v___x_3956_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(v_x_3944_, v___x_3955_, v_tail_3948_);
return v___x_3956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(lean_object* v_x_3959_, lean_object* v_x_3960_){
_start:
{
if (lean_obj_tag(v_x_3959_) == 0)
{
lean_object* v___x_3961_; 
lean_dec(v_x_3960_);
v___x_3961_ = lean_box(0);
return v___x_3961_;
}
else
{
lean_object* v_tail_3962_; 
v_tail_3962_ = lean_ctor_get(v_x_3959_, 1);
if (lean_obj_tag(v_tail_3962_) == 0)
{
lean_object* v_head_3963_; lean_object* v___x_3964_; 
lean_dec(v_x_3960_);
v_head_3963_ = lean_ctor_get(v_x_3959_, 0);
lean_inc(v_head_3963_);
lean_dec_ref_known(v_x_3959_, 2);
v___x_3964_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3963_);
return v___x_3964_;
}
else
{
lean_object* v_head_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
lean_inc(v_tail_3962_);
v_head_3965_ = lean_ctor_get(v_x_3959_, 0);
lean_inc(v_head_3965_);
lean_dec_ref_known(v_x_3959_, 2);
v___x_3966_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_3965_);
v___x_3967_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(v_x_3960_, v___x_3966_, v_tail_3962_);
return v___x_3967_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_3971_ = lean_string_length(v___x_3970_);
return v___x_3971_;
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1);
v___x_3973_ = lean_nat_to_int(v___x_3972_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(lean_object* v_a_3976_){
_start:
{
if (lean_obj_tag(v_a_3976_) == 0)
{
lean_object* v___x_3977_; 
v___x_3977_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0));
return v___x_3977_;
}
else
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; uint8_t v___x_3986_; lean_object* v___x_3987_; 
v___x_3978_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_3979_ = l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(v_a_3976_, v___x_3978_);
v___x_3980_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2);
v___x_3981_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__3));
v___x_3982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3981_);
lean_ctor_set(v___x_3982_, 1, v___x_3979_);
v___x_3983_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_3984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3982_);
lean_ctor_set(v___x_3984_, 1, v___x_3983_);
v___x_3985_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3980_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = 0;
v___x_3987_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3987_, 0, v___x_3985_);
lean_ctor_set_uint8(v___x_3987_, sizeof(void*)*1, v___x_3986_);
return v___x_3987_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(lean_object* v_x_3991_, lean_object* v_x_3992_){
_start:
{
if (lean_obj_tag(v_x_3991_) == 0)
{
lean_object* v___x_3993_; 
v___x_3993_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3993_;
}
else
{
lean_object* v_val_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v_val_3994_ = lean_ctor_get(v_x_3991_, 0);
v___x_3995_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3996_ = lean_unsigned_to_nat(1024u);
v___x_3997_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__1));
v___x_3998_ = lean_box(0);
v___x_3999_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v___x_3998_, v_val_3994_);
v___x_4000_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v___x_3999_);
v___x_4001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3997_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = l_Repr_addAppParen(v___x_4001_, v___x_3996_);
v___x_4003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_3995_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v___x_4004_ = l_Repr_addAppParen(v___x_4003_, v_x_3992_);
return v___x_4004_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___boxed(lean_object* v_x_4005_, lean_object* v_x_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_x_4005_, v_x_4006_);
lean_dec(v_x_4006_);
lean_dec(v_x_4005_);
return v_res_4007_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4020_ = lean_unsigned_to_nat(20u);
v___x_4021_ = lean_nat_to_int(v___x_4020_);
return v___x_4021_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = lean_unsigned_to_nat(19u);
v___x_4025_ = lean_nat_to_int(v___x_4024_);
return v___x_4025_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4028_ = lean_unsigned_to_nat(17u);
v___x_4029_ = lean_nat_to_int(v___x_4028_);
return v___x_4029_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = lean_unsigned_to_nat(18u);
v___x_4037_ = lean_nat_to_int(v___x_4036_);
return v___x_4037_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4040_ = lean_unsigned_to_nat(21u);
v___x_4041_ = lean_nat_to_int(v___x_4040_);
return v___x_4041_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4043_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__0));
v___x_4044_ = lean_string_length(v___x_4043_);
return v___x_4044_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4045_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__18, &l_Lake_Check_instReprConfig_repr___redArg___closed__18_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18);
v___x_4046_ = lean_nat_to_int(v___x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___redArg(lean_object* v_x_4051_){
_start:
{
lean_object* v_challenge__module_4052_; lean_object* v_solution__module_4053_; lean_object* v_theorem__names_4054_; lean_object* v_definition__names_4055_; lean_object* v_permitted__axioms_4056_; lean_object* v_enable__nanoda_x3f_4057_; lean_object* v_external__kernels_x3f_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
v_challenge__module_4052_ = lean_ctor_get(v_x_4051_, 0);
lean_inc_ref(v_challenge__module_4052_);
v_solution__module_4053_ = lean_ctor_get(v_x_4051_, 1);
lean_inc_ref(v_solution__module_4053_);
v_theorem__names_4054_ = lean_ctor_get(v_x_4051_, 2);
lean_inc_ref(v_theorem__names_4054_);
v_definition__names_4055_ = lean_ctor_get(v_x_4051_, 3);
lean_inc(v_definition__names_4055_);
v_permitted__axioms_4056_ = lean_ctor_get(v_x_4051_, 4);
lean_inc_ref(v_permitted__axioms_4056_);
v_enable__nanoda_x3f_4057_ = lean_ctor_get(v_x_4051_, 5);
lean_inc(v_enable__nanoda_x3f_4057_);
v_external__kernels_x3f_4058_ = lean_ctor_get(v_x_4051_, 6);
lean_inc(v_external__kernels_x3f_4058_);
lean_dec_ref(v_x_4051_);
v___x_4059_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__4));
v___x_4060_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__5));
v___x_4061_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__6, &l_Lake_Check_instReprConfig_repr___redArg___closed__6_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6);
v___x_4062_ = l_String_quote(v_challenge__module_4052_);
v___x_4063_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
v___x_4064_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4061_);
lean_ctor_set(v___x_4064_, 1, v___x_4063_);
v___x_4065_ = 0;
v___x_4066_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4066_, 0, v___x_4064_);
lean_ctor_set_uint8(v___x_4066_, sizeof(void*)*1, v___x_4065_);
v___x_4067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4060_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__2));
v___x_4069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4067_);
lean_ctor_set(v___x_4069_, 1, v___x_4068_);
v___x_4070_ = lean_box(1);
v___x_4071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4069_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
v___x_4072_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__7));
v___x_4073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4071_);
lean_ctor_set(v___x_4073_, 1, v___x_4072_);
v___x_4074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
lean_ctor_set(v___x_4074_, 1, v___x_4059_);
v___x_4075_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__8, &l_Lake_Check_instReprConfig_repr___redArg___closed__8_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8);
v___x_4076_ = l_String_quote(v_solution__module_4053_);
v___x_4077_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
v___x_4078_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4075_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
v___x_4079_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
lean_ctor_set_uint8(v___x_4079_, sizeof(void*)*1, v___x_4065_);
v___x_4080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4074_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
lean_ctor_set(v___x_4081_, 1, v___x_4068_);
v___x_4082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
lean_ctor_set(v___x_4082_, 1, v___x_4070_);
v___x_4083_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__9));
v___x_4084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4082_);
lean_ctor_set(v___x_4084_, 1, v___x_4083_);
v___x_4085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
lean_ctor_set(v___x_4085_, 1, v___x_4059_);
v___x_4086_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__10, &l_Lake_Check_instReprConfig_repr___redArg___closed__10_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10);
v___x_4087_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_theorem__names_4054_);
v___x_4088_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4086_);
lean_ctor_set(v___x_4088_, 1, v___x_4087_);
v___x_4089_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
lean_ctor_set_uint8(v___x_4089_, sizeof(void*)*1, v___x_4065_);
v___x_4090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4085_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4090_);
lean_ctor_set(v___x_4091_, 1, v___x_4068_);
v___x_4092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
lean_ctor_set(v___x_4092_, 1, v___x_4070_);
v___x_4093_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__11));
v___x_4094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4092_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
lean_ctor_set(v___x_4095_, 1, v___x_4059_);
v___x_4096_ = lean_unsigned_to_nat(0u);
v___x_4097_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_definition__names_4055_, v___x_4096_);
v___x_4098_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4061_);
lean_ctor_set(v___x_4098_, 1, v___x_4097_);
v___x_4099_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4099_, 0, v___x_4098_);
lean_ctor_set_uint8(v___x_4099_, sizeof(void*)*1, v___x_4065_);
v___x_4100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4095_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
v___x_4101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4100_);
lean_ctor_set(v___x_4101_, 1, v___x_4068_);
v___x_4102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
lean_ctor_set(v___x_4102_, 1, v___x_4070_);
v___x_4103_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__12));
v___x_4104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4102_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4104_);
lean_ctor_set(v___x_4105_, 1, v___x_4059_);
v___x_4106_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_permitted__axioms_4056_);
v___x_4107_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4061_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
lean_ctor_set_uint8(v___x_4108_, sizeof(void*)*1, v___x_4065_);
v___x_4109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4105_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
v___x_4110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
lean_ctor_set(v___x_4110_, 1, v___x_4068_);
v___x_4111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4110_);
lean_ctor_set(v___x_4111_, 1, v___x_4070_);
v___x_4112_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__13));
v___x_4113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4111_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
v___x_4114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
lean_ctor_set(v___x_4114_, 1, v___x_4059_);
v___x_4115_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__14, &l_Lake_Check_instReprConfig_repr___redArg___closed__14_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14);
v___x_4116_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_enable__nanoda_x3f_4057_, v___x_4096_);
lean_dec(v_enable__nanoda_x3f_4057_);
v___x_4117_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4115_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
v___x_4118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
lean_ctor_set_uint8(v___x_4118_, sizeof(void*)*1, v___x_4065_);
v___x_4119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4114_);
lean_ctor_set(v___x_4119_, 1, v___x_4118_);
v___x_4120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4119_);
lean_ctor_set(v___x_4120_, 1, v___x_4068_);
v___x_4121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
lean_ctor_set(v___x_4121_, 1, v___x_4070_);
v___x_4122_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__15));
v___x_4123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4121_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
lean_ctor_set(v___x_4124_, 1, v___x_4059_);
v___x_4125_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__16, &l_Lake_Check_instReprConfig_repr___redArg___closed__16_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16);
v___x_4126_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_external__kernels_x3f_4058_, v___x_4096_);
lean_dec(v_external__kernels_x3f_4058_);
v___x_4127_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4125_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4128_, 0, v___x_4127_);
lean_ctor_set_uint8(v___x_4128_, sizeof(void*)*1, v___x_4065_);
v___x_4129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4124_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
v___x_4130_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__19, &l_Lake_Check_instReprConfig_repr___redArg___closed__19_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19);
v___x_4131_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__20));
v___x_4132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
lean_ctor_set(v___x_4132_, 1, v___x_4129_);
v___x_4133_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__21));
v___x_4134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4132_);
lean_ctor_set(v___x_4134_, 1, v___x_4133_);
v___x_4135_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4130_);
lean_ctor_set(v___x_4135_, 1, v___x_4134_);
v___x_4136_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
lean_ctor_set_uint8(v___x_4136_, sizeof(void*)*1, v___x_4065_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr(lean_object* v_x_4137_, lean_object* v_prec_4138_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l_Lake_Check_instReprConfig_repr___redArg(v_x_4137_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___boxed(lean_object* v_x_4140_, lean_object* v_prec_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Lake_Check_instReprConfig_repr(v_x_4140_, v_prec_4141_);
lean_dec(v_prec_4141_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(lean_object* v_a_4143_, lean_object* v_n_4144_){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v_a_4143_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___boxed(lean_object* v_a_4146_, lean_object* v_n_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(v_a_4146_, v_n_4147_);
lean_dec(v_n_4147_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(lean_object* v_x_4149_, lean_object* v_x_4150_){
_start:
{
lean_object* v___x_4151_; 
v___x_4151_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_x_4149_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___boxed(lean_object* v_x_4152_, lean_object* v_x_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(v_x_4152_, v_x_4153_);
lean_dec(v_x_4153_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(lean_object* v_s_4157_){
_start:
{
uint32_t v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4159_ = 10;
v___x_4160_ = lean_string_push(v_s_4157_, v___x_4159_);
v___x_4161_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v___x_4160_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0___boxed(lean_object* v_s_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v_s_4162_);
return v_res_4164_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1(void){
_start:
{
uint32_t v___x_4166_; lean_object* v___x_4167_; 
v___x_4166_ = 2;
v___x_4167_ = lean_box_uint32(v___x_4166_);
return v___x_4167_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(lean_object* v_msg_4168_){
_start:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4170_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_4171_ = lean_string_append(v___x_4170_, v_msg_4168_);
v___x_4172_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_4171_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4180_; 
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4180_ == 0)
{
lean_object* v_unused_4181_; 
v_unused_4181_ = lean_ctor_get(v___x_4172_, 0);
lean_dec(v_unused_4181_);
v___x_4174_ = v___x_4172_;
v_isShared_4175_ = v_isSharedCheck_4180_;
goto v_resetjp_4173_;
}
else
{
lean_dec(v___x_4172_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4180_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4176_; lean_object* v___x_4178_; 
v___x_4176_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1;
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 0, v___x_4176_);
v___x_4178_ = v___x_4174_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v___x_4176_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
else
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
v_a_4182_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___x_4172_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4172_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed(lean_object* v_msg_4190_, lean_object* v_a_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v_msg_4190_);
lean_dec_ref(v_msg_4190_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(lean_object* v_cmd_4196_, lean_object* v_projectDir_4197_){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; uint8_t v___x_4201_; 
v___x_4199_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__0));
lean_inc_ref(v_projectDir_4197_);
v___x_4200_ = l_System_FilePath_join(v_projectDir_4197_, v___x_4199_);
v___x_4201_ = l_System_FilePath_pathExists(v___x_4200_);
lean_dec_ref(v___x_4200_);
if (v___x_4201_ == 0)
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4202_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_4203_ = lean_string_append(v___x_4202_, v_projectDir_4197_);
lean_dec_ref(v_projectDir_4197_);
v___x_4204_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__1));
v___x_4205_ = lean_string_append(v___x_4203_, v___x_4204_);
v___x_4206_ = lean_string_append(v___x_4205_, v_cmd_4196_);
v___x_4207_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__2));
v___x_4208_ = lean_string_append(v___x_4206_, v___x_4207_);
v___x_4209_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4208_);
lean_dec_ref(v___x_4208_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4218_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4212_ = v___x_4209_;
v_isShared_4213_ = v_isSharedCheck_4218_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4209_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4218_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4214_; lean_object* v___x_4216_; 
v___x_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4214_, 0, v_a_4210_);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 0, v___x_4214_);
v___x_4216_ = v___x_4212_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4214_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
v_a_4219_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4209_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4209_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
else
{
lean_object* v___x_4227_; lean_object* v___x_4228_; 
lean_dec_ref(v_projectDir_4197_);
v___x_4227_ = lean_box(0);
v___x_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4227_);
return v___x_4228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___boxed(lean_object* v_cmd_4229_, lean_object* v_projectDir_4230_, lean_object* v_a_4231_){
_start:
{
lean_object* v_res_4232_; 
v_res_4232_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v_cmd_4229_, v_projectDir_4230_);
lean_dec_ref(v_cmd_4229_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(lean_object* v_lean_4233_, lean_object* v_name_4234_){
_start:
{
lean_object* v_binDir_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v_binDir_4235_ = lean_ctor_get(v_lean_4233_, 6);
lean_inc_ref(v_binDir_4235_);
lean_dec_ref(v_lean_4233_);
v___x_4236_ = l_System_FilePath_join(v_binDir_4235_, v_name_4234_);
v___x_4237_ = l_System_FilePath_exeExtension;
v___x_4238_ = l_System_FilePath_addExtension(v___x_4236_, v___x_4237_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels(lean_object* v_lean_4247_){
_start:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4248_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__0));
v___x_4249_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__1));
lean_inc_ref_n(v_lean_4247_, 4);
v___x_4250_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4247_, v___x_4249_);
v___x_4251_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0));
v___x_4252_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_4253_ = lean_unsigned_to_nat(3u);
v___x_4254_ = lean_mk_empty_array_with_capacity(v___x_4253_);
v___x_4255_ = lean_array_push(v___x_4254_, v___x_4250_);
v___x_4256_ = lean_array_push(v___x_4255_, v___x_4251_);
v___x_4257_ = lean_array_push(v___x_4256_, v___x_4252_);
v___x_4258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4248_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
v___x_4259_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__2));
v___x_4260_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4247_, v___x_4259_);
v___x_4261_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__3));
v___x_4262_ = lean_unsigned_to_nat(2u);
v___x_4263_ = lean_mk_empty_array_with_capacity(v___x_4262_);
v___x_4264_ = lean_array_push(v___x_4263_, v___x_4260_);
v___x_4265_ = lean_array_push(v___x_4264_, v___x_4261_);
v___x_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4259_);
lean_ctor_set(v___x_4266_, 1, v___x_4265_);
v___x_4267_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__4));
v___x_4268_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__5));
v___x_4269_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4247_, v___x_4268_);
v___x_4270_ = lean_unsigned_to_nat(1u);
v___x_4271_ = lean_mk_empty_array_with_capacity(v___x_4270_);
lean_inc_ref_n(v___x_4271_, 2);
v___x_4272_ = lean_array_push(v___x_4271_, v___x_4269_);
v___x_4273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4267_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__6));
v___x_4275_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4247_, v___x_4274_);
v___x_4276_ = lean_array_push(v___x_4271_, v___x_4275_);
v___x_4277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4274_);
lean_ctor_set(v___x_4277_, 1, v___x_4276_);
v___x_4278_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__7));
v___x_4279_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4247_, v___x_4278_);
v___x_4280_ = lean_array_push(v___x_4271_, v___x_4279_);
v___x_4281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4278_);
lean_ctor_set(v___x_4281_, 1, v___x_4280_);
v___x_4282_ = lean_unsigned_to_nat(5u);
v___x_4283_ = lean_mk_empty_array_with_capacity(v___x_4282_);
v___x_4284_ = lean_array_push(v___x_4283_, v___x_4258_);
v___x_4285_ = lean_array_push(v___x_4284_, v___x_4266_);
v___x_4286_ = lean_array_push(v___x_4285_, v___x_4273_);
v___x_4287_ = lean_array_push(v___x_4286_, v___x_4277_);
v___x_4288_ = lean_array_push(v___x_4287_, v___x_4281_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(uint8_t v_a_4289_, lean_object* v_b_4290_, lean_object* v_x_4291_){
_start:
{
if (lean_obj_tag(v_x_4291_) == 0)
{
lean_dec(v_b_4290_);
return v_x_4291_;
}
else
{
lean_object* v_key_4292_; lean_object* v_value_4293_; lean_object* v_tail_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4310_; 
v_key_4292_ = lean_ctor_get(v_x_4291_, 0);
v_value_4293_ = lean_ctor_get(v_x_4291_, 1);
v_tail_4294_ = lean_ctor_get(v_x_4291_, 2);
v_isSharedCheck_4310_ = !lean_is_exclusive(v_x_4291_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4296_ = v_x_4291_;
v_isShared_4297_ = v_isSharedCheck_4310_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_tail_4294_);
lean_inc(v_value_4293_);
lean_inc(v_key_4292_);
lean_dec(v_x_4291_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4310_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; uint8_t v___x_4301_; 
v___x_4298_ = lean_obj_tag_nat(v_key_4292_);
v___x_4299_ = lean_box(v_a_4289_);
v___x_4300_ = lean_obj_tag_nat(v___x_4299_);
lean_dec(v___x_4299_);
v___x_4301_ = lean_nat_dec_eq(v___x_4298_, v___x_4300_);
if (v___x_4301_ == 0)
{
lean_object* v___x_4302_; lean_object* v___x_4304_; 
v___x_4302_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_4289_, v_b_4290_, v_tail_4294_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 2, v___x_4302_);
v___x_4304_ = v___x_4296_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_key_4292_);
lean_ctor_set(v_reuseFailAlloc_4305_, 1, v_value_4293_);
lean_ctor_set(v_reuseFailAlloc_4305_, 2, v___x_4302_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
else
{
lean_object* v___x_4306_; lean_object* v___x_4308_; 
lean_dec(v_value_4293_);
lean_dec(v_key_4292_);
v___x_4306_ = lean_box(v_a_4289_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 1, v_b_4290_);
lean_ctor_set(v___x_4296_, 0, v___x_4306_);
v___x_4308_ = v___x_4296_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4306_);
lean_ctor_set(v_reuseFailAlloc_4309_, 1, v_b_4290_);
lean_ctor_set(v_reuseFailAlloc_4309_, 2, v_tail_4294_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg___boxed(lean_object* v_a_4311_, lean_object* v_b_4312_, lean_object* v_x_4313_){
_start:
{
uint8_t v_a_boxed_4314_; lean_object* v_res_4315_; 
v_a_boxed_4314_ = lean_unbox(v_a_4311_);
v_res_4315_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_boxed_4314_, v_b_4312_, v_x_4313_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_4316_, lean_object* v_x_4317_){
_start:
{
if (lean_obj_tag(v_x_4317_) == 0)
{
return v_x_4316_;
}
else
{
lean_object* v_key_4318_; lean_object* v_value_4319_; lean_object* v_tail_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4344_; 
v_key_4318_ = lean_ctor_get(v_x_4317_, 0);
v_value_4319_ = lean_ctor_get(v_x_4317_, 1);
v_tail_4320_ = lean_ctor_get(v_x_4317_, 2);
v_isSharedCheck_4344_ = !lean_is_exclusive(v_x_4317_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4322_ = v_x_4317_;
v_isShared_4323_ = v_isSharedCheck_4344_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_tail_4320_);
lean_inc(v_value_4319_);
lean_inc(v_key_4318_);
lean_dec(v_x_4317_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4344_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4324_; uint8_t v___x_4325_; uint64_t v___x_4326_; uint64_t v___x_4327_; uint64_t v___x_4328_; uint64_t v_fold_4329_; uint64_t v___x_4330_; uint64_t v___x_4331_; uint64_t v___x_4332_; size_t v___x_4333_; size_t v___x_4334_; size_t v___x_4335_; size_t v___x_4336_; size_t v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4340_; 
v___x_4324_ = lean_array_get_size(v_x_4316_);
v___x_4325_ = lean_unbox(v_key_4318_);
v___x_4326_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v___x_4325_);
v___x_4327_ = 32ULL;
v___x_4328_ = lean_uint64_shift_right(v___x_4326_, v___x_4327_);
v_fold_4329_ = lean_uint64_xor(v___x_4326_, v___x_4328_);
v___x_4330_ = 16ULL;
v___x_4331_ = lean_uint64_shift_right(v_fold_4329_, v___x_4330_);
v___x_4332_ = lean_uint64_xor(v_fold_4329_, v___x_4331_);
v___x_4333_ = lean_uint64_to_usize(v___x_4332_);
v___x_4334_ = lean_usize_of_nat(v___x_4324_);
v___x_4335_ = ((size_t)1ULL);
v___x_4336_ = lean_usize_sub(v___x_4334_, v___x_4335_);
v___x_4337_ = lean_usize_land(v___x_4333_, v___x_4336_);
v___x_4338_ = lean_array_uget_borrowed(v_x_4316_, v___x_4337_);
lean_inc(v___x_4338_);
if (v_isShared_4323_ == 0)
{
lean_ctor_set(v___x_4322_, 2, v___x_4338_);
v___x_4340_ = v___x_4322_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_key_4318_);
lean_ctor_set(v_reuseFailAlloc_4343_, 1, v_value_4319_);
lean_ctor_set(v_reuseFailAlloc_4343_, 2, v___x_4338_);
v___x_4340_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
lean_object* v___x_4341_; 
v___x_4341_ = lean_array_uset(v_x_4316_, v___x_4337_, v___x_4340_);
v_x_4316_ = v___x_4341_;
v_x_4317_ = v_tail_4320_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2___redArg(lean_object* v_i_4345_, lean_object* v_source_4346_, lean_object* v_target_4347_){
_start:
{
lean_object* v___x_4348_; uint8_t v___x_4349_; 
v___x_4348_ = lean_array_get_size(v_source_4346_);
v___x_4349_ = lean_nat_dec_lt(v_i_4345_, v___x_4348_);
if (v___x_4349_ == 0)
{
lean_dec_ref(v_source_4346_);
lean_dec(v_i_4345_);
return v_target_4347_;
}
else
{
lean_object* v_es_4350_; lean_object* v___x_4351_; lean_object* v_source_4352_; lean_object* v_target_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v_es_4350_ = lean_array_fget(v_source_4346_, v_i_4345_);
v___x_4351_ = lean_box(0);
v_source_4352_ = lean_array_fset(v_source_4346_, v_i_4345_, v___x_4351_);
v_target_4353_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4___redArg(v_target_4347_, v_es_4350_);
v___x_4354_ = lean_unsigned_to_nat(1u);
v___x_4355_ = lean_nat_add(v_i_4345_, v___x_4354_);
lean_dec(v_i_4345_);
v_i_4345_ = v___x_4355_;
v_source_4346_ = v_source_4352_;
v_target_4347_ = v_target_4353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1___redArg(lean_object* v_data_4357_){
_start:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v_nbuckets_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4358_ = lean_array_get_size(v_data_4357_);
v___x_4359_ = lean_unsigned_to_nat(2u);
v_nbuckets_4360_ = lean_nat_mul(v___x_4358_, v___x_4359_);
v___x_4361_ = lean_unsigned_to_nat(0u);
v___x_4362_ = lean_box(0);
v___x_4363_ = lean_mk_array(v_nbuckets_4360_, v___x_4362_);
v___x_4364_ = lean_array_propagate_mark(v_data_4357_, v___x_4363_);
v___x_4365_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2___redArg(v___x_4361_, v_data_4357_, v___x_4364_);
return v___x_4365_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(uint8_t v_a_4366_, lean_object* v_x_4367_){
_start:
{
if (lean_obj_tag(v_x_4367_) == 0)
{
uint8_t v___x_4368_; 
v___x_4368_ = 0;
return v___x_4368_;
}
else
{
lean_object* v_key_4369_; lean_object* v_tail_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; uint8_t v___x_4374_; 
v_key_4369_ = lean_ctor_get(v_x_4367_, 0);
v_tail_4370_ = lean_ctor_get(v_x_4367_, 2);
v___x_4371_ = lean_obj_tag_nat(v_key_4369_);
v___x_4372_ = lean_box(v_a_4366_);
v___x_4373_ = lean_obj_tag_nat(v___x_4372_);
lean_dec(v___x_4372_);
v___x_4374_ = lean_nat_dec_eq(v___x_4371_, v___x_4373_);
if (v___x_4374_ == 0)
{
v_x_4367_ = v_tail_4370_;
goto _start;
}
else
{
return v___x_4374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg___boxed(lean_object* v_a_4376_, lean_object* v_x_4377_){
_start:
{
uint8_t v_a_boxed_4378_; uint8_t v_res_4379_; lean_object* v_r_4380_; 
v_a_boxed_4378_ = lean_unbox(v_a_4376_);
v_res_4379_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_boxed_4378_, v_x_4377_);
lean_dec(v_x_4377_);
v_r_4380_ = lean_box(v_res_4379_);
return v_r_4380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(lean_object* v_m_4381_, uint8_t v_a_4382_, lean_object* v_b_4383_){
_start:
{
lean_object* v_size_4384_; lean_object* v_buckets_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4429_; 
v_size_4384_ = lean_ctor_get(v_m_4381_, 0);
v_buckets_4385_ = lean_ctor_get(v_m_4381_, 1);
v_isSharedCheck_4429_ = !lean_is_exclusive(v_m_4381_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4387_ = v_m_4381_;
v_isShared_4388_ = v_isSharedCheck_4429_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_buckets_4385_);
lean_inc(v_size_4384_);
lean_dec(v_m_4381_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4429_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4389_; uint64_t v___x_4390_; uint64_t v___x_4391_; uint64_t v___x_4392_; uint64_t v_fold_4393_; uint64_t v___x_4394_; uint64_t v___x_4395_; uint64_t v___x_4396_; size_t v___x_4397_; size_t v___x_4398_; size_t v___x_4399_; size_t v___x_4400_; size_t v___x_4401_; lean_object* v_bkt_4402_; uint8_t v___x_4403_; 
v___x_4389_ = lean_array_get_size(v_buckets_4385_);
v___x_4390_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_a_4382_);
v___x_4391_ = 32ULL;
v___x_4392_ = lean_uint64_shift_right(v___x_4390_, v___x_4391_);
v_fold_4393_ = lean_uint64_xor(v___x_4390_, v___x_4392_);
v___x_4394_ = 16ULL;
v___x_4395_ = lean_uint64_shift_right(v_fold_4393_, v___x_4394_);
v___x_4396_ = lean_uint64_xor(v_fold_4393_, v___x_4395_);
v___x_4397_ = lean_uint64_to_usize(v___x_4396_);
v___x_4398_ = lean_usize_of_nat(v___x_4389_);
v___x_4399_ = ((size_t)1ULL);
v___x_4400_ = lean_usize_sub(v___x_4398_, v___x_4399_);
v___x_4401_ = lean_usize_land(v___x_4397_, v___x_4400_);
v_bkt_4402_ = lean_array_uget_borrowed(v_buckets_4385_, v___x_4401_);
v___x_4403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_4382_, v_bkt_4402_);
if (v___x_4403_ == 0)
{
lean_object* v___x_4404_; lean_object* v_size_x27_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v_buckets_x27_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; uint8_t v___x_4414_; 
v___x_4404_ = lean_unsigned_to_nat(1u);
v_size_x27_4405_ = lean_nat_add(v_size_4384_, v___x_4404_);
lean_dec(v_size_4384_);
v___x_4406_ = lean_box(v_a_4382_);
lean_inc(v_bkt_4402_);
v___x_4407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4406_);
lean_ctor_set(v___x_4407_, 1, v_b_4383_);
lean_ctor_set(v___x_4407_, 2, v_bkt_4402_);
v_buckets_x27_4408_ = lean_array_uset(v_buckets_4385_, v___x_4401_, v___x_4407_);
v___x_4409_ = lean_unsigned_to_nat(4u);
v___x_4410_ = lean_nat_mul(v_size_x27_4405_, v___x_4409_);
v___x_4411_ = lean_unsigned_to_nat(3u);
v___x_4412_ = lean_nat_div(v___x_4410_, v___x_4411_);
lean_dec(v___x_4410_);
v___x_4413_ = lean_array_get_size(v_buckets_x27_4408_);
v___x_4414_ = lean_nat_dec_le(v___x_4412_, v___x_4413_);
lean_dec(v___x_4412_);
if (v___x_4414_ == 0)
{
lean_object* v_val_4415_; lean_object* v___x_4417_; 
v_val_4415_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1___redArg(v_buckets_x27_4408_);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 1, v_val_4415_);
lean_ctor_set(v___x_4387_, 0, v_size_x27_4405_);
v___x_4417_ = v___x_4387_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_size_x27_4405_);
lean_ctor_set(v_reuseFailAlloc_4418_, 1, v_val_4415_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
else
{
lean_object* v___x_4420_; 
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 1, v_buckets_x27_4408_);
lean_ctor_set(v___x_4387_, 0, v_size_x27_4405_);
v___x_4420_ = v___x_4387_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_size_x27_4405_);
lean_ctor_set(v_reuseFailAlloc_4421_, 1, v_buckets_x27_4408_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
else
{
lean_object* v___x_4422_; lean_object* v_buckets_x27_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4427_; 
lean_inc(v_bkt_4402_);
v___x_4422_ = lean_box(0);
v_buckets_x27_4423_ = lean_array_uset(v_buckets_4385_, v___x_4401_, v___x_4422_);
v___x_4424_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_4382_, v_b_4383_, v_bkt_4402_);
v___x_4425_ = lean_array_uset(v_buckets_x27_4423_, v___x_4401_, v___x_4424_);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 1, v___x_4425_);
v___x_4427_ = v___x_4387_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_size_4384_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v___x_4425_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg___boxed(lean_object* v_m_4430_, lean_object* v_a_4431_, lean_object* v_b_4432_){
_start:
{
uint8_t v_a_boxed_4433_; lean_object* v_res_4434_; 
v_a_boxed_4433_ = lean_unbox(v_a_4431_);
v_res_4434_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(v_m_4430_, v_a_boxed_4433_, v_b_4432_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(lean_object* v_cmd_4438_, lean_object* v_as_4439_, size_t v_sz_4440_, size_t v_i_4441_, lean_object* v_b_4442_){
_start:
{
lean_object* v_a_4445_; uint8_t v___x_4449_; 
v___x_4449_ = lean_usize_dec_lt(v_i_4441_, v_sz_4440_);
if (v___x_4449_ == 0)
{
lean_object* v___x_4450_; 
v___x_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4450_, 0, v_b_4442_);
return v___x_4450_;
}
else
{
lean_object* v_a_4451_; lean_object* v_snd_4452_; lean_object* v_fst_4453_; lean_object* v_fst_4454_; lean_object* v_snd_4455_; lean_object* v_snd_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4554_; 
v_a_4451_ = lean_array_uget_borrowed(v_as_4439_, v_i_4441_);
v_snd_4452_ = lean_ctor_get(v_a_4451_, 1);
v_fst_4453_ = lean_ctor_get(v_a_4451_, 0);
v_fst_4454_ = lean_ctor_get(v_snd_4452_, 0);
v_snd_4455_ = lean_ctor_get(v_snd_4452_, 1);
lean_inc(v_snd_4455_);
v_snd_4456_ = lean_ctor_get(v_b_4442_, 1);
v_isSharedCheck_4554_ = !lean_is_exclusive(v_b_4442_);
if (v_isSharedCheck_4554_ == 0)
{
lean_object* v_unused_4555_; 
v_unused_4555_ = lean_ctor_get(v_b_4442_, 0);
lean_dec(v_unused_4555_);
v___x_4458_ = v_b_4442_;
v_isShared_4459_ = v_isSharedCheck_4554_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_snd_4456_);
lean_dec(v_b_4442_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4554_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4460_; 
v___x_4460_ = lean_box(0);
if (lean_obj_tag(v_snd_4455_) == 1)
{
lean_object* v_val_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4550_; 
v_val_4461_ = lean_ctor_get(v_snd_4455_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v_snd_4455_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4463_ = v_snd_4455_;
v_isShared_4464_ = v_isSharedCheck_4550_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_val_4461_);
lean_dec(v_snd_4455_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4550_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
uint8_t v___x_4465_; 
v___x_4465_ = l_System_FilePath_pathExists(v_val_4461_);
if (v___x_4465_ == 0)
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4466_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4467_ = lean_string_append(v___x_4466_, v_cmd_4438_);
v___x_4468_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
v___x_4469_ = lean_string_append(v___x_4467_, v___x_4468_);
v___x_4470_ = lean_string_append(v___x_4469_, v_fst_4453_);
v___x_4471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__0));
v___x_4472_ = lean_string_append(v___x_4470_, v___x_4471_);
v___x_4473_ = lean_string_append(v___x_4472_, v_val_4461_);
lean_dec(v_val_4461_);
v___x_4474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__1));
v___x_4475_ = lean_string_append(v___x_4473_, v___x_4474_);
v___x_4476_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4475_);
lean_dec_ref(v___x_4475_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4491_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4479_ = v___x_4476_;
v_isShared_4480_ = v_isSharedCheck_4491_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4476_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4491_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4481_; lean_object* v___x_4483_; 
v___x_4481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4481_, 0, v_a_4477_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4481_);
v___x_4483_ = v___x_4463_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4481_);
v___x_4483_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4485_; 
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 0, v___x_4483_);
v___x_4485_ = v___x_4458_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v___x_4483_);
lean_ctor_set(v_reuseFailAlloc_4489_, 1, v_snd_4456_);
v___x_4485_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
lean_object* v___x_4487_; 
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 0, v___x_4485_);
v___x_4487_ = v___x_4479_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4485_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_del_object(v___x_4463_);
lean_del_object(v___x_4458_);
lean_dec(v_snd_4456_);
v_a_4492_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4476_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4476_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
else
{
uint8_t v___x_4500_; 
v___x_4500_ = l_System_FilePath_isDir(v_val_4461_);
if (v___x_4500_ == 0)
{
lean_object* v___x_4501_; 
lean_del_object(v___x_4463_);
v___x_4501_ = lean_io_realpath(v_val_4461_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; uint8_t v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4506_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref_known(v___x_4501_, 1);
v___x_4503_ = lean_unbox(v_fst_4454_);
v___x_4504_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(v_snd_4456_, v___x_4503_, v_a_4502_);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 1, v___x_4504_);
lean_ctor_set(v___x_4458_, 0, v___x_4460_);
v___x_4506_ = v___x_4458_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4460_);
lean_ctor_set(v_reuseFailAlloc_4507_, 1, v___x_4504_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
v_a_4445_ = v___x_4506_;
goto v___jp_4444_;
}
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
lean_del_object(v___x_4458_);
lean_dec(v_snd_4456_);
v_a_4508_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4501_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4501_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
else
{
lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4516_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4517_ = lean_string_append(v___x_4516_, v_cmd_4438_);
v___x_4518_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
v___x_4519_ = lean_string_append(v___x_4517_, v___x_4518_);
v___x_4520_ = lean_string_append(v___x_4519_, v_fst_4453_);
v___x_4521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__0));
v___x_4522_ = lean_string_append(v___x_4520_, v___x_4521_);
v___x_4523_ = lean_string_append(v___x_4522_, v_val_4461_);
lean_dec(v_val_4461_);
v___x_4524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__2));
v___x_4525_ = lean_string_append(v___x_4523_, v___x_4524_);
v___x_4526_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4525_);
lean_dec_ref(v___x_4525_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4541_; 
v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4529_ = v___x_4526_;
v_isShared_4530_ = v_isSharedCheck_4541_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v___x_4526_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4541_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4531_; lean_object* v___x_4533_; 
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v_a_4527_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4531_);
v___x_4533_ = v___x_4463_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v___x_4531_);
v___x_4533_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4535_; 
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 0, v___x_4533_);
v___x_4535_ = v___x_4458_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4533_);
lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_snd_4456_);
v___x_4535_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
lean_object* v___x_4537_; 
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 0, v___x_4535_);
v___x_4537_ = v___x_4529_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v___x_4535_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
return v___x_4537_;
}
}
}
}
}
else
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4549_; 
lean_del_object(v___x_4463_);
lean_del_object(v___x_4458_);
lean_dec(v_snd_4456_);
v_a_4542_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4544_ = v___x_4526_;
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4526_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4547_; 
if (v_isShared_4545_ == 0)
{
v___x_4547_ = v___x_4544_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4542_);
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
}
}
}
else
{
lean_object* v___x_4552_; 
lean_dec(v_snd_4455_);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 0, v___x_4460_);
v___x_4552_ = v___x_4458_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4460_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_snd_4456_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
v_a_4445_ = v___x_4552_;
goto v___jp_4444_;
}
}
}
}
v___jp_4444_:
{
size_t v___x_4446_; size_t v___x_4447_; 
v___x_4446_ = ((size_t)1ULL);
v___x_4447_ = lean_usize_add(v_i_4441_, v___x_4446_);
v_i_4441_ = v___x_4447_;
v_b_4442_ = v_a_4445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___boxed(lean_object* v_cmd_4556_, lean_object* v_as_4557_, lean_object* v_sz_4558_, lean_object* v_i_4559_, lean_object* v_b_4560_, lean_object* v___y_4561_){
_start:
{
size_t v_sz_boxed_4562_; size_t v_i_boxed_4563_; lean_object* v_res_4564_; 
v_sz_boxed_4562_ = lean_unbox_usize(v_sz_4558_);
lean_dec(v_sz_4558_);
v_i_boxed_4563_ = lean_unbox_usize(v_i_4559_);
lean_dec(v_i_4559_);
v_res_4564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(v_cmd_4556_, v_as_4557_, v_sz_boxed_4562_, v_i_boxed_4563_, v_b_4560_);
lean_dec_ref(v_as_4557_);
lean_dec_ref(v_cmd_4556_);
return v_res_4564_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0(void){
_start:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4565_ = lean_box(0);
v___x_4566_ = lean_unsigned_to_nat(16u);
v___x_4567_ = lean_mk_array(v___x_4566_, v___x_4565_);
return v___x_4567_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1(void){
_start:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v_store_4570_; 
v___x_4568_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0, &l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0);
v___x_4569_ = lean_unsigned_to_nat(0u);
v_store_4570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_store_4570_, 0, v___x_4569_);
lean_ctor_set(v_store_4570_, 1, v___x_4568_);
return v_store_4570_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2(void){
_start:
{
lean_object* v_store_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v_store_4571_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1, &l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1);
v___x_4572_ = lean_box(0);
v___x_4573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4572_);
lean_ctor_set(v___x_4573_, 1, v_store_4571_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(lean_object* v_cmd_4574_, lean_object* v_entries_4575_){
_start:
{
lean_object* v___x_4577_; size_t v_sz_4578_; size_t v___x_4579_; lean_object* v___x_4580_; 
v___x_4577_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2);
v_sz_4578_ = lean_array_size(v_entries_4575_);
v___x_4579_ = ((size_t)0ULL);
v___x_4580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(v_cmd_4574_, v_entries_4575_, v_sz_4578_, v___x_4579_, v___x_4577_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4595_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4583_ = v___x_4580_;
v_isShared_4584_ = v_isSharedCheck_4595_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v___x_4580_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4595_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v_fst_4585_; 
v_fst_4585_ = lean_ctor_get(v_a_4581_, 0);
if (lean_obj_tag(v_fst_4585_) == 0)
{
lean_object* v_snd_4586_; lean_object* v___x_4587_; lean_object* v___x_4589_; 
v_snd_4586_ = lean_ctor_get(v_a_4581_, 1);
lean_inc(v_snd_4586_);
lean_dec(v_a_4581_);
v___x_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4587_, 0, v_snd_4586_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4587_);
v___x_4589_ = v___x_4583_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___x_4587_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
else
{
lean_object* v_val_4591_; lean_object* v___x_4593_; 
lean_inc_ref(v_fst_4585_);
lean_dec(v_a_4581_);
v_val_4591_ = lean_ctor_get(v_fst_4585_, 0);
lean_inc(v_val_4591_);
lean_dec_ref_known(v_fst_4585_, 1);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v_val_4591_);
v___x_4593_ = v___x_4583_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_val_4591_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
}
else
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4603_; 
v_a_4596_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4598_ = v___x_4580_;
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4580_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4601_; 
if (v_isShared_4599_ == 0)
{
v___x_4601_ = v___x_4598_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___boxed(lean_object* v_cmd_4604_, lean_object* v_entries_4605_, lean_object* v_a_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(v_cmd_4604_, v_entries_4605_);
lean_dec_ref(v_entries_4605_);
lean_dec_ref(v_cmd_4604_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0(lean_object* v_00_u03b2_4608_, lean_object* v_m_4609_, uint8_t v_a_4610_, lean_object* v_b_4611_){
_start:
{
lean_object* v___x_4612_; 
v___x_4612_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(v_m_4609_, v_a_4610_, v_b_4611_);
return v___x_4612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___boxed(lean_object* v_00_u03b2_4613_, lean_object* v_m_4614_, lean_object* v_a_4615_, lean_object* v_b_4616_){
_start:
{
uint8_t v_a_boxed_4617_; lean_object* v_res_4618_; 
v_a_boxed_4617_ = lean_unbox(v_a_4615_);
v_res_4618_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0(v_00_u03b2_4613_, v_m_4614_, v_a_boxed_4617_, v_b_4616_);
return v_res_4618_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0(lean_object* v_00_u03b2_4619_, uint8_t v_a_4620_, lean_object* v_x_4621_){
_start:
{
uint8_t v___x_4622_; 
v___x_4622_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_4620_, v_x_4621_);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4623_, lean_object* v_a_4624_, lean_object* v_x_4625_){
_start:
{
uint8_t v_a_boxed_4626_; uint8_t v_res_4627_; lean_object* v_r_4628_; 
v_a_boxed_4626_ = lean_unbox(v_a_4624_);
v_res_4627_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0(v_00_u03b2_4623_, v_a_boxed_4626_, v_x_4625_);
lean_dec(v_x_4625_);
v_r_4628_ = lean_box(v_res_4627_);
return v_r_4628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1(lean_object* v_00_u03b2_4629_, lean_object* v_data_4630_){
_start:
{
lean_object* v___x_4631_; 
v___x_4631_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1___redArg(v_data_4630_);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2(lean_object* v_00_u03b2_4632_, uint8_t v_a_4633_, lean_object* v_b_4634_, lean_object* v_x_4635_){
_start:
{
lean_object* v___x_4636_; 
v___x_4636_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_4633_, v_b_4634_, v_x_4635_);
return v___x_4636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4637_, lean_object* v_a_4638_, lean_object* v_b_4639_, lean_object* v_x_4640_){
_start:
{
uint8_t v_a_boxed_4641_; lean_object* v_res_4642_; 
v_a_boxed_4641_ = lean_unbox(v_a_4638_);
v_res_4642_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2(v_00_u03b2_4637_, v_a_boxed_4641_, v_b_4639_, v_x_4640_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4643_, lean_object* v_i_4644_, lean_object* v_source_4645_, lean_object* v_target_4646_){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2___redArg(v_i_4644_, v_source_4645_, v_target_4646_);
return v___x_4647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4648_, lean_object* v_x_4649_, lean_object* v_x_4650_){
_start:
{
lean_object* v___x_4651_; 
v___x_4651_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4___redArg(v_x_4649_, v_x_4650_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext(lean_object* v_cmd_4663_, uint8_t v_paranoid_4664_, uint8_t v_inadvisablyNoSandbox_4665_, lean_object* v_lean_4666_, lean_object* v_lake_4667_, lean_object* v_projectDir_4668_, lean_object* v_moduleStore_4669_){
_start:
{
lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v___y_4675_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v_whichSandbox_4704_; 
if (v_inadvisablyNoSandbox_4665_ == 0)
{
uint8_t v___x_4780_; 
v___x_4780_ = l_System_Platform_isLinux;
if (v___x_4780_ == 0)
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
lean_dec_ref(v_moduleStore_4669_);
lean_dec_ref(v_projectDir_4668_);
lean_dec_ref(v_lean_4666_);
v___x_4781_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4782_ = lean_string_append(v___x_4781_, v_cmd_4663_);
v___x_4783_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6));
v___x_4784_ = lean_string_append(v___x_4782_, v___x_4783_);
v___x_4785_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4784_);
lean_dec_ref(v___x_4784_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4794_; 
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4788_ = v___x_4785_;
v_isShared_4789_ = v_isSharedCheck_4794_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4785_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4794_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4790_; lean_object* v___x_4792_; 
v___x_4790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4790_, 0, v_a_4786_);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 0, v___x_4790_);
v___x_4792_ = v___x_4788_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4790_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
else
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
v_a_4795_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4785_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4785_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
else
{
lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___y_4806_; 
v___x_4803_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7));
v___x_4804_ = lean_io_getenv(v___x_4803_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_object* v___x_4842_; 
v___x_4842_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__8));
v___y_4806_ = v___x_4842_;
goto v___jp_4805_;
}
else
{
lean_object* v_val_4843_; 
v_val_4843_ = lean_ctor_get(v___x_4804_, 0);
lean_inc(v_val_4843_);
lean_dec_ref_known(v___x_4804_, 1);
v___y_4806_ = v_val_4843_;
goto v___jp_4805_;
}
v___jp_4805_:
{
lean_object* v___x_4807_; lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4841_; 
lean_inc_ref(v___y_4806_);
v___x_4807_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___y_4806_);
v_a_4808_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4810_ = v___x_4807_;
v_isShared_4811_ = v_isSharedCheck_4841_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4807_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4841_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
if (lean_obj_tag(v_a_4808_) == 1)
{
lean_object* v_val_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4819_; 
lean_del_object(v___x_4810_);
lean_dec_ref(v___y_4806_);
v_val_4812_ = lean_ctor_get(v_a_4808_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v_a_4808_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4814_ = v_a_4808_;
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_val_4812_);
lean_dec(v_a_4808_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4817_; 
if (v_isShared_4815_ == 0)
{
v___x_4817_ = v___x_4814_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_val_4812_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
v_whichSandbox_4704_ = v___x_4817_;
goto v___jp_4703_;
}
}
}
else
{
lean_object* v___x_4820_; lean_object* v___x_4821_; 
lean_dec(v_a_4808_);
lean_dec_ref(v_moduleStore_4669_);
lean_dec_ref(v_projectDir_4668_);
lean_dec_ref(v_lean_4666_);
v___x_4820_ = l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError(v_cmd_4663_, v___y_4806_);
lean_dec_ref(v___y_4806_);
v___x_4821_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4820_);
lean_dec_ref(v___x_4820_);
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4832_; 
v_a_4822_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4824_ = v___x_4821_;
v_isShared_4825_ = v_isSharedCheck_4832_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4821_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4832_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4811_ == 0)
{
lean_ctor_set(v___x_4810_, 0, v_a_4822_);
v___x_4827_ = v___x_4810_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4822_);
v___x_4827_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
lean_object* v___x_4829_; 
if (v_isShared_4825_ == 0)
{
lean_ctor_set(v___x_4824_, 0, v___x_4827_);
v___x_4829_ = v___x_4824_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4827_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
lean_del_object(v___x_4810_);
v_a_4833_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4821_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4821_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
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
lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4844_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__9));
v___x_4845_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_4844_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_object* v___x_4846_; 
lean_dec_ref_known(v___x_4845_, 1);
v___x_4846_ = lean_box(0);
v_whichSandbox_4704_ = v___x_4846_;
goto v___jp_4703_;
}
else
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
lean_dec_ref(v_moduleStore_4669_);
lean_dec_ref(v_projectDir_4668_);
lean_dec_ref(v_lean_4666_);
v_a_4847_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4845_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4845_);
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
v___jp_4671_:
{
lean_object* v___x_4678_; 
v___x_4678_ = lean_io_realpath(v_projectDir_4668_);
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4694_; 
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4681_ = v___x_4678_;
v_isShared_4682_ = v_isSharedCheck_4694_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4678_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4694_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v_home_4683_; lean_object* v_lake_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4692_; 
v_home_4683_ = lean_ctor_get(v_lake_4667_, 0);
v_lake_4684_ = lean_ctor_get(v_lake_4667_, 5);
v___x_4685_ = lean_box(0);
v___x_4686_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_4687_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
v___x_4688_ = lean_box(1);
lean_inc_ref(v_home_4683_);
lean_inc_ref(v_lake_4684_);
v___x_4689_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_4689_, 0, v_a_4679_);
lean_ctor_set(v___x_4689_, 1, v___x_4685_);
lean_ctor_set(v___x_4689_, 2, v___x_4685_);
lean_ctor_set(v___x_4689_, 3, v___x_4686_);
lean_ctor_set(v___x_4689_, 4, v___x_4686_);
lean_ctor_set(v___x_4689_, 5, v___x_4686_);
lean_ctor_set(v___x_4689_, 6, v___y_4672_);
lean_ctor_set(v___x_4689_, 7, v___x_4687_);
lean_ctor_set(v___x_4689_, 8, v___x_4687_);
lean_ctor_set(v___x_4689_, 9, v___y_4674_);
lean_ctor_set(v___x_4689_, 10, v_lake_4684_);
lean_ctor_set(v___x_4689_, 11, v_home_4683_);
lean_ctor_set(v___x_4689_, 12, v___y_4676_);
lean_ctor_set(v___x_4689_, 13, v___y_4673_);
lean_ctor_set(v___x_4689_, 14, v___y_4675_);
lean_ctor_set(v___x_4689_, 15, v___x_4688_);
lean_ctor_set(v___x_4689_, 16, v___y_4677_);
lean_ctor_set(v___x_4689_, 17, v_moduleStore_4669_);
v___x_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4689_);
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 0, v___x_4690_);
v___x_4692_ = v___x_4681_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4690_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
else
{
lean_object* v_a_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4702_; 
lean_dec_ref(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec_ref(v_moduleStore_4669_);
v_a_4695_ = lean_ctor_get(v___x_4678_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4697_ = v___x_4678_;
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_a_4695_);
lean_dec(v___x_4678_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4700_; 
if (v_isShared_4698_ == 0)
{
v___x_4700_ = v___x_4697_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_a_4695_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
}
v___jp_4703_:
{
lean_object* v_sysroot_4705_; lean_object* v_binDir_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v_whichLean4Export_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v_whichLeanChecker_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v_a_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4779_; 
v_sysroot_4705_ = lean_ctor_get(v_lean_4666_, 0);
lean_inc_ref(v_sysroot_4705_);
v_binDir_4706_ = lean_ctor_get(v_lean_4666_, 6);
v___x_4707_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0));
lean_inc_ref_n(v_binDir_4706_, 2);
v___x_4708_ = l_System_FilePath_join(v_binDir_4706_, v___x_4707_);
v___x_4709_ = l_System_FilePath_exeExtension;
v_whichLean4Export_4710_ = l_System_FilePath_addExtension(v___x_4708_, v___x_4709_);
v___x_4711_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1));
v___x_4712_ = l_System_FilePath_join(v_binDir_4706_, v___x_4711_);
v_whichLeanChecker_4713_ = l_System_FilePath_addExtension(v___x_4712_, v___x_4709_);
v___x_4714_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2));
v___x_4715_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4714_);
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
v_isSharedCheck_4779_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4718_ = v___x_4715_;
v_isShared_4719_ = v_isSharedCheck_4779_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_a_4716_);
lean_dec(v___x_4715_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4779_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
if (lean_obj_tag(v_a_4716_) == 1)
{
lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4754_; 
lean_dec_ref_known(v_a_4716_, 1);
lean_del_object(v___x_4718_);
v___x_4720_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__4));
v___x_4721_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4720_);
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4724_ = v___x_4721_;
v_isShared_4725_ = v_isSharedCheck_4754_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4721_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4754_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
if (lean_obj_tag(v_a_4722_) == 1)
{
lean_del_object(v___x_4724_);
if (v_paranoid_4664_ == 0)
{
lean_object* v_val_4726_; lean_object* v___x_4727_; 
lean_dec_ref(v_lean_4666_);
v_val_4726_ = lean_ctor_get(v_a_4722_, 0);
lean_inc(v_val_4726_);
lean_dec_ref_known(v_a_4722_, 1);
v___x_4727_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3));
v___y_4672_ = v_sysroot_4705_;
v___y_4673_ = v_whichLeanChecker_4713_;
v___y_4674_ = v_whichSandbox_4704_;
v___y_4675_ = v_val_4726_;
v___y_4676_ = v_whichLean4Export_4710_;
v___y_4677_ = v___x_4727_;
goto v___jp_4671_;
}
else
{
lean_object* v_val_4728_; lean_object* v___x_4729_; 
v_val_4728_ = lean_ctor_get(v_a_4722_, 0);
lean_inc(v_val_4728_);
lean_dec_ref_known(v_a_4722_, 1);
v___x_4729_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels(v_lean_4666_);
v___y_4672_ = v_sysroot_4705_;
v___y_4673_ = v_whichLeanChecker_4713_;
v___y_4674_ = v_whichSandbox_4704_;
v___y_4675_ = v_val_4728_;
v___y_4676_ = v_whichLean4Export_4710_;
v___y_4677_ = v___x_4729_;
goto v___jp_4671_;
}
}
else
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; 
lean_dec(v_a_4722_);
lean_dec_ref(v_whichLeanChecker_4713_);
lean_dec_ref(v_whichLean4Export_4710_);
lean_dec_ref(v_sysroot_4705_);
lean_dec(v_whichSandbox_4704_);
lean_dec_ref(v_moduleStore_4669_);
lean_dec_ref(v_projectDir_4668_);
lean_dec_ref(v_lean_4666_);
v___x_4730_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4731_ = lean_string_append(v___x_4730_, v_cmd_4663_);
v___x_4732_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4));
v___x_4733_ = lean_string_append(v___x_4731_, v___x_4732_);
v___x_4734_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4733_);
lean_dec_ref(v___x_4733_);
if (lean_obj_tag(v___x_4734_) == 0)
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4745_; 
v_a_4735_ = lean_ctor_get(v___x_4734_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4734_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4737_ = v___x_4734_;
v_isShared_4738_ = v_isSharedCheck_4745_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___x_4734_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4745_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4725_ == 0)
{
lean_ctor_set(v___x_4724_, 0, v_a_4735_);
v___x_4740_ = v___x_4724_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4735_);
v___x_4740_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
lean_object* v___x_4742_; 
if (v_isShared_4738_ == 0)
{
lean_ctor_set(v___x_4737_, 0, v___x_4740_);
v___x_4742_ = v___x_4737_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4740_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
}
else
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
lean_del_object(v___x_4724_);
v_a_4746_ = lean_ctor_get(v___x_4734_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4734_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___x_4734_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4734_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
}
}
else
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
lean_dec(v_a_4716_);
lean_dec_ref(v_whichLeanChecker_4713_);
lean_dec_ref(v_whichLean4Export_4710_);
lean_dec_ref(v_sysroot_4705_);
lean_dec(v_whichSandbox_4704_);
lean_dec_ref(v_moduleStore_4669_);
lean_dec_ref(v_projectDir_4668_);
lean_dec_ref(v_lean_4666_);
v___x_4755_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4756_ = lean_string_append(v___x_4755_, v_cmd_4663_);
v___x_4757_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5));
v___x_4758_ = lean_string_append(v___x_4756_, v___x_4757_);
v___x_4759_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4758_);
lean_dec_ref(v___x_4758_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4770_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4762_ = v___x_4759_;
v_isShared_4763_ = v_isSharedCheck_4770_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4759_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4770_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4719_ == 0)
{
lean_ctor_set(v___x_4718_, 0, v_a_4760_);
v___x_4765_ = v___x_4718_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
lean_object* v___x_4767_; 
if (v_isShared_4763_ == 0)
{
lean_ctor_set(v___x_4762_, 0, v___x_4765_);
v___x_4767_ = v___x_4762_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4765_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4778_; 
lean_del_object(v___x_4718_);
v_a_4771_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4773_ = v___x_4759_;
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4759_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___boxed(lean_object* v_cmd_4855_, lean_object* v_paranoid_4856_, lean_object* v_inadvisablyNoSandbox_4857_, lean_object* v_lean_4858_, lean_object* v_lake_4859_, lean_object* v_projectDir_4860_, lean_object* v_moduleStore_4861_, lean_object* v_a_4862_){
_start:
{
uint8_t v_paranoid_boxed_4863_; uint8_t v_inadvisablyNoSandbox_boxed_4864_; lean_object* v_res_4865_; 
v_paranoid_boxed_4863_ = lean_unbox(v_paranoid_4856_);
v_inadvisablyNoSandbox_boxed_4864_ = lean_unbox(v_inadvisablyNoSandbox_4857_);
v_res_4865_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v_cmd_4855_, v_paranoid_boxed_4863_, v_inadvisablyNoSandbox_boxed_4864_, v_lean_4858_, v_lake_4859_, v_projectDir_4860_, v_moduleStore_4861_);
lean_dec_ref(v_lake_4859_);
lean_dec_ref(v_cmd_4855_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(lean_object* v_init_4872_, lean_object* v_x_4873_){
_start:
{
lean_object* v_d_4876_; 
if (lean_obj_tag(v_x_4873_) == 0)
{
lean_object* v_k_4879_; lean_object* v_v_4880_; lean_object* v_l_4881_; lean_object* v_r_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v_k_4879_ = lean_ctor_get(v_x_4873_, 1);
v_v_4880_ = lean_ctor_get(v_x_4873_, 2);
v_l_4881_ = lean_ctor_get(v_x_4873_, 3);
v_r_4882_ = lean_ctor_get(v_x_4873_, 4);
v___x_4883_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
v___x_4884_ = lean_box(0);
v___x_4885_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_4886_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_4872_, v_l_4881_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc(v_a_4887_);
lean_dec_ref_known(v___x_4886_, 1);
if (lean_obj_tag(v_a_4887_) == 0)
{
lean_object* v_a_4888_; 
v_a_4888_ = lean_ctor_get(v_a_4887_, 0);
lean_inc(v_a_4888_);
lean_dec_ref_known(v_a_4887_, 1);
v_d_4876_ = v_a_4888_;
goto v___jp_4875_;
}
else
{
lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4925_; 
v_isSharedCheck_4925_ = !lean_is_exclusive(v_a_4887_);
if (v_isSharedCheck_4925_ == 0)
{
lean_object* v_unused_4926_; 
v_unused_4926_ = lean_ctor_get(v_a_4887_, 0);
lean_dec(v_unused_4926_);
v___x_4890_ = v_a_4887_;
v_isShared_4891_ = v_isSharedCheck_4925_;
goto v_resetjp_4889_;
}
else
{
lean_dec(v_a_4887_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4925_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4924_; 
v___x_4892_ = lean_unsigned_to_nat(0u);
v___x_4893_ = lean_array_get_borrowed(v___x_4883_, v_v_4880_, v___x_4892_);
lean_inc(v___x_4893_);
v___x_4894_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4893_);
v_a_4895_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4897_ = v___x_4894_;
v_isShared_4898_ = v_isSharedCheck_4924_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4894_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4924_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
if (lean_obj_tag(v_a_4895_) == 0)
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4899_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1));
v___x_4900_ = lean_string_append(v___x_4899_, v_k_4879_);
v___x_4901_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2));
v___x_4902_ = lean_string_append(v___x_4900_, v___x_4901_);
v___x_4903_ = lean_string_append(v___x_4902_, v___x_4893_);
v___x_4904_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v___x_4905_ = lean_string_append(v___x_4903_, v___x_4904_);
v___x_4906_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4905_);
lean_dec_ref(v___x_4905_);
if (lean_obj_tag(v___x_4906_) == 0)
{
lean_object* v_a_4907_; lean_object* v___x_4909_; 
v_a_4907_ = lean_ctor_get(v___x_4906_, 0);
lean_inc(v_a_4907_);
lean_dec_ref_known(v___x_4906_, 1);
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 0, v_a_4907_);
v___x_4909_ = v___x_4897_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_a_4907_);
v___x_4909_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
lean_object* v___x_4911_; 
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 0, v___x_4909_);
v___x_4911_ = v___x_4890_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4909_);
v___x_4911_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
lean_object* v___x_4912_; 
v___x_4912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4911_);
lean_ctor_set(v___x_4912_, 1, v___x_4884_);
v_d_4876_ = v___x_4912_;
goto v___jp_4875_;
}
}
}
else
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
lean_del_object(v___x_4897_);
lean_del_object(v___x_4890_);
v_a_4915_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4917_ = v___x_4906_;
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4906_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
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
lean_dec_ref_known(v_a_4895_, 1);
lean_del_object(v___x_4897_);
lean_del_object(v___x_4890_);
v_init_4872_ = v___x_4885_;
v_x_4873_ = v_r_4882_;
goto _start;
}
}
}
}
}
else
{
return v___x_4886_;
}
}
else
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4927_, 0, v_init_4872_);
v___x_4928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4927_);
return v___x_4928_;
}
v___jp_4875_:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4877_, 0, v_d_4876_);
v___x_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
return v___x_4878_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___boxed(lean_object* v_init_4929_, lean_object* v_x_4930_, lean_object* v___y_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_4929_, v_x_4930_);
lean_dec(v_x_4930_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(lean_object* v_k_4933_, lean_object* v_v_4934_, lean_object* v_t_4935_){
_start:
{
if (lean_obj_tag(v_t_4935_) == 0)
{
lean_object* v_size_4936_; lean_object* v_k_4937_; lean_object* v_v_4938_; lean_object* v_l_4939_; lean_object* v_r_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_5220_; 
v_size_4936_ = lean_ctor_get(v_t_4935_, 0);
v_k_4937_ = lean_ctor_get(v_t_4935_, 1);
v_v_4938_ = lean_ctor_get(v_t_4935_, 2);
v_l_4939_ = lean_ctor_get(v_t_4935_, 3);
v_r_4940_ = lean_ctor_get(v_t_4935_, 4);
v_isSharedCheck_5220_ = !lean_is_exclusive(v_t_4935_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_4942_ = v_t_4935_;
v_isShared_4943_ = v_isSharedCheck_5220_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_r_4940_);
lean_inc(v_l_4939_);
lean_inc(v_v_4938_);
lean_inc(v_k_4937_);
lean_inc(v_size_4936_);
lean_dec(v_t_4935_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_5220_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
uint8_t v___x_4944_; 
v___x_4944_ = lean_string_compare(v_k_4933_, v_k_4937_);
switch(v___x_4944_)
{
case 0:
{
lean_object* v_impl_4945_; lean_object* v___x_4946_; 
lean_dec(v_size_4936_);
v_impl_4945_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_4933_, v_v_4934_, v_l_4939_);
v___x_4946_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4940_) == 0)
{
lean_object* v_size_4947_; lean_object* v_size_4948_; lean_object* v_k_4949_; lean_object* v_v_4950_; lean_object* v_l_4951_; lean_object* v_r_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; uint8_t v___x_4955_; 
v_size_4947_ = lean_ctor_get(v_r_4940_, 0);
v_size_4948_ = lean_ctor_get(v_impl_4945_, 0);
v_k_4949_ = lean_ctor_get(v_impl_4945_, 1);
v_v_4950_ = lean_ctor_get(v_impl_4945_, 2);
v_l_4951_ = lean_ctor_get(v_impl_4945_, 3);
v_r_4952_ = lean_ctor_get(v_impl_4945_, 4);
lean_inc(v_r_4952_);
v___x_4953_ = lean_unsigned_to_nat(3u);
v___x_4954_ = lean_nat_mul(v___x_4953_, v_size_4947_);
v___x_4955_ = lean_nat_dec_lt(v___x_4954_, v_size_4948_);
lean_dec(v___x_4954_);
if (v___x_4955_ == 0)
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4959_; 
lean_dec(v_r_4952_);
v___x_4956_ = lean_nat_add(v___x_4946_, v_size_4948_);
v___x_4957_ = lean_nat_add(v___x_4956_, v_size_4947_);
lean_dec(v___x_4956_);
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 3, v_impl_4945_);
lean_ctor_set(v___x_4942_, 0, v___x_4957_);
v___x_4959_ = v___x_4942_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4957_);
lean_ctor_set(v_reuseFailAlloc_4960_, 1, v_k_4937_);
lean_ctor_set(v_reuseFailAlloc_4960_, 2, v_v_4938_);
lean_ctor_set(v_reuseFailAlloc_4960_, 3, v_impl_4945_);
lean_ctor_set(v_reuseFailAlloc_4960_, 4, v_r_4940_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
else
{
lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_5026_; 
lean_inc(v_l_4951_);
lean_inc(v_v_4950_);
lean_inc(v_k_4949_);
lean_inc(v_size_4948_);
v_isSharedCheck_5026_ = !lean_is_exclusive(v_impl_4945_);
if (v_isSharedCheck_5026_ == 0)
{
lean_object* v_unused_5027_; lean_object* v_unused_5028_; lean_object* v_unused_5029_; lean_object* v_unused_5030_; lean_object* v_unused_5031_; 
v_unused_5027_ = lean_ctor_get(v_impl_4945_, 4);
lean_dec(v_unused_5027_);
v_unused_5028_ = lean_ctor_get(v_impl_4945_, 3);
lean_dec(v_unused_5028_);
v_unused_5029_ = lean_ctor_get(v_impl_4945_, 2);
lean_dec(v_unused_5029_);
v_unused_5030_ = lean_ctor_get(v_impl_4945_, 1);
lean_dec(v_unused_5030_);
v_unused_5031_ = lean_ctor_get(v_impl_4945_, 0);
lean_dec(v_unused_5031_);
v___x_4962_ = v_impl_4945_;
v_isShared_4963_ = v_isSharedCheck_5026_;
goto v_resetjp_4961_;
}
else
{
lean_dec(v_impl_4945_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_5026_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v_size_4964_; lean_object* v_size_4965_; lean_object* v_k_4966_; lean_object* v_v_4967_; lean_object* v_l_4968_; lean_object* v_r_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; uint8_t v___x_4972_; 
v_size_4964_ = lean_ctor_get(v_l_4951_, 0);
v_size_4965_ = lean_ctor_get(v_r_4952_, 0);
v_k_4966_ = lean_ctor_get(v_r_4952_, 1);
v_v_4967_ = lean_ctor_get(v_r_4952_, 2);
v_l_4968_ = lean_ctor_get(v_r_4952_, 3);
v_r_4969_ = lean_ctor_get(v_r_4952_, 4);
v___x_4970_ = lean_unsigned_to_nat(2u);
v___x_4971_ = lean_nat_mul(v___x_4970_, v_size_4964_);
v___x_4972_ = lean_nat_dec_lt(v_size_4965_, v___x_4971_);
lean_dec(v___x_4971_);
if (v___x_4972_ == 0)
{
lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_5001_; 
lean_inc(v_r_4969_);
lean_inc(v_l_4968_);
lean_inc(v_v_4967_);
lean_inc(v_k_4966_);
v_isSharedCheck_5001_ = !lean_is_exclusive(v_r_4952_);
if (v_isSharedCheck_5001_ == 0)
{
lean_object* v_unused_5002_; lean_object* v_unused_5003_; lean_object* v_unused_5004_; lean_object* v_unused_5005_; lean_object* v_unused_5006_; 
v_unused_5002_ = lean_ctor_get(v_r_4952_, 4);
lean_dec(v_unused_5002_);
v_unused_5003_ = lean_ctor_get(v_r_4952_, 3);
lean_dec(v_unused_5003_);
v_unused_5004_ = lean_ctor_get(v_r_4952_, 2);
lean_dec(v_unused_5004_);
v_unused_5005_ = lean_ctor_get(v_r_4952_, 1);
lean_dec(v_unused_5005_);
v_unused_5006_ = lean_ctor_get(v_r_4952_, 0);
lean_dec(v_unused_5006_);
v___x_4974_ = v_r_4952_;
v_isShared_4975_ = v_isSharedCheck_5001_;
goto v_resetjp_4973_;
}
else
{
lean_dec(v_r_4952_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_5001_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; lean_object* v___x_4989_; lean_object* v___y_4991_; 
v___x_4976_ = lean_nat_add(v___x_4946_, v_size_4948_);
lean_dec(v_size_4948_);
v___x_4977_ = lean_nat_add(v___x_4976_, v_size_4947_);
lean_dec(v___x_4976_);
v___x_4989_ = lean_nat_add(v___x_4946_, v_size_4964_);
if (lean_obj_tag(v_l_4968_) == 0)
{
lean_object* v_size_4999_; 
v_size_4999_ = lean_ctor_get(v_l_4968_, 0);
lean_inc(v_size_4999_);
v___y_4991_ = v_size_4999_;
goto v___jp_4990_;
}
else
{
lean_object* v___x_5000_; 
v___x_5000_ = lean_unsigned_to_nat(0u);
v___y_4991_ = v___x_5000_;
goto v___jp_4990_;
}
v___jp_4978_:
{
lean_object* v___x_4982_; lean_object* v___x_4984_; 
v___x_4982_ = lean_nat_add(v___y_4979_, v___y_4981_);
lean_dec(v___y_4981_);
lean_dec(v___y_4979_);
if (v_isShared_4975_ == 0)
{
lean_ctor_set(v___x_4974_, 4, v_r_4940_);
lean_ctor_set(v___x_4974_, 3, v_r_4969_);
lean_ctor_set(v___x_4974_, 2, v_v_4938_);
lean_ctor_set(v___x_4974_, 1, v_k_4937_);
lean_ctor_set(v___x_4974_, 0, v___x_4982_);
v___x_4984_ = v___x_4974_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v___x_4982_);
lean_ctor_set(v_reuseFailAlloc_4988_, 1, v_k_4937_);
lean_ctor_set(v_reuseFailAlloc_4988_, 2, v_v_4938_);
lean_ctor_set(v_reuseFailAlloc_4988_, 3, v_r_4969_);
lean_ctor_set(v_reuseFailAlloc_4988_, 4, v_r_4940_);
v___x_4984_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
lean_object* v___x_4986_; 
if (v_isShared_4963_ == 0)
{
lean_ctor_set(v___x_4962_, 4, v___x_4984_);
lean_ctor_set(v___x_4962_, 3, v___y_4980_);
lean_ctor_set(v___x_4962_, 2, v_v_4967_);
lean_ctor_set(v___x_4962_, 1, v_k_4966_);
lean_ctor_set(v___x_4962_, 0, v___x_4977_);
v___x_4986_ = v___x_4962_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v___x_4977_);
lean_ctor_set(v_reuseFailAlloc_4987_, 1, v_k_4966_);
lean_ctor_set(v_reuseFailAlloc_4987_, 2, v_v_4967_);
lean_ctor_set(v_reuseFailAlloc_4987_, 3, v___y_4980_);
lean_ctor_set(v_reuseFailAlloc_4987_, 4, v___x_4984_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
v___jp_4990_:
{
lean_object* v___x_4992_; lean_object* v___x_4994_; 
v___x_4992_ = lean_nat_add(v___x_4989_, v___y_4991_);
lean_dec(v___y_4991_);
lean_dec(v___x_4989_);
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 4, v_l_4968_);
lean_ctor_set(v___x_4942_, 3, v_l_4951_);
lean_ctor_set(v___x_4942_, 2, v_v_4950_);
lean_ctor_set(v___x_4942_, 1, v_k_4949_);
lean_ctor_set(v___x_4942_, 0, v___x_4992_);
v___x_4994_ = v___x_4942_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v___x_4992_);
lean_ctor_set(v_reuseFailAlloc_4998_, 1, v_k_4949_);
lean_ctor_set(v_reuseFailAlloc_4998_, 2, v_v_4950_);
lean_ctor_set(v_reuseFailAlloc_4998_, 3, v_l_4951_);
lean_ctor_set(v_reuseFailAlloc_4998_, 4, v_l_4968_);
v___x_4994_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
lean_object* v___x_4995_; 
v___x_4995_ = lean_nat_add(v___x_4946_, v_size_4947_);
if (lean_obj_tag(v_r_4969_) == 0)
{
lean_object* v_size_4996_; 
v_size_4996_ = lean_ctor_get(v_r_4969_, 0);
lean_inc(v_size_4996_);
v___y_4979_ = v___x_4995_;
v___y_4980_ = v___x_4994_;
v___y_4981_ = v_size_4996_;
goto v___jp_4978_;
}
else
{
lean_object* v___x_4997_; 
v___x_4997_ = lean_unsigned_to_nat(0u);
v___y_4979_ = v___x_4995_;
v___y_4980_ = v___x_4994_;
v___y_4981_ = v___x_4997_;
goto v___jp_4978_;
}
}
}
}
}
else
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5012_; 
lean_del_object(v___x_4942_);
v___x_5007_ = lean_nat_add(v___x_4946_, v_size_4948_);
lean_dec(v_size_4948_);
v___x_5008_ = lean_nat_add(v___x_5007_, v_size_4947_);
lean_dec(v___x_5007_);
v___x_5009_ = lean_nat_add(v___x_4946_, v_size_4947_);
v___x_5010_ = lean_nat_add(v___x_5009_, v_size_4965_);
lean_dec(v___x_5009_);
lean_inc_ref(v_r_4940_);
if (v_isShared_4963_ == 0)
{
lean_ctor_set(v___x_4962_, 4, v_r_4940_);
lean_ctor_set(v___x_4962_, 3, v_r_4952_);
lean_ctor_set(v___x_4962_, 2, v_v_4938_);
lean_ctor_set(v___x_4962_, 1, v_k_4937_);
lean_ctor_set(v___x_4962_, 0, v___x_5010_);
v___x_5012_ = v___x_4962_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5010_);
lean_ctor_set(v_reuseFailAlloc_5025_, 1, v_k_4937_);
lean_ctor_set(v_reuseFailAlloc_5025_, 2, v_v_4938_);
lean_ctor_set(v_reuseFailAlloc_5025_, 3, v_r_4952_);
lean_ctor_set(v_reuseFailAlloc_5025_, 4, v_r_4940_);
v___x_5012_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5019_; 
v_isSharedCheck_5019_ = !lean_is_exclusive(v_r_4940_);
if (v_isSharedCheck_5019_ == 0)
{
lean_object* v_unused_5020_; lean_object* v_unused_5021_; lean_object* v_unused_5022_; lean_object* v_unused_5023_; lean_object* v_unused_5024_; 
v_unused_5020_ = lean_ctor_get(v_r_4940_, 4);
lean_dec(v_unused_5020_);
v_unused_5021_ = lean_ctor_get(v_r_4940_, 3);
lean_dec(v_unused_5021_);
v_unused_5022_ = lean_ctor_get(v_r_4940_, 2);
lean_dec(v_unused_5022_);
v_unused_5023_ = lean_ctor_get(v_r_4940_, 1);
lean_dec(v_unused_5023_);
v_unused_5024_ = lean_ctor_get(v_r_4940_, 0);
lean_dec(v_unused_5024_);
v___x_5014_ = v_r_4940_;
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
else
{
lean_dec(v_r_4940_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5017_; 
if (v_isShared_5015_ == 0)
{
lean_ctor_set(v___x_5014_, 4, v___x_5012_);
lean_ctor_set(v___x_5014_, 3, v_l_4951_);
lean_ctor_set(v___x_5014_, 2, v_v_4950_);
lean_ctor_set(v___x_5014_, 1, v_k_4949_);
lean_ctor_set(v___x_5014_, 0, v___x_5008_);
v___x_5017_ = v___x_5014_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5008_);
lean_ctor_set(v_reuseFailAlloc_5018_, 1, v_k_4949_);
lean_ctor_set(v_reuseFailAlloc_5018_, 2, v_v_4950_);
lean_ctor_set(v_reuseFailAlloc_5018_, 3, v_l_4951_);
lean_ctor_set(v_reuseFailAlloc_5018_, 4, v___x_5012_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5032_; 
v_l_5032_ = lean_ctor_get(v_impl_4945_, 3);
if (lean_obj_tag(v_l_5032_) == 0)
{
lean_object* v_r_5033_; lean_object* v_k_5034_; lean_object* v_v_5035_; lean_object* v___x_5037_; uint8_t v_isShared_5038_; uint8_t v_isSharedCheck_5046_; 
lean_inc_ref(v_l_5032_);
v_r_5033_ = lean_ctor_get(v_impl_4945_, 4);
v_k_5034_ = lean_ctor_get(v_impl_4945_, 1);
v_v_5035_ = lean_ctor_get(v_impl_4945_, 2);
v_isSharedCheck_5046_ = !lean_is_exclusive(v_impl_4945_);
if (v_isSharedCheck_5046_ == 0)
{
lean_object* v_unused_5047_; lean_object* v_unused_5048_; 
v_unused_5047_ = lean_ctor_get(v_impl_4945_, 3);
lean_dec(v_unused_5047_);
v_unused_5048_ = lean_ctor_get(v_impl_4945_, 0);
lean_dec(v_unused_5048_);
v___x_5037_ = v_impl_4945_;
v_isShared_5038_ = v_isSharedCheck_5046_;
goto v_resetjp_5036_;
}
else
{
lean_inc(v_r_5033_);
lean_inc(v_v_5035_);
lean_inc(v_k_5034_);
lean_dec(v_impl_4945_);
v___x_5037_ = lean_box(0);
v_isShared_5038_ = v_isSharedCheck_5046_;
goto v_resetjp_5036_;
}
v_resetjp_5036_:
{
lean_object* v___x_5039_; lean_object* v___x_5041_; 
v___x_5039_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5033_);
if (v_isShared_5038_ == 0)
{
lean_ctor_set(v___x_5037_, 3, v_r_5033_);
lean_ctor_set(v___x_5037_, 2, v_v_4938_);
lean_ctor_set(v___x_5037_, 1, v_k_4937_);
lean_ctor_set(v___x_5037_, 0, v___x_4946_);
v___x_5041_ = v___x_5037_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v___x_4946_);
lean_ctor_set(v_reuseFailAlloc_5045_, 1, v_k_4937_);
lean_ctor_set(v_reuseFailAlloc_5045_, 2, v_v_4938_);
lean_ctor_set(v_reuseFailAlloc_5045_, 3, v_r_5033_);
lean_ctor_set(v_reuseFailAlloc_5045_, 4, v_r_5033_);
v___x_5041_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
lean_object* v___x_5043_; 
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 4, v___x_5041_);
lean_ctor_set(v___x_4942_, 3, v_l_5032_);
lean_ctor_set(v___x_4942_, 2, v_v_5035_);
lean_ctor_set(v___x_4942_, 1, v_k_5034_);
lean_ctor_set(v___x_4942_, 0, v___x_5039_);
v___x_5043_ = v___x_4942_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v___x_5039_);
lean_ctor_set(v_reuseFailAlloc_5044_, 1, v_k_5034_);
lean_ctor_set(v_reuseFailAlloc_5044_, 2, v_v_5035_);
lean_ctor_set(v_reuseFailAlloc_5044_, 3, v_l_5032_);
lean_ctor_set(v_reuseFailAlloc_5044_, 4, v___x_5041_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
}
}
else
{
lean_object* v_r_5049_; 
v_r_5049_ = lean_ctor_get(v_impl_4945_, 4);
lean_inc(v_r_5049_);
if (lean_obj_tag(v_r_5049_) == 0)
{
lean_object* v_k_5050_; lean_object* v_v_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5074_; 
lean_inc(v_l_5032_);
v_k_5050_ = lean_ctor_get(v_impl_4945_, 1);
v_v_5051_ = lean_ctor_get(v_impl_4945_, 2);
v_isSharedCheck_5074_ = !lean_is_exclusive(v_impl_4945_);
if (v_isSharedCheck_5074_ == 0)
{
lean_object* v_unused_5075_; lean_object* v_unused_5076_; lean_object* v_unused_5077_; 
v_unused_5075_ = lean_ctor_get(v_impl_4945_, 4);
lean_dec(v_unused_5075_);
v_unused_5076_ = lean_ctor_get(v_impl_4945_, 3);
lean_dec(v_unused_5076_);
v_unused_5077_ = lean_ctor_get(v_impl_4945_, 0);
lean_dec(v_unused_5077_);
v___x_5053_ = v_impl_4945_;
v_isShared_5054_ = v_isSharedCheck_5074_;
goto v_resetjp_5052_;
}
else
{
lean_inc(v_v_5051_);
lean_inc(v_k_5050_);
lean_dec(v_impl_4945_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5074_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v_k_5055_; lean_object* v_v_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5070_; 
v_k_5055_ = lean_ctor_get(v_r_5049_, 1);
v_v_5056_ = lean_ctor_get(v_r_5049_, 2);
v_isSharedCheck_5070_ = !lean_is_exclusive(v_r_5049_);
if (v_isSharedCheck_5070_ == 0)
{
lean_object* v_unused_5071_; lean_object* v_unused_5072_; lean_object* v_unused_5073_; 
v_unused_5071_ = lean_ctor_get(v_r_5049_, 4);
lean_dec(v_unused_5071_);
v_unused_5072_ = lean_ctor_get(v_r_5049_, 3);
lean_dec(v_unused_5072_);
v_unused_5073_ = lean_ctor_get(v_r_5049_, 0);
lean_dec(v_unused_5073_);
v___x_5058_ = v_r_5049_;
v_isShared_5059_ = v_isSharedCheck_5070_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_v_5056_);
lean_inc(v_k_5055_);
lean_dec(v_r_5049_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5070_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5060_; lean_object* v___x_5062_; 
v___x_5060_ = lean_unsigned_to_nat(3u);
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 4, v_l_5032_);
lean_ctor_set(v___x_5058_, 3, v_l_5032_);
lean_ctor_set(v___x_5058_, 2, v_v_5051_);
lean_ctor_set(v___x_5058_, 1, v_k_5050_);
lean_ctor_set(v___x_5058_, 0, v___x_4946_);
v___x_5062_ = v___x_5058_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v___x_4946_);
lean_ctor_set(v_reuseFailAlloc_5069_, 1, v_k_5050_);
lean_ctor_set(v_reuseFailAlloc_5069_, 2, v_v_5051_);
lean_ctor_set(v_reuseFailAlloc_5069_, 3, v_l_5032_);
lean_ctor_set(v_reuseFailAlloc_5069_, 4, v_l_5032_);
v___x_5062_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
lean_object* v___x_5064_; 
if (v_isShared_5054_ == 0)
{
lean_ctor_set(v___x_5053_, 4, v_l_5032_);
lean_ctor_set(v___x_5053_, 2, v_v_4938_);
lean_ctor_set(v___x_5053_, 1, v_k_4937_);
lean_ctor_set(v___x_5053_, 0, v___x_4946_);
v___x_5064_ = v___x_5053_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5068_; 
v_reuseFailAlloc_5068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5068_, 0, v___x_4946_);
lean_ctor_set(v_reuseFailAlloc_5068_, 1, v_k_4937_);
lean_ctor_set(v_reuseFailAlloc_5068_, 2, v_v_4938_);
lean_ctor_set(v_reuseFailAlloc_5068_, 3, v_l_5032_);
lean_ctor_set(v_reuseFailAlloc_5068_, 4, v_l_5032_);
v___x_5064_ = v_reuseFailAlloc_5068_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
lean_object* v___x_5066_; 
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 4, v___x_5064_);
lean_ctor_set(v___x_4942_, 3, v___x_5062_);
lean_ctor_set(v___x_4942_, 2, v_v_5056_);
lean_ctor_set(v___x_4942_, 1, v_k_5055_);
lean_ctor_set(v___x_4942_, 0, v___x_5060_);
v___x_5066_ = v___x_4942_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v___x_5060_);
lean_ctor_set(v_reuseFailAlloc_5067_, 1, v_k_5055_);
lean_ctor_set(v_reuseFailAlloc_5067_, 2, v_v_5056_);
lean_ctor_set(v_reuseFailAlloc_5067_, 3, v___x_5062_);
lean_ctor_set(v_reuseFailAlloc_5067_, 4, v___x_5064_);
v___x_5066_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
return v___x_5066_;
}
}
}
}
}
}
else
{
lean_object* v___x_5078_; lean_object* v___x_5080_; 
v___x_5078_ = lean_unsigned_to_nat(2u);
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 4, v_r_5049_);
lean_ctor_set(v___x_4942_, 3, v_impl_4945_);
lean_ctor_set(v___x_4942_, 0, v___x_5078_);
v___x_5080_ = v___x_4942_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5078_);
lean_ctor_set(v_reuseFailAlloc_5081_, 1, v_k_4937_);
lean_ctor_set(v_reuseFailAlloc_5081_, 2, v_v_4938_);
lean_ctor_set(v_reuseFailAlloc_5081_, 3, v_impl_4945_);
lean_ctor_set(v_reuseFailAlloc_5081_, 4, v_r_5049_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
}
}
case 1:
{
lean_object* v___x_5083_; 
lean_dec(v_v_4938_);
lean_dec(v_k_4937_);
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 2, v_v_4934_);
lean_ctor_set(v___x_4942_, 1, v_k_4933_);
v___x_5083_ = v___x_4942_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v_size_4936_);
lean_ctor_set(v_reuseFailAlloc_5084_, 1, v_k_4933_);
lean_ctor_set(v_reuseFailAlloc_5084_, 2, v_v_4934_);
lean_ctor_set(v_reuseFailAlloc_5084_, 3, v_l_4939_);
lean_ctor_set(v_reuseFailAlloc_5084_, 4, v_r_4940_);
v___x_5083_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
return v___x_5083_;
}
}
default: 
{
lean_object* v_impl_5085_; lean_object* v___x_5086_; 
lean_dec(v_size_4936_);
v_impl_5085_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_4933_, v_v_4934_, v_r_4940_);
v___x_5086_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4939_) == 0)
{
lean_object* v_size_5087_; lean_object* v_size_5088_; lean_object* v_k_5089_; lean_object* v_v_5090_; lean_object* v_l_5091_; lean_object* v_r_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; uint8_t v___x_5095_; 
v_size_5087_ = lean_ctor_get(v_l_4939_, 0);
v_size_5088_ = lean_ctor_get(v_impl_5085_, 0);
v_k_5089_ = lean_ctor_get(v_impl_5085_, 1);
v_v_5090_ = lean_ctor_get(v_impl_5085_, 2);
v_l_5091_ = lean_ctor_get(v_impl_5085_, 3);
lean_inc(v_l_5091_);
v_r_5092_ = lean_ctor_get(v_impl_5085_, 4);
v___x_5093_ = lean_unsigned_to_nat(3u);
v___x_5094_ = lean_nat_mul(v___x_5093_, v_size_5087_);
v___x_5095_ = lean_nat_dec_lt(v___x_5094_, v_size_5088_);
lean_dec(v___x_5094_);
if (v___x_5095_ == 0)
{
lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5099_; 
lean_dec(v_l_5091_);
v___x_5096_ = lean_nat_add(v___x_5086_, v_size_5087_);
v___x_5097_ = lean_nat_add(v___x_5096_, v_size_5088_);
lean_dec(v___x_5096_);
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 4, v_impl_5085_);
lean_ctor_set(v___x_4942_, 0, v___x_5097_);
v___x_5099_ = v___x_4942_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v___x_5097_);
lean_ctor_set(v_reuseFailAlloc_5100_, 1, v_k_4937_);
lean_ctor_set(v_reuseFailAlloc_5100_, 2, v_v_4938_);
lean_ctor_set(v_reuseFailAlloc_5100_, 3, v_l_4939_);
lean_ctor_set(v_reuseFailAlloc_5100_, 4, v_impl_5085_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
else
{
lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5164_; 
lean_inc(v_r_5092_);
lean_inc(v_v_5090_);
lean_inc(v_k_5089_);
lean_inc(v_size_5088_);
v_isSharedCheck_5164_ = !lean_is_exclusive(v_impl_5085_);
if (v_isSharedCheck_5164_ == 0)
{
lean_object* v_unused_5165_; lean_object* v_unused_5166_; lean_object* v_unused_5167_; lean_object* v_unused_5168_; lean_object* v_unused_5169_; 
v_unused_5165_ = lean_ctor_get(v_impl_5085_, 4);
lean_dec(v_unused_5165_);
v_unused_5166_ = lean_ctor_get(v_impl_5085_, 3);
lean_dec(v_unused_5166_);
v_unused_5167_ = lean_ctor_get(v_impl_5085_, 2);
lean_dec(v_unused_5167_);
v_unused_5168_ = lean_ctor_get(v_impl_5085_, 1);
lean_dec(v_unused_5168_);
v_unused_5169_ = lean_ctor_get(v_impl_5085_, 0);
lean_dec(v_unused_5169_);
v___x_5102_ = v_impl_5085_;
v_isShared_5103_ = v_isSharedCheck_5164_;
goto v_resetjp_5101_;
}
else
{
lean_dec(v_impl_5085_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5164_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v_size_5104_; lean_object* v_k_5105_; lean_object* v_v_5106_; lean_object* v_l_5107_; lean_object* v_r_5108_; lean_object* v_size_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; uint8_t v___x_5112_; 
v_size_5104_ = lean_ctor_get(v_l_5091_, 0);
v_k_5105_ = lean_ctor_get(v_l_5091_, 1);
v_v_5106_ = lean_ctor_get(v_l_5091_, 2);
v_l_5107_ = lean_ctor_get(v_l_5091_, 3);
v_r_5108_ = lean_ctor_get(v_l_5091_, 4);
v_size_5109_ = lean_ctor_get(v_r_5092_, 0);
v___x_5110_ = lean_unsigned_to_nat(2u);
v___x_5111_ = lean_nat_mul(v___x_5110_, v_size_5109_);
v___x_5112_ = lean_nat_dec_lt(v_size_5104_, v___x_5111_);
lean_dec(v___x_5111_);
if (v___x_5112_ == 0)
{
lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5140_; 
lean_inc(v_r_5108_);
lean_inc(v_l_5107_);
lean_inc(v_v_5106_);
lean_inc(v_k_5105_);
v_isSharedCheck_5140_ = !lean_is_exclusive(v_l_5091_);
if (v_isSharedCheck_5140_ == 0)
{
lean_object* v_unused_5141_; lean_object* v_unused_5142_; lean_object* v_unused_5143_; lean_object* v_unused_5144_; lean_object* v_unused_5145_; 
v_unused_5141_ = lean_ctor_get(v_l_5091_, 4);
lean_dec(v_unused_5141_);
v_unused_5142_ = lean_ctor_get(v_l_5091_, 3);
lean_dec(v_unused_5142_);
v_unused_5143_ = lean_ctor_get(v_l_5091_, 2);
lean_dec(v_unused_5143_);
v_unused_5144_ = lean_ctor_get(v_l_5091_, 1);
lean_dec(v_unused_5144_);
v_unused_5145_ = lean_ctor_get(v_l_5091_, 0);
lean_dec(v_unused_5145_);
v___x_5114_ = v_l_5091_;
v_isShared_5115_ = v_isSharedCheck_5140_;
goto v_resetjp_5113_;
}
else
{
lean_dec(v_l_5091_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5140_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___y_5119_; lean_object* v___y_5120_; lean_object* v___y_5121_; lean_object* v___y_5130_; 
v___x_5116_ = lean_nat_add(v___x_5086_, v_size_5087_);
v___x_5117_ = lean_nat_add(v___x_5116_, v_size_5088_);
lean_dec(v_size_5088_);
if (lean_obj_tag(v_l_5107_) == 0)
{
lean_object* v_size_5138_; 
v_size_5138_ = lean_ctor_get(v_l_5107_, 0);
lean_inc(v_size_5138_);
v___y_5130_ = v_size_5138_;
goto v___jp_5129_;
}
else
{
lean_object* v___x_5139_; 
v___x_5139_ = lean_unsigned_to_nat(0u);
v___y_5130_ = v___x_5139_;
goto v___jp_5129_;
}
v___jp_5118_:
{
lean_object* v___x_5122_; lean_object* v___x_5124_; 
v___x_5122_ = lean_nat_add(v___y_5120_, v___y_5121_);
lean_dec(v___y_5121_);
lean_dec(v___y_5120_);
if (v_isShared_5115_ == 0)
{
lean_ctor_set(v___x_5114_, 4, v_r_5092_);
lean_ctor_set(v___x_5114_, 3, v_r_5108_);
lean_ctor_set(v___x_5114_, 2, v_v_5090_);
lean_ctor_set(v___x_5114_, 1, v_k_5089_);
lean_ctor_set(v___x_5114_, 0, v___x_5122_);
v___x_5124_ = v___x_5114_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v___x_5122_);
lean_ctor_set(v_reuseFailAlloc_5128_, 1, v_k_5089_);
lean_ctor_set(v_reuseFailAlloc_5128_, 2, v_v_5090_);
lean_ctor_set(v_reuseFailAlloc_5128_, 3, v_r_5108_);
lean_ctor_set(v_reuseFailAlloc_5128_, 4, v_r_5092_);
v___x_5124_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
lean_object* v___x_5126_; 
if (v_isShared_5103_ == 0)
{
lean_ctor_set(v___x_5102_, 4, v___x_5124_);
lean_ctor_set(v___x_5102_, 3, v___y_5119_);
lean_ctor_set(v___x_5102_, 2, v_v_5106_);
lean_ctor_set(v___x_5102_, 1, v_k_5105_);
lean_ctor_set(v___x_5102_, 0, v___x_5117_);
v___x_5126_ = v___x_5102_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v___x_5117_);
lean_ctor_set(v_reuseFailAlloc_5127_, 1, v_k_5105_);
lean_ctor_set(v_reuseFailAlloc_5127_, 2, v_v_5106_);
lean_ctor_set(v_reuseFailAlloc_5127_, 3, v___y_5119_);
lean_ctor_set(v_reuseFailAlloc_5127_, 4, v___x_5124_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
v___jp_5129_:
{
lean_object* v___x_5131_; lean_object* v___x_5133_; 
v___x_5131_ = lean_nat_add(v___x_5116_, v___y_5130_);
lean_dec(v___y_5130_);
lean_dec(v___x_5116_);
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 4, v_l_5107_);
lean_ctor_set(v___x_4942_, 0, v___x_5131_);
v___x_5133_ = v___x_4942_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v___x_5131_);
lean_ctor_set(v_reuseFailAlloc_5137_, 1, v_k_4937_);
lean_ctor_set(v_reuseFailAlloc_5137_, 2, v_v_4938_);
lean_ctor_set(v_reuseFailAlloc_5137_, 3, v_l_4939_);
lean_ctor_set(v_reuseFailAlloc_5137_, 4, v_l_5107_);
v___x_5133_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
lean_object* v___x_5134_; 
v___x_5134_ = lean_nat_add(v___x_5086_, v_size_5109_);
if (lean_obj_tag(v_r_5108_) == 0)
{
lean_object* v_size_5135_; 
v_size_5135_ = lean_ctor_get(v_r_5108_, 0);
lean_inc(v_size_5135_);
v___y_5119_ = v___x_5133_;
v___y_5120_ = v___x_5134_;
v___y_5121_ = v_size_5135_;
goto v___jp_5118_;
}
else
{
lean_object* v___x_5136_; 
v___x_5136_ = lean_unsigned_to_nat(0u);
v___y_5119_ = v___x_5133_;
v___y_5120_ = v___x_5134_;
v___y_5121_ = v___x_5136_;
goto v___jp_5118_;
}
}
}
}
}
else
{
lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5150_; 
lean_del_object(v___x_4942_);
v___x_5146_ = lean_nat_add(v___x_5086_, v_size_5087_);
v___x_5147_ = lean_nat_add(v___x_5146_, v_size_5088_);
lean_dec(v_size_5088_);
v___x_5148_ = lean_nat_add(v___x_5146_, v_size_5104_);
lean_dec(v___x_5146_);
lean_inc_ref(v_l_4939_);
if (v_isShared_5103_ == 0)
{
lean_ctor_set(v___x_5102_, 4, v_l_5091_);
lean_ctor_set(v___x_5102_, 3, v_l_4939_);
lean_ctor_set(v___x_5102_, 2, v_v_4938_);
lean_ctor_set(v___x_5102_, 1, v_k_4937_);
lean_ctor_set(v___x_5102_, 0, v___x_5148_);
v___x_5150_ = v___x_5102_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v___x_5148_);
lean_ctor_set(v_reuseFailAlloc_5163_, 1, v_k_4937_);
lean_ctor_set(v_reuseFailAlloc_5163_, 2, v_v_4938_);
lean_ctor_set(v_reuseFailAlloc_5163_, 3, v_l_4939_);
lean_ctor_set(v_reuseFailAlloc_5163_, 4, v_l_5091_);
v___x_5150_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5157_; 
v_isSharedCheck_5157_ = !lean_is_exclusive(v_l_4939_);
if (v_isSharedCheck_5157_ == 0)
{
lean_object* v_unused_5158_; lean_object* v_unused_5159_; lean_object* v_unused_5160_; lean_object* v_unused_5161_; lean_object* v_unused_5162_; 
v_unused_5158_ = lean_ctor_get(v_l_4939_, 4);
lean_dec(v_unused_5158_);
v_unused_5159_ = lean_ctor_get(v_l_4939_, 3);
lean_dec(v_unused_5159_);
v_unused_5160_ = lean_ctor_get(v_l_4939_, 2);
lean_dec(v_unused_5160_);
v_unused_5161_ = lean_ctor_get(v_l_4939_, 1);
lean_dec(v_unused_5161_);
v_unused_5162_ = lean_ctor_get(v_l_4939_, 0);
lean_dec(v_unused_5162_);
v___x_5152_ = v_l_4939_;
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
else
{
lean_dec(v_l_4939_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5155_; 
if (v_isShared_5153_ == 0)
{
lean_ctor_set(v___x_5152_, 4, v_r_5092_);
lean_ctor_set(v___x_5152_, 3, v___x_5150_);
lean_ctor_set(v___x_5152_, 2, v_v_5090_);
lean_ctor_set(v___x_5152_, 1, v_k_5089_);
lean_ctor_set(v___x_5152_, 0, v___x_5147_);
v___x_5155_ = v___x_5152_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5147_);
lean_ctor_set(v_reuseFailAlloc_5156_, 1, v_k_5089_);
lean_ctor_set(v_reuseFailAlloc_5156_, 2, v_v_5090_);
lean_ctor_set(v_reuseFailAlloc_5156_, 3, v___x_5150_);
lean_ctor_set(v_reuseFailAlloc_5156_, 4, v_r_5092_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5170_; 
v_l_5170_ = lean_ctor_get(v_impl_5085_, 3);
lean_inc(v_l_5170_);
if (lean_obj_tag(v_l_5170_) == 0)
{
lean_object* v_r_5171_; lean_object* v_k_5172_; lean_object* v_v_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5196_; 
v_r_5171_ = lean_ctor_get(v_impl_5085_, 4);
v_k_5172_ = lean_ctor_get(v_impl_5085_, 1);
v_v_5173_ = lean_ctor_get(v_impl_5085_, 2);
v_isSharedCheck_5196_ = !lean_is_exclusive(v_impl_5085_);
if (v_isSharedCheck_5196_ == 0)
{
lean_object* v_unused_5197_; lean_object* v_unused_5198_; 
v_unused_5197_ = lean_ctor_get(v_impl_5085_, 3);
lean_dec(v_unused_5197_);
v_unused_5198_ = lean_ctor_get(v_impl_5085_, 0);
lean_dec(v_unused_5198_);
v___x_5175_ = v_impl_5085_;
v_isShared_5176_ = v_isSharedCheck_5196_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_r_5171_);
lean_inc(v_v_5173_);
lean_inc(v_k_5172_);
lean_dec(v_impl_5085_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5196_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v_k_5177_; lean_object* v_v_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5192_; 
v_k_5177_ = lean_ctor_get(v_l_5170_, 1);
v_v_5178_ = lean_ctor_get(v_l_5170_, 2);
v_isSharedCheck_5192_ = !lean_is_exclusive(v_l_5170_);
if (v_isSharedCheck_5192_ == 0)
{
lean_object* v_unused_5193_; lean_object* v_unused_5194_; lean_object* v_unused_5195_; 
v_unused_5193_ = lean_ctor_get(v_l_5170_, 4);
lean_dec(v_unused_5193_);
v_unused_5194_ = lean_ctor_get(v_l_5170_, 3);
lean_dec(v_unused_5194_);
v_unused_5195_ = lean_ctor_get(v_l_5170_, 0);
lean_dec(v_unused_5195_);
v___x_5180_ = v_l_5170_;
v_isShared_5181_ = v_isSharedCheck_5192_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_v_5178_);
lean_inc(v_k_5177_);
lean_dec(v_l_5170_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5192_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5182_; lean_object* v___x_5184_; 
v___x_5182_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5171_, 2);
if (v_isShared_5181_ == 0)
{
lean_ctor_set(v___x_5180_, 4, v_r_5171_);
lean_ctor_set(v___x_5180_, 3, v_r_5171_);
lean_ctor_set(v___x_5180_, 2, v_v_4938_);
lean_ctor_set(v___x_5180_, 1, v_k_4937_);
lean_ctor_set(v___x_5180_, 0, v___x_5086_);
v___x_5184_ = v___x_5180_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5086_);
lean_ctor_set(v_reuseFailAlloc_5191_, 1, v_k_4937_);
lean_ctor_set(v_reuseFailAlloc_5191_, 2, v_v_4938_);
lean_ctor_set(v_reuseFailAlloc_5191_, 3, v_r_5171_);
lean_ctor_set(v_reuseFailAlloc_5191_, 4, v_r_5171_);
v___x_5184_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
lean_object* v___x_5186_; 
lean_inc(v_r_5171_);
if (v_isShared_5176_ == 0)
{
lean_ctor_set(v___x_5175_, 3, v_r_5171_);
lean_ctor_set(v___x_5175_, 0, v___x_5086_);
v___x_5186_ = v___x_5175_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v___x_5086_);
lean_ctor_set(v_reuseFailAlloc_5190_, 1, v_k_5172_);
lean_ctor_set(v_reuseFailAlloc_5190_, 2, v_v_5173_);
lean_ctor_set(v_reuseFailAlloc_5190_, 3, v_r_5171_);
lean_ctor_set(v_reuseFailAlloc_5190_, 4, v_r_5171_);
v___x_5186_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
lean_object* v___x_5188_; 
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 4, v___x_5186_);
lean_ctor_set(v___x_4942_, 3, v___x_5184_);
lean_ctor_set(v___x_4942_, 2, v_v_5178_);
lean_ctor_set(v___x_4942_, 1, v_k_5177_);
lean_ctor_set(v___x_4942_, 0, v___x_5182_);
v___x_5188_ = v___x_4942_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v___x_5182_);
lean_ctor_set(v_reuseFailAlloc_5189_, 1, v_k_5177_);
lean_ctor_set(v_reuseFailAlloc_5189_, 2, v_v_5178_);
lean_ctor_set(v_reuseFailAlloc_5189_, 3, v___x_5184_);
lean_ctor_set(v_reuseFailAlloc_5189_, 4, v___x_5186_);
v___x_5188_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
return v___x_5188_;
}
}
}
}
}
}
else
{
lean_object* v_r_5199_; 
v_r_5199_ = lean_ctor_get(v_impl_5085_, 4);
lean_inc(v_r_5199_);
if (lean_obj_tag(v_r_5199_) == 0)
{
lean_object* v_k_5200_; lean_object* v_v_5201_; lean_object* v___x_5203_; uint8_t v_isShared_5204_; uint8_t v_isSharedCheck_5212_; 
v_k_5200_ = lean_ctor_get(v_impl_5085_, 1);
v_v_5201_ = lean_ctor_get(v_impl_5085_, 2);
v_isSharedCheck_5212_ = !lean_is_exclusive(v_impl_5085_);
if (v_isSharedCheck_5212_ == 0)
{
lean_object* v_unused_5213_; lean_object* v_unused_5214_; lean_object* v_unused_5215_; 
v_unused_5213_ = lean_ctor_get(v_impl_5085_, 4);
lean_dec(v_unused_5213_);
v_unused_5214_ = lean_ctor_get(v_impl_5085_, 3);
lean_dec(v_unused_5214_);
v_unused_5215_ = lean_ctor_get(v_impl_5085_, 0);
lean_dec(v_unused_5215_);
v___x_5203_ = v_impl_5085_;
v_isShared_5204_ = v_isSharedCheck_5212_;
goto v_resetjp_5202_;
}
else
{
lean_inc(v_v_5201_);
lean_inc(v_k_5200_);
lean_dec(v_impl_5085_);
v___x_5203_ = lean_box(0);
v_isShared_5204_ = v_isSharedCheck_5212_;
goto v_resetjp_5202_;
}
v_resetjp_5202_:
{
lean_object* v___x_5205_; lean_object* v___x_5207_; 
v___x_5205_ = lean_unsigned_to_nat(3u);
if (v_isShared_5204_ == 0)
{
lean_ctor_set(v___x_5203_, 4, v_l_5170_);
lean_ctor_set(v___x_5203_, 2, v_v_4938_);
lean_ctor_set(v___x_5203_, 1, v_k_4937_);
lean_ctor_set(v___x_5203_, 0, v___x_5086_);
v___x_5207_ = v___x_5203_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v___x_5086_);
lean_ctor_set(v_reuseFailAlloc_5211_, 1, v_k_4937_);
lean_ctor_set(v_reuseFailAlloc_5211_, 2, v_v_4938_);
lean_ctor_set(v_reuseFailAlloc_5211_, 3, v_l_5170_);
lean_ctor_set(v_reuseFailAlloc_5211_, 4, v_l_5170_);
v___x_5207_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
lean_object* v___x_5209_; 
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 4, v_r_5199_);
lean_ctor_set(v___x_4942_, 3, v___x_5207_);
lean_ctor_set(v___x_4942_, 2, v_v_5201_);
lean_ctor_set(v___x_4942_, 1, v_k_5200_);
lean_ctor_set(v___x_4942_, 0, v___x_5205_);
v___x_5209_ = v___x_4942_;
goto v_reusejp_5208_;
}
else
{
lean_object* v_reuseFailAlloc_5210_; 
v_reuseFailAlloc_5210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5210_, 0, v___x_5205_);
lean_ctor_set(v_reuseFailAlloc_5210_, 1, v_k_5200_);
lean_ctor_set(v_reuseFailAlloc_5210_, 2, v_v_5201_);
lean_ctor_set(v_reuseFailAlloc_5210_, 3, v___x_5207_);
lean_ctor_set(v_reuseFailAlloc_5210_, 4, v_r_5199_);
v___x_5209_ = v_reuseFailAlloc_5210_;
goto v_reusejp_5208_;
}
v_reusejp_5208_:
{
return v___x_5209_;
}
}
}
}
else
{
lean_object* v___x_5216_; lean_object* v___x_5218_; 
v___x_5216_ = lean_unsigned_to_nat(2u);
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 4, v_impl_5085_);
lean_ctor_set(v___x_4942_, 3, v_r_5199_);
lean_ctor_set(v___x_4942_, 0, v___x_5216_);
v___x_5218_ = v___x_4942_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v___x_5216_);
lean_ctor_set(v_reuseFailAlloc_5219_, 1, v_k_4937_);
lean_ctor_set(v_reuseFailAlloc_5219_, 2, v_v_4938_);
lean_ctor_set(v_reuseFailAlloc_5219_, 3, v_r_5199_);
lean_ctor_set(v_reuseFailAlloc_5219_, 4, v_impl_5085_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
return v___x_5218_;
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
lean_object* v___x_5221_; lean_object* v___x_5222_; 
v___x_5221_ = lean_unsigned_to_nat(1u);
v___x_5222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5221_);
lean_ctor_set(v___x_5222_, 1, v_k_4933_);
lean_ctor_set(v___x_5222_, 2, v_v_4934_);
lean_ctor_set(v___x_5222_, 3, v_t_4935_);
lean_ctor_set(v___x_5222_, 4, v_t_4935_);
return v___x_5222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(lean_object* v_init_5224_, lean_object* v_x_5225_){
_start:
{
lean_object* v_d_5228_; 
if (lean_obj_tag(v_x_5225_) == 0)
{
lean_object* v_k_5231_; lean_object* v_v_5232_; lean_object* v_l_5233_; lean_object* v_r_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; 
v_k_5231_ = lean_ctor_get(v_x_5225_, 1);
v_v_5232_ = lean_ctor_get(v_x_5225_, 2);
v_l_5233_ = lean_ctor_get(v_x_5225_, 3);
v_r_5234_ = lean_ctor_get(v_x_5225_, 4);
v___x_5235_ = lean_box(0);
v___x_5236_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_5237_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v_init_5224_, v_l_5233_);
if (lean_obj_tag(v___x_5237_) == 0)
{
lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5273_; 
v_a_5238_ = lean_ctor_get(v___x_5237_, 0);
v_isSharedCheck_5273_ = !lean_is_exclusive(v___x_5237_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5240_ = v___x_5237_;
v_isShared_5241_ = v_isSharedCheck_5273_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___x_5237_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5273_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
if (lean_obj_tag(v_a_5238_) == 0)
{
lean_object* v_a_5242_; 
lean_del_object(v___x_5240_);
v_a_5242_ = lean_ctor_get(v_a_5238_, 0);
lean_inc(v_a_5242_);
lean_dec_ref_known(v_a_5238_, 1);
v_d_5228_ = v_a_5242_;
goto v___jp_5227_;
}
else
{
lean_object* v___x_5244_; uint8_t v_isShared_5245_; uint8_t v_isSharedCheck_5271_; 
v_isSharedCheck_5271_ = !lean_is_exclusive(v_a_5238_);
if (v_isSharedCheck_5271_ == 0)
{
lean_object* v_unused_5272_; 
v_unused_5272_ = lean_ctor_get(v_a_5238_, 0);
lean_dec(v_unused_5272_);
v___x_5244_ = v_a_5238_;
v_isShared_5245_ = v_isSharedCheck_5271_;
goto v_resetjp_5243_;
}
else
{
lean_dec(v_a_5238_);
v___x_5244_ = lean_box(0);
v_isShared_5245_ = v_isSharedCheck_5271_;
goto v_resetjp_5243_;
}
v_resetjp_5243_:
{
lean_object* v___x_5246_; lean_object* v___x_5247_; uint8_t v___x_5248_; 
v___x_5246_ = lean_array_get_size(v_v_5232_);
v___x_5247_ = lean_unsigned_to_nat(0u);
v___x_5248_ = lean_nat_dec_eq(v___x_5246_, v___x_5247_);
if (v___x_5248_ == 0)
{
lean_del_object(v___x_5244_);
lean_del_object(v___x_5240_);
v_init_5224_ = v___x_5236_;
v_x_5225_ = v_r_5234_;
goto _start;
}
else
{
lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; 
v___x_5250_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1));
v___x_5251_ = lean_string_append(v___x_5250_, v_k_5231_);
v___x_5252_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___closed__0));
v___x_5253_ = lean_string_append(v___x_5251_, v___x_5252_);
v___x_5254_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5253_);
lean_dec_ref(v___x_5253_);
if (lean_obj_tag(v___x_5254_) == 0)
{
lean_object* v_a_5255_; lean_object* v___x_5257_; 
v_a_5255_ = lean_ctor_get(v___x_5254_, 0);
lean_inc(v_a_5255_);
lean_dec_ref_known(v___x_5254_, 1);
if (v_isShared_5245_ == 0)
{
lean_ctor_set_tag(v___x_5244_, 0);
lean_ctor_set(v___x_5244_, 0, v_a_5255_);
v___x_5257_ = v___x_5244_;
goto v_reusejp_5256_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5255_);
v___x_5257_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5256_;
}
v_reusejp_5256_:
{
lean_object* v___x_5259_; 
if (v_isShared_5241_ == 0)
{
lean_ctor_set_tag(v___x_5240_, 1);
lean_ctor_set(v___x_5240_, 0, v___x_5257_);
v___x_5259_ = v___x_5240_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v___x_5257_);
v___x_5259_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
lean_object* v___x_5260_; 
v___x_5260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5260_, 0, v___x_5259_);
lean_ctor_set(v___x_5260_, 1, v___x_5235_);
v_d_5228_ = v___x_5260_;
goto v___jp_5227_;
}
}
}
else
{
lean_object* v_a_5263_; lean_object* v___x_5265_; uint8_t v_isShared_5266_; uint8_t v_isSharedCheck_5270_; 
lean_del_object(v___x_5244_);
lean_del_object(v___x_5240_);
v_a_5263_ = lean_ctor_get(v___x_5254_, 0);
v_isSharedCheck_5270_ = !lean_is_exclusive(v___x_5254_);
if (v_isSharedCheck_5270_ == 0)
{
v___x_5265_ = v___x_5254_;
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
else
{
lean_inc(v_a_5263_);
lean_dec(v___x_5254_);
v___x_5265_ = lean_box(0);
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
v_resetjp_5264_:
{
lean_object* v___x_5268_; 
if (v_isShared_5266_ == 0)
{
v___x_5268_ = v___x_5265_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v_a_5263_);
v___x_5268_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
return v___x_5268_;
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
return v___x_5237_;
}
}
else
{
lean_object* v___x_5274_; lean_object* v___x_5275_; 
v___x_5274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5274_, 0, v_init_5224_);
v___x_5275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5275_, 0, v___x_5274_);
return v___x_5275_;
}
v___jp_5227_:
{
lean_object* v___x_5229_; lean_object* v___x_5230_; 
v___x_5229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5229_, 0, v_d_5228_);
v___x_5230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5230_, 0, v___x_5229_);
return v___x_5230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___boxed(lean_object* v_init_5276_, lean_object* v_x_5277_, lean_object* v___y_5278_){
_start:
{
lean_object* v_res_5279_; 
v_res_5279_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v_init_5276_, v_x_5277_);
lean_dec(v_x_5277_);
return v_res_5279_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(lean_object* v_cfg_5285_){
_start:
{
lean_object* v___y_5288_; lean_object* v_a_5289_; lean_object* v___y_5302_; lean_object* v_externalKernels_5303_; lean_object* v___y_5316_; uint8_t v___y_5317_; lean_object* v___y_5318_; lean_object* v_a_5319_; uint8_t v___y_5333_; lean_object* v___y_5334_; lean_object* v_enable__nanoda_x3f_5347_; lean_object* v_external__kernels_x3f_5348_; lean_object* v___y_5350_; 
v_enable__nanoda_x3f_5347_ = lean_ctor_get(v_cfg_5285_, 5);
lean_inc(v_enable__nanoda_x3f_5347_);
v_external__kernels_x3f_5348_ = lean_ctor_get(v_cfg_5285_, 6);
lean_inc(v_external__kernels_x3f_5348_);
lean_dec_ref(v_cfg_5285_);
if (lean_obj_tag(v_external__kernels_x3f_5348_) == 0)
{
lean_object* v___x_5381_; 
v___x_5381_ = lean_box(1);
v___y_5350_ = v___x_5381_;
goto v___jp_5349_;
}
else
{
lean_object* v_val_5382_; 
v_val_5382_ = lean_ctor_get(v_external__kernels_x3f_5348_, 0);
lean_inc(v_val_5382_);
lean_dec_ref_known(v_external__kernels_x3f_5348_, 1);
v___y_5350_ = v_val_5382_;
goto v___jp_5349_;
}
v___jp_5287_:
{
lean_object* v_fst_5290_; 
v_fst_5290_ = lean_ctor_get(v_a_5289_, 0);
lean_inc(v_fst_5290_);
lean_dec_ref(v_a_5289_);
if (lean_obj_tag(v_fst_5290_) == 0)
{
lean_object* v___x_5291_; lean_object* v___x_5292_; 
v___x_5291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5291_, 0, v___y_5288_);
v___x_5292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5292_, 0, v___x_5291_);
return v___x_5292_;
}
else
{
lean_object* v_val_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5300_; 
lean_dec(v___y_5288_);
v_val_5293_ = lean_ctor_get(v_fst_5290_, 0);
v_isSharedCheck_5300_ = !lean_is_exclusive(v_fst_5290_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5295_ = v_fst_5290_;
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_val_5293_);
lean_dec(v_fst_5290_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5298_; 
if (v_isShared_5296_ == 0)
{
lean_ctor_set_tag(v___x_5295_, 0);
v___x_5298_ = v___x_5295_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_val_5293_);
v___x_5298_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
return v___x_5298_;
}
}
}
}
v___jp_5301_:
{
lean_object* v___x_5304_; 
v___x_5304_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v___y_5302_, v_externalKernels_5303_);
if (lean_obj_tag(v___x_5304_) == 0)
{
lean_object* v_a_5305_; lean_object* v_a_5306_; 
v_a_5305_ = lean_ctor_get(v___x_5304_, 0);
lean_inc(v_a_5305_);
lean_dec_ref_known(v___x_5304_, 1);
v_a_5306_ = lean_ctor_get(v_a_5305_, 0);
lean_inc(v_a_5306_);
lean_dec(v_a_5305_);
v___y_5288_ = v_externalKernels_5303_;
v_a_5289_ = v_a_5306_;
goto v___jp_5287_;
}
else
{
lean_object* v_a_5307_; lean_object* v___x_5309_; uint8_t v_isShared_5310_; uint8_t v_isSharedCheck_5314_; 
lean_dec(v_externalKernels_5303_);
v_a_5307_ = lean_ctor_get(v___x_5304_, 0);
v_isSharedCheck_5314_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5314_ == 0)
{
v___x_5309_ = v___x_5304_;
v_isShared_5310_ = v_isSharedCheck_5314_;
goto v_resetjp_5308_;
}
else
{
lean_inc(v_a_5307_);
lean_dec(v___x_5304_);
v___x_5309_ = lean_box(0);
v_isShared_5310_ = v_isSharedCheck_5314_;
goto v_resetjp_5308_;
}
v_resetjp_5308_:
{
lean_object* v___x_5312_; 
if (v_isShared_5310_ == 0)
{
v___x_5312_ = v___x_5309_;
goto v_reusejp_5311_;
}
else
{
lean_object* v_reuseFailAlloc_5313_; 
v_reuseFailAlloc_5313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5313_, 0, v_a_5307_);
v___x_5312_ = v_reuseFailAlloc_5313_;
goto v_reusejp_5311_;
}
v_reusejp_5311_:
{
return v___x_5312_;
}
}
}
}
v___jp_5315_:
{
lean_object* v_fst_5320_; 
v_fst_5320_ = lean_ctor_get(v_a_5319_, 0);
lean_inc(v_fst_5320_);
lean_dec_ref(v_a_5319_);
if (lean_obj_tag(v_fst_5320_) == 0)
{
if (v___y_5317_ == 0)
{
v___y_5302_ = v___y_5318_;
v_externalKernels_5303_ = v___y_5316_;
goto v___jp_5301_;
}
else
{
lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; 
v___x_5321_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__4));
v___x_5322_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0));
v___x_5323_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v___x_5321_, v___x_5322_, v___y_5316_);
v___y_5302_ = v___y_5318_;
v_externalKernels_5303_ = v___x_5323_;
goto v___jp_5301_;
}
}
else
{
lean_object* v_val_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5331_; 
lean_dec_ref(v___y_5318_);
lean_dec(v___y_5316_);
v_val_5324_ = lean_ctor_get(v_fst_5320_, 0);
v_isSharedCheck_5331_ = !lean_is_exclusive(v_fst_5320_);
if (v_isSharedCheck_5331_ == 0)
{
v___x_5326_ = v_fst_5320_;
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_val_5324_);
lean_dec(v_fst_5320_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v___x_5329_; 
if (v_isShared_5327_ == 0)
{
lean_ctor_set_tag(v___x_5326_, 0);
v___x_5329_ = v___x_5326_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_val_5324_);
v___x_5329_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
return v___x_5329_;
}
}
}
}
v___jp_5332_:
{
lean_object* v___x_5335_; lean_object* v___x_5336_; 
v___x_5335_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_5336_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v___x_5335_, v___y_5334_);
if (lean_obj_tag(v___x_5336_) == 0)
{
lean_object* v_a_5337_; lean_object* v_a_5338_; 
v_a_5337_ = lean_ctor_get(v___x_5336_, 0);
lean_inc(v_a_5337_);
lean_dec_ref_known(v___x_5336_, 1);
v_a_5338_ = lean_ctor_get(v_a_5337_, 0);
lean_inc(v_a_5338_);
lean_dec(v_a_5337_);
v___y_5316_ = v___y_5334_;
v___y_5317_ = v___y_5333_;
v___y_5318_ = v___x_5335_;
v_a_5319_ = v_a_5338_;
goto v___jp_5315_;
}
else
{
lean_object* v_a_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5346_; 
lean_dec(v___y_5334_);
v_a_5339_ = lean_ctor_get(v___x_5336_, 0);
v_isSharedCheck_5346_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5341_ = v___x_5336_;
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_a_5339_);
lean_dec(v___x_5336_);
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
v___jp_5349_:
{
if (lean_obj_tag(v_enable__nanoda_x3f_5347_) == 0)
{
uint8_t v___x_5351_; 
v___x_5351_ = 0;
v___y_5333_ = v___x_5351_;
v___y_5334_ = v___y_5350_;
goto v___jp_5332_;
}
else
{
lean_object* v_val_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5380_; 
v_val_5352_ = lean_ctor_get(v_enable__nanoda_x3f_5347_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v_enable__nanoda_x3f_5347_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5354_ = v_enable__nanoda_x3f_5347_;
v_isShared_5355_ = v_isSharedCheck_5380_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_val_5352_);
lean_dec(v_enable__nanoda_x3f_5347_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5380_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
uint8_t v___x_5356_; 
v___x_5356_ = lean_unbox(v_val_5352_);
if (v___x_5356_ == 0)
{
uint8_t v___x_5357_; 
lean_del_object(v___x_5354_);
v___x_5357_ = lean_unbox(v_val_5352_);
lean_dec(v_val_5352_);
v___y_5333_ = v___x_5357_;
v___y_5334_ = v___y_5350_;
goto v___jp_5332_;
}
else
{
if (lean_obj_tag(v___y_5350_) == 0)
{
lean_object* v___x_5358_; lean_object* v___x_5359_; 
lean_dec_ref_known(v___y_5350_, 5);
lean_dec(v_val_5352_);
v___x_5358_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__1));
v___x_5359_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5358_);
if (lean_obj_tag(v___x_5359_) == 0)
{
lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5370_; 
v_a_5360_ = lean_ctor_get(v___x_5359_, 0);
v_isSharedCheck_5370_ = !lean_is_exclusive(v___x_5359_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5362_ = v___x_5359_;
v_isShared_5363_ = v_isSharedCheck_5370_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5359_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5370_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5365_; 
if (v_isShared_5355_ == 0)
{
lean_ctor_set_tag(v___x_5354_, 0);
lean_ctor_set(v___x_5354_, 0, v_a_5360_);
v___x_5365_ = v___x_5354_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_a_5360_);
v___x_5365_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
lean_object* v___x_5367_; 
if (v_isShared_5363_ == 0)
{
lean_ctor_set(v___x_5362_, 0, v___x_5365_);
v___x_5367_ = v___x_5362_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v___x_5365_);
v___x_5367_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
return v___x_5367_;
}
}
}
}
else
{
lean_object* v_a_5371_; lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5378_; 
lean_del_object(v___x_5354_);
v_a_5371_ = lean_ctor_get(v___x_5359_, 0);
v_isSharedCheck_5378_ = !lean_is_exclusive(v___x_5359_);
if (v_isSharedCheck_5378_ == 0)
{
v___x_5373_ = v___x_5359_;
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
else
{
lean_inc(v_a_5371_);
lean_dec(v___x_5359_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v___x_5376_; 
if (v_isShared_5374_ == 0)
{
v___x_5376_ = v___x_5373_;
goto v_reusejp_5375_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_a_5371_);
v___x_5376_ = v_reuseFailAlloc_5377_;
goto v_reusejp_5375_;
}
v_reusejp_5375_:
{
return v___x_5376_;
}
}
}
}
else
{
uint8_t v___x_5379_; 
lean_del_object(v___x_5354_);
v___x_5379_ = lean_unbox(v_val_5352_);
lean_dec(v_val_5352_);
v___y_5333_ = v___x_5379_;
v___y_5334_ = v___y_5350_;
goto v___jp_5332_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___boxed(lean_object* v_cfg_5383_, lean_object* v_a_5384_){
_start:
{
lean_object* v_res_5385_; 
v_res_5385_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v_cfg_5383_);
return v_res_5385_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(lean_object* v_00_u03b2_5386_, lean_object* v_k_5387_, lean_object* v_v_5388_, lean_object* v_t_5389_, lean_object* v_hl_5390_){
_start:
{
lean_object* v___x_5391_; 
v___x_5391_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_5387_, v_v_5388_, v_t_5389_);
return v___x_5391_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(lean_object* v_a_5409_, lean_object* v_a_5410_){
_start:
{
if (lean_obj_tag(v_a_5409_) == 0)
{
lean_object* v___x_5411_; 
v___x_5411_ = l_List_reverse___redArg(v_a_5410_);
return v___x_5411_;
}
else
{
lean_object* v_head_5412_; lean_object* v_tail_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5424_; 
v_head_5412_ = lean_ctor_get(v_a_5409_, 0);
v_tail_5413_ = lean_ctor_get(v_a_5409_, 1);
v_isSharedCheck_5424_ = !lean_is_exclusive(v_a_5409_);
if (v_isSharedCheck_5424_ == 0)
{
v___x_5415_ = v_a_5409_;
v_isShared_5416_ = v_isSharedCheck_5424_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_tail_5413_);
lean_inc(v_head_5412_);
lean_dec(v_a_5409_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5424_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
lean_object* v_fst_5417_; uint8_t v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5421_; 
v_fst_5417_ = lean_ctor_get(v_head_5412_, 0);
lean_inc(v_fst_5417_);
lean_dec(v_head_5412_);
v___x_5418_ = 1;
v___x_5419_ = l_Lean_Name_toString(v_fst_5417_, v___x_5418_);
if (v_isShared_5416_ == 0)
{
lean_ctor_set(v___x_5415_, 1, v_a_5410_);
lean_ctor_set(v___x_5415_, 0, v___x_5419_);
v___x_5421_ = v___x_5415_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v___x_5419_);
lean_ctor_set(v_reuseFailAlloc_5423_, 1, v_a_5410_);
v___x_5421_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
v_a_5409_ = v_tail_5413_;
v_a_5410_ = v___x_5421_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(lean_object* v_as_5425_, size_t v_i_5426_, size_t v_stop_5427_, lean_object* v_b_5428_){
_start:
{
lean_object* v___y_5430_; uint8_t v___x_5434_; 
v___x_5434_ = lean_usize_dec_eq(v_i_5426_, v_stop_5427_);
if (v___x_5434_ == 0)
{
lean_object* v___x_5435_; lean_object* v_fst_5436_; lean_object* v___x_5437_; uint8_t v___x_5438_; 
v___x_5435_ = lean_array_uget_borrowed(v_as_5425_, v_i_5426_);
v_fst_5436_ = lean_ctor_get(v___x_5435_, 0);
v___x_5437_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms));
v___x_5438_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v___x_5437_, v_fst_5436_);
if (v___x_5438_ == 0)
{
lean_object* v___x_5439_; 
lean_inc(v___x_5435_);
v___x_5439_ = lean_array_push(v_b_5428_, v___x_5435_);
v___y_5430_ = v___x_5439_;
goto v___jp_5429_;
}
else
{
v___y_5430_ = v_b_5428_;
goto v___jp_5429_;
}
}
else
{
return v_b_5428_;
}
v___jp_5429_:
{
size_t v___x_5431_; size_t v___x_5432_; 
v___x_5431_ = ((size_t)1ULL);
v___x_5432_ = lean_usize_add(v_i_5426_, v___x_5431_);
v_i_5426_ = v___x_5432_;
v_b_5428_ = v___y_5430_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1___boxed(lean_object* v_as_5440_, lean_object* v_i_5441_, lean_object* v_stop_5442_, lean_object* v_b_5443_){
_start:
{
size_t v_i_boxed_5444_; size_t v_stop_boxed_5445_; lean_object* v_res_5446_; 
v_i_boxed_5444_ = lean_unbox_usize(v_i_5441_);
lean_dec(v_i_5441_);
v_stop_boxed_5445_ = lean_unbox_usize(v_stop_5442_);
lean_dec(v_stop_5442_);
v_res_5446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_as_5440_, v_i_boxed_5444_, v_stop_boxed_5445_, v_b_5443_);
lean_dec_ref(v_as_5440_);
return v_res_5446_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(lean_object* v_a_5449_, lean_object* v_a_5450_){
_start:
{
if (lean_obj_tag(v_a_5449_) == 0)
{
lean_object* v___x_5451_; 
v___x_5451_ = l_List_reverse___redArg(v_a_5450_);
return v___x_5451_;
}
else
{
lean_object* v_head_5452_; lean_object* v_tail_5453_; lean_object* v___x_5455_; uint8_t v_isShared_5456_; uint8_t v_isSharedCheck_5473_; 
v_head_5452_ = lean_ctor_get(v_a_5449_, 0);
v_tail_5453_ = lean_ctor_get(v_a_5449_, 1);
v_isSharedCheck_5473_ = !lean_is_exclusive(v_a_5449_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5455_ = v_a_5449_;
v_isShared_5456_ = v_isSharedCheck_5473_;
goto v_resetjp_5454_;
}
else
{
lean_inc(v_tail_5453_);
lean_inc(v_head_5452_);
lean_dec(v_a_5449_);
v___x_5455_ = lean_box(0);
v_isShared_5456_ = v_isSharedCheck_5473_;
goto v_resetjp_5454_;
}
v_resetjp_5454_:
{
lean_object* v_fst_5457_; lean_object* v_snd_5458_; lean_object* v___x_5459_; uint8_t v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5470_; 
v_fst_5457_ = lean_ctor_get(v_head_5452_, 0);
lean_inc(v_fst_5457_);
v_snd_5458_ = lean_ctor_get(v_head_5452_, 1);
lean_inc(v_snd_5458_);
lean_dec(v_head_5452_);
v___x_5459_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__0));
v___x_5460_ = 1;
v___x_5461_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_5457_, v___x_5460_);
v___x_5462_ = lean_string_append(v___x_5459_, v___x_5461_);
lean_dec_ref(v___x_5461_);
v___x_5463_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__1));
v___x_5464_ = lean_string_append(v___x_5462_, v___x_5463_);
v___x_5465_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_snd_5458_, v___x_5460_);
v___x_5466_ = lean_string_append(v___x_5464_, v___x_5465_);
lean_dec_ref(v___x_5465_);
v___x_5467_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_5468_ = lean_string_append(v___x_5466_, v___x_5467_);
if (v_isShared_5456_ == 0)
{
lean_ctor_set(v___x_5455_, 1, v_a_5450_);
lean_ctor_set(v___x_5455_, 0, v___x_5468_);
v___x_5470_ = v___x_5455_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v___x_5468_);
lean_ctor_set(v_reuseFailAlloc_5472_, 1, v_a_5450_);
v___x_5470_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
v_a_5449_ = v_tail_5453_;
v_a_5450_ = v___x_5470_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(lean_object* v_exported_5479_){
_start:
{
lean_object* v___y_5482_; lean_object* v_used_5495_; lean_object* v___x_5504_; lean_object* v___x_5505_; uint8_t v___x_5506_; 
v_used_5495_ = l_Lake_Check_usedAxioms(v_exported_5479_);
v___x_5504_ = lean_array_get_size(v_used_5495_);
v___x_5505_ = lean_unsigned_to_nat(0u);
v___x_5506_ = lean_nat_dec_eq(v___x_5504_, v___x_5505_);
if (v___x_5506_ == 0)
{
lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; 
v___x_5507_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__2));
v___x_5508_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0));
lean_inc_ref(v_used_5495_);
v___x_5509_ = lean_array_to_list(v_used_5495_);
v___x_5510_ = lean_box(0);
v___x_5511_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(v___x_5509_, v___x_5510_);
v___x_5512_ = l_String_intercalate(v___x_5508_, v___x_5511_);
v___x_5513_ = lean_string_append(v___x_5507_, v___x_5512_);
lean_dec_ref(v___x_5512_);
v___x_5514_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_5513_);
if (lean_obj_tag(v___x_5514_) == 0)
{
lean_dec_ref_known(v___x_5514_, 1);
goto v___jp_5496_;
}
else
{
lean_dec_ref(v_used_5495_);
return v___x_5514_;
}
}
else
{
lean_object* v___x_5515_; lean_object* v___x_5516_; 
v___x_5515_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__3));
v___x_5516_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_5515_);
if (lean_obj_tag(v___x_5516_) == 0)
{
lean_dec_ref_known(v___x_5516_, 1);
goto v___jp_5496_;
}
else
{
lean_dec_ref(v_used_5495_);
return v___x_5516_;
}
}
v___jp_5481_:
{
lean_object* v___x_5483_; lean_object* v___x_5484_; uint8_t v___x_5485_; 
v___x_5483_ = lean_array_get_size(v___y_5482_);
v___x_5484_ = lean_unsigned_to_nat(0u);
v___x_5485_ = lean_nat_dec_eq(v___x_5483_, v___x_5484_);
if (v___x_5485_ == 0)
{
lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; 
v___x_5486_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__0));
v___x_5487_ = lean_array_to_list(v___y_5482_);
v___x_5488_ = lean_box(0);
v___x_5489_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(v___x_5487_, v___x_5488_);
v___x_5490_ = l_String_intercalate(v___x_5486_, v___x_5489_);
v___x_5491_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_5491_, 0, v___x_5490_);
v___x_5492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5492_, 0, v___x_5491_);
return v___x_5492_;
}
else
{
lean_object* v___x_5493_; lean_object* v___x_5494_; 
lean_dec_ref(v___y_5482_);
v___x_5493_ = lean_box(0);
v___x_5494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5494_, 0, v___x_5493_);
return v___x_5494_;
}
}
v___jp_5496_:
{
lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; uint8_t v___x_5500_; 
v___x_5497_ = lean_unsigned_to_nat(0u);
v___x_5498_ = lean_array_get_size(v_used_5495_);
v___x_5499_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__1));
v___x_5500_ = lean_nat_dec_lt(v___x_5497_, v___x_5498_);
if (v___x_5500_ == 0)
{
lean_dec_ref(v_used_5495_);
v___y_5482_ = v___x_5499_;
goto v___jp_5481_;
}
else
{
size_t v___x_5501_; size_t v___x_5502_; lean_object* v___x_5503_; 
v___x_5501_ = ((size_t)0ULL);
v___x_5502_ = lean_usize_of_nat(v___x_5498_);
v___x_5503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_used_5495_, v___x_5501_, v___x_5502_, v___x_5499_);
lean_dec_ref(v_used_5495_);
v___y_5482_ = v___x_5503_;
goto v___jp_5481_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___boxed(lean_object* v_exported_5517_, lean_object* v_a_5518_){
_start:
{
lean_object* v_res_5519_; 
v_res_5519_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_5517_);
return v_res_5519_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(lean_object* v_exported_5520_, lean_object* v_a_5521_){
_start:
{
lean_object* v___x_5523_; 
v___x_5523_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_5520_);
return v___x_5523_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___boxed(lean_object* v_exported_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_){
_start:
{
lean_object* v_res_5527_; 
v_res_5527_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(v_exported_5524_, v_a_5525_);
lean_dec_ref(v_a_5525_);
return v_res_5527_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(lean_object* v_exportPath_5528_, lean_object* v___y_5529_){
_start:
{
lean_object* v___x_5531_; 
lean_inc_ref(v_exportPath_5528_);
v___x_5531_ = l___private_Lake_CLI_Check_0__Lake_Check_runKernels(v_exportPath_5528_, v___y_5529_);
if (lean_obj_tag(v___x_5531_) == 0)
{
uint8_t v___x_5532_; lean_object* v___x_5533_; 
lean_dec_ref_known(v___x_5531_, 1);
v___x_5532_ = 0;
v___x_5533_ = lean_io_prim_handle_mk(v_exportPath_5528_, v___x_5532_);
lean_dec_ref(v_exportPath_5528_);
if (lean_obj_tag(v___x_5533_) == 0)
{
lean_object* v_a_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; 
v_a_5534_ = lean_ctor_get(v___x_5533_, 0);
lean_inc(v_a_5534_);
lean_dec_ref_known(v___x_5533_, 1);
v___x_5535_ = lean_stream_of_handle(v_a_5534_);
v___x_5536_ = l_LeanExport_parseStream(v___x_5535_);
if (lean_obj_tag(v___x_5536_) == 0)
{
lean_object* v_a_5537_; lean_object* v___x_5538_; 
v_a_5537_ = lean_ctor_get(v___x_5536_, 0);
lean_inc(v_a_5537_);
lean_dec_ref_known(v___x_5536_, 1);
v___x_5538_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_a_5537_);
return v___x_5538_;
}
else
{
lean_object* v_a_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5546_; 
v_a_5539_ = lean_ctor_get(v___x_5536_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5541_ = v___x_5536_;
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_a_5539_);
lean_dec(v___x_5536_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v___x_5544_; 
if (v_isShared_5542_ == 0)
{
v___x_5544_ = v___x_5541_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_a_5539_);
v___x_5544_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
return v___x_5544_;
}
}
}
}
else
{
lean_object* v_a_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5554_; 
v_a_5547_ = lean_ctor_get(v___x_5533_, 0);
v_isSharedCheck_5554_ = !lean_is_exclusive(v___x_5533_);
if (v_isSharedCheck_5554_ == 0)
{
v___x_5549_ = v___x_5533_;
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_a_5547_);
lean_dec(v___x_5533_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v___x_5552_; 
if (v_isShared_5550_ == 0)
{
v___x_5552_ = v___x_5549_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_a_5547_);
v___x_5552_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
return v___x_5552_;
}
}
}
}
else
{
lean_dec_ref(v_exportPath_5528_);
return v___x_5531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0___boxed(lean_object* v_exportPath_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_){
_start:
{
lean_object* v_res_5558_; 
v_res_5558_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(v_exportPath_5555_, v___y_5556_);
lean_dec_ref(v___y_5556_);
return v_res_5558_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(lean_object* v_m_5559_, uint8_t v_a_5560_){
_start:
{
lean_object* v_buckets_5561_; lean_object* v___x_5562_; uint64_t v___x_5563_; uint64_t v___x_5564_; uint64_t v___x_5565_; uint64_t v_fold_5566_; uint64_t v___x_5567_; uint64_t v___x_5568_; uint64_t v___x_5569_; size_t v___x_5570_; size_t v___x_5571_; size_t v___x_5572_; size_t v___x_5573_; size_t v___x_5574_; lean_object* v___x_5575_; uint8_t v___x_5576_; 
v_buckets_5561_ = lean_ctor_get(v_m_5559_, 1);
v___x_5562_ = lean_array_get_size(v_buckets_5561_);
v___x_5563_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_a_5560_);
v___x_5564_ = 32ULL;
v___x_5565_ = lean_uint64_shift_right(v___x_5563_, v___x_5564_);
v_fold_5566_ = lean_uint64_xor(v___x_5563_, v___x_5565_);
v___x_5567_ = 16ULL;
v___x_5568_ = lean_uint64_shift_right(v_fold_5566_, v___x_5567_);
v___x_5569_ = lean_uint64_xor(v_fold_5566_, v___x_5568_);
v___x_5570_ = lean_uint64_to_usize(v___x_5569_);
v___x_5571_ = lean_usize_of_nat(v___x_5562_);
v___x_5572_ = ((size_t)1ULL);
v___x_5573_ = lean_usize_sub(v___x_5571_, v___x_5572_);
v___x_5574_ = lean_usize_land(v___x_5570_, v___x_5573_);
v___x_5575_ = lean_array_uget_borrowed(v_buckets_5561_, v___x_5574_);
v___x_5576_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_5560_, v___x_5575_);
return v___x_5576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg___boxed(lean_object* v_m_5577_, lean_object* v_a_5578_){
_start:
{
uint8_t v_a_boxed_5579_; uint8_t v_res_5580_; lean_object* v_r_5581_; 
v_a_boxed_5579_ = lean_unbox(v_a_5578_);
v_res_5580_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_m_5577_, v_a_boxed_5579_);
lean_dec_ref(v_m_5577_);
v_r_5581_ = lean_box(v_res_5580_);
return v_r_5581_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject(lean_object* v_a_5583_){
_start:
{
lean_object* v_moduleStore_5585_; lean_object* v___f_5586_; uint8_t v___x_5587_; uint8_t v___x_5588_; 
v_moduleStore_5585_ = lean_ctor_get(v_a_5583_, 17);
v___f_5586_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkProject___closed__0));
v___x_5587_ = 0;
v___x_5588_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_moduleStore_5585_, v___x_5587_);
if (v___x_5588_ == 0)
{
lean_object* v___x_5589_; 
v___x_5589_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_5583_);
if (lean_obj_tag(v___x_5589_) == 0)
{
lean_object* v___x_5590_; 
lean_dec_ref_known(v___x_5589_, 1);
v___x_5590_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v___f_5586_, v_a_5583_);
return v___x_5590_;
}
else
{
return v___x_5589_;
}
}
else
{
lean_object* v___x_5591_; 
v___x_5591_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v___f_5586_, v_a_5583_);
return v___x_5591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___boxed(lean_object* v_a_5592_, lean_object* v_a_5593_){
_start:
{
lean_object* v_res_5594_; 
v_res_5594_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v_a_5592_);
lean_dec_ref(v_a_5592_);
return v_res_5594_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0(lean_object* v_00_u03b2_5595_, lean_object* v_m_5596_, uint8_t v_a_5597_){
_start:
{
uint8_t v___x_5598_; 
v___x_5598_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_m_5596_, v_a_5597_);
return v___x_5598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___boxed(lean_object* v_00_u03b2_5599_, lean_object* v_m_5600_, lean_object* v_a_5601_){
_start:
{
uint8_t v_a_boxed_5602_; uint8_t v_res_5603_; lean_object* v_r_5604_; 
v_a_boxed_5602_ = lean_unbox(v_a_5601_);
v_res_5603_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0(v_00_u03b2_5599_, v_m_5600_, v_a_boxed_5602_);
lean_dec_ref(v_m_5600_);
v_r_5604_ = lean_box(v_res_5603_);
return v_r_5604_;
}
}
static lean_object* _init_l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_5605_; lean_object* v___x_5606_; 
v___x_5605_ = 0;
v___x_5606_ = lean_box_uint32(v___x_5605_);
return v___x_5606_;
}
}
static lean_object* _init_l_Lake_Check_runComparator___lam__0___closed__0(void){
_start:
{
lean_object* v___x_5607_; lean_object* v___x_5608_; 
v___x_5607_ = l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1;
v___x_5608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5608_, 0, v___x_5607_);
return v___x_5608_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___lam__0(lean_object* v_____r_5609_){
_start:
{
lean_object* v___x_5611_; lean_object* v___x_5612_; 
v___x_5611_ = lean_obj_once(&l_Lake_Check_runComparator___lam__0___closed__0, &l_Lake_Check_runComparator___lam__0___closed__0_once, _init_l_Lake_Check_runComparator___lam__0___closed__0);
v___x_5612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5612_, 0, v___x_5611_);
return v___x_5612_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___lam__0___boxed(lean_object* v_____r_5613_, lean_object* v___y_5614_){
_start:
{
lean_object* v_res_5615_; 
v_res_5615_ = l_Lake_Check_runComparator___lam__0(v_____r_5613_);
return v_res_5615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(size_t v_sz_5616_, size_t v_i_5617_, lean_object* v_bs_5618_){
_start:
{
uint8_t v___x_5619_; 
v___x_5619_ = lean_usize_dec_lt(v_i_5617_, v_sz_5616_);
if (v___x_5619_ == 0)
{
return v_bs_5618_;
}
else
{
lean_object* v_v_5620_; lean_object* v___x_5621_; lean_object* v_bs_x27_5622_; lean_object* v___x_5623_; size_t v___x_5624_; size_t v___x_5625_; lean_object* v___x_5626_; 
v_v_5620_ = lean_array_uget(v_bs_5618_, v_i_5617_);
v___x_5621_ = lean_unsigned_to_nat(0u);
v_bs_x27_5622_ = lean_array_uset(v_bs_5618_, v_i_5617_, v___x_5621_);
v___x_5623_ = l_String_toName(v_v_5620_);
v___x_5624_ = ((size_t)1ULL);
v___x_5625_ = lean_usize_add(v_i_5617_, v___x_5624_);
v___x_5626_ = lean_array_uset(v_bs_x27_5622_, v_i_5617_, v___x_5623_);
v_i_5617_ = v___x_5625_;
v_bs_5618_ = v___x_5626_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0___boxed(lean_object* v_sz_5628_, lean_object* v_i_5629_, lean_object* v_bs_5630_){
_start:
{
size_t v_sz_boxed_5631_; size_t v_i_boxed_5632_; lean_object* v_res_5633_; 
v_sz_boxed_5631_ = lean_unbox_usize(v_sz_5628_);
lean_dec(v_sz_5628_);
v_i_boxed_5632_ = lean_unbox_usize(v_i_5629_);
lean_dec(v_i_5629_);
v_res_5633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_boxed_5631_, v_i_boxed_5632_, v_bs_5630_);
return v_res_5633_;
}
}
static lean_object* _init_l_Lake_Check_runComparator___boxed__const__1(void){
_start:
{
uint32_t v___x_5642_; lean_object* v___x_5643_; 
v___x_5642_ = 1;
v___x_5643_ = lean_box_uint32(v___x_5642_);
return v___x_5643_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator(lean_object* v_configFile_x3f_5644_, lean_object* v_challengeFromExport_x3f_5645_, lean_object* v_solutionFromExport_x3f_5646_, uint8_t v_paranoid_5647_, uint8_t v_inadvisablyNoSandbox_5648_, lean_object* v_lean_5649_, lean_object* v_lake_5650_, lean_object* v_projectDir_5651_){
_start:
{
lean_object* v___y_5654_; lean_object* v_a_5655_; lean_object* v_a_5663_; lean_object* v___y_5686_; lean_object* v___x_5696_; lean_object* v___x_5697_; uint8_t v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; uint8_t v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; 
v___x_5696_ = ((lean_object*)(l_Lake_Check_runComparator___closed__2));
v___x_5697_ = ((lean_object*)(l_Lake_Check_runComparator___closed__3));
v___x_5698_ = 2;
v___x_5699_ = lean_box(v___x_5698_);
v___x_5700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5699_);
lean_ctor_set(v___x_5700_, 1, v_challengeFromExport_x3f_5645_);
v___x_5701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5701_, 0, v___x_5697_);
lean_ctor_set(v___x_5701_, 1, v___x_5700_);
v___x_5702_ = ((lean_object*)(l_Lake_Check_runComparator___closed__4));
v___x_5703_ = 1;
v___x_5704_ = lean_box(v___x_5703_);
v___x_5705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5704_);
lean_ctor_set(v___x_5705_, 1, v_solutionFromExport_x3f_5646_);
v___x_5706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5706_, 0, v___x_5702_);
lean_ctor_set(v___x_5706_, 1, v___x_5705_);
v___x_5707_ = lean_unsigned_to_nat(2u);
v___x_5708_ = lean_mk_empty_array_with_capacity(v___x_5707_);
v___x_5709_ = lean_array_push(v___x_5708_, v___x_5701_);
v___x_5710_ = lean_array_push(v___x_5709_, v___x_5706_);
v___x_5711_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(v___x_5696_, v___x_5710_);
lean_dec_ref(v___x_5710_);
if (lean_obj_tag(v___x_5711_) == 0)
{
lean_object* v_a_5712_; lean_object* v___x_5714_; uint8_t v_isShared_5715_; uint8_t v_isSharedCheck_5903_; 
v_a_5712_ = lean_ctor_get(v___x_5711_, 0);
v_isSharedCheck_5903_ = !lean_is_exclusive(v___x_5711_);
if (v_isSharedCheck_5903_ == 0)
{
v___x_5714_ = v___x_5711_;
v_isShared_5715_ = v_isSharedCheck_5903_;
goto v_resetjp_5713_;
}
else
{
lean_inc(v_a_5712_);
lean_dec(v___x_5711_);
v___x_5714_ = lean_box(0);
v_isShared_5715_ = v_isSharedCheck_5903_;
goto v_resetjp_5713_;
}
v_resetjp_5713_:
{
if (lean_obj_tag(v_a_5712_) == 0)
{
lean_object* v_a_5716_; lean_object* v___x_5718_; 
lean_dec_ref(v_projectDir_5651_);
lean_dec_ref(v_lean_5649_);
v_a_5716_ = lean_ctor_get(v_a_5712_, 0);
lean_inc(v_a_5716_);
lean_dec_ref_known(v_a_5712_, 1);
if (v_isShared_5715_ == 0)
{
lean_ctor_set(v___x_5714_, 0, v_a_5716_);
v___x_5718_ = v___x_5714_;
goto v_reusejp_5717_;
}
else
{
lean_object* v_reuseFailAlloc_5719_; 
v_reuseFailAlloc_5719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5719_, 0, v_a_5716_);
v___x_5718_ = v_reuseFailAlloc_5719_;
goto v_reusejp_5717_;
}
v_reusejp_5717_:
{
return v___x_5718_;
}
}
else
{
lean_object* v_a_5720_; lean_object* v___x_5721_; 
lean_del_object(v___x_5714_);
v_a_5720_ = lean_ctor_get(v_a_5712_, 0);
lean_inc_n(v_a_5720_, 2);
lean_dec_ref_known(v_a_5712_, 1);
v___x_5721_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_5696_, v_paranoid_5647_, v_inadvisablyNoSandbox_5648_, v_lean_5649_, v_lake_5650_, v_projectDir_5651_, v_a_5720_);
if (lean_obj_tag(v___x_5721_) == 0)
{
lean_object* v_a_5722_; lean_object* v___x_5724_; uint8_t v_isShared_5725_; uint8_t v_isSharedCheck_5894_; 
v_a_5722_ = lean_ctor_get(v___x_5721_, 0);
v_isSharedCheck_5894_ = !lean_is_exclusive(v___x_5721_);
if (v_isSharedCheck_5894_ == 0)
{
v___x_5724_ = v___x_5721_;
v_isShared_5725_ = v_isSharedCheck_5894_;
goto v_resetjp_5723_;
}
else
{
lean_inc(v_a_5722_);
lean_dec(v___x_5721_);
v___x_5724_ = lean_box(0);
v_isShared_5725_ = v_isSharedCheck_5894_;
goto v_resetjp_5723_;
}
v_resetjp_5723_:
{
if (lean_obj_tag(v_a_5722_) == 0)
{
lean_object* v_a_5726_; lean_object* v___x_5728_; 
lean_dec(v_a_5720_);
v_a_5726_ = lean_ctor_get(v_a_5722_, 0);
lean_inc(v_a_5726_);
lean_dec_ref_known(v_a_5722_, 1);
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 0, v_a_5726_);
v___x_5728_ = v___x_5724_;
goto v_reusejp_5727_;
}
else
{
lean_object* v_reuseFailAlloc_5729_; 
v_reuseFailAlloc_5729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5729_, 0, v_a_5726_);
v___x_5728_ = v_reuseFailAlloc_5729_;
goto v_reusejp_5727_;
}
v_reusejp_5727_:
{
return v___x_5728_;
}
}
else
{
lean_object* v_a_5730_; lean_object* v___y_5732_; lean_object* v___y_5733_; size_t v___y_5734_; uint8_t v___y_5735_; lean_object* v___y_5736_; lean_object* v___y_5737_; lean_object* v___y_5738_; lean_object* v___y_5739_; lean_object* v___y_5784_; size_t v___y_5785_; lean_object* v___y_5786_; lean_object* v___y_5787_; lean_object* v___y_5788_; lean_object* v___y_5789_; lean_object* v___y_5790_; uint8_t v___y_5791_; lean_object* v___y_5812_; lean_object* v___y_5813_; size_t v___y_5814_; lean_object* v___y_5815_; lean_object* v___y_5816_; lean_object* v___y_5817_; lean_object* v___y_5818_; lean_object* v___y_5821_; size_t v___y_5822_; lean_object* v___y_5823_; lean_object* v___y_5824_; lean_object* v___y_5825_; lean_object* v___y_5826_; lean_object* v___y_5827_; uint8_t v___y_5828_; size_t v___y_5851_; lean_object* v___y_5852_; lean_object* v___y_5853_; lean_object* v___y_5854_; lean_object* v___y_5855_; lean_object* v___y_5856_; lean_object* v___y_5857_; lean_object* v___y_5868_; 
lean_del_object(v___x_5724_);
v_a_5730_ = lean_ctor_get(v_a_5722_, 0);
lean_inc(v_a_5730_);
lean_dec_ref_known(v_a_5722_, 1);
if (lean_obj_tag(v_configFile_x3f_5644_) == 0)
{
lean_object* v___x_5892_; 
v___x_5892_ = ((lean_object*)(l_Lake_Check_runComparator___closed__7));
v___y_5868_ = v___x_5892_;
goto v___jp_5867_;
}
else
{
lean_object* v_val_5893_; 
v_val_5893_ = lean_ctor_get(v_configFile_x3f_5644_, 0);
v___y_5868_ = v_val_5893_;
goto v___jp_5867_;
}
v___jp_5731_:
{
lean_object* v_projectDir_5740_; lean_object* v_leanPrefix_5741_; lean_object* v_leanPath_5742_; lean_object* v_binPath_5743_; lean_object* v_whichSandbox_5744_; lean_object* v_whichLake_5745_; lean_object* v_lakeHome_5746_; lean_object* v_whichLean4Export_5747_; lean_object* v_whichLeanChecker_5748_; lean_object* v_whichEnvBin_5749_; lean_object* v_bundledKernels_5750_; lean_object* v_moduleStore_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5776_; 
v_projectDir_5740_ = lean_ctor_get(v_a_5730_, 0);
v_leanPrefix_5741_ = lean_ctor_get(v_a_5730_, 6);
v_leanPath_5742_ = lean_ctor_get(v_a_5730_, 7);
v_binPath_5743_ = lean_ctor_get(v_a_5730_, 8);
v_whichSandbox_5744_ = lean_ctor_get(v_a_5730_, 9);
v_whichLake_5745_ = lean_ctor_get(v_a_5730_, 10);
v_lakeHome_5746_ = lean_ctor_get(v_a_5730_, 11);
v_whichLean4Export_5747_ = lean_ctor_get(v_a_5730_, 12);
v_whichLeanChecker_5748_ = lean_ctor_get(v_a_5730_, 13);
v_whichEnvBin_5749_ = lean_ctor_get(v_a_5730_, 14);
v_bundledKernels_5750_ = lean_ctor_get(v_a_5730_, 16);
v_moduleStore_5751_ = lean_ctor_get(v_a_5730_, 17);
v_isSharedCheck_5776_ = !lean_is_exclusive(v_a_5730_);
if (v_isSharedCheck_5776_ == 0)
{
lean_object* v_unused_5777_; lean_object* v_unused_5778_; lean_object* v_unused_5779_; lean_object* v_unused_5780_; lean_object* v_unused_5781_; lean_object* v_unused_5782_; 
v_unused_5777_ = lean_ctor_get(v_a_5730_, 15);
lean_dec(v_unused_5777_);
v_unused_5778_ = lean_ctor_get(v_a_5730_, 5);
lean_dec(v_unused_5778_);
v_unused_5779_ = lean_ctor_get(v_a_5730_, 4);
lean_dec(v_unused_5779_);
v_unused_5780_ = lean_ctor_get(v_a_5730_, 3);
lean_dec(v_unused_5780_);
v_unused_5781_ = lean_ctor_get(v_a_5730_, 2);
lean_dec(v_unused_5781_);
v_unused_5782_ = lean_ctor_get(v_a_5730_, 1);
lean_dec(v_unused_5782_);
v___x_5753_ = v_a_5730_;
v_isShared_5754_ = v_isSharedCheck_5776_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_moduleStore_5751_);
lean_inc(v_bundledKernels_5750_);
lean_inc(v_whichEnvBin_5749_);
lean_inc(v_whichLeanChecker_5748_);
lean_inc(v_whichLean4Export_5747_);
lean_inc(v_lakeHome_5746_);
lean_inc(v_whichLake_5745_);
lean_inc(v_whichSandbox_5744_);
lean_inc(v_binPath_5743_);
lean_inc(v_leanPath_5742_);
lean_inc(v_leanPrefix_5741_);
lean_inc(v_projectDir_5740_);
lean_dec(v_a_5730_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5776_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___x_5755_; lean_object* v___x_5756_; size_t v_sz_5757_; lean_object* v___x_5758_; lean_object* v___x_5760_; 
v___x_5755_ = l_String_toName(v___y_5739_);
v___x_5756_ = l_String_toName(v___y_5738_);
v_sz_5757_ = lean_array_size(v___y_5737_);
v___x_5758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_5757_, v___y_5734_, v___y_5737_);
lean_inc_ref(v_moduleStore_5751_);
lean_inc_ref(v_bundledKernels_5750_);
lean_inc(v___y_5733_);
lean_inc_ref(v_whichEnvBin_5749_);
lean_inc_ref(v_whichLeanChecker_5748_);
lean_inc_ref(v_whichLean4Export_5747_);
lean_inc_ref(v_lakeHome_5746_);
lean_inc_ref(v_whichLake_5745_);
lean_inc(v_whichSandbox_5744_);
lean_inc_ref(v_leanPrefix_5741_);
lean_inc_ref(v___x_5758_);
lean_inc_ref(v___y_5732_);
lean_inc_ref(v___y_5736_);
lean_inc(v___x_5756_);
lean_inc(v___x_5755_);
lean_inc_ref(v_projectDir_5740_);
if (v_isShared_5754_ == 0)
{
lean_ctor_set(v___x_5753_, 15, v___y_5733_);
lean_ctor_set(v___x_5753_, 5, v___x_5758_);
lean_ctor_set(v___x_5753_, 4, v___y_5732_);
lean_ctor_set(v___x_5753_, 3, v___y_5736_);
lean_ctor_set(v___x_5753_, 2, v___x_5756_);
lean_ctor_set(v___x_5753_, 1, v___x_5755_);
v___x_5760_ = v___x_5753_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v_projectDir_5740_);
lean_ctor_set(v_reuseFailAlloc_5775_, 1, v___x_5755_);
lean_ctor_set(v_reuseFailAlloc_5775_, 2, v___x_5756_);
lean_ctor_set(v_reuseFailAlloc_5775_, 3, v___y_5736_);
lean_ctor_set(v_reuseFailAlloc_5775_, 4, v___y_5732_);
lean_ctor_set(v_reuseFailAlloc_5775_, 5, v___x_5758_);
lean_ctor_set(v_reuseFailAlloc_5775_, 6, v_leanPrefix_5741_);
lean_ctor_set(v_reuseFailAlloc_5775_, 7, v_leanPath_5742_);
lean_ctor_set(v_reuseFailAlloc_5775_, 8, v_binPath_5743_);
lean_ctor_set(v_reuseFailAlloc_5775_, 9, v_whichSandbox_5744_);
lean_ctor_set(v_reuseFailAlloc_5775_, 10, v_whichLake_5745_);
lean_ctor_set(v_reuseFailAlloc_5775_, 11, v_lakeHome_5746_);
lean_ctor_set(v_reuseFailAlloc_5775_, 12, v_whichLean4Export_5747_);
lean_ctor_set(v_reuseFailAlloc_5775_, 13, v_whichLeanChecker_5748_);
lean_ctor_set(v_reuseFailAlloc_5775_, 14, v_whichEnvBin_5749_);
lean_ctor_set(v_reuseFailAlloc_5775_, 15, v___y_5733_);
lean_ctor_set(v_reuseFailAlloc_5775_, 16, v_bundledKernels_5750_);
lean_ctor_set(v_reuseFailAlloc_5775_, 17, v_moduleStore_5751_);
v___x_5760_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
if (v___y_5735_ == 0)
{
lean_object* v___x_5761_; 
lean_dec_ref(v___x_5758_);
lean_dec(v___x_5756_);
lean_dec(v___x_5755_);
lean_dec_ref(v_moduleStore_5751_);
lean_dec_ref(v_bundledKernels_5750_);
lean_dec_ref(v_whichEnvBin_5749_);
lean_dec_ref(v_whichLeanChecker_5748_);
lean_dec_ref(v_whichLean4Export_5747_);
lean_dec_ref(v_lakeHome_5746_);
lean_dec_ref(v_whichLake_5745_);
lean_dec(v_whichSandbox_5744_);
lean_dec_ref(v_leanPrefix_5741_);
lean_dec_ref(v_projectDir_5740_);
lean_dec_ref(v___y_5736_);
lean_dec(v___y_5733_);
lean_dec_ref(v___y_5732_);
v___x_5761_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt(v___x_5760_);
lean_dec_ref(v___x_5760_);
if (lean_obj_tag(v___x_5761_) == 0)
{
lean_object* v_a_5762_; lean_object* v___x_5763_; 
v_a_5762_ = lean_ctor_get(v___x_5761_, 0);
lean_inc(v_a_5762_);
lean_dec_ref_known(v___x_5761_, 1);
v___x_5763_ = l_Lake_Check_runComparator___lam__0(v_a_5762_);
v___y_5686_ = v___x_5763_;
goto v___jp_5685_;
}
else
{
lean_object* v_a_5764_; 
v_a_5764_ = lean_ctor_get(v___x_5761_, 0);
lean_inc(v_a_5764_);
lean_dec_ref_known(v___x_5761_, 1);
v_a_5663_ = v_a_5764_;
goto v___jp_5662_;
}
}
else
{
lean_object* v___x_5765_; 
v___x_5765_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v___x_5760_);
lean_dec_ref(v___x_5760_);
if (lean_obj_tag(v___x_5765_) == 0)
{
lean_object* v_a_5766_; lean_object* v_fst_5767_; lean_object* v_snd_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; 
v_a_5766_ = lean_ctor_get(v___x_5765_, 0);
lean_inc(v_a_5766_);
lean_dec_ref_known(v___x_5765_, 1);
v_fst_5767_ = lean_ctor_get(v_a_5766_, 0);
lean_inc(v_fst_5767_);
v_snd_5768_ = lean_ctor_get(v_a_5766_, 1);
lean_inc(v_snd_5768_);
lean_dec(v_a_5766_);
v___x_5769_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_5769_, 0, v_projectDir_5740_);
lean_ctor_set(v___x_5769_, 1, v___x_5755_);
lean_ctor_set(v___x_5769_, 2, v___x_5756_);
lean_ctor_set(v___x_5769_, 3, v___y_5736_);
lean_ctor_set(v___x_5769_, 4, v___y_5732_);
lean_ctor_set(v___x_5769_, 5, v___x_5758_);
lean_ctor_set(v___x_5769_, 6, v_leanPrefix_5741_);
lean_ctor_set(v___x_5769_, 7, v_fst_5767_);
lean_ctor_set(v___x_5769_, 8, v_snd_5768_);
lean_ctor_set(v___x_5769_, 9, v_whichSandbox_5744_);
lean_ctor_set(v___x_5769_, 10, v_whichLake_5745_);
lean_ctor_set(v___x_5769_, 11, v_lakeHome_5746_);
lean_ctor_set(v___x_5769_, 12, v_whichLean4Export_5747_);
lean_ctor_set(v___x_5769_, 13, v_whichLeanChecker_5748_);
lean_ctor_set(v___x_5769_, 14, v_whichEnvBin_5749_);
lean_ctor_set(v___x_5769_, 15, v___y_5733_);
lean_ctor_set(v___x_5769_, 16, v_bundledKernels_5750_);
lean_ctor_set(v___x_5769_, 17, v_moduleStore_5751_);
v___x_5770_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt(v___x_5769_);
lean_dec_ref_known(v___x_5769_, 18);
if (lean_obj_tag(v___x_5770_) == 0)
{
lean_object* v_a_5771_; lean_object* v___x_5772_; 
v_a_5771_ = lean_ctor_get(v___x_5770_, 0);
lean_inc(v_a_5771_);
lean_dec_ref_known(v___x_5770_, 1);
v___x_5772_ = l_Lake_Check_runComparator___lam__0(v_a_5771_);
v___y_5686_ = v___x_5772_;
goto v___jp_5685_;
}
else
{
lean_object* v_a_5773_; 
v_a_5773_ = lean_ctor_get(v___x_5770_, 0);
lean_inc(v_a_5773_);
lean_dec_ref_known(v___x_5770_, 1);
v_a_5663_ = v_a_5773_;
goto v___jp_5662_;
}
}
else
{
lean_object* v_a_5774_; 
lean_dec_ref(v___x_5758_);
lean_dec(v___x_5756_);
lean_dec(v___x_5755_);
lean_dec_ref(v_moduleStore_5751_);
lean_dec_ref(v_bundledKernels_5750_);
lean_dec_ref(v_whichEnvBin_5749_);
lean_dec_ref(v_whichLeanChecker_5748_);
lean_dec_ref(v_whichLean4Export_5747_);
lean_dec_ref(v_lakeHome_5746_);
lean_dec_ref(v_whichLake_5745_);
lean_dec(v_whichSandbox_5744_);
lean_dec_ref(v_leanPrefix_5741_);
lean_dec_ref(v_projectDir_5740_);
lean_dec_ref(v___y_5736_);
lean_dec(v___y_5733_);
lean_dec_ref(v___y_5732_);
v_a_5774_ = lean_ctor_get(v___x_5765_, 0);
lean_inc(v_a_5774_);
lean_dec_ref_known(v___x_5765_, 1);
v_a_5663_ = v_a_5774_;
goto v___jp_5662_;
}
}
}
}
}
v___jp_5783_:
{
lean_object* v_projectDir_5792_; lean_object* v___x_5793_; 
v_projectDir_5792_ = lean_ctor_get(v_a_5730_, 0);
lean_inc_ref(v_projectDir_5792_);
v___x_5793_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_5696_, v_projectDir_5792_);
if (lean_obj_tag(v___x_5793_) == 0)
{
lean_object* v_a_5794_; lean_object* v___x_5796_; uint8_t v_isShared_5797_; uint8_t v_isSharedCheck_5802_; 
v_a_5794_ = lean_ctor_get(v___x_5793_, 0);
v_isSharedCheck_5802_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5802_ == 0)
{
v___x_5796_ = v___x_5793_;
v_isShared_5797_ = v_isSharedCheck_5802_;
goto v_resetjp_5795_;
}
else
{
lean_inc(v_a_5794_);
lean_dec(v___x_5793_);
v___x_5796_ = lean_box(0);
v_isShared_5797_ = v_isSharedCheck_5802_;
goto v_resetjp_5795_;
}
v_resetjp_5795_:
{
if (lean_obj_tag(v_a_5794_) == 1)
{
lean_object* v_val_5798_; lean_object* v___x_5800_; 
lean_dec_ref(v___y_5790_);
lean_dec_ref(v___y_5789_);
lean_dec_ref(v___y_5788_);
lean_dec_ref(v___y_5787_);
lean_dec(v___y_5786_);
lean_dec_ref(v___y_5784_);
lean_dec(v_a_5730_);
v_val_5798_ = lean_ctor_get(v_a_5794_, 0);
lean_inc(v_val_5798_);
lean_dec_ref_known(v_a_5794_, 1);
if (v_isShared_5797_ == 0)
{
lean_ctor_set(v___x_5796_, 0, v_val_5798_);
v___x_5800_ = v___x_5796_;
goto v_reusejp_5799_;
}
else
{
lean_object* v_reuseFailAlloc_5801_; 
v_reuseFailAlloc_5801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5801_, 0, v_val_5798_);
v___x_5800_ = v_reuseFailAlloc_5801_;
goto v_reusejp_5799_;
}
v_reusejp_5799_:
{
return v___x_5800_;
}
}
else
{
lean_del_object(v___x_5796_);
lean_dec(v_a_5794_);
v___y_5732_ = v___y_5784_;
v___y_5733_ = v___y_5786_;
v___y_5734_ = v___y_5785_;
v___y_5735_ = v___y_5791_;
v___y_5736_ = v___y_5787_;
v___y_5737_ = v___y_5788_;
v___y_5738_ = v___y_5789_;
v___y_5739_ = v___y_5790_;
goto v___jp_5731_;
}
}
}
else
{
lean_object* v_a_5803_; lean_object* v___x_5805_; uint8_t v_isShared_5806_; uint8_t v_isSharedCheck_5810_; 
lean_dec_ref(v___y_5790_);
lean_dec_ref(v___y_5789_);
lean_dec_ref(v___y_5788_);
lean_dec_ref(v___y_5787_);
lean_dec(v___y_5786_);
lean_dec_ref(v___y_5784_);
lean_dec(v_a_5730_);
v_a_5803_ = lean_ctor_get(v___x_5793_, 0);
v_isSharedCheck_5810_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5810_ == 0)
{
v___x_5805_ = v___x_5793_;
v_isShared_5806_ = v_isSharedCheck_5810_;
goto v_resetjp_5804_;
}
else
{
lean_inc(v_a_5803_);
lean_dec(v___x_5793_);
v___x_5805_ = lean_box(0);
v_isShared_5806_ = v_isSharedCheck_5810_;
goto v_resetjp_5804_;
}
v_resetjp_5804_:
{
lean_object* v___x_5808_; 
if (v_isShared_5806_ == 0)
{
v___x_5808_ = v___x_5805_;
goto v_reusejp_5807_;
}
else
{
lean_object* v_reuseFailAlloc_5809_; 
v_reuseFailAlloc_5809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5809_, 0, v_a_5803_);
v___x_5808_ = v_reuseFailAlloc_5809_;
goto v_reusejp_5807_;
}
v_reusejp_5807_:
{
return v___x_5808_;
}
}
}
}
v___jp_5811_:
{
uint8_t v___x_5819_; 
v___x_5819_ = 1;
v___y_5784_ = v___y_5812_;
v___y_5785_ = v___y_5814_;
v___y_5786_ = v___y_5813_;
v___y_5787_ = v___y_5815_;
v___y_5788_ = v___y_5816_;
v___y_5789_ = v___y_5817_;
v___y_5790_ = v___y_5818_;
v___y_5791_ = v___x_5819_;
goto v___jp_5783_;
}
v___jp_5820_:
{
lean_object* v___x_5829_; 
v___x_5829_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v___y_5827_);
if (lean_obj_tag(v___x_5829_) == 0)
{
lean_object* v_a_5830_; lean_object* v___x_5832_; uint8_t v_isShared_5833_; uint8_t v_isSharedCheck_5841_; 
v_a_5830_ = lean_ctor_get(v___x_5829_, 0);
v_isSharedCheck_5841_ = !lean_is_exclusive(v___x_5829_);
if (v_isSharedCheck_5841_ == 0)
{
v___x_5832_ = v___x_5829_;
v_isShared_5833_ = v_isSharedCheck_5841_;
goto v_resetjp_5831_;
}
else
{
lean_inc(v_a_5830_);
lean_dec(v___x_5829_);
v___x_5832_ = lean_box(0);
v_isShared_5833_ = v_isSharedCheck_5841_;
goto v_resetjp_5831_;
}
v_resetjp_5831_:
{
if (lean_obj_tag(v_a_5830_) == 0)
{
lean_object* v_a_5834_; lean_object* v___x_5836_; 
lean_dec_ref(v___y_5826_);
lean_dec_ref(v___y_5825_);
lean_dec_ref(v___y_5824_);
lean_dec_ref(v___y_5823_);
lean_dec_ref(v___y_5821_);
lean_dec(v_a_5730_);
lean_dec(v_a_5720_);
v_a_5834_ = lean_ctor_get(v_a_5830_, 0);
lean_inc(v_a_5834_);
lean_dec_ref_known(v_a_5830_, 1);
if (v_isShared_5833_ == 0)
{
lean_ctor_set(v___x_5832_, 0, v_a_5834_);
v___x_5836_ = v___x_5832_;
goto v_reusejp_5835_;
}
else
{
lean_object* v_reuseFailAlloc_5837_; 
v_reuseFailAlloc_5837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5837_, 0, v_a_5834_);
v___x_5836_ = v_reuseFailAlloc_5837_;
goto v_reusejp_5835_;
}
v_reusejp_5835_:
{
return v___x_5836_;
}
}
else
{
lean_object* v_a_5838_; uint8_t v___x_5839_; 
lean_del_object(v___x_5832_);
v_a_5838_ = lean_ctor_get(v_a_5830_, 0);
lean_inc(v_a_5838_);
lean_dec_ref_known(v_a_5830_, 1);
v___x_5839_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_a_5720_, v___x_5698_);
if (v___x_5839_ == 0)
{
lean_dec(v_a_5720_);
v___y_5812_ = v___y_5821_;
v___y_5813_ = v_a_5838_;
v___y_5814_ = v___y_5822_;
v___y_5815_ = v___y_5823_;
v___y_5816_ = v___y_5824_;
v___y_5817_ = v___y_5825_;
v___y_5818_ = v___y_5826_;
goto v___jp_5811_;
}
else
{
uint8_t v___x_5840_; 
v___x_5840_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_a_5720_, v___x_5703_);
lean_dec(v_a_5720_);
if (v___x_5840_ == 0)
{
v___y_5812_ = v___y_5821_;
v___y_5813_ = v_a_5838_;
v___y_5814_ = v___y_5822_;
v___y_5815_ = v___y_5823_;
v___y_5816_ = v___y_5824_;
v___y_5817_ = v___y_5825_;
v___y_5818_ = v___y_5826_;
goto v___jp_5811_;
}
else
{
if (v___y_5828_ == 0)
{
v___y_5732_ = v___y_5821_;
v___y_5733_ = v_a_5838_;
v___y_5734_ = v___y_5822_;
v___y_5735_ = v___y_5828_;
v___y_5736_ = v___y_5823_;
v___y_5737_ = v___y_5824_;
v___y_5738_ = v___y_5825_;
v___y_5739_ = v___y_5826_;
goto v___jp_5731_;
}
else
{
v___y_5784_ = v___y_5821_;
v___y_5785_ = v___y_5822_;
v___y_5786_ = v_a_5838_;
v___y_5787_ = v___y_5823_;
v___y_5788_ = v___y_5824_;
v___y_5789_ = v___y_5825_;
v___y_5790_ = v___y_5826_;
v___y_5791_ = v___y_5828_;
goto v___jp_5783_;
}
}
}
}
}
}
else
{
lean_object* v_a_5842_; lean_object* v___x_5844_; uint8_t v_isShared_5845_; uint8_t v_isSharedCheck_5849_; 
lean_dec_ref(v___y_5826_);
lean_dec_ref(v___y_5825_);
lean_dec_ref(v___y_5824_);
lean_dec_ref(v___y_5823_);
lean_dec_ref(v___y_5821_);
lean_dec(v_a_5730_);
lean_dec(v_a_5720_);
v_a_5842_ = lean_ctor_get(v___x_5829_, 0);
v_isSharedCheck_5849_ = !lean_is_exclusive(v___x_5829_);
if (v_isSharedCheck_5849_ == 0)
{
v___x_5844_ = v___x_5829_;
v_isShared_5845_ = v_isSharedCheck_5849_;
goto v_resetjp_5843_;
}
else
{
lean_inc(v_a_5842_);
lean_dec(v___x_5829_);
v___x_5844_ = lean_box(0);
v_isShared_5845_ = v_isSharedCheck_5849_;
goto v_resetjp_5843_;
}
v_resetjp_5843_:
{
lean_object* v___x_5847_; 
if (v_isShared_5845_ == 0)
{
v___x_5847_ = v___x_5844_;
goto v_reusejp_5846_;
}
else
{
lean_object* v_reuseFailAlloc_5848_; 
v_reuseFailAlloc_5848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5848_, 0, v_a_5842_);
v___x_5847_ = v_reuseFailAlloc_5848_;
goto v_reusejp_5846_;
}
v_reusejp_5846_:
{
return v___x_5847_;
}
}
}
}
v___jp_5850_:
{
size_t v_sz_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; uint8_t v___x_5862_; 
v_sz_5858_ = lean_array_size(v___y_5857_);
v___x_5859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_5858_, v___y_5851_, v___y_5857_);
v___x_5860_ = lean_array_get_size(v___y_5852_);
v___x_5861_ = lean_unsigned_to_nat(0u);
v___x_5862_ = lean_nat_dec_eq(v___x_5860_, v___x_5861_);
if (v___x_5862_ == 0)
{
v___y_5821_ = v___x_5859_;
v___y_5822_ = v___y_5851_;
v___y_5823_ = v___y_5852_;
v___y_5824_ = v___y_5853_;
v___y_5825_ = v___y_5854_;
v___y_5826_ = v___y_5856_;
v___y_5827_ = v___y_5855_;
v___y_5828_ = v___x_5862_;
goto v___jp_5820_;
}
else
{
lean_object* v___x_5863_; uint8_t v___x_5864_; 
v___x_5863_ = lean_array_get_size(v___x_5859_);
v___x_5864_ = lean_nat_dec_eq(v___x_5863_, v___x_5861_);
if (v___x_5864_ == 0)
{
v___y_5821_ = v___x_5859_;
v___y_5822_ = v___y_5851_;
v___y_5823_ = v___y_5852_;
v___y_5824_ = v___y_5853_;
v___y_5825_ = v___y_5854_;
v___y_5826_ = v___y_5856_;
v___y_5827_ = v___y_5855_;
v___y_5828_ = v___x_5864_;
goto v___jp_5820_;
}
else
{
lean_object* v___x_5865_; lean_object* v___x_5866_; 
lean_dec_ref(v___x_5859_);
lean_dec_ref(v___y_5856_);
lean_dec_ref(v___y_5855_);
lean_dec_ref(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec_ref(v___y_5852_);
lean_dec(v_a_5730_);
lean_dec(v_a_5720_);
v___x_5865_ = ((lean_object*)(l_Lake_Check_runComparator___closed__5));
v___x_5866_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5865_);
return v___x_5866_;
}
}
}
v___jp_5867_:
{
lean_object* v___x_5869_; 
v___x_5869_ = l_IO_FS_readFile(v___y_5868_);
if (lean_obj_tag(v___x_5869_) == 0)
{
lean_object* v_a_5870_; lean_object* v___x_5871_; 
v_a_5870_ = lean_ctor_get(v___x_5869_, 0);
lean_inc(v_a_5870_);
lean_dec_ref_known(v___x_5869_, 1);
v___x_5871_ = l_Lean_Json_parse(v_a_5870_);
if (lean_obj_tag(v___x_5871_) == 0)
{
lean_object* v_a_5872_; 
lean_dec(v_a_5730_);
lean_dec(v_a_5720_);
v_a_5872_ = lean_ctor_get(v___x_5871_, 0);
lean_inc(v_a_5872_);
lean_dec_ref_known(v___x_5871_, 1);
v___y_5654_ = v___y_5868_;
v_a_5655_ = v_a_5872_;
goto v___jp_5653_;
}
else
{
lean_object* v_a_5873_; lean_object* v___x_5874_; 
v_a_5873_ = lean_ctor_get(v___x_5871_, 0);
lean_inc(v_a_5873_);
lean_dec_ref_known(v___x_5871_, 1);
v___x_5874_ = l_Lake_Check_instFromJsonConfig_fromJson(v_a_5873_);
if (lean_obj_tag(v___x_5874_) == 0)
{
lean_object* v_a_5875_; 
lean_dec(v_a_5730_);
lean_dec(v_a_5720_);
v_a_5875_ = lean_ctor_get(v___x_5874_, 0);
lean_inc(v_a_5875_);
lean_dec_ref_known(v___x_5874_, 1);
v___y_5654_ = v___y_5868_;
v_a_5655_ = v_a_5875_;
goto v___jp_5653_;
}
else
{
lean_object* v_a_5876_; lean_object* v_challenge__module_5877_; lean_object* v_solution__module_5878_; lean_object* v_theorem__names_5879_; lean_object* v_definition__names_5880_; lean_object* v_permitted__axioms_5881_; size_t v_sz_5882_; size_t v___x_5883_; lean_object* v___x_5884_; 
v_a_5876_ = lean_ctor_get(v___x_5874_, 0);
lean_inc(v_a_5876_);
lean_dec_ref_known(v___x_5874_, 1);
v_challenge__module_5877_ = lean_ctor_get(v_a_5876_, 0);
lean_inc_ref(v_challenge__module_5877_);
v_solution__module_5878_ = lean_ctor_get(v_a_5876_, 1);
lean_inc_ref(v_solution__module_5878_);
v_theorem__names_5879_ = lean_ctor_get(v_a_5876_, 2);
v_definition__names_5880_ = lean_ctor_get(v_a_5876_, 3);
v_permitted__axioms_5881_ = lean_ctor_get(v_a_5876_, 4);
lean_inc_ref(v_permitted__axioms_5881_);
v_sz_5882_ = lean_array_size(v_theorem__names_5879_);
v___x_5883_ = ((size_t)0ULL);
lean_inc_ref(v_theorem__names_5879_);
v___x_5884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_5882_, v___x_5883_, v_theorem__names_5879_);
if (lean_obj_tag(v_definition__names_5880_) == 0)
{
lean_object* v___x_5885_; 
v___x_5885_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___y_5851_ = v___x_5883_;
v___y_5852_ = v___x_5884_;
v___y_5853_ = v_permitted__axioms_5881_;
v___y_5854_ = v_solution__module_5878_;
v___y_5855_ = v_a_5876_;
v___y_5856_ = v_challenge__module_5877_;
v___y_5857_ = v___x_5885_;
goto v___jp_5850_;
}
else
{
lean_object* v_val_5886_; 
v_val_5886_ = lean_ctor_get(v_definition__names_5880_, 0);
lean_inc(v_val_5886_);
v___y_5851_ = v___x_5883_;
v___y_5852_ = v___x_5884_;
v___y_5853_ = v_permitted__axioms_5881_;
v___y_5854_ = v_solution__module_5878_;
v___y_5855_ = v_a_5876_;
v___y_5856_ = v_challenge__module_5877_;
v___y_5857_ = v_val_5886_;
goto v___jp_5850_;
}
}
}
}
else
{
lean_object* v_a_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; 
lean_dec(v_a_5730_);
lean_dec(v_a_5720_);
v_a_5887_ = lean_ctor_get(v___x_5869_, 0);
lean_inc(v_a_5887_);
lean_dec_ref_known(v___x_5869_, 1);
v___x_5888_ = ((lean_object*)(l_Lake_Check_runComparator___closed__6));
v___x_5889_ = lean_io_error_to_string(v_a_5887_);
v___x_5890_ = lean_string_append(v___x_5888_, v___x_5889_);
lean_dec_ref(v___x_5889_);
v___x_5891_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5890_);
lean_dec_ref(v___x_5890_);
return v___x_5891_;
}
}
}
}
}
else
{
lean_object* v_a_5895_; lean_object* v___x_5897_; uint8_t v_isShared_5898_; uint8_t v_isSharedCheck_5902_; 
lean_dec(v_a_5720_);
v_a_5895_ = lean_ctor_get(v___x_5721_, 0);
v_isSharedCheck_5902_ = !lean_is_exclusive(v___x_5721_);
if (v_isSharedCheck_5902_ == 0)
{
v___x_5897_ = v___x_5721_;
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
else
{
lean_inc(v_a_5895_);
lean_dec(v___x_5721_);
v___x_5897_ = lean_box(0);
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
v_resetjp_5896_:
{
lean_object* v___x_5900_; 
if (v_isShared_5898_ == 0)
{
v___x_5900_ = v___x_5897_;
goto v_reusejp_5899_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_a_5895_);
v___x_5900_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5899_;
}
v_reusejp_5899_:
{
return v___x_5900_;
}
}
}
}
}
}
else
{
lean_object* v_a_5904_; lean_object* v___x_5906_; uint8_t v_isShared_5907_; uint8_t v_isSharedCheck_5911_; 
lean_dec_ref(v_projectDir_5651_);
lean_dec_ref(v_lean_5649_);
v_a_5904_ = lean_ctor_get(v___x_5711_, 0);
v_isSharedCheck_5911_ = !lean_is_exclusive(v___x_5711_);
if (v_isSharedCheck_5911_ == 0)
{
v___x_5906_ = v___x_5711_;
v_isShared_5907_ = v_isSharedCheck_5911_;
goto v_resetjp_5905_;
}
else
{
lean_inc(v_a_5904_);
lean_dec(v___x_5711_);
v___x_5906_ = lean_box(0);
v_isShared_5907_ = v_isSharedCheck_5911_;
goto v_resetjp_5905_;
}
v_resetjp_5905_:
{
lean_object* v___x_5909_; 
if (v_isShared_5907_ == 0)
{
v___x_5909_ = v___x_5906_;
goto v_reusejp_5908_;
}
else
{
lean_object* v_reuseFailAlloc_5910_; 
v_reuseFailAlloc_5910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5910_, 0, v_a_5904_);
v___x_5909_ = v_reuseFailAlloc_5910_;
goto v_reusejp_5908_;
}
v_reusejp_5908_:
{
return v___x_5909_;
}
}
}
v___jp_5653_:
{
lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; 
v___x_5656_ = ((lean_object*)(l_Lake_Check_runComparator___closed__0));
v___x_5657_ = lean_string_append(v___x_5656_, v___y_5654_);
v___x_5658_ = ((lean_object*)(l_Lake_Check_runComparator___closed__1));
v___x_5659_ = lean_string_append(v___x_5657_, v___x_5658_);
v___x_5660_ = lean_string_append(v___x_5659_, v_a_5655_);
lean_dec_ref(v_a_5655_);
v___x_5661_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5660_);
lean_dec_ref(v___x_5660_);
return v___x_5661_;
}
v___jp_5662_:
{
lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; 
v___x_5664_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_5665_ = lean_io_error_to_string(v_a_5663_);
v___x_5666_ = lean_string_append(v___x_5664_, v___x_5665_);
lean_dec_ref(v___x_5665_);
v___x_5667_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_5666_);
if (lean_obj_tag(v___x_5667_) == 0)
{
lean_object* v___x_5669_; uint8_t v_isShared_5670_; uint8_t v_isSharedCheck_5675_; 
v_isSharedCheck_5675_ = !lean_is_exclusive(v___x_5667_);
if (v_isSharedCheck_5675_ == 0)
{
lean_object* v_unused_5676_; 
v_unused_5676_ = lean_ctor_get(v___x_5667_, 0);
lean_dec(v_unused_5676_);
v___x_5669_ = v___x_5667_;
v_isShared_5670_ = v_isSharedCheck_5675_;
goto v_resetjp_5668_;
}
else
{
lean_dec(v___x_5667_);
v___x_5669_ = lean_box(0);
v_isShared_5670_ = v_isSharedCheck_5675_;
goto v_resetjp_5668_;
}
v_resetjp_5668_:
{
lean_object* v___x_5671_; lean_object* v___x_5673_; 
v___x_5671_ = l_Lake_Check_runComparator___boxed__const__1;
if (v_isShared_5670_ == 0)
{
lean_ctor_set(v___x_5669_, 0, v___x_5671_);
v___x_5673_ = v___x_5669_;
goto v_reusejp_5672_;
}
else
{
lean_object* v_reuseFailAlloc_5674_; 
v_reuseFailAlloc_5674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5674_, 0, v___x_5671_);
v___x_5673_ = v_reuseFailAlloc_5674_;
goto v_reusejp_5672_;
}
v_reusejp_5672_:
{
return v___x_5673_;
}
}
}
else
{
lean_object* v_a_5677_; lean_object* v___x_5679_; uint8_t v_isShared_5680_; uint8_t v_isSharedCheck_5684_; 
v_a_5677_ = lean_ctor_get(v___x_5667_, 0);
v_isSharedCheck_5684_ = !lean_is_exclusive(v___x_5667_);
if (v_isSharedCheck_5684_ == 0)
{
v___x_5679_ = v___x_5667_;
v_isShared_5680_ = v_isSharedCheck_5684_;
goto v_resetjp_5678_;
}
else
{
lean_inc(v_a_5677_);
lean_dec(v___x_5667_);
v___x_5679_ = lean_box(0);
v_isShared_5680_ = v_isSharedCheck_5684_;
goto v_resetjp_5678_;
}
v_resetjp_5678_:
{
lean_object* v___x_5682_; 
if (v_isShared_5680_ == 0)
{
v___x_5682_ = v___x_5679_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5683_; 
v_reuseFailAlloc_5683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5683_, 0, v_a_5677_);
v___x_5682_ = v_reuseFailAlloc_5683_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
return v___x_5682_;
}
}
}
}
v___jp_5685_:
{
lean_object* v_a_5687_; lean_object* v___x_5689_; uint8_t v_isShared_5690_; uint8_t v_isSharedCheck_5695_; 
v_a_5687_ = lean_ctor_get(v___y_5686_, 0);
v_isSharedCheck_5695_ = !lean_is_exclusive(v___y_5686_);
if (v_isSharedCheck_5695_ == 0)
{
v___x_5689_ = v___y_5686_;
v_isShared_5690_ = v_isSharedCheck_5695_;
goto v_resetjp_5688_;
}
else
{
lean_inc(v_a_5687_);
lean_dec(v___y_5686_);
v___x_5689_ = lean_box(0);
v_isShared_5690_ = v_isSharedCheck_5695_;
goto v_resetjp_5688_;
}
v_resetjp_5688_:
{
lean_object* v_a_5691_; lean_object* v___x_5693_; 
v_a_5691_ = lean_ctor_get(v_a_5687_, 0);
lean_inc(v_a_5691_);
lean_dec(v_a_5687_);
if (v_isShared_5690_ == 0)
{
lean_ctor_set(v___x_5689_, 0, v_a_5691_);
v___x_5693_ = v___x_5689_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5694_; 
v_reuseFailAlloc_5694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5694_, 0, v_a_5691_);
v___x_5693_ = v_reuseFailAlloc_5694_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
return v___x_5693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___boxed(lean_object* v_configFile_x3f_5912_, lean_object* v_challengeFromExport_x3f_5913_, lean_object* v_solutionFromExport_x3f_5914_, lean_object* v_paranoid_5915_, lean_object* v_inadvisablyNoSandbox_5916_, lean_object* v_lean_5917_, lean_object* v_lake_5918_, lean_object* v_projectDir_5919_, lean_object* v_a_5920_){
_start:
{
uint8_t v_paranoid_boxed_5921_; uint8_t v_inadvisablyNoSandbox_boxed_5922_; lean_object* v_res_5923_; 
v_paranoid_boxed_5921_ = lean_unbox(v_paranoid_5915_);
v_inadvisablyNoSandbox_boxed_5922_ = lean_unbox(v_inadvisablyNoSandbox_5916_);
v_res_5923_ = l_Lake_Check_runComparator(v_configFile_x3f_5912_, v_challengeFromExport_x3f_5913_, v_solutionFromExport_x3f_5914_, v_paranoid_boxed_5921_, v_inadvisablyNoSandbox_boxed_5922_, v_lean_5917_, v_lake_5918_, v_projectDir_5919_);
lean_dec_ref(v_lake_5918_);
lean_dec(v_configFile_x3f_5912_);
return v_res_5923_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runCheck(lean_object* v_fromExport_x3f_5924_, uint8_t v_paranoid_5925_, uint8_t v_inadvisablyNoSandbox_5926_, lean_object* v_lean_5927_, lean_object* v_lake_5928_, lean_object* v_projectDir_5929_){
_start:
{
lean_object* v___x_5931_; lean_object* v___x_5932_; uint8_t v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; 
v___x_5931_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__0));
v___x_5932_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_5933_ = 0;
v___x_5934_ = lean_box(v___x_5933_);
v___x_5935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5935_, 0, v___x_5934_);
lean_ctor_set(v___x_5935_, 1, v_fromExport_x3f_5924_);
v___x_5936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5932_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
v___x_5937_ = lean_unsigned_to_nat(1u);
v___x_5938_ = lean_mk_empty_array_with_capacity(v___x_5937_);
v___x_5939_ = lean_array_push(v___x_5938_, v___x_5936_);
v___x_5940_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(v___x_5931_, v___x_5939_);
lean_dec_ref(v___x_5939_);
if (lean_obj_tag(v___x_5940_) == 0)
{
lean_object* v_a_5941_; lean_object* v___x_5943_; uint8_t v_isShared_5944_; uint8_t v_isSharedCheck_6050_; 
v_a_5941_ = lean_ctor_get(v___x_5940_, 0);
v_isSharedCheck_6050_ = !lean_is_exclusive(v___x_5940_);
if (v_isSharedCheck_6050_ == 0)
{
v___x_5943_ = v___x_5940_;
v_isShared_5944_ = v_isSharedCheck_6050_;
goto v_resetjp_5942_;
}
else
{
lean_inc(v_a_5941_);
lean_dec(v___x_5940_);
v___x_5943_ = lean_box(0);
v_isShared_5944_ = v_isSharedCheck_6050_;
goto v_resetjp_5942_;
}
v_resetjp_5942_:
{
if (lean_obj_tag(v_a_5941_) == 0)
{
lean_object* v_a_5945_; lean_object* v___x_5947_; 
lean_dec_ref(v_projectDir_5929_);
lean_dec_ref(v_lean_5927_);
v_a_5945_ = lean_ctor_get(v_a_5941_, 0);
lean_inc(v_a_5945_);
lean_dec_ref_known(v_a_5941_, 1);
if (v_isShared_5944_ == 0)
{
lean_ctor_set(v___x_5943_, 0, v_a_5945_);
v___x_5947_ = v___x_5943_;
goto v_reusejp_5946_;
}
else
{
lean_object* v_reuseFailAlloc_5948_; 
v_reuseFailAlloc_5948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5948_, 0, v_a_5945_);
v___x_5947_ = v_reuseFailAlloc_5948_;
goto v_reusejp_5946_;
}
v_reusejp_5946_:
{
return v___x_5947_;
}
}
else
{
lean_object* v_a_5949_; lean_object* v___x_5950_; 
lean_del_object(v___x_5943_);
v_a_5949_ = lean_ctor_get(v_a_5941_, 0);
lean_inc_n(v_a_5949_, 2);
lean_dec_ref_known(v_a_5941_, 1);
v___x_5950_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_5931_, v_paranoid_5925_, v_inadvisablyNoSandbox_5926_, v_lean_5927_, v_lake_5928_, v_projectDir_5929_, v_a_5949_);
if (lean_obj_tag(v___x_5950_) == 0)
{
lean_object* v_a_5951_; lean_object* v___x_5953_; uint8_t v_isShared_5954_; uint8_t v_isSharedCheck_6041_; 
v_a_5951_ = lean_ctor_get(v___x_5950_, 0);
v_isSharedCheck_6041_ = !lean_is_exclusive(v___x_5950_);
if (v_isSharedCheck_6041_ == 0)
{
v___x_5953_ = v___x_5950_;
v_isShared_5954_ = v_isSharedCheck_6041_;
goto v_resetjp_5952_;
}
else
{
lean_inc(v_a_5951_);
lean_dec(v___x_5950_);
v___x_5953_ = lean_box(0);
v_isShared_5954_ = v_isSharedCheck_6041_;
goto v_resetjp_5952_;
}
v_resetjp_5952_:
{
if (lean_obj_tag(v_a_5951_) == 0)
{
lean_object* v_a_5955_; lean_object* v___x_5957_; 
lean_dec(v_a_5949_);
v_a_5955_ = lean_ctor_get(v_a_5951_, 0);
lean_inc(v_a_5955_);
lean_dec_ref_known(v_a_5951_, 1);
if (v_isShared_5954_ == 0)
{
lean_ctor_set(v___x_5953_, 0, v_a_5955_);
v___x_5957_ = v___x_5953_;
goto v_reusejp_5956_;
}
else
{
lean_object* v_reuseFailAlloc_5958_; 
v_reuseFailAlloc_5958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5958_, 0, v_a_5955_);
v___x_5957_ = v_reuseFailAlloc_5958_;
goto v_reusejp_5956_;
}
v_reusejp_5956_:
{
return v___x_5957_;
}
}
else
{
lean_object* v_a_5959_; uint8_t v___x_6021_; 
lean_del_object(v___x_5953_);
v_a_5959_ = lean_ctor_get(v_a_5951_, 0);
lean_inc(v_a_5959_);
lean_dec_ref_known(v_a_5951_, 1);
v___x_6021_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_a_5949_, v___x_5933_);
lean_dec(v_a_5949_);
if (v___x_6021_ == 0)
{
lean_object* v_projectDir_6022_; lean_object* v___x_6023_; 
v_projectDir_6022_ = lean_ctor_get(v_a_5959_, 0);
lean_inc_ref(v_projectDir_6022_);
v___x_6023_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_5931_, v_projectDir_6022_);
if (lean_obj_tag(v___x_6023_) == 0)
{
lean_object* v_a_6024_; lean_object* v___x_6026_; uint8_t v_isShared_6027_; uint8_t v_isSharedCheck_6032_; 
v_a_6024_ = lean_ctor_get(v___x_6023_, 0);
v_isSharedCheck_6032_ = !lean_is_exclusive(v___x_6023_);
if (v_isSharedCheck_6032_ == 0)
{
v___x_6026_ = v___x_6023_;
v_isShared_6027_ = v_isSharedCheck_6032_;
goto v_resetjp_6025_;
}
else
{
lean_inc(v_a_6024_);
lean_dec(v___x_6023_);
v___x_6026_ = lean_box(0);
v_isShared_6027_ = v_isSharedCheck_6032_;
goto v_resetjp_6025_;
}
v_resetjp_6025_:
{
if (lean_obj_tag(v_a_6024_) == 1)
{
lean_object* v_val_6028_; lean_object* v___x_6030_; 
lean_dec(v_a_5959_);
v_val_6028_ = lean_ctor_get(v_a_6024_, 0);
lean_inc(v_val_6028_);
lean_dec_ref_known(v_a_6024_, 1);
if (v_isShared_6027_ == 0)
{
lean_ctor_set(v___x_6026_, 0, v_val_6028_);
v___x_6030_ = v___x_6026_;
goto v_reusejp_6029_;
}
else
{
lean_object* v_reuseFailAlloc_6031_; 
v_reuseFailAlloc_6031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6031_, 0, v_val_6028_);
v___x_6030_ = v_reuseFailAlloc_6031_;
goto v_reusejp_6029_;
}
v_reusejp_6029_:
{
return v___x_6030_;
}
}
else
{
lean_del_object(v___x_6026_);
lean_dec(v_a_6024_);
goto v___jp_5960_;
}
}
}
else
{
lean_object* v_a_6033_; lean_object* v___x_6035_; uint8_t v_isShared_6036_; uint8_t v_isSharedCheck_6040_; 
lean_dec(v_a_5959_);
v_a_6033_ = lean_ctor_get(v___x_6023_, 0);
v_isSharedCheck_6040_ = !lean_is_exclusive(v___x_6023_);
if (v_isSharedCheck_6040_ == 0)
{
v___x_6035_ = v___x_6023_;
v_isShared_6036_ = v_isSharedCheck_6040_;
goto v_resetjp_6034_;
}
else
{
lean_inc(v_a_6033_);
lean_dec(v___x_6023_);
v___x_6035_ = lean_box(0);
v_isShared_6036_ = v_isSharedCheck_6040_;
goto v_resetjp_6034_;
}
v_resetjp_6034_:
{
lean_object* v___x_6038_; 
if (v_isShared_6036_ == 0)
{
v___x_6038_ = v___x_6035_;
goto v_reusejp_6037_;
}
else
{
lean_object* v_reuseFailAlloc_6039_; 
v_reuseFailAlloc_6039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6039_, 0, v_a_6033_);
v___x_6038_ = v_reuseFailAlloc_6039_;
goto v_reusejp_6037_;
}
v_reusejp_6037_:
{
return v___x_6038_;
}
}
}
}
else
{
goto v___jp_5960_;
}
v___jp_5960_:
{
lean_object* v_projectDir_5961_; lean_object* v_theoremNames_5962_; lean_object* v_definitionNames_5963_; lean_object* v_leanPrefix_5964_; lean_object* v_leanPath_5965_; lean_object* v_binPath_5966_; lean_object* v_whichSandbox_5967_; lean_object* v_whichLake_5968_; lean_object* v_lakeHome_5969_; lean_object* v_whichLean4Export_5970_; lean_object* v_whichLeanChecker_5971_; lean_object* v_whichEnvBin_5972_; lean_object* v_bundledKernels_5973_; lean_object* v_moduleStore_5974_; lean_object* v___x_5976_; uint8_t v_isShared_5977_; uint8_t v_isSharedCheck_6016_; 
v_projectDir_5961_ = lean_ctor_get(v_a_5959_, 0);
v_theoremNames_5962_ = lean_ctor_get(v_a_5959_, 3);
v_definitionNames_5963_ = lean_ctor_get(v_a_5959_, 4);
v_leanPrefix_5964_ = lean_ctor_get(v_a_5959_, 6);
v_leanPath_5965_ = lean_ctor_get(v_a_5959_, 7);
v_binPath_5966_ = lean_ctor_get(v_a_5959_, 8);
v_whichSandbox_5967_ = lean_ctor_get(v_a_5959_, 9);
v_whichLake_5968_ = lean_ctor_get(v_a_5959_, 10);
v_lakeHome_5969_ = lean_ctor_get(v_a_5959_, 11);
v_whichLean4Export_5970_ = lean_ctor_get(v_a_5959_, 12);
v_whichLeanChecker_5971_ = lean_ctor_get(v_a_5959_, 13);
v_whichEnvBin_5972_ = lean_ctor_get(v_a_5959_, 14);
v_bundledKernels_5973_ = lean_ctor_get(v_a_5959_, 16);
v_moduleStore_5974_ = lean_ctor_get(v_a_5959_, 17);
v_isSharedCheck_6016_ = !lean_is_exclusive(v_a_5959_);
if (v_isSharedCheck_6016_ == 0)
{
lean_object* v_unused_6017_; lean_object* v_unused_6018_; lean_object* v_unused_6019_; lean_object* v_unused_6020_; 
v_unused_6017_ = lean_ctor_get(v_a_5959_, 15);
lean_dec(v_unused_6017_);
v_unused_6018_ = lean_ctor_get(v_a_5959_, 5);
lean_dec(v_unused_6018_);
v_unused_6019_ = lean_ctor_get(v_a_5959_, 2);
lean_dec(v_unused_6019_);
v_unused_6020_ = lean_ctor_get(v_a_5959_, 1);
lean_dec(v_unused_6020_);
v___x_5976_ = v_a_5959_;
v_isShared_5977_ = v_isSharedCheck_6016_;
goto v_resetjp_5975_;
}
else
{
lean_inc(v_moduleStore_5974_);
lean_inc(v_bundledKernels_5973_);
lean_inc(v_whichEnvBin_5972_);
lean_inc(v_whichLeanChecker_5971_);
lean_inc(v_whichLean4Export_5970_);
lean_inc(v_lakeHome_5969_);
lean_inc(v_whichLake_5968_);
lean_inc(v_whichSandbox_5967_);
lean_inc(v_binPath_5966_);
lean_inc(v_leanPath_5965_);
lean_inc(v_leanPrefix_5964_);
lean_inc(v_definitionNames_5963_);
lean_inc(v_theoremNames_5962_);
lean_inc(v_projectDir_5961_);
lean_dec(v_a_5959_);
v___x_5976_ = lean_box(0);
v_isShared_5977_ = v_isSharedCheck_6016_;
goto v_resetjp_5975_;
}
v_resetjp_5975_:
{
lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5982_; 
v___x_5978_ = lean_box(1);
v___x_5979_ = lean_box(0);
v___x_5980_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms));
if (v_isShared_5977_ == 0)
{
lean_ctor_set(v___x_5976_, 15, v___x_5978_);
lean_ctor_set(v___x_5976_, 5, v___x_5980_);
lean_ctor_set(v___x_5976_, 2, v___x_5979_);
lean_ctor_set(v___x_5976_, 1, v___x_5979_);
v___x_5982_ = v___x_5976_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_6015_; 
v_reuseFailAlloc_6015_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_6015_, 0, v_projectDir_5961_);
lean_ctor_set(v_reuseFailAlloc_6015_, 1, v___x_5979_);
lean_ctor_set(v_reuseFailAlloc_6015_, 2, v___x_5979_);
lean_ctor_set(v_reuseFailAlloc_6015_, 3, v_theoremNames_5962_);
lean_ctor_set(v_reuseFailAlloc_6015_, 4, v_definitionNames_5963_);
lean_ctor_set(v_reuseFailAlloc_6015_, 5, v___x_5980_);
lean_ctor_set(v_reuseFailAlloc_6015_, 6, v_leanPrefix_5964_);
lean_ctor_set(v_reuseFailAlloc_6015_, 7, v_leanPath_5965_);
lean_ctor_set(v_reuseFailAlloc_6015_, 8, v_binPath_5966_);
lean_ctor_set(v_reuseFailAlloc_6015_, 9, v_whichSandbox_5967_);
lean_ctor_set(v_reuseFailAlloc_6015_, 10, v_whichLake_5968_);
lean_ctor_set(v_reuseFailAlloc_6015_, 11, v_lakeHome_5969_);
lean_ctor_set(v_reuseFailAlloc_6015_, 12, v_whichLean4Export_5970_);
lean_ctor_set(v_reuseFailAlloc_6015_, 13, v_whichLeanChecker_5971_);
lean_ctor_set(v_reuseFailAlloc_6015_, 14, v_whichEnvBin_5972_);
lean_ctor_set(v_reuseFailAlloc_6015_, 15, v___x_5978_);
lean_ctor_set(v_reuseFailAlloc_6015_, 16, v_bundledKernels_5973_);
lean_ctor_set(v_reuseFailAlloc_6015_, 17, v_moduleStore_5974_);
v___x_5982_ = v_reuseFailAlloc_6015_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
lean_object* v___x_5983_; 
v___x_5983_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v___x_5982_);
lean_dec_ref(v___x_5982_);
if (lean_obj_tag(v___x_5983_) == 0)
{
lean_object* v___x_5985_; uint8_t v_isShared_5986_; uint8_t v_isSharedCheck_5991_; 
v_isSharedCheck_5991_ = !lean_is_exclusive(v___x_5983_);
if (v_isSharedCheck_5991_ == 0)
{
lean_object* v_unused_5992_; 
v_unused_5992_ = lean_ctor_get(v___x_5983_, 0);
lean_dec(v_unused_5992_);
v___x_5985_ = v___x_5983_;
v_isShared_5986_ = v_isSharedCheck_5991_;
goto v_resetjp_5984_;
}
else
{
lean_dec(v___x_5983_);
v___x_5985_ = lean_box(0);
v_isShared_5986_ = v_isSharedCheck_5991_;
goto v_resetjp_5984_;
}
v_resetjp_5984_:
{
lean_object* v___x_5987_; lean_object* v___x_5989_; 
v___x_5987_ = l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1;
if (v_isShared_5986_ == 0)
{
lean_ctor_set(v___x_5985_, 0, v___x_5987_);
v___x_5989_ = v___x_5985_;
goto v_reusejp_5988_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v___x_5987_);
v___x_5989_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5988_;
}
v_reusejp_5988_:
{
return v___x_5989_;
}
}
}
else
{
lean_object* v_a_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; 
v_a_5993_ = lean_ctor_get(v___x_5983_, 0);
lean_inc(v_a_5993_);
lean_dec_ref_known(v___x_5983_, 1);
v___x_5994_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_5995_ = lean_io_error_to_string(v_a_5993_);
v___x_5996_ = lean_string_append(v___x_5994_, v___x_5995_);
lean_dec_ref(v___x_5995_);
v___x_5997_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_5996_);
if (lean_obj_tag(v___x_5997_) == 0)
{
lean_object* v___x_5999_; uint8_t v_isShared_6000_; uint8_t v_isSharedCheck_6005_; 
v_isSharedCheck_6005_ = !lean_is_exclusive(v___x_5997_);
if (v_isSharedCheck_6005_ == 0)
{
lean_object* v_unused_6006_; 
v_unused_6006_ = lean_ctor_get(v___x_5997_, 0);
lean_dec(v_unused_6006_);
v___x_5999_ = v___x_5997_;
v_isShared_6000_ = v_isSharedCheck_6005_;
goto v_resetjp_5998_;
}
else
{
lean_dec(v___x_5997_);
v___x_5999_ = lean_box(0);
v_isShared_6000_ = v_isSharedCheck_6005_;
goto v_resetjp_5998_;
}
v_resetjp_5998_:
{
lean_object* v___x_6001_; lean_object* v___x_6003_; 
v___x_6001_ = l_Lake_Check_runComparator___boxed__const__1;
if (v_isShared_6000_ == 0)
{
lean_ctor_set(v___x_5999_, 0, v___x_6001_);
v___x_6003_ = v___x_5999_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v___x_6001_);
v___x_6003_ = v_reuseFailAlloc_6004_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
return v___x_6003_;
}
}
}
else
{
lean_object* v_a_6007_; lean_object* v___x_6009_; uint8_t v_isShared_6010_; uint8_t v_isSharedCheck_6014_; 
v_a_6007_ = lean_ctor_get(v___x_5997_, 0);
v_isSharedCheck_6014_ = !lean_is_exclusive(v___x_5997_);
if (v_isSharedCheck_6014_ == 0)
{
v___x_6009_ = v___x_5997_;
v_isShared_6010_ = v_isSharedCheck_6014_;
goto v_resetjp_6008_;
}
else
{
lean_inc(v_a_6007_);
lean_dec(v___x_5997_);
v___x_6009_ = lean_box(0);
v_isShared_6010_ = v_isSharedCheck_6014_;
goto v_resetjp_6008_;
}
v_resetjp_6008_:
{
lean_object* v___x_6012_; 
if (v_isShared_6010_ == 0)
{
v___x_6012_ = v___x_6009_;
goto v_reusejp_6011_;
}
else
{
lean_object* v_reuseFailAlloc_6013_; 
v_reuseFailAlloc_6013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6013_, 0, v_a_6007_);
v___x_6012_ = v_reuseFailAlloc_6013_;
goto v_reusejp_6011_;
}
v_reusejp_6011_:
{
return v___x_6012_;
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
lean_object* v_a_6042_; lean_object* v___x_6044_; uint8_t v_isShared_6045_; uint8_t v_isSharedCheck_6049_; 
lean_dec(v_a_5949_);
v_a_6042_ = lean_ctor_get(v___x_5950_, 0);
v_isSharedCheck_6049_ = !lean_is_exclusive(v___x_5950_);
if (v_isSharedCheck_6049_ == 0)
{
v___x_6044_ = v___x_5950_;
v_isShared_6045_ = v_isSharedCheck_6049_;
goto v_resetjp_6043_;
}
else
{
lean_inc(v_a_6042_);
lean_dec(v___x_5950_);
v___x_6044_ = lean_box(0);
v_isShared_6045_ = v_isSharedCheck_6049_;
goto v_resetjp_6043_;
}
v_resetjp_6043_:
{
lean_object* v___x_6047_; 
if (v_isShared_6045_ == 0)
{
v___x_6047_ = v___x_6044_;
goto v_reusejp_6046_;
}
else
{
lean_object* v_reuseFailAlloc_6048_; 
v_reuseFailAlloc_6048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6048_, 0, v_a_6042_);
v___x_6047_ = v_reuseFailAlloc_6048_;
goto v_reusejp_6046_;
}
v_reusejp_6046_:
{
return v___x_6047_;
}
}
}
}
}
}
else
{
lean_object* v_a_6051_; lean_object* v___x_6053_; uint8_t v_isShared_6054_; uint8_t v_isSharedCheck_6058_; 
lean_dec_ref(v_projectDir_5929_);
lean_dec_ref(v_lean_5927_);
v_a_6051_ = lean_ctor_get(v___x_5940_, 0);
v_isSharedCheck_6058_ = !lean_is_exclusive(v___x_5940_);
if (v_isSharedCheck_6058_ == 0)
{
v___x_6053_ = v___x_5940_;
v_isShared_6054_ = v_isSharedCheck_6058_;
goto v_resetjp_6052_;
}
else
{
lean_inc(v_a_6051_);
lean_dec(v___x_5940_);
v___x_6053_ = lean_box(0);
v_isShared_6054_ = v_isSharedCheck_6058_;
goto v_resetjp_6052_;
}
v_resetjp_6052_:
{
lean_object* v___x_6056_; 
if (v_isShared_6054_ == 0)
{
v___x_6056_ = v___x_6053_;
goto v_reusejp_6055_;
}
else
{
lean_object* v_reuseFailAlloc_6057_; 
v_reuseFailAlloc_6057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6057_, 0, v_a_6051_);
v___x_6056_ = v_reuseFailAlloc_6057_;
goto v_reusejp_6055_;
}
v_reusejp_6055_:
{
return v___x_6056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runCheck___boxed(lean_object* v_fromExport_x3f_6059_, lean_object* v_paranoid_6060_, lean_object* v_inadvisablyNoSandbox_6061_, lean_object* v_lean_6062_, lean_object* v_lake_6063_, lean_object* v_projectDir_6064_, lean_object* v_a_6065_){
_start:
{
uint8_t v_paranoid_boxed_6066_; uint8_t v_inadvisablyNoSandbox_boxed_6067_; lean_object* v_res_6068_; 
v_paranoid_boxed_6066_ = lean_unbox(v_paranoid_6060_);
v_inadvisablyNoSandbox_boxed_6067_ = lean_unbox(v_inadvisablyNoSandbox_6061_);
v_res_6068_ = l_Lake_Check_runCheck(v_fromExport_x3f_6059_, v_paranoid_boxed_6066_, v_inadvisablyNoSandbox_boxed_6067_, v_lean_6062_, v_lake_6063_, v_projectDir_6064_);
lean_dec_ref(v_lake_6063_);
return v_res_6068_;
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
